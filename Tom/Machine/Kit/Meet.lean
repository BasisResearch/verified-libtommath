import Tom.Machine.Kit.Frame
import Tom.Machine.Kit.Call
import Tom.Machine.Img
import Tom.Machine.Api.Two
import Tom.Machine.Api.Un

/-!
# The meet: kinded witness bundles, standard contracts, one call rule

Stated over the existing terms (`At`, `Frm`, `Sound`, `Iv`, `MpAt`, `Ram`, `Img`,
`writeLog`); no new representation of memory.

* **Kinds** (`Kind`): what a region holds — `ram` (untracked RAM: the callees'
  stack area), `frz m0` (RAM holding `m0`'s bytes: the function's own frame,
  read back through its write log), `code` (`Img`), `mpS p dp a` (an `mp_int`
  struct: the header fields and geometry, `Hdr`), `mpD dp n f` (a digit array,
  `Dig`). `Kind.Fits` (footprint inside the region), `Kind.Wit` (the witness).
* **Bundles** `Bundle ρ κ m := ∀ r, Fits ∧ Wit`, built once from a contract's
  Pre (`Two.bundle`, `Un.bundle`, `Split.bundle`); `Bundle.keep` along a `Frm`
  (`Misses` decided on names), `Bundle.pull σ` (a callee's bundle by renaming,
  free), `St.push` (a callee's new witnesses and frame back along `σ`).
* **The state** `St ρ isW W κ m M`: sound layout, the bundle at `M`, the frame
  since the entry. Stores into the own frame: `St.store`.
* **Contracts** (`Contract`): entry, argument/result registers, regions,
  layout, kinds before (`kind`) and after (`out`), write set, scalar residue
  `Res`, arithmetic post `Q`. **`call_std`** (a `jal` site: fetch, target,
  argument and saved registers decided by computation) and **`tail_std`**.
* **Projections** (`St.ram`, `St.hdr`, `St.dig`, `St.frz` + `rd_log`,
  `St.disj`) and the tactic **`facts h`**, which assembles a segment's fact
  record from them; `iv_norm`/`iv_omega` normalise interval arithmetic by
  computing the layout.
* **The stack split** (`Split`): a contract's stack region cut into the own
  frame (`none`) and the callees' area.

## How to write a function (the route; models `Fn/MpMod2dMain.lean`, `Fn/MpMul2dMain.lean`, `Fn/MpRshdMain.lean`, `Fn/MpCopyMain.lean`)

1. **Regions.** The contract's family (`Api/Un`, `Api/Two`, …) with its stack
   cut by `Split` into our frame `none` (`f` = our frame size) and the callees'
   area `some .stk`. The entry state, once: `St.two`/`St.un` from the Pre's
   fields (`hP.ra_ hP.ga … hP.img hP.lay`). Put the scalar residue in the
   context once (`sp_ge`, `sp_al`, `used_le`, `alloc_lt`, the room).
2. **Entry.** `Triple.lmap (fun _ h => h.sub (L' := entry1 …) (K' := v.keepR1) rfl rfl)`.
3. **Segments**, one `refine` each, in continuation form: `St.seq0` (no
   stores), `h.seqW none rfl seg fun M h => ?_` (stores into our frame),
   `h.seqD r rfl seg hi hv …` (one digit), `St.seqU`/`seqUS`/`seqH` (header
   fields). Every fact record a segment asks for is `(by facts h)`; its code
   is `(h.img (some .code)).mpX` (a local `cd`).
4. **Calls.** `refine call_std C ⟨params⟩ σ h (cd h) w imm ret hres fun x M hq h => ?_`
   (`w`, `imm` from the disassembly, `ret = pc + 4`; `hres` the residue, often
   `⟨by omega, …⟩`). A tail call: `tail_std C ⟨params⟩ σ (h.forget none rfl)
   hres hra fun x M cf hq h hat => ⟨…⟩`. `σ` renames the callee's regions into
   ours; our kinds follow the callee's writes (`Kind.push`) with no step of
   ours. A callee whose contract is missing gets a `Contract` instance in
   `Api/StdLib.lean` (leaves) or `Api/Std.lean`.
5. **Loops** over an `mp_int`'s digits: the invariant `∃ M, St … (Kind.set κ r
   (.mpD dp n (ovl g old i))) m M ∧ At pc (L i) M …` and `Triple.countup_from`;
   each iteration is `St.seqOvl`, its kinds renormalised by `Kind.set_set`.
6. **Joins and the result.** Re-abstract an `mp_int` by `St.setMp`, normalise
   the kinds by `St.congrK (by intro r; rcases r with … <;> rfl)` so that the
   paths meet in one lemma; the result is `h.mpAt rS rD rfl rfl` and the frame
   `h.unsplit (by simp [Two.lay])`.
-/
namespace Tom.Machine

open Vsa.Sim

/-! ## Kinds and witnesses -/

/-- What a region holds. -/
inductive Kind
  /-- RAM whose contents nobody tracks (the callees' stack area, a scratch buffer). -/
  | ram
  /-- RAM holding the bytes of `m0` (a function's own frame, by its write log). -/
  | frz (m0 : Mem)
  /-- The text section. -/
  | code
  /-- An `mp_int`'s struct at `p`, digits at `dp`, value `a` (its header fields). -/
  | mpS (p dp : Nat) (a : MpInt)
  /-- A digit array: `n` digits `f` at `dp`. -/
  | mpD (dp n : Nat) (f : Nat → Nat)

/-- The kind's footprint lies in the region. -/
def Kind.Fits : Kind → Iv → Prop
  | .ram, _ | .frz _, _ => True
  | .code, I => textIv.Sub I
  | .mpS p _ _, I => Iv.Sub ⟨p, 24⟩ I
  | .mpD dp n _, I => Iv.Sub ⟨dp, 4 * n⟩ I

/-- An `mp_int` header: the four fields and the geometry. -/
structure Hdr (m : Mem) (p dp : Nat) (a : MpInt) : Prop where
  used : bytesT4 m p = BitVec.ofNat 32 a.used
  alloc : bytesT4 m (p + 4) = BitVec.ofNat 32 a.alloc
  sign : bytesT4 m (p + 8) = BitVec.ofNat 32 a.sign
  dpv : bytesT8 m (p + 16) = BitVec.ofNat 64 dp
  geom : MpGeom p dp a.alloc

/-- A digit array in RAM. -/
structure Dig (m : Mem) (dp n : Nat) (f : Nat → Nat) : Prop where
  ram : Ram dp (4 * n)
  al : dp % 4 = 0
  arr : ArrAt m dp n f

/-- The witness a region of kind `k` at `I` carries in `m`. -/
def Kind.Wit : Kind → Iv → Mem → Prop
  | .ram, I, _ => Ram I.base I.len
  | .frz m0, I, m => Ram I.base I.len ∧ ∀ x, I.In x → m[x]? = m0[x]?
  | .code, _, m => Img m
  | .mpS p dp a, _, m => Hdr m p dp a
  | .mpD dp n f, _, m => Dig m dp n f

/-- `k` is RAM nobody tracks. -/
def Kind.isRam : Kind → Bool
  | .ram => true
  | _ => false

theorem Hdr.of_mpAt {m : Mem} {p dp : Nat} {a : MpInt} (h : MpAt m p dp a) (g : MpGeom p dp a.alloc) :
    Hdr m p dp a :=
  { used := by simpa [Layout.offUsed] using h.used, alloc := by simpa [Layout.offAlloc] using h.alloc
    sign := by simpa [Layout.offSign] using h.sign, dpv := by simpa [Layout.offDp] using h.dpv, geom := g }

theorem Dig.of_mpAt {m : Mem} {p dp : Nat} {a : MpInt} (h : MpAt m p dp a) (g : MpGeom p dp a.alloc) :
    Dig m dp a.alloc a.digit :=
  { ram := by simpa [Layout.sizeofDigit] using g.ds, al := g.ds_al, arr := h.arr }

theorem Hdr.mpAt {m : Mem} {p dp : Nat} {a : MpInt} (h : Hdr m p dp a) (d : Dig m dp a.alloc a.digit) :
    MpAt m p dp a :=
  { used := by simpa [Layout.offUsed] using h.used, alloc := by simpa [Layout.offAlloc] using h.alloc
    sign := by simpa [Layout.offSign] using h.sign, dpv := by simpa [Layout.offDp] using h.dpv
    digits := fun i hi => by simpa [Layout.sizeofDigit] using d.arr i hi }

section
variable {ι : Type} {ρ : ι → Iv}

/-- **The frame rule for witnesses**: a witness reads only its region. -/
theorem Kind.reads {r : ι} : ∀ {k : Kind}, k.Fits (ρ r) → Reads ρ [r] (k.Wit (ρ r))
  | .ram, _ => fun _ _ _ h => h
  | .frz _, _ => fun _ _ hs h => ⟨h.1, fun x hx => (hs x (Or.inl hx)).trans (h.2 x hx)⟩
  | .code, hf => Img.reads hf
  | .mpS p dp a, hf => Reads.of_sub hf fun M M' hs0 h =>
      have hs : ∀ x, p ≤ x → x < p + 24 → M'[x]? = M[x]? := hs0
      have h4 : ∀ o, o + 4 ≤ 24 → bytesT4 M' (p + o) = bytesT4 M (p + o) :=
        fun _ ho => bytesT4_congr fun x h1 h2 => hs x (by omega) (by omega)
      { used := by rw [show p = p + 0 from rfl, h4 0 (by decide)]; exact h.used
        alloc := by rw [h4 4 (by decide)]; exact h.alloc
        sign := by rw [h4 8 (by decide)]; exact h.sign
        dpv := by rw [bytesT8_congr fun x h1 h2 => hs x (by omega) (by omega)]; exact h.dpv
        geom := h.geom }
  | .mpD dp n f, hf => fun M M' hs h => { h with arr := ArrAt.reads hf M M' hs h.arr }

/-! ## Bundles -/

/-- **A witness bundle**: every region's witness, by its kind. -/
def Bundle (ρ : ι → Iv) (κ : ι → Kind) (m : Mem) : Prop := ∀ r, (κ r).Fits (ρ r) ∧ (κ r).Wit (ρ r) m

variable [DecidableEq ι] {isW : ι → Bool}

/-- **Keep** an unwritten region's witness along a frame (`Misses` decided on names). -/
theorem Bundle.keep {κ : ι → Kind} {m M : Mem} {ws : List ι} (hB : Bundle ρ κ m) (hS : Sound ρ isW)
    (hF : Frm ρ ws m M) (r : ι) (hm : Misses isW [r] ws = true := by decide) :
    (κ r).Fits (ρ r) ∧ (κ r).Wit (ρ r) M :=
  ⟨(hB r).1, hF.keep hS (Kind.reads (hB r).1) (hB r).2 hm⟩

/-- `ws` misses every name outside it, when all of `ws` is written. -/
theorem misses_of_not_mem {ws : List ι} (hw : ws.all isW = true) {r : ι} (hr : r ∉ ws) :
    Misses isW [r] ws = true := by
  simp only [Misses, List.all_cons, List.all_nil, Bool.and_true, List.all_eq_true]
  intro w hw'
  have : isW w = true := List.all_eq_true.1 hw w hw'
  simp only [Sep, this, Bool.or_true, Bool.and_true, Bool.not_eq_true', decide_eq_false_iff_not]
  exact fun h => hr (h ▸ hw')

/-- One region's kind changed. -/
def Kind.set (κ : ι → Kind) (r : ι) (k : Kind) : ι → Kind := fun r' => if r' = r then k else κ r'

end

/-! ## The state of a function: sound layout, witnesses at `M`, frame since the entry -/

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι}

/-- At memory `M`: the layout is sound, every region has its witness, and `M`
differs from the entry memory `m` only in the written names `W`. -/
structure St (ρ : ι → Iv) (isW : ι → Bool) (W : List ι) (κ : ι → Kind) (m M : Mem) : Prop where
  sound : Sound ρ isW
  wit : Bundle ρ κ M
  frm : Frm ρ W m M

/-- **The step rule**: a frame in `ws ⊆ W` (all written), new witnesses on `ws`,
the old ones elsewhere. -/
theorem St.step {κ κ' : ι → Kind} {m M M' : Mem} {ws : List ι} (h : St ρ isW W κ m M)
    (hF : Frm ρ ws M M') (hw : ws.all isW = true) (hsub : SubN ws W = true)
    (hnew : ∀ r ∈ ws, (κ' r).Fits (ρ r) ∧ (κ' r).Wit (ρ r) M') (hold : ∀ r, r ∉ ws → κ' r = κ r) :
    St ρ isW W κ' m M' :=
  { sound := h.sound
    wit := fun r => by
      by_cases hr : r ∈ ws
      · exact hnew r hr
      · rw [hold r hr]; exact h.wit.keep h.sound hF r (misses_of_not_mem hw hr)
    frm := Frm.step h.frm hF hsub }

/-- A write log inside `ρ r`. -/
theorem logIn_out {r : ι} : ∀ {log : List WEntry} {x : Nat}, LogIn ρ r log → ¬ (ρ r).In x → OutL log x
  | [], _, _, _ => trivial
  | e :: _, _, h, hx => ⟨by have := h.1; unfold Iv.Sub Iv.In at *; simp only at *; omega, logIn_out h.2 hx⟩

theorem getElem?_insert_congr {M M' : Mem} {x k : Nat} {v : BitVec 8} (h : M[x]? = M'[x]?) :
    (M.insert k v)[x]? = (M'.insert k v)[x]? := by
  simp only [Std.ExtHashMap.getElem?_insert, h]

theorem applyW_congr {M M' : Mem} {x : Nat} (h : M[x]? = M'[x]?) (e : WEntry) :
    (applyW M e)[x]? = (applyW M' e)[x]? := by
  obtain ⟨a, w, d⟩ := e
  unfold applyW
  split <;> simp only [writeMap4, writeMap8, Std.ExtHashMap.getElem?_insert, h]

theorem writeLog_congr_at {x : Nat} : ∀ {M M' : Mem} (log : List WEntry), M[x]? = M'[x]? →
    (writeLog M log)[x]? = (writeLog M' log)[x]?
  | _, _, [], h => h
  | _, _, e :: log, h => writeLog_congr_at (M := applyW _ e) (M' := applyW _ e) log (applyW_congr h e)

/-- **A store into the function's own frame** (`frz`): the snapshot takes the log. -/
theorem St.store {κ : ι → Kind} {m M m0 : Mem} {r : ι} {log : List WEntry} (h : St ρ isW W κ m M)
    (hlog : LogIn ρ r log) (hk : κ r = .frz m0 := by rfl) (hw : isW r = true := by decide)
    (hW : SubN [r] W = true := by decide) :
    St ρ isW W (Kind.set κ r (.frz (writeLog m0 log))) m (writeLog M log) :=
  h.step (Frm.store hlog) (by simp [hw]) hW
    (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      have hw0 := (h.wit r').2; rw [hk] at hw0
      simp only [Kind.set, if_true, Kind.Fits, Kind.Wit, true_and]
      exact ⟨hw0.1, fun x hx => writeLog_congr_at log (hw0.2 x hx)⟩)
    (fun r' hr' => by simp only [List.mem_singleton] at hr'; simp [Kind.set, hr'])

theorem St.img {κ : ι → Kind} {m M : Mem} (h : St ρ isW W κ m M) (r : ι) (hk : κ r = .code := by rfl) :
    Img M := by have := (h.wit r).2; rw [hk] at this; exact this

end


open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic

/-- Every pin of `L'` is `X`'s first hit (closed by `rfl`: the keys are literals,
the values are compared as terms). -/
def SubR (L' X : GRegs) : Prop := L'.map (fun q => lookupG q.1 X) = L'.map (fun q => some q.2)

theorem SubR.gholds {σ : Vsa.Machine.MState} {X : GRegs} (hX : GHolds σ X) :
    ∀ {L' : GRegs}, SubR L' X → GHolds σ L'
  | [], _ => trivial
  | (_, _) :: _, h => by
    simp only [SubR, List.map_cons, List.cons.injEq] at h
    exact ⟨gholds_lookup X hX h.1, SubR.gholds hX h.2⟩

/-- Reshape an `At` (`SubR` by `rfl`). -/
theorem At.sub {pc : BitVec 64} {L L' K K' : GRegs} {m : Mem} {outp : Array String} {c : Vsa.Machine.Config}
    (h : At pc L m K outp c) (hL : SubR L' (L ++ K)) (hK : SubR K' (L ++ K)) : At pc L' m K' outp c :=
  have hall : GHolds c.σ (L ++ K) := gholds_append.2 ⟨h.regs, h.keep⟩
  { h with regs := hL.gholds hall, keep := hK.gholds hall }

/-- Reshape the pinned registers only. -/
theorem At.subL {pc : BitVec 64} {L0 L K : GRegs} {m : Mem} {outp : Array String} {c : Vsa.Machine.Config}
    (h : At pc L0 m K outp c) (hL : SubR L (L0 ++ K)) : At pc L m K outp c :=
  { h with regs := hL.gholds (gholds_append.2 ⟨h.regs, h.keep⟩) }

/-- The keep-set joins the pins. -/
theorem At.cat {pc : BitVec 64} {L K K' : GRegs} {m : Mem} {outp : Array String} {c : Vsa.Machine.Config}
    (h : At pc L m K outp c) (hK : SubR K' (L ++ K)) : At pc (L ++ K) m K' outp c :=
  { h with regs := gholds_append.2 ⟨h.regs, h.keep⟩, keep := hK.gholds (gholds_append.2 ⟨h.regs, h.keep⟩) }

/-- A precondition reshaped to the registers a segment names (`SubR` by `rfl`). -/
theorem _root_.Vsa.Logic.Triple.pre {pc : BitVec 64} {L0 L K : GRegs} {m : Mem} {outp : Array String}
    {Q : Vsa.Machine.Config → Prop} (h : Triple (At pc L m K outp) Q) (hL : SubR L (L0 ++ K) := by exact rfl) :
    Triple (At pc L0 m K outp) Q :=
  Triple.lmap (fun _ hc => hc.subL hL) h


/-! ## Moving witnesses -/

theorem Ram.sub {a n b k : Nat} (h : Ram a n) (h1 : a ≤ b) (h2 : b + k ≤ a + n) : Ram b k :=
  ⟨by have := h.lo_ge; omega, by have := h.hi_le; omega, by have := h.off; omega⟩

/-- Witnesses restrict to sub-intervals. -/
theorem Kind.Wit.sub {I J : Iv} {m : Mem} : ∀ {k : Kind}, k.Wit I m → J.Sub I → k.Wit J m
  | .ram, h, hs => Ram.sub h hs.1 hs.2
  | .frz _, h, hs => ⟨Ram.sub h.1 hs.1 hs.2, fun x hx => h.2 x ⟨by have := hs.1; have := hx.1; omega,
      by have := hs.2; have := hx.2; omega⟩⟩
  | .code, h, _ | .mpS .., h, _ | .mpD .., h, _ => h

/-- A kind whose witness does not mention its interval. -/
def Kind.indep : Kind → Bool
  | .code | .mpS .. | .mpD .. => true
  | _ => false

theorem Kind.Wit.indep {I J : Iv} {m : Mem} : ∀ {k : Kind}, k.indep = true → k.Wit I m → k.Wit J m
  | .code, _, h | .mpS .., _, h | .mpD .., _, h => h

theorem Kind.Fits.mono {I J : Iv} : ∀ {k : Kind}, k.Fits J → J.Sub I → k.Fits I
  | .ram, _, _ | .frz _, _, _ => trivial
  | .code, h, hs | .mpS .., h, hs | .mpD .., h, hs => Iv.Sub.trans h hs

theorem Kind.eq_ram : ∀ {k : Kind}, k.isRam = true → k = .ram
  | .ram, _ => rfl

section
variable {ι κR : Type} [DecidableEq ι] [DecidableEq κR] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι}

/-- **The callee's bundle by renaming** (free: `σ`, the sub-intervals, kinds equal). -/
theorem Bundle.pull {κ : ι → Kind} {m : Mem} {ρc : κR → Iv} {κc : κR → Kind} (σ : κR → ι)
    (hB : Bundle ρ κ m) (hsub : ∀ k, (ρc k).Sub (ρ (σ k))) (hk : ∀ k, κc k = κ (σ k))
    (hfit : ∀ k, (κc k).Fits (ρc k)) : Bundle ρc κc m :=
  fun k => ⟨hfit k, by rw [hk]; exact (hB (σ k)).2.sub (hsub k)⟩

/-- The caller's kinds after a callee wrote `wsc`: the callee's new kinds on
their images (RAM stays RAM), the old ones elsewhere. -/
def Kind.push (σ : κR → ι) (wsc : List κR) (κ : ι → Kind) (κc : κR → Kind) (r : ι) : Kind :=
  match wsc.find? (fun k => decide (σ k = r)) with
  | some k => if (κc k).isRam then κ r else κc k
  | none => κ r

theorem find?_none_of_not_mem {σ : κR → ι} {wsc : List κR} {r : ι} (hr : r ∉ wsc.map σ) :
    wsc.find? (fun k => decide (σ k = r)) = none :=
  List.find?_eq_none.2 fun k hk h => hr (List.mem_map.2 ⟨k, hk, of_decide_eq_true h⟩)

/-- **The callee's frame and witnesses, in the caller's names.** -/
theorem St.push {κ : ι → Kind} {m M M' : Mem} {ρc : κR → Iv} {κc : κR → Kind} {wsc : List κR}
    (h : St ρ isW W κ m M) (σ : κR → ι) (hsub : ∀ k, (ρc k).Sub (ρ (σ k)))
    (hF : Frm ρc wsc M M') (hBc : Bundle ρc κc M')
    (hram : ∀ k ∈ wsc, (κc k).isRam = true → (κ (σ k)).isRam = true)
    (hind : ∀ k ∈ wsc, (κc k).isRam = false → (κc k).indep = true)
    (hw : (wsc.map σ).all isW = true) (hW : SubN (wsc.map σ) W = true) :
    St ρ isW W (Kind.push σ wsc κ κc) m M' :=
  h.step (Frm.push σ hsub hF) hw hW
    (fun r hr => by
      unfold Kind.push
      cases hf : wsc.find? (fun k => decide (σ k = r)) with
      | none => exact absurd hr (by
          obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
          have := List.find?_eq_none.1 hf k hk; simp at this)
      | some k =>
        have hk := List.mem_of_find?_eq_some hf
        have hσ : σ k = r := of_decide_eq_true (List.find?_some (p := fun k => decide (σ k = r)) hf)
        subst hσ
        dsimp only
        cases hr' : (κc k).isRam
        · simp only [Bool.false_eq_true, if_false]
          exact ⟨(hBc k).1.mono (hsub k), (hBc k).2.indep (hind k hk hr')⟩
        · simp only [if_true]
          have he := Kind.eq_ram (hram k hk hr')
          rw [he]; exact ⟨trivial, by have := (h.wit (σ k)).2; rw [he] at this; exact this⟩)
    (fun r hr => by unfold Kind.push; rw [find?_none_of_not_mem hr])

end

/-! ## Splitting the stack region: the function's own frame, its callees' area below -/

section
variable {R : Type} [DecidableEq R] {ρ : R → Iv} {isW : R → Bool} {s : R} {f : Nat}

/-- The top `f` bytes of the stack region `s` as the own frame (`none`). -/
def Split.lay (ρ : R → Iv) (s : R) (f : Nat) : Option R → Iv
  | none => ⟨(ρ s).base + (ρ s).len - f, f⟩
  | some r => if r = s then ⟨(ρ s).base, (ρ s).len - f⟩ else ρ r

def Split.wr (isW : R → Bool) : Option R → Bool
  | none => true
  | some r => isW r

/-- The own frame holds `m0`'s bytes. -/
def Split.kind (κ : R → Kind) (m0 : Mem) : Option R → Kind
  | none => .frz m0
  | some r => κ r

theorem Split.sub_none (hf : f ≤ (ρ s).len) : (Split.lay ρ s f none).Sub (ρ s) := by
  simp only [Split.lay, Iv.Sub]; omega

theorem Split.sub_some (r : R) : (Split.lay ρ s f (some r)).Sub (ρ r) := by
  simp only [Split.lay]; split
  · subst r; simp only [Iv.Sub]; omega
  · exact Iv.sub_self _

theorem Split.sound (hS : Sound ρ isW) (hs : isW s = true) (hf : f ≤ (ρ s).len) :
    Sound (Split.lay ρ s f) (Split.wr isW) := by
  have own : ∀ t, Sep (Split.wr isW) none (some t) = true → (Split.lay ρ s f none).Disj (Split.lay ρ s f (some t)) := by
    intro t _
    by_cases ht : t = s
    · subst ht; simp only [Split.lay, if_true, Iv.Disj, Disj]; omega
    · exact hS.sub (Split.sub_none hf) (Split.sub_some t) (by simp [Sep, hs, Ne.symm ht])
  intro r t h
  cases r <;> cases t
  · simp [Sep] at h
  · exact own _ h
  · exact Disj.symm (own _ (by simp [Sep, Split.wr]))
  · rename_i r t
    exact hS.sub (Split.sub_some r) (Split.sub_some t) (by simpa [Sep, Split.wr] using h)

theorem Split.unframe {ws : List (Option R)} {m M : Mem} (hf : f ≤ (ρ s).len) (h : Frm (Split.lay ρ s f) ws m M) :
    Frm ρ (ws.map (fun o => o.getD s)) m M :=
  Frm.push _ (fun o => by cases o; exact Split.sub_none hf; exact Split.sub_some _) h

theorem Split.bundle {κ : R → Kind} {m : Mem} (hB : Bundle ρ κ m) (hk : κ s = .ram) (hf : f ≤ (ρ s).len) :
    Bundle (Split.lay ρ s f) (Split.kind κ m) m
  | none => ⟨trivial, by
      have := (hB s).2; rw [hk] at this
      exact ⟨Kind.Wit.sub (k := .ram) this (Split.sub_none hf), fun _ _ => rfl⟩⟩
  | some r => by
      by_cases hr : r = s
      · subst hr
        exact ⟨by simp only [Split.kind, hk, Kind.Fits], by
          simp only [Split.kind]; exact (hB r).2.sub (Split.sub_some r)⟩
      · simp only [Split.kind, Split.lay, if_neg hr]; exact hB r

end

/-! ## The standard region families' kinds -/

def Two.kind (pa adp pb bdp : Nat) (a b : MpInt) : Api.Two.R → Kind
  | .stk => .ram
  | .aS => .mpS pa adp a
  | .aD => .mpD adp a.alloc a.digit
  | .bS => .mpS pb bdp b
  | .bD => .mpD bdp b.alloc b.digit
  | .code => .code

theorem Two.bundle {m : Mem} {F sp pa adp pb bdp : Nat} {a b : MpInt} (hra : MpAt m pa adp a)
    (hga : MpGeom pa adp a.alloc) (hrb : MpAt m pb bdp b) (hgb : MpGeom pb bdp b.alloc) (hrs : Ram (sp - F) F)
    (himg : Img m) : Bundle (Api.Two.lay F sp pa adp pb bdp a b) (Two.kind pa adp pb bdp a b) m
  | .stk => ⟨trivial, hrs⟩
  | .aS => ⟨Iv.sub_self _, Hdr.of_mpAt hra hga⟩
  | .aD => ⟨Iv.sub_self _, Dig.of_mpAt hra hga⟩
  | .bS => ⟨Iv.sub_self _, Hdr.of_mpAt hrb hgb⟩
  | .bD => ⟨Iv.sub_self _, Dig.of_mpAt hrb hgb⟩
  | .code => ⟨Iv.sub_self _, himg⟩

def Un.kind (pa adp : Nat) (a : MpInt) : Api.Un.R → Kind
  | .stk => .ram
  | .aS => .mpS pa adp a
  | .aD => .mpD adp a.alloc a.digit
  | .code => .code

theorem Un.bundle {m : Mem} {F sp pa adp : Nat} {a : MpInt} (hra : MpAt m pa adp a)
    (hga : MpGeom pa adp a.alloc) (hrs : Ram (sp - F) F) (himg : Img m) :
    Bundle (Api.Un.lay F sp pa adp a) (Un.kind pa adp a) m
  | .stk => ⟨trivial, hrs⟩
  | .aS => ⟨Iv.sub_self _, Hdr.of_mpAt hra hga⟩
  | .aD => ⟨Iv.sub_self _, Dig.of_mpAt hra hga⟩
  | .code => ⟨Iv.sub_self _, himg⟩


/-! ## Projections: one rule per atom kind -/


/-- The RAM a kind certifies. -/
def Kind.ramI : Kind → Iv → Iv
  | .ram, I | .frz _, I => I
  | .code, _ => ⟨0x80000000, 0⟩
  | .mpS p _ _, _ => ⟨p, 24⟩
  | .mpD dp n _, _ => ⟨dp, 4 * n⟩

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind} {m M : Mem}

theorem St.ram (h : St ρ isW W κ m M) (r : ι) : Ram ((κ r).ramI (ρ r)).base ((κ r).ramI (ρ r)).len := by
  have hw := (h.wit r).2
  generalize κ r = k at hw ⊢
  cases k with
  | ram => exact hw
  | frz _ => exact hw.1
  | code => show Ram 0x80000000 0; exact ⟨by decide, by decide, by unfold tohostAddr; decide⟩
  | mpS p dp a => show Ram p 24; simpa [Layout.sizeofMpInt] using hw.geom.st
  | mpD dp n f => exact hw.ram

theorem St.hdr (h : St ρ isW W κ m M) (r : ι) {p dp : Nat} {a : MpInt} (hk : κ r = .mpS p dp a) :
    Hdr M p dp a := by have := (h.wit r).2; rw [hk] at this; exact this

theorem St.dig (h : St ρ isW W κ m M) (r : ι) {dp n : Nat} {f : Nat → Nat} (hk : κ r = .mpD dp n f) :
    Dig M dp n f := by have := (h.wit r).2; rw [hk] at this; exact this

theorem St.mpAt (h : St ρ isW W κ m M) (rS rD : ι) {p dp : Nat} {a : MpInt} (hS : κ rS = .mpS p dp a)
    (hD : κ rD = .mpD dp a.alloc a.digit) : MpAt M p dp a := (h.hdr rS hS).mpAt (h.dig rD hD)

theorem St.frz (h : St ρ isW W κ m M) (r : ι) {m0 : Mem} (hk : κ r = .frz m0) {a : Nat}
    (hs : Iv.Sub ⟨a, 8⟩ (ρ r)) : bytesT8 M a = bytesT8 m0 a := by
  have hw := (h.wit r).2; rw [hk] at hw
  exact bytesT8_congr fun x h1 h2 => hw.2 x ⟨by have := hs.1; simp only at this; omega,
    by have := hs.2; simp only at this; omega⟩

theorem St.disj (h : St ρ isW W κ m M) (r t : ι) (hsep : Sep isW r t = true := by decide) :
    Disj (ρ r).base (ρ r).len (ρ t).base (ρ t).len := h.sound r t hsep

end

theorem bytesT8_log' (pre post : List WEntry) (m : Mem) (a : Nat) (v : BitVec 64) (hout : OutLRange post a 8) :
    bytesT8 (writeLog m (pre ++ (a, 8, v) :: post)) a = v := by
  rw [writeLog_append]; exact bytesT8_log ((a, 8, v) :: post) _ 0 a v rfl hout

theorem bytesT8_log'' (L pre post : List WEntry) (m : Mem) (a : Nat) (v : BitVec 64)
    (hL : L = pre ++ (a, 8, v) :: post) (hout : OutLRange post a 8) : bytesT8 (writeLog m L) a = v := by
  subst hL; exact bytesT8_log' pre post m a v hout

/-- A class of closed region types: their names, for the projection tactics. -/
class Names (ι : Type) where
  all : List ι

instance : Names Api.Two.R := ⟨[.stk, .aS, .aD, .bS, .bD, .code]⟩
instance : Names Api.Un.R := ⟨[.stk, .aS, .aD, .code]⟩
instance {R : Type} [Names R] : Names (Option R) := ⟨none :: (Names.all : List R).map some⟩

section Tac
open Lean Meta Elab Tactic

/-- `(ρ r).base` by computation. -/
dsimproc_decl ivBase (Iv.base _) := fun e => do
  let_expr Iv.base x := e | return .continue
  let x ← whnfD x
  let_expr Iv.mk b _ := x | return .continue
  return .visit b

/-- `(ρ r).len` by computation. -/
dsimproc_decl ivLen (Iv.len _) := fun e => do
  let_expr Iv.len x := e | return .continue
  let x ← whnfD x
  let_expr Iv.mk _ l := x | return .continue
  return .visit l

/-- The literal-valued `Nat` constants (code bases, layout offsets) in `e`. -/
def natConsts (e : Expr) : MetaM (Array Name) := do
  let mut out := #[]
  for c in e.getUsedConstants do
    let pre := c.getPrefix
    if pre == `Tom.Machine.Code || pre == `Tom.Layout || pre == `Vsa.Sim then
      if let some info := (← getEnv).find? c then
        if info.type == mkConst ``Nat then out := out.push c
  return out

/-- Normalise interval facts to linear arithmetic: `Iv.Sub`/`Iv.Disj`/`Disj`,
the layout's intervals by computation, code bases and offsets to literals. -/
def ivNormAt (loc : Option FVarId) : TacticM Unit := withMainContext do
  let e ← match loc with
    | some h => instantiateMVars (← h.getType)
    | none => instantiateMVars (← getMainTarget)
  let cs ← natConsts e
  let lems ← (cs ++ #[``Iv.Sub, ``Iv.In, ``Iv.Disj, ``Tom.Machine.Disj, ``Tom.Machine.textIv]).mapM
    fun c => `(Lean.Parser.Tactic.simpLemma| $(mkIdent c):ident)
  let lems := lems ++ #[← `(Lean.Parser.Tactic.simpLemma| ivBase), ← `(Lean.Parser.Tactic.simpLemma| ivLen)]
  match loc with
  | some h =>
    let hs ← `(term| $(mkIdent (← h.getUserName)))
    evalTactic (← `(tactic| try simp only [$lems,*] at $(⟨hs.raw⟩):ident))
  | none => evalTactic (← `(tactic| try simp only [$lems,*]))

elab "iv_norm" : tactic => do ivNormAt none; ivNormAt none
elab "iv_omega" : tactic => do ivNormAt none; ivNormAt none; evalTactic (← `(tactic| omega))

/-- The elements of a literal list (by computation). -/
partial def listSpine (e : Expr) : MetaM (List Expr) := do
  let e ← whnfD e
  match e.getAppFnArgs with
  | (``List.cons, #[_, h, t]) => return h :: (← listSpine t)
  | (``List.nil, _) => return []
  | _ => throwError "listSpine: not a literal list {e}"

/-- `m0 = writeLog (… (writeLog base l₁) …) lₙ`: the base and the concatenated log. -/
partial def logSpine (e : Expr) : MetaM (Expr × List Expr) := do
  let e ← whnfR e
  match e.getAppFnArgs with
  | (``Vsa.Sim.writeLog, #[b, l]) => do
      let (b', l0) ← logSpine b
      return (b', l0 ++ (← listSpine l))
  | _ => return (e, [])

def tryTac (t : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  try
    Term.withoutErrToSorry t
    if (← getUnsolvedGoals).isEmpty then return true else s.restore; return false
  catch _ => s.restore; return false

/-- `bytesT8 m0 a = v` with `m0` a nest of write logs: the last writer of `a`. -/
def rdLog : TacticM Unit := withMainContext do
  evalTactic (← `(tactic| try simp only [← Vsa.Sim.writeLog_append]))
  withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let_expr Eq _ lhs v := tgt | throwError "rd_log: not an equation"
  let_expr Vsa.Sim.bytesT8 m0 a := lhs | throwError "rd_log: not a bytesT8 read"
  let m0 ← whnfR m0
  let_expr Vsa.Sim.writeLog base L := m0 | throwError "rd_log: not a write log"
  let es ← listSpine L
  let n := es.length
  let ty := mkConst ``Vsa.Sim.WEntry
  for i in (List.range n).reverse do
    let e := es[i]!
    let_expr Prod.mk _ _ a' rest := e | continue
    let_expr Prod.mk _ _ w v' := rest | continue
    unless (← withReducible (isDefEq w (mkNatLit 8))) && (← withReducible (isDefEq a' a)) do continue
    let pre ← mkListLit ty (es.take i)
    let post ← mkListLit ty (es.drop (i + 1))
    let s ← saveState
    try
      let entry ← mkAppM ``Prod.mk #[a, ← mkAppM ``Prod.mk #[mkNatLit 8, v]]
      let rhs ← mkAppM ``HAppend.hAppend #[pre, ← mkAppM ``List.cons #[entry, post]]
      unless ← isDefEq v' v do throwError "rd_log: value"
      unless ← isDefEq L rhs do throwError "rd_log: log"
      let hout ← mkFreshExprMVar (mkApp3 (mkConst ``Vsa.Sim.OutLRange) post a (mkNatLit 8))
      let pf := mkAppN (mkConst ``bytesT8_log'') #[L, pre, post, base, a, v, ← mkEqRefl L, hout]
      (← getMainGoal).assign pf
      setGoals [hout.mvarId!]
      evalTactic (← `(tactic| ((simp only [Vsa.Sim.OutLRange, and_true, true_and]) <;> omega)))
      if (← getUnsolvedGoals).isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "rd_log: no writer"

elab "rd_log" : tactic => rdLog

/-- `LogIn ρ r log`: the log's entries (by computation), each inside `ρ r` (`iv_omega`). -/
elab "login" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let_expr Tom.Machine.LogIn ι ρ r L := tgt | throwError "login: not a LogIn goal"
  let es ← listSpine L
  let lit ← mkListLit (mkConst ``Vsa.Sim.WEntry) es
  let g ← (← getMainGoal).replaceTargetDefEq (mkApp4 (mkConst ``Tom.Machine.LogIn) ι ρ r lit)
  replaceMainGoal [g]
  evalTactic (← `(tactic| simp only [Tom.Machine.LogIn, and_true]))
  evalTactic (← `(tactic| iv_omega))

/-- The region names of `ι`. -/
def regionNames (ι : Expr) : MetaM (List Expr) := do
  let inst ← synthInstance (mkApp (mkConst ``Names) ι)
  listSpine (← mkAppOptM ``Names.all #[ι, inst])

/-- **Facts from the state** `facts h` (`h : St …`): a segment's fact record,
field by field by the projections (a region's RAM, header fields, digits, the
own frame's write log, disjointness of two regions), then `omega`. -/
partial def factsCore (h : Expr) (names : List Expr) (κ : Expr) (fuel : Nat) : TacticM Unit := withMainContext do
  if fuel = 0 then throwError "facts: out of fuel"
  let tgt0 ← instantiateMVars (← getMainTarget)
  let tgt ← whnfR tgt0
  let hs ← Term.exprToSyntax h
  let attempt (t : TSyntax `tactic) : TacticM Bool := tryTac (evalTactic t)
  let head : Option Name := match tgt0.eq? with
    | some (_, lhs, _) => lhs.getAppFn.constName?
    | none => none
  let clean (e : Expr) : TacticM Expr := do
    if let some n := e.getAppFn.constName? then
      -- structure fields (`p.dp`, `a.alloc`), not class methods (`sp - 2160` would unfold `Nat.sub`)
      if let some info ← getProjectionFnInfo? n then
        unless info.fromClass do return ← whnfD e
    return e
  if ← attempt (← `(tactic| assumption)) then return
  let kinds ← names.mapM fun r => do
    let k ← whnfD (mkApp κ r)
    if k.isAppOf ``Kind.mpS || k.isAppOf ``Kind.mpD then
      return (r, mkAppN k.getAppFn (← k.getAppArgs.mapM clean))
    return (r, k)
  if tgt.isAppOf ``Ram then
    for (r, _) in kinds do
      let rs ← Term.exprToSyntax r
      if ← attempt (← `(tactic| exact Ram.sub (St.ram $hs $rs) (by iv_omega) (by iv_omega))) then return
  else if head == some ``Vsa.Sim.bytesT4 || head == some ``Vsa.Sim.bytesT8 then
    let some (_, lhs, _) := tgt0.eq? | throwError "facts: read"
    let x := lhs.appArg!
    let w4 := head == some ``Vsa.Sim.bytesT4
    let same (y : Expr) : TacticM Bool := withReducible (isDefEq x y)
    let addN (p : Expr) (k : Nat) : TacticM Expr := mkAppM ``HAdd.hAdd #[p, mkNatLit k]
    for (r, kr) in kinds do
      let rs ← Term.exprToSyntax r
      if kr.isAppOf ``Kind.mpS then
        let p := kr.getArg! 0
        if w4 then
          if ← same p then if ← attempt (← `(tactic| exact (St.hdr $hs $rs rfl).used)) then return
          if ← same (← addN p 4) then if ← attempt (← `(tactic| exact (St.hdr $hs $rs rfl).alloc)) then return
          if ← same (← addN p 8) then if ← attempt (← `(tactic| exact (St.hdr $hs $rs rfl).sign)) then return
        else
          if ← same (← addN p 16) then if ← attempt (← `(tactic| exact (St.hdr $hs $rs rfl).dpv)) then return
      if kr.isAppOf ``Kind.mpD && w4 then
        let dp := kr.getArg! 0
        if x.isAppOf ``HAdd.hAdd then
          if ← withReducible (isDefEq (x.getArg! 4) dp) then
            if ← attempt (← `(tactic| exact (St.dig $hs $rs rfl).arr _ (by (try dsimp only); omega))) then return
      if kr.isAppOf ``Kind.frz && !w4 then
        if ← tryTac (do evalTactic (← `(tactic| rw [St.frz $hs $rs rfl (by iv_omega)])); rdLog) then return
  else if tgt.isAppOf ``Or then
    if ← attempt (← `(tactic| omega)) then return
    for (r, _) in kinds do
      for (t, _) in kinds do
        let rs ← Term.exprToSyntax r
        let ts ← Term.exprToSyntax t
        if ← tryTac (do
            evalTactic (← `(tactic| have $(mkIdent `hd):ident := St.disj $hs $rs $ts))
            withMainContext do
              let some ld := (← getLCtx).findFromUserName? `hd | throwError "no hd"
              ivNormAt (some ld.fvarId)
            withMainContext do
              let some ld := (← getLCtx).findFromUserName? `hd | throwError "no hd"
              ivNormAt (some ld.fvarId)
            evalTactic (← `(tactic| (iv_norm; omega)))) then return
  else
    if ← attempt (← `(tactic| assumption)) then return
    if ← attempt (← `(tactic| omega)) then return
    for (r, kr) in kinds do
      let rs ← Term.exprToSyntax r
      if kr.isAppOf ``Kind.mpS then
        if ← attempt (← `(tactic| (have := (St.hdr $hs $rs rfl).geom.st_al; (try dsimp only at this); omega))) then return
      if kr.isAppOf ``Kind.mpD then
        if ← attempt (← `(tactic| (have := (St.dig $hs $rs rfl).al; (try dsimp only at this); omega))) then return
        if ← attempt (← `(tactic| (have := (St.dig $hs $rs rfl).ram.hi_le; (try dsimp only at this); omega))) then return
    if ← attempt (← `(tactic| exact MpInt.Shape.digit_lt ‹_› _)) then return
    if ← attempt (← `(tactic| (apply Nat.lt_of_lt_of_le (MpInt.Shape.digit_lt ‹_› _); decide))) then return
  -- a record: its fields
  if let some n := tgt.getAppFn.constName? then
    if isStructure (← getEnv) n && n != ``Ram then
      let gs ← (← getMainGoal).constructor
      for g in gs do
        setGoals [g]
        factsCore h names κ (fuel - 1)
      setGoals []
      return
  throwError "facts: cannot close {tgt0}"

elab "facts " h:term : tactic => withMainContext do
  let hE ← Term.elabTerm h none
  let hT ← whnfR (← instantiateMVars (← inferType hE))
  let args := hT.getAppArgs
  unless hT.isAppOf ``St do throwError "facts: expected a St hypothesis"
  let ι := args[0]!
  let κ := args[5]!
  let names ← regionNames ι
  factsCore hE names κ 4

end Tac

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind} {m M : Mem}
  {pc pc' : BitVec 64} {L0 L L' K : GRegs} {o : Array String} {Q : Vsa.Machine.Config → Prop}

/-- A segment that stores into the own frame `r` (`frz`), then the rest. -/
theorem St.seqW (h : St ρ isW W κ m M) (r : ι) {m0 : Mem} {log : List WEntry} (hk : κ r = .frz m0)
    (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M log) K o))
    (k : ∀ M', St ρ isW W (Kind.set κ r (.frz (writeLog m0 log))) m M' → Triple (At pc' L' M' K o) Q)
    (hlog : LogIn ρ r log := by login) (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q :=
  (Triple.seq hseg (k _ (h.store hlog hk hw hW))).pre hL

/-- A segment that stores digit `i` of the array `r`, then the rest. -/
theorem St.seqD (h : St ρ isW W κ m M) (r : ι) {dp n i v : Nat} {f : Nat → Nat} (hk : κ r = .mpD dp n f)
    (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M [(dp + 4 * i, 4, BitVec.ofNat 64 v)]) K o))
    (hi : i < n) (hv : v < 2 ^ 32)
    (k : ∀ M', St ρ isW W (Kind.set κ r (.mpD dp n (fun j => if j = i then v else f j))) m M' →
      Triple (At pc' L' M' K o) Q)
    (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q := by
  refine Triple.pre ?_ hL
  have hf := (h.wit r).1; rw [hk] at hf
  have hd := (h.wit r).2; rw [hk] at hd
  refine Triple.seq hseg (k _ (h.step (Frm.sw (w := r) (Iv.Sub.trans (Iv.sub_elem hi) hf)) (by simp [hw]) hW
    (fun r' hr' => ?_) (fun r' hr' => ?_)))
  · simp only [List.mem_singleton] at hr'; subst hr'
    simp only [Kind.set, if_true, Kind.Fits, Kind.Wit]
    exact ⟨hf, { ram := hd.ram, al := hd.al, arr := hd.arr.set i v hv }⟩
  · simp only [List.mem_singleton] at hr'; simp [Kind.set, hr']

/-- A segment with an empty log. -/
theorem St.seq0 (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M []) K o)) (k : Triple (At pc' L' M K o) Q)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q := (Triple.seq hseg k).pre hL

/-- Forget the own frame's contents (before a tail call reuses it). -/
theorem St.forget (h : St ρ isW W κ m M) (r : ι) {m0 : Mem} (hk : κ r = .frz m0) :
    St ρ isW W (Kind.set κ r .ram) m M := by
  refine ⟨h.sound, fun r' => ?_, h.frm⟩
  unfold Kind.set
  by_cases hr : r' = r
  · subst hr; simp only [if_true, Kind.Fits, Kind.Wit, true_and]
    have := (h.wit r').2; rw [hk] at this; exact this.1
  · simp only [hr, if_false]; exact h.wit r'

/-- **Re-abstract an `mp_int`**: its struct and digit kinds as one value `a'`
with the same header and the digits `f`. -/
theorem St.setMp (h : St ρ isW W κ m M) (rS rD : ι) {p dp n : Nat} {a : MpInt} {f : Nat → Nat}
    (hS : κ rS = .mpS p dp a) (hD : κ rD = .mpD dp n f) (a' : MpInt) (hu : a'.used = a.used)
    (hal : a'.alloc = a.alloc) (hsg : a'.sign = a.sign) (hn : a.alloc = n) (hf : ∀ j, j < n → a'.digit j = f j) :
    St ρ isW W (Kind.set (Kind.set κ rS (.mpS p dp a')) rD (.mpD dp a'.alloc a'.digit)) m M := by
  refine ⟨h.sound, fun r => ?_, h.frm⟩
  have wS := h.wit rS; have wD := h.wit rD
  rw [hS] at wS; rw [hD] at wD
  unfold Kind.set
  by_cases hr : r = rD
  · subst hr; simp only [if_true]
    have d : Dig M dp n f := wD.2
    refine ⟨by show Iv.Sub ⟨dp, 4 * a'.alloc⟩ _; rw [hal, hn]; exact wD.1, ?_⟩
    show Dig M dp a'.alloc a'.digit
    rw [hal, hn]; exact { ram := d.ram, al := d.al, arr := d.arr.congr fun j hj => (hf j hj).symm }
  · simp only [hr, if_false]
    by_cases hr' : r = rS
    · subst hr'; simp only [if_true]
      have e : Hdr M p dp a := wS.2
      refine ⟨wS.1, ?_⟩
      show Hdr M p dp a'
      exact { used := by rw [hu]; exact e.used, alloc := by rw [hal]; exact e.alloc
              sign := by rw [hsg]; exact e.sign, dpv := e.dpv, geom := by rw [hal]; exact e.geom }
    · simp only [hr', if_false]; exact h.wit r

end

/-- The frame in the contract's names. -/
theorem St.unsplit {R : Type} [DecidableEq R] {ρ : R → Iv} {isW : R → Bool} {s : R} {f : Nat}
    {W : List (Option R)} {κ : Option R → Kind} {m M : Mem} (h : St (Split.lay ρ s f) (Split.wr isW) W κ m M)
    (hf : f ≤ (ρ s).len) {ws : List R} (hws : SubN (W.map (fun o => o.getD s)) ws = true := by decide) :
    Frm ρ ws m M :=
  (Split.unframe hf h.frm).mono hws

/-- The entry state of a one-operand function (`a` written) with an own frame of `f` bytes. -/
theorem St.un {m : Mem} {F f sp pa adp : Nat} {a : MpInt} (hra : MpAt m pa adp a)
    (hga : MpGeom pa adp a.alloc) (hrs : Ram (sp - F) F) (himg : Img m)
    (hS : Sound (Api.Un.lay F sp pa adp a) Api.Un.isW) (hf : f ≤ F) :
    St (Split.lay (Api.Un.lay F sp pa adp a) .stk f) (Split.wr Api.Un.isW)
      [none, some .stk, some .aS, some .aD] (Split.kind (Un.kind pa adp a) m) m m :=
  ⟨Split.sound hS rfl hf, Split.bundle (Un.bundle hra hga hrs himg) rfl hf, Frm.refl _ _⟩

/-- The entry state of a two-operand function (`b` written) with an own frame of `f` bytes. -/
theorem St.two {m : Mem} {F f sp pa adp pb bdp : Nat} {a b : MpInt} (hra : MpAt m pa adp a)
    (hga : MpGeom pa adp a.alloc) (hrb : MpAt m pb bdp b) (hgb : MpGeom pb bdp b.alloc) (hrs : Ram (sp - F) F)
    (himg : Img m) (hS : Sound (Api.Two.lay F sp pa adp pb bdp a b) Api.Two.isW) (hf : f ≤ F) :
    St (Split.lay (Api.Two.lay F sp pa adp pb bdp a b) .stk f) (Split.wr Api.Two.isW)
      [none, some .stk, some .bS, some .bD] (Split.kind (Two.kind pa adp pb bdp a b) m) m m :=
  ⟨Split.sound hS rfl hf, Split.bundle (Two.bundle hra hga hrb hgb hrs himg) rfl hf, Frm.refl _ _⟩


theorem Kind.set_set {ι : Type} [DecidableEq ι] (κ : ι → Kind) (r : ι) (a b : Kind) :
    Kind.set (Kind.set κ r a) r b = Kind.set κ r b := by
  funext r'; unfold Kind.set; split <;> simp_all

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind} {m M : Mem}
  {pc pc' : BitVec 64} {L0 L L' K : GRegs} {o : Array String} {Q : Vsa.Machine.Config → Prop}

theorem St.congrK (h : St ρ isW W κ m M) {κ' : ι → Kind} (hk : ∀ r, κ r = κ' r) : St ρ isW W κ' m M := by
  have : κ = κ' := funext hk
  subst this; exact h

/-- **The in-place array step** (`ArrFrm.step` over `St`): a segment storing
`g i` into element `i` of the digit array `r` that holds `ovl g old i`. -/
theorem St.seqOvl (h : St ρ isW W κ m M) (r : ι) {dp n i v : Nat} {g old : Nat → Nat}
    (hk : κ r = .mpD dp n (ovl g old i))
    (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M [(dp + 4 * i, 4, BitVec.ofNat 64 v)]) K o))
    (hi : i < n) (hv : v < 2 ^ 32) (hgv : v = g i)
    (k : ∀ M', St ρ isW W (Kind.set κ r (.mpD dp n (ovl g old (i + 1)))) m M' → Triple (At pc' L' M' K o) Q)
    (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q := by
  have hf : (fun j => if j = i then v else ovl g old i j) = ovl g old (i + 1) := by
    funext j; simp only [ovl]
    by_cases hj : j = i
    · subst hj; simp [hgv]
    · rw [if_neg hj]; by_cases hl : j < i
      · rw [if_pos hl, if_pos (by omega)]
      · rw [if_neg hl, if_neg (by omega)]
  exact h.seqD r hk hseg hi hv (fun M' h' => k M' (by rw [← hf]; exact h')) hw hW hL

theorem Hdr.setU {M : Mem} {p dp : Nat} {a : MpInt} (e : Hdr M p dp a) (u : Nat) (hu : u < 2 ^ 32) :
    Hdr (writeLog M [(p, 4, BitVec.ofNat 64 u)]) p dp { a with used := u } :=
  { used := bytesT4_sw_self M p u hu
    alloc := by rw [bytesT4_sw_out _ _ _ _ (Or.inr (Nat.le_refl _))]; exact e.alloc
    sign := by rw [bytesT4_sw_out _ _ _ _ (Or.inr (by omega))]; exact e.sign
    dpv := by rw [bytesT8_sw_out _ _ _ _ (Or.inr (by omega))]; exact e.dpv
    geom := e.geom }

theorem Hdr.setS {M : Mem} {p dp : Nat} {a : MpInt} (e : Hdr M p dp a) (s : Nat) (hs : s < 2 ^ 32) :
    Hdr (writeLog M [(p + 8, 4, BitVec.ofNat 64 s)]) p dp { a with sign := s } :=
  { used := by rw [bytesT4_sw_out _ _ _ _ (Or.inl (by omega))]; exact e.used
    alloc := by rw [bytesT4_sw_out _ _ _ _ (Or.inl (by omega))]; exact e.alloc
    sign := bytesT4_sw_self M (p + 8) s hs
    dpv := by rw [bytesT8_sw_out _ _ _ _ (Or.inr (by omega))]; exact e.dpv
    geom := e.geom }

/-- A segment storing header fields of the `mp_int` whose struct is `r`
(`log` inside it), with the header after. -/
theorem St.seqH (h : St ρ isW W κ m M) (r : ι) {p dp : Nat} {a a' : MpInt} {log : List WEntry}
    (hk : κ r = .mpS p dp a) (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M log) K o))
    (hlog : Iv.Sub ⟨p, 24⟩ (ρ r) → LogIn ρ r log) (hh : Hdr M p dp a → Hdr (writeLog M log) p dp a')
    (k : ∀ M', St ρ isW W (Kind.set κ r (.mpS p dp a')) m M' → Triple (At pc' L' M' K o) Q)
    (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q := by
  refine Triple.pre ?_ hL
  have hf := (h.wit r).1; rw [hk] at hf
  have hd := (h.wit r).2; rw [hk] at hd
  refine Triple.seq hseg (k _ (h.step (Frm.store (hlog hf)) (by simp [hw]) hW (fun r' hr' => ?_) (fun r' hr' => ?_)))
  · simp only [List.mem_singleton] at hr'; subst hr'
    simp only [Kind.set, if_true, Kind.Fits, Kind.Wit]
    exact ⟨hf, hh hd⟩
  · simp only [List.mem_singleton] at hr'; simp [Kind.set, hr']

/-- A segment storing an `mp_int`'s `used` (`r` its struct). -/
theorem St.seqU (h : St ρ isW W κ m M) (r : ι) {p dp u : Nat} {a : MpInt} (hk : κ r = .mpS p dp a)
    (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M [(p, 4, BitVec.ofNat 64 u)]) K o)) (hu : u < 2 ^ 32)
    (k : ∀ M', St ρ isW W (Kind.set κ r (.mpS p dp { a with used := u })) m M' → Triple (At pc' L' M' K o) Q)
    (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q :=
  h.seqH r hk hseg (fun hf => ⟨Iv.Sub.trans (J := ⟨p, 24⟩) ⟨Nat.le_refl _, by simp only; omega⟩ hf, trivial⟩)
    (fun e => e.setU u hu) k hw hW hL

/-- A segment storing an `mp_int`'s `used` and `sign`. -/
theorem St.seqUS (h : St ρ isW W κ m M) (r : ι) {p dp u s : Nat} {a : MpInt} (hk : κ r = .mpS p dp a)
    (hseg : Triple (At pc L M K o)
      (At pc' L' (writeLog M [(p, 4, BitVec.ofNat 64 u), (p + 8, 4, BitVec.ofNat 64 s)]) K o))
    (hu : u < 2 ^ 32) (hs : s < 2 ^ 32)
    (k : ∀ M', St ρ isW W (Kind.set κ r (.mpS p dp { a with used := u, sign := s })) m M' →
      Triple (At pc' L' M' K o) Q)
    (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q :=
  h.seqH r hk hseg (fun hf => ⟨Iv.Sub.trans (J := ⟨p, 24⟩) ⟨Nat.le_refl _, by simp only; omega⟩ hf,
      Iv.Sub.trans (J := ⟨p, 24⟩) ⟨by simp only; omega, by simp only; omega⟩ hf, trivial⟩)
    (fun e => by
      rw [show [(p, 4, BitVec.ofNat 64 u), (p + 8, 4, BitVec.ofNat 64 s)] = [(p, 4, BitVec.ofNat 64 u)] ++ [(p + 8, 4, BitVec.ofNat 64 s)] from rfl, writeLog_append]
      exact (e.setU u hu).setS s hs) k hw hW hL

end

/-! ## Contracts and the call rule -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
open Sail.ConcurrencyInterfaceV1.PreSail

/-- The pins other than `ra`. -/
def dropRa (L : GRegs) : GRegs := L.filter (fun q => q.1 != 1)

def gD (n : Nat) (L : GRegs) : BitVec 64 := (lookupG n L).getD 0

/-- The callee-saved registers, read off a register list. -/
def Abi.ofL (L : GRegs) : Abi :=
  { sp := gD 2 L, gp := gD 3 L, tp := gD 4 L, s0 := gD 8 L
    s := ⟨gD 9 L, gD 18 L, gD 19 L, gD 20 L, gD 21 L, gD 22 L, gD 23 L, gD 24 L, gD 25 L, gD 26 L, gD 27 L⟩ }

theorem gholds_ofL {σ : Vsa.Machine.MState} {L : GRegs} (hL : GHolds σ L)
    (hk : abiKeys.all (fun n => (lookupG n L).isSome) = true) : GHolds σ (Abi.ofL L).keep := by
  have g : ∀ n ∈ abiKeys, gprGet σ n = some (gD n L) := by
    intro n hn
    have := List.all_eq_true.1 hk n hn
    unfold gD
    cases h : lookupG n L with
    | none => simp [h] at this
    | some v => exact gholds_lookup L hL h
  exact ⟨g 2 (by decide), g 3 (by decide), g 4 (by decide), g 8 (by decide), g 9 (by decide),
    g 18 (by decide), g 19 (by decide), g 20 (by decide), g 21 (by decide), g 22 (by decide), g 23 (by decide),
    g 24 (by decide), g 25 (by decide), g 26 (by decide), g 27 (by decide), trivial⟩

/-- **A standard contract**: entry, argument and result registers, regions with
their layout and kinds (the Pre's witnesses), write set, the scalar residue
`Res`, the result's kinds `out` and its arithmetic `Q`. -/
structure Contract where
  P : Type
  X : Type
  R : Type
  [deq : DecidableEq R]
  all : List R
  hall : ∀ r, r ∈ all
  entry : BitVec 64
  args : P → GRegs
  rets : P → BitVec 64 → GRegs
  lay : P → R → Iv
  kind : P → R → Kind
  out : P → X → R → Kind
  isW : R → Bool
  ws : List R
  Res : P → Prop
  Q : P → X → Prop
  fits : ∀ p r, (kind p r).Fits (lay p r)
  out_ram : ∀ p x r, r ∈ ws → (out p x r).isRam = true → (kind p r).isRam = true
  out_ind : ∀ p x r, r ∈ ws → (out p x r).isRam = false → (out p x r).indep = true
  spec : ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p ra) M v.keep outp cf ∧ Q p x ∧ Bundle (lay p) (out p x) M ∧ Frm (lay p) ws m M)

attribute [instance] Contract.deq

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι}

/-- **Run a contract** from its entry: the callee's Pre from the caller's
bundle along `σ`, its Post and frame back along `σ`. -/
theorem Contract.run (C : Contract) (p : C.P) (σ : C.R → ι) {κ : ι → Kind} {m M : Mem}
    (hSt : St ρ isW W κ m M) {L K K' : GRegs} {outp : Array String} {ra : BitVec 64}
    (hres : C.Res p) (hra : ra.toNat % 4 = 0)
    (hsub : ∀ r, (C.lay p r).Sub (ρ (σ r))) (hk : ∀ r, C.kind p r = κ (σ r))
    (hsep : SepPres isW C.isW σ C.all = true) (hw : (C.ws.map σ).all isW = true)
    (hW : SubN (C.ws.map σ) W = true) (hargs : SubR ((1, ra) :: C.args p) (L ++ K))
    (hkeys : abiKeys.all (fun n => (lookupG n (L ++ K)).isSome) = true)
    (hK' : SubR K' (C.rets p ra ++ (Abi.ofL (L ++ K)).keep)) :
    Triple (At C.entry L M K outp)
      (fun cf => ∃ x M', At ra (C.rets p ra ++ (Abi.ofL (L ++ K)).keep) M' K' outp cf ∧ C.Q p x ∧
        St ρ isW W (Kind.push σ C.ws κ (C.out p x)) m M') := by
  intro c hc
  have hall : GHolds c.σ (L ++ K) := gholds_append.2 ⟨hc.regs, hc.keep⟩
  have hc' : At C.entry ((1, ra) :: C.args p) M (Abi.ofL (L ++ K)).keep outp c :=
    { hc with regs := hargs.gholds hall, keep := gholds_ofL hall hkeys }
  obtain ⟨c', hs, x, M', hat, hq, hBo, hFo⟩ := C.spec hra hres (hSt.sound.pull σ C.all C.hall hsub hsep)
    (hSt.wit.pull σ hsub hk (C.fits p)) c hc'
  exact ⟨c', hs, x, M', hat.cat hK', hq, hSt.push σ hsub hFo hBo
    (fun k hk' h => by rw [← hk]; exact C.out_ram p x k hk' h) (fun k hk' h => C.out_ind p x k hk' h) hw hW⟩

theorem Triple.ex {P Q : Vsa.Machine.Config → Prop} {α β : Type} {A : α → β → Vsa.Machine.Config → Prop}
    {Φ : α → β → Prop} (h : Triple P (fun cf => ∃ x y, A x y cf ∧ Φ x y))
    (k : ∀ x y, Φ x y → Triple (A x y) Q) : Triple P Q := by
  intro c hc
  obtain ⟨c1, hs1, x, y, hA, hΦ⟩ := h c hc
  obtain ⟨c2, hs2, hq⟩ := k x y hΦ c1 hA
  exact ⟨c2, hs1.trans hs2, hq⟩

/-- **The call rule**: `jal ra, C.entry` at `pc` (word `w`, offset `imm`, all
decided), the contract, then the continuation at `ret = pc + 4` with the
caller's kinds updated along `σ`. -/
theorem call_std (C : Contract) (p : C.P) (σ : C.R → ι) {κ : ι → Kind} {m M : Mem}
    (hSt : St ρ isW W κ m M) {base : Nat} {code : List (BitVec 32)} (hc : CodeAt M base code)
    {pc : BitVec 64} (w : BitVec 32) (imm : BitVec 21) (ret : BitVec 64) {L K : GRegs} {outp : Array String}
    {Q : Vsa.Machine.Config → Prop} (hres : C.Res p)
    (k : ∀ x M', C.Q p x → St ρ isW W (Kind.push σ C.ws κ (C.out p x)) m M' →
      Triple (At ret (C.rets p ret ++ (Abi.ofL (((1, ret) :: dropRa L) ++ K)).keep) M' K outp) Q)
    (hsub : ∀ r, (C.lay p r).Sub (ρ (σ r)) := by intro r; cases r <;> iv_omega)
    (hk : ∀ r, C.kind p r = κ (σ r) := by intro r; cases r <;> rfl)
    (hwd : WordIn base code pc.toNat w = true := by decide +kernel)
    (hdec : ∀ s : SequentialState RegisterType trivialChoiceSource,
      s.regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa) →
      s.regs.get? Register.cur_privilege = some ((Privilege.Machine) : RegisterType Register.cur_privilege) →
      s.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg) →
      (ext_decode w).run s = .ok (instruction.JAL (imm, regidx.Regidx 0x01#5)) s :=
        by exact fun s h1 h2 h3 => decodeW s h1 h2 h3)
    (hword : ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append (w.extractLsb' 8 8)).append
      (w.extractLsb' 0 8)) = w := by decide)
    (hnotrvc : Sail.BitVec.extractLsb ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append
      (w.extractLsb' 8 8)).append (w.extractLsb' 0 8)) 1 0 = (0b11#2 : BitVec 2) := by decide)
    (hpc : pc + Functions.sign_extend (m := 64) imm = C.entry := by decide)
    (hal : C.entry.toNat % 4 = 0 := by decide) (hret : Sail.BitVec.addInt pc 4 = ret := by decide)
    (hra : ret.toNat % 4 = 0 := by decide)
    (hfe : 0x80000000 ≤ pc.toNat ∧ FetchOK pc.toNat ∧ pc.toNat % 4 = 0 :=
      by exact ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩)
    (hsep : SepPres isW C.isW σ C.all = true := by decide) (hw : (C.ws.map σ).all isW = true := by decide)
    (hW : SubN (C.ws.map σ) W = true := by decide)
    (hLk : (keysG (dropRa L)).all (fun n => decide (2 ≤ n) && decide (n ≤ 31)) = true := by exact rfl)
    (hKk : (keysG K).all (fun n => decide (2 ≤ n) && decide (n ≤ 31)) = true := by exact rfl)
    (hargs : SubR ((1, ret) :: C.args p) (((1, ret) :: dropRa L) ++ K) := by exact rfl)
    (hkeys : abiKeys.all (fun n => (lookupG n (((1, ret) :: dropRa L) ++ K)).isSome) = true := by exact rfl)
    (hK' : SubR K (C.rets p ret ++ (Abi.ofL (((1, ret) :: dropRa L) ++ K)).keep) := by exact rfl) :
    Triple (At pc L M K outp) Q := by
  have hj := jal_at (L := L) (L' := dropRa L) (keep := K) (outp := outp) (m := M) (hc.word hwd) hword hnotrvc
    hdec hfe (by rw [hpc]; exact hal) (fun _ h => (List.mem_filter.1 h).1)
    (fun n hn => by have := List.all_eq_true.1 hLk n hn; simpa using this)
    (fun n hn => by have := List.all_eq_true.1 hKk n hn; simpa using this)
  rw [hpc, hret] at hj
  exact Triple.seq hj (Triple.ex (C.run p σ hSt hres hra hsub hk hsep hw hW hargs hkeys hK')
    fun x M' ⟨hq, hS'⟩ => k x M' hq hS')

/-- **The tail-call rule**: at `C.entry` with the caller's `ra` (a `j`, or a
segment that ends there), the contract's return is the caller's. -/
theorem tail_std (C : Contract) (p : C.P) (σ : C.R → ι) {κ : ι → Kind} {m M : Mem}
    (hSt : St ρ isW W κ m M) {L K L' K' : GRegs} {outp : Array String} {ra : BitVec 64}
    {Q : Vsa.Machine.Config → Prop} (hres : C.Res p) (hra : ra.toNat % 4 = 0)
    (k : ∀ x M' cf, C.Q p x → St ρ isW W (Kind.push σ C.ws κ (C.out p x)) m M' → At ra L' M' K' outp cf → Q cf)
    (hsub : ∀ r, (C.lay p r).Sub (ρ (σ r)) := by intro r; cases r <;> iv_omega)
    (hk : ∀ r, C.kind p r = κ (σ r) := by intro r; cases r <;> rfl)
    (hsep : SepPres isW C.isW σ C.all = true := by decide) (hw : (C.ws.map σ).all isW = true := by decide)
    (hW : SubN (C.ws.map σ) W = true := by decide)
    (hargs : SubR ((1, ra) :: C.args p) (L ++ K) := by exact rfl)
    (hkeys : abiKeys.all (fun n => (lookupG n (L ++ K)).isSome) = true := by exact rfl)
    (hK' : SubR K' (C.rets p ra ++ (Abi.ofL (L ++ K)).keep) := by exact rfl)
    (hL' : SubR L' ((C.rets p ra ++ (Abi.ofL (L ++ K)).keep) ++ K') := by exact rfl) :
    Triple (At C.entry L M K outp) Q :=
  Triple.rmap (fun cf ⟨x, M', hat, hq, hS'⟩ => k x M' cf hq hS' (hat.subL hL'))
    (C.run p σ hSt hres hra hsub hk hsep hw hW hargs hkeys hK')

end


end Tom.Machine
