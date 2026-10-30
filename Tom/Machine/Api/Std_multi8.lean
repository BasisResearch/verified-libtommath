import Tom.Machine.Kit.MeetHeapN
import Tom.Machine.Api.StdHeapFn
import Tom.Machine.Api.MpInitMulti
import Tom.Machine.Api.MpClearMulti
import Tom.Machine.Fn.MpInitMultiMain
import Tom.Machine.Fn.MpClearMultiMain

/-!
# `mp_init_multi` and `mp_clear_multi` as multi-site contracts

`Kit/MeetHeapN.lean`'s `HContractN` instances of the varargs functions at any arity `k`, from the
old-route proofs
`Fn.MpInitMulti.correct` / `Fn.MpClearMulti.correct` (`Api/MpInitMulti.lean`,
`Api/MpClearMulti.lean`), re-read as `Std.mpInitSize`/`Std.mpClear` are (`Api/StdHeapFn.lean`).

The callee's regions `MR k`: its stack, the code, per argument `i : Fin k` the struct `.st i` and
the digit array `.dg i`, the site (`mp_init_multi`: laid `Iv.nil`, placed at the fresh block;
`mp_clear_multi`: the live block, retired to `Iv.nil`), and per stack argument `j : Fin (k - 7)` its
word `.sa j` at `sp + 8 j` (arguments 8 on, the `NULL` included, `StackArgs`): read only, of kind
`.frz m0` — a snapshot `m0` of the caller's frame (a `P` field) whose words the residue states
(`sargs`). For `k ≤ 7` there is none (`Fin 0`).

* `mpInitMultiN k`: `X = Option (List Nat)` (`some qs`: every struct `zeroN 32` at `qs[i]`,
  the heap `qs.map (·, 128) ++ H`; `none`: `MP_MEM`, the structs forgotten as RAM, heap `H`).
  Each new block is placed by `PlaceM.foot` (in the arena, off `H`'s blocks: `Heap.blk`,
  `Apart.off`), apart from the others by `Apart.pw`; its alignment (for `MpGeom`) from the
  chunk walk (`Heap.al16`).
* `mpClearMultiN k`: the live `xs` (`Arg`: struct, digits, value), heap `blocks xs ++ H` → `H`,
  every struct and block forgotten as RAM, every site at `Iv.nil`.

Arity 8 and more (`s_mp_invmod_slow`'s `mp_init_multi`/`mp_clear_multi`, `mp_exteuclid`, …) passes
the arguments from the ninth on on the caller's stack (`StackArgs`): the `.sa j` regions.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap
open Tom.Machine.Api.Multi

/-! ## Indices and regions -/

/-- `0, …, k-1` (structural, so `decide` evaluates it). -/
def finL : (k : Nat) → List (Fin k)
  | 0 => []
  | k + 1 => ⟨0, Nat.succ_pos k⟩ :: (finL k).map Fin.succ

theorem mem_finL : ∀ {k : Nat} (i : Fin k), i ∈ finL k
  | 0, i => i.elim0
  | k + 1, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem (mem_finL j))

/-- A varargs callee's regions: stack, code, per argument its struct and digits, and the stack
arguments' words (arguments `8 + j`, the `NULL` included; none for `k ≤ 7`). -/
inductive MR (k : Nat) | stk | code | st (i : Fin k) | dg (i : Fin k) | sa (j : Fin (k - 7))
  deriving DecidableEq

def MR.sts (k : Nat) : List (MR k) := (finL k).map .st
def MR.dgs (k : Nat) : List (MR k) := (finL k).map .dg
def MR.sas (k : Nat) : List (MR k) := (finL (k - 7)).map .sa
def MR.all (k : Nat) : List (MR k) := .stk :: .code :: (MR.sts k ++ MR.dgs k ++ MR.sas k)
def MR.ws (k : Nat) : List (MR k) := .stk :: (MR.sts k ++ MR.dgs k)

def MR.isW {k : Nat} : MR k → Bool
  | .code | .sa _ => false
  | _ => true

theorem MR.hall (k : Nat) (r : MR k) : r ∈ MR.all k := by
  cases r with
  | stk => exact List.mem_cons_self ..
  | code => exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  | st i => exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem (mem_finL i)))))
  | dg i => exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (mem_finL i)))))
  | sa j => exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_right _ (List.mem_map_of_mem (mem_finL j))))

theorem MR.sa_not_ws {k : Nat} {j : Fin (k - 7)} : MR.sa j ∉ MR.ws k := by
  intro h
  rcases List.mem_cons.1 h with h | h
  · cases h
  · rcases List.mem_append.1 h with h | h <;> (obtain ⟨i, _, hi⟩ := List.mem_map.1 h; cases hi)

/-- A struct off the stack window `[sp - F, sp)` and off each stack argument's word is off the
window with the stack arguments, `[sp - F, sp + 8 n)`. -/
theorem disj_window {p sp F n : Nat} (h0 : Disj p 24 (sp - F) F) (hF : F ≤ sp)
    (h1 : ∀ j < n, Disj p 24 (sp + 8 * j) 8) : Disj p 24 (sp - F) (F + 8 * n) := by
  unfold Disj at *
  rcases h0 with h0 | h0
  · exact .inl h0
  · by_cases hn : sp + 8 * n ≤ p
    · exact .inr (by omega)
    · have := h1 ((p - sp) / 8) (by omega)
      omega

theorem MR.dg_ws {k : Nat} (i : Fin k) : MR.dg i ∈ MR.ws k :=
  List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map_of_mem (mem_finL i)))

theorem MR.st_ws {k : Nat} (i : Fin k) : MR.st i ∈ MR.ws k :=
  List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem (mem_finL i)))

theorem MR.mem_dgs {k : Nat} {r : MR k} (h : r ∈ MR.dgs k) : ∃ i, r = .dg i := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 h; exact ⟨i, rfl⟩

theorem MR.dg_dgs {k : Nat} (i : Fin k) : MR.dg i ∈ MR.dgs k := List.mem_map_of_mem (mem_finL i)

theorem MR.not_dgs {k : Nat} {i : Fin k} : MR.st i ∉ MR.dgs k := fun h => by
  obtain ⟨j, hj⟩ := MR.mem_dgs h; cases hj

theorem MR.stk_not_dgs {k : Nat} : (MR.stk : MR k) ∉ MR.dgs k := fun h => by
  obtain ⟨j, hj⟩ := MR.mem_dgs h; cases hj

theorem MR.code_not_ws {k : Nat} : (MR.code : MR k) ∉ MR.ws k := by
  intro h
  rcases List.mem_cons.1 h with h | h
  · cases h
  · rcases List.mem_append.1 h with h | h <;> (obtain ⟨j, _, hj⟩ := List.mem_map.1 h; cases hj)

/-! ## Registers: the pointers, the `NULL`, then `sp`, `gp` -/

theorem keys_argRegs_ge : ∀ (i : Nat) (xs : List Nat), ∀ q ∈ argRegs i xs, 10 + i ≤ q.1
  | _, [], _, h => by simp [argRegs] at h
  | i, x :: ys, q, h => by
    simp only [argRegs] at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · simp only; omega
      · have := keys_argRegs_ge (i + 1) ys q h; omega
    · simp at h

theorem SubR.cons_skip {L X : GRegs} {n : Nat} (v : BitVec 64) (h : SubR L X) (hn : ∀ q ∈ L, q.1 ≠ n) :
    SubR L ((n, v) :: X) := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    simp only [SubR, List.map_cons, List.cons.injEq] at h ⊢
    refine ⟨?_, ih h.2 fun q' hq' => hn q' (List.mem_cons_of_mem _ hq')⟩
    simp only [lookupG]
    split
    · next e => exact absurd e.symm (hn q (List.mem_cons_self ..))
    · exact h.1

theorem subR_argRegs : ∀ (i : Nat) (xs : List Nat) (Z : GRegs), SubR (argRegs i xs) (argRegs i xs ++ Z)
  | _, [], _ => rfl
  | i, x :: ys, Z => by
    simp only [argRegs]
    split
    · simp only [SubR, List.map_cons, List.cons_append, List.cons.injEq]
      refine ⟨by simp [lookupG], ?_⟩
      exact SubR.cons_skip (n := 10 + i) (BitVec.ofNat 64 x) (subR_argRegs (i + 1) ys Z)
        (fun q hq => by have := keys_argRegs_ge (i + 1) ys q hq; omega)
    · rfl

theorem lookupG_argRegs_lo : ∀ (i : Nat) (xs : List Nat) (Y : GRegs) (n : Nat), n < 10 →
    lookupG n (argRegs i xs ++ Y) = lookupG n Y
  | _, [], _, _, _ => rfl
  | i, x :: ys, Y, n, hn => by
    simp only [argRegs]
    split
    · simp only [List.cons_append, lookupG]
      split
      · omega
      · exact lookupG_argRegs_lo (i + 1) ys Y n hn
    · rfl

/-- The callee's pins: `ra`, the arguments, `sp`, `gp`. -/
def varArgs (sp : Nat) (ps : List Nat) : GRegs :=
  argRegs 0 (args ps) ++ [(2, BitVec.ofNat 64 sp), (3, gpV)]

theorem varArgs_sub (ra : BitVec 64) (sp : Nat) (ps : List Nat) (K : GRegs) :
    SubR ((1, ra) :: argRegs 0 (args ps)) (((1, ra) :: varArgs sp ps) ++ K) := by
  simp only [SubR, List.map_cons, List.cons_append, List.cons.injEq]
  refine ⟨by simp [lookupG], ?_⟩
  have h := subR_argRegs 0 (args ps) ([(2, BitVec.ofNat 64 sp), (3, gpV)] ++ K)
  rw [← List.append_assoc] at h
  exact SubR.cons_skip ra h (fun q hq => by have := keys_argRegs_ge 0 _ q hq; omega)

theorem varArgs_sp (ra : BitVec 64) (sp : Nat) (ps : List Nat) :
    lookupG 2 ((1, ra) :: varArgs sp ps) = some (BitVec.ofNat 64 sp) := by
  simp only [lookupG, varArgs, show (1 = 2) = False from by decide, ite_false]
  rw [lookupG_argRegs_lo 0 _ _ 2 (by omega)]; rfl

theorem varArgs_gp (ra : BitVec 64) (sp : Nat) (ps : List Nat) :
    lookupG 3 ((1, ra) :: varArgs sp ps) = some gpV := by
  simp only [lookupG, varArgs, show (1 = 3) = False from by decide, ite_false]
  rw [lookupG_argRegs_lo 0 _ _ 3 (by omega)]; rfl

/-! ## Live blocks are 16-aligned (the chunk walk) -/

theorem walk_al {m : Mem} : ∀ {p top : Nat} {cs : List Vsa.Sim.DlHeap.Chunk},
    Vsa.Sim.DlHeap.ChunkWalk m p top cs → ∀ c ∈ cs, c.addr % 16 = p % 16
  | _, _, _, .top, _, h => absurd h List.not_mem_nil
  | _, _, _, .chunk _ _ _ h16 _ hw, c, hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    · have := walk_al hw c hc; omega

/-- **A live block starts 16-aligned.** -/
theorem Heap.al16 {m : Mem} {H : List (Nat × Nat)} (h : Heap m H) {e : Nat × Nat} (he : e ∈ H) :
    e.1 % 16 = 0 := by
  obtain ⟨_, m', ⟨_, top, brk, chunks, bins, W⟩⟩ := h
  obtain ⟨c, hc, _, h1, _⟩ := W.heap.exact e he he
  have := walk_al W.heap.walk c hc
  have e2 : Vsa.Sim.DlHeap.heapStart = 0x80019d10 := rfl
  omega

/-- A live block of a heap whose other blocks it misses is fresh for them. -/
theorem fresh_of_heap {M : Mem} {B H : List (Nat × Nat)} (hH : Heap M (B ++ H)) {e : Nat × Nat} (he : e ∈ B)
    (hoff : ∀ e' ∈ H, ∀ a, InBlk e a → ¬ InBlk e' a) : Fresh H e.1 e.2 :=
  have hb := Fn.Alloc.Heap.blk hH (List.mem_append_left _ he)
  have ha := Heap.al16 hH (List.mem_append_left _ he)
  have eS : heapStart = 0x80019d10 := rfl
  ⟨by omega, ha, by omega, hb.2, hoff⟩

/-! ## `mp_init_multi(p₀, …, p_{k-1}, NULL)` -/

structure IMP where
  sp : Nat
  ps : List Nat
  H : List (Nat × Nat)
  /-- The caller's memory the stack arguments' words are read from (any, for `k ≤ 7`). -/
  m0 : Mem

def IM.lay (k : Nat) (p : IMP) : MR k → Iv
  | .stk => ⟨p.sp - MpInitMulti.F, MpInitMulti.F⟩
  | .code => textIv
  | .st i => ⟨p.ps.getD i 0, 24⟩
  | .dg _ => Iv.nil
  | .sa j => ⟨p.sp + 8 * j, 8⟩

def IM.out (k : Nat) (p : IMP) : Option (List Nat) → MR k → Kind
  | _, .code => .code
  | _, .sa _ => .frz p.m0
  | some qs, .st i => .mpS (p.ps.getD i 0) (qs.getD i 0) (MpInt.zeroN defPrec)
  | some qs, .dg i => .mpD (qs.getD i 0) defPrec (MpInt.zeroN defPrec).digit
  | _, _ => .ram

def IM.site' (k : Nat) : Option (List Nat) → MR k → Iv
  | some qs, .dg i => ⟨qs.getD i 0, 4 * defPrec⟩
  | _, _ => Iv.nil

def IM.hout (H : List (Nat × Nat)) : Option (List Nat) → List (Nat × Nat)
  | some qs => qs.map (fun q => (q, 4 * defPrec)) ++ H
  | none => H

def IM.rets (x : Option (List Nat)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | some _ => 0#64 | none => MpInit.memBV)]

structure IMRes (k : Nat) (p : IMP) : Prop where
  stk : StkRes p.sp MpInitMulti.F
  /-- One pointer per argument. -/
  len : p.ps.length = k
  /-- The structs are 8-aligned and off the heap (the caller's frame). -/
  al : ∀ i : Fin k, p.ps.getD i 0 % 8 = 0
  soff : ∀ i : Fin k, OffHeap (p.ps.getD i 0) 24
  /-- The stack arguments (arguments `8 + j`, the `NULL` last) in `m0`'s words at `sp + 8 j`. -/
  sargs : ∀ j : Fin (k - 7), bytesT8 p.m0 (p.sp + 8 * j) = BitVec.ofNat 64 ((args p.ps).getD (8 + j) 0)
  hi : p.sp + 8 * (k - 7) ≤ 0x100000000

theorem getD_idx {α : Type} {l : List α} {d : α} {j : Nat} (h : j < l.length) : l.getD j d = l[j] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem mem_idx {l : List Nat} {x : Nat} (h : x ∈ l) : ∃ i : Fin l.length, l.getD i 0 = x := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 h
  exact ⟨⟨j, hj⟩, getD_idx hj⟩

/-- **`mp_init_multi` at arity `k`.** -/
def mpInitMultiN (k : Nat) : HContractN where
  P := IMP
  X := Option (List Nat)
  R := MR k
  all := MR.all k
  hall := MR.hall k
  entry := Fn.MpInitMulti.entry
  args p := varArgs p.sp p.ps
  rets _ x ra := IM.rets x ra
  lay := IM.lay k
  kind p := fun | .code => .code | .sa _ => .frz p.m0 | _ => .ram
  out := IM.out k
  isW := MR.isW
  ws := MR.ws k
  sites := MR.dgs k
  site' _ := IM.site' k
  hin p := p.H
  hout p := IM.hout p.H
  Res := IMRes k
  Q _ x := match x with | some qs => qs.length = k | none => True
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  sites_ws s hs := by obtain ⟨i, rfl⟩ := MR.mem_dgs hs; exact MR.dg_ws i
  sites_w s hs := by obtain ⟨i, rfl⟩ := MR.mem_dgs hs; rfl
  out_ind p x r hr hs h := by cases x <;> cases r <;> first | exact absurd hr MR.sa_not_ws | simp_all [IM.out, Kind.isRam, Kind.indep]
  pos p _ r := by
    cases r with
    | stk => exact .inl (show 0 < MpInitMulti.F by decide)
    | code => exact .inl (show 0 < textLen by decide)
    | st _ => exact .inl (show 0 < 24 by decide)
    | dg _ => exact .inr (.inl (show 0x80000000 < heapStart by decide))
    | sa _ => exact .inl (show 0 < 8 by decide)
  spec := by
    intro p m v outp ra hra hres hS hB hH _ c hc
    obtain ⟨sp, ps, H, m0⟩ := p
    obtain ⟨hst, hlen, hal, hso, hsa, hhi⟩ := hres
    dsimp only at hlen hst hal hso hsa hhi
    subst hlen
    have hctx := hst.ctx hc (varArgs_sp ra sp ps) (varArgs_gp ra sp ps) (hB .code).2 hH.imp hra
    have hF := hst.lo
    have eE : heapEnd = 0x87800000 := rfl
    have hal0 : argLen (ps.length + 1) = 8 * (ps.length - 7) := by unfold argLen; omega
    -- the structs, from the bundle and the layout
    have sram : ∀ i : Fin ps.length, Ram (ps.getD i 0) 24 := fun i => (hB (.st i)).2
    have sdisj : ∀ (i : Fin ps.length) (r : MR ps.length), r ≠ .st i →
        (IM.lay ps.length ⟨sp, ps, H, m0⟩ (.st i)).Disj (IM.lay _ ⟨sp, ps, H, m0⟩ r) := fun i r hr =>
      hS _ _ (by simp [Sep, MR.isW, Ne.symm hr])
    have hstr : Structs ps (sp - MpInitMulti.F) (MpInitMulti.F + argLen (ps.length + 1)) := by
      rw [hal0]
      refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, ?_, fun q hq => ?_, fun q hq => ?_⟩
      · obtain ⟨i, rfl⟩ := mem_idx hq; exact sram i
      · obtain ⟨i, rfl⟩ := mem_idx hq; exact hal i
      · obtain ⟨i, rfl⟩ := mem_idx hq; exact hso i
      · refine List.pairwise_iff_getElem.2 fun i j hi hj hij => ?_
        have := sdisj ⟨i, hi⟩ (.st ⟨j, hj⟩) (by simp; omega)
        simp only [IM.lay, Iv.Disj, getD_idx hi, getD_idx hj] at this
        simpa using this
      · obtain ⟨i, rfl⟩ := mem_idx hq
        have h0 := sdisj i .stk (by simp)
        simp only [IM.lay, Iv.Disj] at h0
        refine disj_window h0 (by have := hst.lo; omega) fun j hj => ?_
        have := sdisj i (.sa ⟨j, hj⟩) (by simp)
        simpa [IM.lay, Iv.Disj] using this
      · obtain ⟨i, rfl⟩ := mem_idx hq
        have := sdisj i .code (by simp)
        simpa [IM.lay, Iv.Disj, textIv] using this
    have hpre : MpInitMulti.Pre m v H sp ps ra :=
      { heap := hH.heap, st := hstr
        sargs := fun j hj h8 => by
          have hj' : j - 8 < ps.length - 7 := by simp [args] at hj; omega
          have hw : Kind.Wit (.frz m0) (IM.lay ps.length ⟨sp, ps, H, m0⟩ (.sa ⟨j - 8, hj'⟩)) m := (hB (.sa ⟨j - 8, hj'⟩)).2
          rw [show (args ps)[j] = (args ps).getD (8 + (j - 8)) 0 by rw [getD_idx (by omega)]; congr 1; omega,
            ← hsa ⟨j - 8, hj'⟩]
          exact bytesT8_congr fun x h1 h2 => hw.2 x ⟨by simp only [IM.lay]; omega, by simp only [IM.lay]; omega⟩
        args_hi := by rw [hal0]; exact hhi
        len := by omega
        ctx := ⟨hctx.img, hctx.impure, hctx.gp, hctx.sp_v, hctx.sp_al, hctx.sp_lo, hctx.sp_hi⟩
        ra_al := hra }
    obtain ⟨c', hs, r, M, hat, hpost⟩ := Fn.MpInitMulti.correct hpre c (hc.subL (varArgs_sub ra sp ps _))
    -- the frame: the stack, the structs, the footprint
    have hW : ∀ a, MpInitMulti.W ps H sp a → InAny (IM.lay ps.length ⟨sp, ps, H, m0⟩) (MR.ws ps.length) a ∨ Foot H a :=
      fun a ha => by
        rcases ha with h | ⟨q, hq, h⟩ | h
        · exact .inl (InAny.of_mem (List.mem_cons_self ..) (stk_in hst h))
        · obtain ⟨i, rfl⟩ := mem_idx hq
          exact .inl (InAny.of_mem (MR.st_ws i) h)
        · exact .inr h
    have himp : ∀ (M : Mem), Keep (MpInitMulti.W ps H sp) m M → ImpureAt M := fun M hf =>
      ImpureAt.of_keep hf (fun a h1 h2 hw => by
        rcases hw with h | ⟨q, hq, h⟩ | h
        · exact offHeap_imp hst.off (stk_in hst h).1 (stk_in hst h).2 ⟨h1, h2⟩
        · obtain ⟨i, rfl⟩ := mem_idx hq
          exact offHeap_imp (hso i) h.1 h.2 ⟨h1, h2⟩
        · exact impure_off_foot h1 h2 h) hH.imp
    cases hpost with
    | ok ys hp zero live heap apart frame =>
      have hyl : ys.length = ps.length := by rw [← hp]; simp [ptrs]
      -- the `i`-th argument
      have hy : ∀ i : Fin ps.length, ∃ y ∈ ys, y.1 = ps.getD i 0 ∧ y.2.1 = (ys.map (·.2.1)).getD i 0 ∧
          digBlk y.2.1 y.2.2 = ((ys.map (·.2.1)).getD i 0, 4 * defPrec) := fun i => by
        have hi : i.val < ys.length := by omega
        refine ⟨ys[i.val], List.getElem_mem hi, ?_, ?_, ?_⟩
        · rw [getD_idx i.2]; subst hp; simp [ptrs]
        · rw [getD_idx (by simpa using hi)]; simp
        · rw [getD_idx (by simpa using hi)]
          simp [zero _ (List.getElem_mem hi), MpInt.zeroN]
      have hblk : blocks ys = (ys.map (·.2.1)).map (fun q => (q, 4 * defPrec)) := by
        simp only [blocks, List.map_map]
        refine List.map_congr_left fun y hy' => ?_
        simp [zero y hy', MpInt.zeroN]
      have heap' : Heap M (IM.hout H (some (ys.map (·.2.1)))) := by
        simpa [IM.hout, hblk] using heap
      have hmemB : ∀ i : Fin ps.length, ((ys.map (·.2.1)).getD i 0, 4 * defPrec) ∈ blocks ys := fun i => by
        obtain ⟨y, hy', _, _, he⟩ := hy i
        rw [← he]; exact List.mem_map_of_mem hy'
      have hfr : ∀ i : Fin ps.length, Fresh H ((ys.map (·.2.1)).getD i 0) (4 * defPrec) := fun i =>
        fresh_of_heap heap (hmemB i) (apart.off _ (hmemB i))
      have hgeom : ∀ i : Fin ps.length, MpGeom (ps.getD i 0) ((ys.map (·.2.1)).getD i 0) defPrec := fun i =>
        geom_fresh (sram i) (hal i) (hso i) (hfr i) (by decide)
      have hlive : ∀ i : Fin ps.length,
          MpAt M (ps.getD i 0) ((ys.map (·.2.1)).getD i 0) (MpInt.zeroN defPrec) := fun i => by
        obtain ⟨y, hy', h1, h2, _⟩ := hy i
        rw [← h1, ← h2, ← zero y hy']; exact live y hy'
      refine ⟨c', hs, some (ys.map (·.2.1)), M, hat, by simpa using hyl, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | code => exact absurd hr MR.code_not_ws
                | st i => exact ⟨Iv.sub_self _, Hdr.of_mpAt (hlive i) (hgeom i)⟩
                | dg i => exact absurd (MR.dg_dgs i) hrs
                | sa j => exact absurd hr MR.sa_not_ws
              wsite := fun s hs => by
                obtain ⟨i, rfl⟩ := MR.mem_dgs hs
                exact ⟨Iv.sub_self _, Dig.of_mpAt (hlive i) (hgeom i)⟩
              place := fun s hs => by
                obtain ⟨i, rfl⟩ := MR.mem_dgs hs
                exact .place (.fresh (hfr i) (by decide))
              apart := fun s hs t ht hst' => by
                obtain ⟨i, rfl⟩ := MR.mem_dgs hs
                obtain ⟨j, rfl⟩ := MR.mem_dgs ht
                have hij : i.val ≠ j.val := fun e => hst' (by rw [Fin.ext e])
                have hpw := apart.pw
                rw [hblk, List.pairwise_map] at hpw
                have hpw' := List.pairwise_iff_getElem.1 hpw
                have hi : i.val < (ys.map (·.2.1)).length := by simp; omega
                have hj : j.val < (ys.map (·.2.1)).length := by simp; omega
                simp only [IM.site', Iv.Disj]
                rw [getD_idx hi, getD_idx hj]
                rcases Nat.lt_or_gt_of_ne hij with h | h
                · exact hpw' i.val j.val hi hj h
                · have := hpw' j.val i.val hj hi h; unfold Disj at this ⊢; omega
              frame := Keep.mono frame fun a h => hW a h
              heap := ⟨heap', himp M frame⟩
              foot := fun a ha => .inl (by simpa [IM.hout] using Foot.of_append ha)
              off := fun s hs => by
                obtain ⟨i, rfl⟩ := MR.mem_dgs hs
                refine Off.of_blk heap' ?_ (show 0 < 4 * defPrec by decide)
                have hm := hmemB i
                rw [hblk] at hm
                simp only [IM.hout, IM.site']
                exact List.mem_append_left _ hm }
    | mem kk hk cleared dp heap frame =>
      refine ⟨c', hs, none, M, hat, trivial, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | code => exact absurd hr MR.code_not_ws
                | st i => exact ⟨trivial, sram i⟩
                | dg i => exact absurd (MR.dg_dgs i) hrs
                | sa j => exact absurd hr MR.sa_not_ws
              wsite := fun s hs => by
                obtain ⟨i, rfl⟩ := MR.mem_dgs hs
                exact ⟨trivial, Ram.nil⟩
              place := fun s hs => by
                obtain ⟨i, rfl⟩ := MR.mem_dgs hs
                exact .place .nil
              apart := fun s hs t ht _ => by
                obtain ⟨i, rfl⟩ := MR.mem_dgs hs
                obtain ⟨j, rfl⟩ := MR.mem_dgs ht
                show Iv.nil.Disj Iv.nil
                exact Or.inl (by decide)
              frame := Keep.mono frame fun a h => hW a h
              heap := ⟨heap, himp M frame⟩
              foot := fun a ha => .inl ha
              off := fun s hs => by
                obtain ⟨i, rfl⟩ := MR.mem_dgs hs
                exact Off.nil H }

/-! ## `mp_clear_multi(x₀, …, x_{k-1}, NULL)` of live `mp_int`s -/

/-- The `i`-th argument (or a cleared dummy). -/
def argAt (xs : List Arg) (i : Nat) : Arg := xs.getD i (0, 0, MpInt.cleared)

structure CMP where
  sp : Nat
  xs : List Arg
  H : List (Nat × Nat)
  /-- The caller's memory the stack arguments' words are read from (any, for `k ≤ 7`). -/
  m0 : Mem

def CM.lay (k : Nat) (p : CMP) : MR k → Iv
  | .stk => ⟨p.sp - MpClearMulti.F, MpClearMulti.F⟩
  | .code => textIv
  | .st i => ⟨(argAt p.xs i).1, 24⟩
  | .dg i => ⟨(argAt p.xs i).2.1, 4 * (argAt p.xs i).2.2.alloc⟩
  | .sa j => ⟨p.sp + 8 * j, 8⟩

def CM.kind (k : Nat) (p : CMP) : MR k → Kind
  | .stk => .ram
  | .code => .code
  | .st i => .mpS (argAt p.xs i).1 (argAt p.xs i).2.1 (argAt p.xs i).2.2
  | .dg i => .mpD (argAt p.xs i).2.1 (argAt p.xs i).2.2.alloc (argAt p.xs i).2.2.digit
  | .sa _ => .frz p.m0

structure CMRes (k : Nat) (p : CMP) : Prop where
  stk : StkRes p.sp MpClearMulti.F
  len : p.xs.length = k
  soff : ∀ i : Fin k, OffHeap (argAt p.xs i).1 24
  /-- Nonempty digit arrays (`pos`; every live `mp_int` has `alloc > 0`). -/
  apos : ∀ i : Fin k, 0 < (argAt p.xs i).2.2.alloc
  /-- The stack arguments (arguments `8 + j`, the `NULL` last) in `m0`'s words at `sp + 8 j`. -/
  sargs : ∀ j : Fin (k - 7), bytesT8 p.m0 (p.sp + 8 * j) =
    BitVec.ofNat 64 ((args (ptrs p.xs)).getD (8 + j) 0)
  hi : p.sp + 8 * (k - 7) ≤ 0x100000000

theorem argAt_idx {xs : List Arg} {j : Nat} (h : j < xs.length) : argAt xs j = xs[j] := getD_idx h

theorem mem_argAt {xs : List Arg} {x : Arg} (h : x ∈ xs) : ∃ i : Fin xs.length, argAt xs i = x := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 h
  exact ⟨⟨j, hj⟩, argAt_idx hj⟩

theorem foot_split {B H : List (Nat × Nat)} {a : Nat} (h : Foot H a) :
    Foot (B ++ H) a ∨ ∃ e ∈ B, InBlk e a := by
  by_cases hb : ∃ e ∈ B, InBlk e a
  · exact .inr hb
  · rcases h with hg | ⟨h1, h2, h3⟩
    · exact .inl (.inl hg)
    · refine .inl (.inr ⟨h1, h2, fun e he hx => ?_⟩)
      rcases List.mem_append.1 he with he | he
      · exact hb ⟨e, he, hx⟩
      · exact h3 e he hx

/-- **`mp_clear_multi` at arity `k`.** -/
def mpClearMultiN (k : Nat) : HContractN where
  P := CMP
  X := Unit
  R := MR k
  all := MR.all k
  hall := MR.hall k
  entry := Fn.MpClearMulti.entry
  args p := varArgs p.sp (ptrs p.xs)
  rets _ _ ra := [(1, ra)]
  lay := CM.lay k
  kind := CM.kind k
  out p _ := fun | .code => .code | .sa _ => .frz p.m0 | _ => .ram
  isW := MR.isW
  ws := MR.ws k
  sites := MR.dgs k
  site' _ _ _ := Iv.nil
  hin p := blocks p.xs ++ p.H
  hout p _ := p.H
  Res := CMRes k
  Q _ _ := True
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  sites_ws s hs := by obtain ⟨i, rfl⟩ := MR.mem_dgs hs; exact MR.dg_ws i
  sites_w s hs := by obtain ⟨i, rfl⟩ := MR.mem_dgs hs; rfl
  out_ind p x r hr hs h := by cases r <;> first | exact absurd hr MR.sa_not_ws | simp_all [Kind.isRam, Kind.indep]
  pos p h r := by
    cases r with
    | stk => exact .inl (show 0 < MpClearMulti.F by decide)
    | code => exact .inl (show 0 < textLen by decide)
    | st _ => exact .inl (show 0 < 24 by decide)
    | dg i => exact .inl (show 0 < 4 * (argAt p.xs i).2.2.alloc by have := h.apos i; omega)
    | sa _ => exact .inl (show 0 < 8 by decide)
  spec := by
    intro p m v outp ra hra hres hS hB hH _ c hc
    obtain ⟨sp, xs, H, m0⟩ := p
    obtain ⟨hst, hlen, hso, hap, hsa, hhi⟩ := hres
    dsimp only at hlen hst hso hap hsa hhi
    subst hlen
    have hctx := hst.ctx hc (varArgs_sp ra sp _) (varArgs_gp ra sp _) (hB .code).2 hH.imp hra
    have hF := hst.lo
    have eE : heapEnd = 0x87800000 := rfl
    have hpl : (ptrs xs).length = xs.length := by simp [ptrs]
    have hal0 : argLen (xs.length + 1) = 8 * (xs.length - 7) := by unfold argLen; omega
    have sdisj : ∀ (r t : MR xs.length), r ≠ t → MR.isW r = true →
        (CM.lay xs.length ⟨sp, xs, H, m0⟩ r).Disj (CM.lay _ ⟨sp, xs, H, m0⟩ t) := fun r t hr hc' =>
      hS _ _ (by simp [Sep, hr, hc'])
    have hdr : ∀ i : Fin xs.length, Hdr m (argAt xs i).1 (argAt xs i).2.1 (argAt xs i).2.2 :=
      fun i => (hB (.st i)).2
    have hdg : ∀ i : Fin xs.length, Dig m (argAt xs i).2.1 (argAt xs i).2.2.alloc (argAt xs i).2.2.digit :=
      fun i => (hB (.dg i)).2
    have hstr : Structs (ptrs xs) (sp - MpClearMulti.F) (MpClearMulti.F + argLen (xs.length + 1)) := by
      rw [hal0]
      refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, ?_, fun q hq => ?_, fun q hq => ?_⟩
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq; obtain ⟨i, rfl⟩ := mem_argAt hx
        simpa [Layout.sizeofMpInt] using (Hdr.geom (hdr i)).st
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq; obtain ⟨i, rfl⟩ := mem_argAt hx
        exact (Hdr.geom (hdr i)).st_al
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq; obtain ⟨i, rfl⟩ := mem_argAt hx
        exact hso i
      · refine List.pairwise_iff_getElem.2 fun i j hi hj hij => ?_
        have hi' : i < xs.length := by omega
        have hj' : j < xs.length := by omega
        have := sdisj (.st ⟨i, hi'⟩) (.st ⟨j, hj'⟩) (by simp; omega) rfl
        simp only [CM.lay, Iv.Disj, argAt_idx hi', argAt_idx hj'] at this
        simpa [ptrs] using this
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq; obtain ⟨i, rfl⟩ := mem_argAt hx
        have h0 := sdisj (.st i) .stk (by simp) rfl
        simp only [CM.lay, Iv.Disj] at h0
        refine disj_window h0 (by have := hst.lo; omega) fun j hj => ?_
        have := sdisj (.st i) (.sa ⟨j, by omega⟩) (by simp) rfl
        simpa [CM.lay, Iv.Disj] using this
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq; obtain ⟨i, rfl⟩ := mem_argAt hx
        have := sdisj (.st i) .code (by simp) rfl
        simpa [CM.lay, Iv.Disj, textIv] using this
    have hbpw : (blocks xs).Pairwise fun e e' => Disj e.1 e.2 e'.1 e'.2 := by
      refine List.pairwise_iff_getElem.2 fun i j hi hj hij => ?_
      have hi' : i < xs.length := by simpa [blocks] using hi
      have hj' : j < xs.length := by simpa [blocks] using hj
      have := sdisj (.dg ⟨i, hi'⟩) (.dg ⟨j, hj'⟩) (by simp; omega) rfl
      simp only [CM.lay, Iv.Disj, argAt_idx hi', argAt_idx hj'] at this
      simpa [blocks] using this
    have hpre : MpClearMulti.Pre m v H sp xs ra :=
      { live := fun x hx => by obtain ⟨i, rfl⟩ := mem_argAt hx; exact Hdr.mpAt (hdr i) (hdg i)
        heap := hH.heap, bpw := hbpw, st := hstr
        sargs := fun j hj h8 => by
          have hj' : j - 8 < xs.length - 7 := by simp [args, ptrs] at hj; omega
          have hw : Kind.Wit (.frz m0) (CM.lay xs.length ⟨sp, xs, H, m0⟩ (.sa ⟨j - 8, hj'⟩)) m := (hB (.sa ⟨j - 8, hj'⟩)).2
          rw [show (args (ptrs xs))[j] = (args (ptrs xs)).getD (8 + (j - 8)) 0 by rw [getD_idx (by omega)]; congr 1; omega,
            ← hsa ⟨j - 8, hj'⟩]
          exact bytesT8_congr fun x h1 h2 => hw.2 x ⟨by simp only [CM.lay]; omega, by simp only [CM.lay]; omega⟩
        args_hi := by rw [hal0]; exact hhi
        ctx := ⟨hctx.img, hctx.impure, hctx.gp, hctx.sp_v, hctx.sp_al, hctx.sp_lo, hctx.sp_hi⟩
        ra_al := hra }
    obtain ⟨c', hs, M, hat, hpost⟩ := Fn.MpClearMulti.correct hpre c (hc.subL (varArgs_sub ra sp _ _))
    have hW : ∀ a, MpClearMulti.W xs H sp a →
        InAny (CM.lay xs.length ⟨sp, xs, H, m0⟩) (MR.ws xs.length) a ∨ Foot (blocks xs ++ H) a := fun a ha => by
      rcases ha with h | ⟨x, hx, h | h⟩ | h
      · exact .inl (InAny.of_mem (List.mem_cons_self ..) (stk_in hst h))
      · obtain ⟨i, rfl⟩ := mem_argAt hx; exact .inl (InAny.of_mem (MR.st_ws i) h)
      · obtain ⟨i, rfl⟩ := mem_argAt hx; exact .inl (InAny.of_mem (MR.dg_ws i) h)
      · rcases foot_split (B := blocks xs) h with h | ⟨e, he, hx⟩
        · exact .inr h
        · obtain ⟨x, hx', rfl⟩ := List.mem_map.1 he
          obtain ⟨i, rfl⟩ := mem_argAt hx'
          exact .inl (InAny.of_mem (MR.dg_ws i) hx)
    refine ⟨c', hs, (), M, hat, trivial, ?_⟩
    exact { wit := fun r hr hrs => by
              cases r with
              | stk => exact ⟨trivial, (hB .stk).2⟩
              | code => exact absurd hr MR.code_not_ws
              | st i => exact ⟨trivial, (by simpa [Layout.sizeofMpInt] using (Hdr.geom (hdr i)).st :
                  Ram (argAt xs i).1 24)⟩
              | dg i => exact absurd (MR.dg_dgs i) hrs
              | sa j => exact absurd hr MR.sa_not_ws
            wsite := fun s hs => by
              obtain ⟨i, rfl⟩ := MR.mem_dgs hs
              exact ⟨trivial, Ram.nil⟩
            place := fun s hs => .place .nil
            apart := fun s hs t ht _ => by
              show Iv.nil.Disj Iv.nil
              exact Or.inl (by decide)
            frame := Keep.mono hpost.frame fun a h => hW a h
            heap := ⟨hpost.heap, ImpureAt.of_keep hpost.frame (fun a h1 h2 hw => by
                rcases hw with h | ⟨x, hx, h | h⟩ | h
                · exact offHeap_imp hst.off (stk_in hst h).1 (stk_in hst h).2 ⟨h1, h2⟩
                · obtain ⟨i, rfl⟩ := mem_argAt hx; exact offHeap_imp (hso i) h.1 h.2 ⟨h1, h2⟩
                · have hb := Fn.Alloc.Heap.blk hH.heap (List.mem_append_left _ (List.mem_map_of_mem hx))
                  have e : heapStart = 0x80019d10 := rfl
                  unfold InBlk at h; unfold impurePtr at h2; simp only at hb h; omega
                · exact impure_off_foot h1 h2 h) hH.imp⟩
            foot := fun a ha => by
              rcases foot_split (B := blocks xs) ha with h | ⟨e, he, hx⟩
              · exact .inl h
              · obtain ⟨x, hx', rfl⟩ := List.mem_map.1 he
                obtain ⟨i, rfl⟩ := mem_argAt hx'
                exact .inr ⟨.dg i, MR.dg_dgs i, hx⟩
            off := fun s hs => Off.nil H }

/-! ## A caller's side conditions (`call_heapN`'s `hsub`, `hk`)

`mr_split`: the cases of an `MR k` region (`k ≤ 9`, stack arguments `j < 9`; the indices out of
range closed by `omega`); `mr_iv`: `iv_omega` with the argument lists' `getD`/`argAt` evaluated. The generator
passes `(by mr_split <;> mr_iv)` and `(by mr_split <;> rfl)` (`scripts/gen_asm.py`, `call_heapN`). -/

theorem IM.F_eq : MpInitMulti.F = 672 := rfl
theorem CM.F_eq : MpClearMulti.F = 640 := rfl

macro "mr_split" : tactic => `(tactic| (intro r; rcases r with _ | _ |
  ⟨_ | _ | _ | _ | _ | _ | _ | _ | _, hi⟩ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _, hi⟩ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _, hi⟩ <;>
  (try (exfalso; omega))))

macro "mr_iv" : tactic =>
  `(tactic| (iv_norm; (try simp only [Tom.Machine.Std.argAt, Tom.Machine.Std.IM.F_eq, Tom.Machine.Std.CM.F_eq, List.getD_cons_zero, List.getD_cons_succ] at *); omega))

/-! ## The arities the callers use (names for the generator's callee table) -/

abbrev mpInitMulti2 : HContractN := mpInitMultiN 2
abbrev mpInitMulti3 : HContractN := mpInitMultiN 3
abbrev mpClearMulti2 : HContractN := mpClearMultiN 2
abbrev mpClearMulti3 : HContractN := mpClearMultiN 3

/-- No stack arguments below arity 8 (`IMRes.sargs`, `CMRes.sargs` for `k ≤ 7`). -/
theorem no_sargs {k : Nat} (hk : k ≤ 7) {P : Fin (k - 7) → Prop} : ∀ j, P j := fun j => absurd j.2 (by omega)

end Tom.Machine.Std
