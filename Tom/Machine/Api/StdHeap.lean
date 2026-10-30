import Tom.Machine.Kit.MeetHeap
import Tom.Machine.Api.StdLib
import Tom.Machine.Api.Exch
import Tom.Machine.Fn.ExchMain
import Tom.Machine.Fn.CallocMain
import Tom.Machine.Fn.AllocFree
import Tom.Machine.Fn.AllocRealloc

/-!
# Allocating contracts as `HContract` records (`Kit/MeetHeap.lean`), and `mp_exch`

* `calloc(n, 4)` (`MP_CALLOC(n, sizeof(mp_digit))`): the site `.site` is placed
  at the fresh block, a zeroed digit array of `n` digits, or stays `Iv.nil`.
* `free(dp)` of a live digit array: the site (the array) retired to `Iv.nil`.
* `realloc(dp, 4 n')` (grow) of a live digit array: the site re-placed at the
  fresh block holding the old digits (the rest unknown), or kept.
* `mp_exch(a, b)` (a plain `Contract`): the two structs swap their headers.

Each is its `Api/Alloc.lean` statement re-read: `Ctx` from the stack residue
(`sp` and `gp` pinned in the arguments), `Heap`/`_impure_ptr` from `AHeap`.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

theorem At.gp_eq {pc : BitVec 64} {L : GRegs} {m : Mem} {v : Abi} {outp : Array String} {c : Vsa.Machine.Config}
    (h : At pc L m v.keep outp c) {x : BitVec 64} (hx : lookupG 3 L = some x) : v.gp = x := by
  have h1 := gholds_lookup L h.regs hx
  have h2 := gholds_lookup (n := 3) (v := v.gp) v.keep h.keep rfl
  rw [h1] at h2; exact (Option.some.inj h2).symm

/-- The stack residue of an allocator call with `F` bytes. -/
structure StkRes (sp F : Nat) : Prop where
  al : sp % 16 = 0
  lo : heapEnd + F ≤ sp
  hi : sp ≤ 0x100000000

theorem StkRes.ctx {m : Mem} {v : Abi} {outp : Array String} {c : Vsa.Machine.Config} {sp F : Nat}
    {pc ra : BitVec 64} {L : GRegs} (h : StkRes sp F) (hat : At pc L m v.keep outp c)
    (hs : lookupG 2 L = some (BitVec.ofNat 64 sp)) (hg : lookupG 3 L = some gpV) (himg : Img m)
    (himp : ImpureAt m) (hra : ra.toNat % 4 = 0) : Ctx m v sp F ra :=
  { img := himg, impure := himp, gp := At.gp_eq hat hg, sp_v := At.sp_eq hat hs, sp_al := h.al
    sp_lo := h.lo, sp_hi := h.hi, ra_al := hra }

theorem stk_in {sp F a : Nat} (h : StkRes sp F) (hs : Stk sp F a) : (⟨sp - F, F⟩ : Iv).In a := by
  have := h.lo; unfold Stk at hs; simp only [Iv.In]; omega

theorem stk_off_imp {sp F a : Nat} (h : StkRes sp F) (hs : Stk sp F a) : ¬ ImpI a := by
  have := h.lo; have eE : heapEnd = 0x87800000 := rfl
  unfold Stk at hs; unfold ImpI impurePtr; omega

/-- The block `(q, n)` is off the allocator once it is live. -/
theorem off_blk {H : List (Nat × Nat)} {q n : Nat} (hf : Fresh H q n) (hn : 0 < n) :
    Off ⟨q, n⟩ ((q, n) :: H) :=
  { lo := show 0x80000000 ≤ q by have := hf.lo; have e : heapStart = 0x80019d10 := rfl; omega
    pt := fun a ha hf' => by
      simp only [Iv.In] at ha
      rcases hf' with (hg | ⟨_, _, hb⟩) | hi
      · have := Global.lt hg; have := hf.lo; omega
      · exact hb (q, n) (List.mem_cons_self ..) ⟨ha.1, ha.2⟩
      · have := hf.lo; have e : heapStart = 0x80019d10 := rfl; unfold ImpI impurePtr at hi; omega
    edge := fun h => by simp only at h; omega }

theorem foot_uncons {H : List (Nat × Nat)} {e : Nat × Nat} {a : Nat} (h : Foot H a) :
    Foot (e :: H) a ∨ InBlk e a := by
  by_cases hb : InBlk e a
  · exact .inr hb
  · rcases h with hg | ⟨h1, h2, h3⟩
    · exact .inl (.inl hg)
    · exact .inl (.inr ⟨h1, h2, fun e' he => by
        rcases List.mem_cons.1 he with rfl | he
        · exact hb
        · exact h3 e' he⟩)

/-! ## `calloc(n, 4)` -/

inductive Ca | stk | site | code
  deriving DecidableEq

structure CaP where
  sp : Nat
  n : Nat
  H : List (Nat × Nat)

structure CaRes (p : CaP) : Prop where
  stk : StkRes p.sp callocDepth
  n_pos : 0 < p.n
  n_lt : p.n < 2 ^ 32

/-- The zeroed digit array at `q`, or nothing. -/
def Ca.siteK (n : Nat) : Option Nat → Kind
  | none => .ram
  | some q => .mpD q n (fun _ => 0)

def Ca.siteI (n : Nat) : Option Nat → Iv
  | none => Iv.nil
  | some q => ⟨q, 4 * n⟩

def Ca.hout (n : Nat) (H : List (Nat × Nat)) : Option Nat → List (Nat × Nat)
  | none => H
  | some q => (q, 4 * n) :: H

/-- A non-null result is a fresh block. -/
def Ca.Q (n : Nat) (H : List (Nat × Nat)) : Option Nat → Prop
  | none => True
  | some q => Fresh H q (4 * n)

def Ca.lay (sp : Nat) : Ca → Iv
  | .stk => ⟨sp - callocDepth, callocDepth⟩
  | .site => Iv.nil
  | .code => textIv

def calloc : HContract where
  P := CaP
  X := Option Nat
  R := Ca
  all := [.stk, .site, .code]
  hall r := by cases r <;> simp
  entry := callocEntry
  args p := [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.n), (11, 4#64)]
  rets _ x ra := [(1, ra), (10, BitVec.ofNat 64 (x.getD 0))]
  lay p := Ca.lay p.sp
  kind _ := fun | .code => .code | _ => .ram
  out p x := fun | .stk => .ram | .site => Ca.siteK p.n x | .code => .code
  isW := fun | .code => false | _ => true
  ws := [.stk, .site]
  site := .site
  site' p x := Ca.siteI p.n x
  hin p := p.H
  hout p x := Ca.hout p.n p.H x
  Res := CaRes
  Q p x := Ca.Q p.n p.H x
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by cases r <;> simp_all [Kind.isRam]
  pos p _ r := by
    cases r with
    | stk => exact .inl (show 0 < callocDepth by decide)
    | site => exact .inr (.inl (show 0x80000000 < heapStart by decide))
    | code => exact .inl (show 0 < textLen by decide)
  spec := by
    intro p m v outp ra hra hres hS hB hH _ c hc
    obtain ⟨sp, n, H⟩ := p
    have hctx := hres.stk.ctx hc rfl rfl (hB .code).2 hH.imp hra
    obtain ⟨c', hs, q, M, hat, hpost⟩ := Fn.Calloc.calloc_correct hctx hH.heap hres.n_lt (by decide) c
      (hc.subL rfl)
    have hW : ∀ a, callocW H sp a → InAny (Ca.lay sp) [Ca.stk, .site] a ∨ Foot H a := fun a ha => ha.elim .inr fun h => .inl (.inl (stk_in hres.stk h))
    have himp : ∀ a, ImpI a → ¬ callocW H sp a := fun a hi hw =>
      hw.elim (impure_off_foot hi.1 hi.2) (fun hs => stk_off_imp hres.stk hs hi)
    cases hpost with
    | null h =>
      refine ⟨c', hs, none, M, hat, trivial, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | site => exact absurd rfl hrs
                | code => simp at hr
              wsite := ⟨trivial, Ram.nil⟩, place := .keep
              frame := HFrm.ofKeep h.keep hW, heap := ⟨h.heap, ImpureAt.of_keep h.keep (fun a h1 h2 => himp a ⟨h1, h2⟩) hH.imp⟩
              foot := fun a ha => .inl ha, off := Off.nil H }
    | @ok q h zero =>
      have hf := h.fresh
      rw [Nat.mul_comm] at hf
      change Fresh H q (4 * n) at hf
      have hn1 : 0 < n := hres.n_pos
      have hn : 0 < 4 * n := by omega
      refine ⟨c', hs, some q, M, hat, hf, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | site => exact absurd rfl hrs
                | code => simp at hr
              wsite := ⟨Iv.sub_self _,
                { ram := (Place.fresh (I := Iv.nil) hf hn).ram Ram.nil, al := by have := hf.al; omega
                  arr := fun j hj => by
                    rw [bytesT4_zero fun t ht => by
                      rw [show q + 4 * j + t = q + (4 * j + t) by omega]; exact zero _ (by omega)] }⟩
              place := .fresh hf hn
              frame := HFrm.ofKeep h.keep hW
              heap := ⟨by have := h.heap; rwa [Nat.mul_comm] at this, ImpureAt.of_keep h.keep (fun a h1 h2 => himp a ⟨h1, h2⟩) hH.imp⟩
              foot := fun a ha => .inl (Foot.of_cons ha), off := off_blk hf hn }

/-! ## `free(dp)` of a live digit array -/

inductive Fr | stk | site | code
  deriving DecidableEq

structure FrP where
  sp : Nat
  dp : Nat
  n : Nat
  f : Nat → Nat
  H : List (Nat × Nat)

def Fr.lay (sp dp n : Nat) : Fr → Iv
  | .stk => ⟨sp - depth, depth⟩
  | .site => ⟨dp, 4 * n⟩
  | .code => textIv

def free : HContract where
  P := FrP
  X := Unit
  R := Fr
  all := [.stk, .site, .code]
  hall r := by cases r <;> simp
  entry := freeEntry
  args p := [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.dp)]
  rets _ _ ra := [(1, ra)]
  lay p := Fr.lay p.sp p.dp p.n
  kind p := fun | .stk => .ram | .site => .mpD p.dp p.n p.f | .code => .code
  out _ _ := fun | .code => .code | _ => .ram
  isW := fun | .code => false | _ => true
  ws := [.stk, .site]
  site := .site
  site' _ _ := Iv.nil
  hin p := (p.dp, 4 * p.n) :: p.H
  hout p _ := p.H
  Res p := StkRes p.sp depth ∧ 0 < p.n
  Q _ _ := True
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by cases r <;> simp_all [Kind.isRam]
  pos p h r := by
    cases r with
    | stk => exact .inl (show 0 < depth by decide)
    | site => exact .inl (show 0 < 4 * p.n by have := h.2; omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := by
    intro p m v outp ra hra hres hS hB hH _ c hc
    obtain ⟨sp, dp, n, f, H⟩ := p
    have hctx := hres.1.ctx hc rfl rfl (hB .code).2 hH.imp hra
    obtain ⟨c', hs, M, hat, hpost⟩ := Fn.Alloc.free_correct hctx hH.heap c (hc.subL rfl)
    have hW : ∀ a, blkW H dp (4 * n) sp a → InAny (Fr.lay sp dp n) [Fr.stk, .site] a ∨ Foot ((dp, 4 * n) :: H) a :=
      fun a ha => by
        rcases ha with h | h | h
        · exact .inr h
        · exact .inl (.inr (.inl h))
        · exact .inl (.inl (stk_in hres.1 h))
    have himp : ∀ a, ImpI a → ¬ blkW H dp (4 * n) sp a := fun a hi hw => by
      rcases hw with h | h | h
      · exact impure_off_foot hi.1 hi.2 h
      · have := (hB .site).2.ram.lo_ge
        have hd := Fn.Alloc.Heap.blk hH.heap (List.mem_cons_self ..)
        have e : heapStart = 0x80019d10 := rfl
        unfold InBlk at h; unfold ImpI impurePtr at hi; simp only at h hd; omega
      · exact stk_off_imp hres.1 h hi
    refine ⟨c', hs, (), M, hat, trivial, ?_⟩
    exact { wit := fun r hr hrs => by
              cases r with
              | stk => exact ⟨trivial, (hB .stk).2⟩
              | site => exact absurd rfl hrs
              | code => simp at hr
            wsite := ⟨trivial, Ram.nil⟩, place := .nil
            frame := HFrm.ofKeep hpost.keep hW, heap := ⟨hpost.heap, ImpureAt.of_keep hpost.keep (fun a h1 h2 => himp a ⟨h1, h2⟩) hH.imp⟩
            foot := fun a ha => foot_uncons ha, off := Off.nil H }

/-! ## `realloc(dp, 4 n')` (grow) of a live digit array -/

structure RaP where
  sp : Nat
  dp : Nat
  n : Nat
  f : Nat → Nat
  n' : Nat
  H : List (Nat × Nat)

structure RaRes (p : RaP) : Prop where
  stk : StkRes p.sp depth
  pos : 0 < p.n
  grow : p.n < p.n'
  lt : 4 * p.n' < 2 ^ 64

/-- The grown array: the old digits below `n`, the block's bytes above. -/
def Ra.out (p : RaP) : Option (Nat × (Nat → Nat)) → Fr → Kind
  | none, .site => .mpD p.dp p.n p.f
  | some (q, g), .site => .mpD q p.n' g
  | _, .code => .code
  | _, .stk => .ram

def Ra.site' (p : RaP) : Option (Nat × (Nat → Nat)) → Iv
  | none => ⟨p.dp, 4 * p.n⟩
  | some (q, _) => ⟨q, 4 * p.n'⟩

def Ra.hout (p : RaP) : Option (Nat × (Nat → Nat)) → List (Nat × Nat)
  | none => (p.dp, 4 * p.n) :: p.H
  | some (q, _) => (q, 4 * p.n') :: p.H

def Ra.Q (p : RaP) : Option (Nat × (Nat → Nat)) → Prop
  | none => True
  | some (_, g) => ∀ j, j < p.n → g j = p.f j

def realloc : HContract where
  P := RaP
  X := Option (Nat × (Nat → Nat))
  R := Fr
  all := [.stk, .site, .code]
  hall r := by cases r <;> simp
  entry := Api.Alloc.reallocEntry
  args p := [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.dp), (11, BitVec.ofNat 64 (4 * p.n'))]
  rets _ x ra := [(1, ra), (10, BitVec.ofNat 64 (match x with | none => 0 | some (q, _) => q))]
  lay p := Fr.lay p.sp p.dp p.n
  kind p := fun | .stk => .ram | .site => .mpD p.dp p.n p.f | .code => .code
  out := Ra.out
  isW := fun | .code => false | _ => true
  ws := [.stk, .site]
  site := .site
  site' := Ra.site'
  hin p := (p.dp, 4 * p.n) :: p.H
  hout := Ra.hout
  Res := RaRes
  Q := Ra.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by cases x <;> cases r <;> simp_all [Ra.out, Kind.isRam]
  pos p h r := by
    cases r with
    | stk => exact .inl (show 0 < depth by decide)
    | site => exact .inl (show 0 < 4 * p.n by have := h.pos; omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := by
    intro p m v outp ra hra hres hS hB hH hoff c hc
    obtain ⟨sp, dp, n, f, n', H⟩ := p
    have hst : StkRes sp depth := hres.stk
    have hpos : 0 < n := hres.pos
    have hgr : n < n' := hres.grow
    have hlt : 4 * n' < 2 ^ 64 := hres.lt
    have hctx := hst.ctx hc rfl rfl (hB .code).2 hH.imp hra
    obtain ⟨c', hs, q, M, hat, hpost⟩ := Fn.Alloc.realloc_correct hctx hH.heap (show 4 * n < 4 * n' by omega) hlt c
      (hc.subL rfl)
    have hd : Dig m dp n f := (hB .site).2
    have hW : ∀ a, blkW H dp (4 * n) sp a → InAny (Fr.lay sp dp n) [Fr.stk, .site] a ∨ Foot ((dp, 4 * n) :: H) a :=
      fun a ha => by
        rcases ha with h | h | h
        · exact .inr h
        · exact .inl (.inr (.inl h))
        · exact .inl (.inl (stk_in hst h))
    have himp : ∀ a, ImpI a → ¬ blkW H dp (4 * n) sp a := fun a hi hw => by
      rcases hw with h | h | h
      · exact impure_off_foot hi.1 hi.2 h
      · have hb := Fn.Alloc.Heap.blk hH.heap (List.mem_cons_self ..)
        have e : heapStart = 0x80019d10 := rfl
        unfold InBlk at h; unfold ImpI impurePtr at hi; simp only at h hb; omega
      · exact stk_off_imp hst h hi
    have hstk : ∀ r, r ∈ [Fr.stk, .site] → r ≠ .site → ∀ x, (Ra.out ⟨sp, dp, n, f, n', H⟩ x r).Fits (Fr.lay sp dp n r) ∧
        (Ra.out ⟨sp, dp, n, f, n', H⟩ x r).Wit (Fr.lay sp dp n r) M := fun r hr hrs x => by
      cases r with
      | stk => cases x <;> exact ⟨trivial, (hB .stk).2⟩
      | site => exact absurd rfl hrs
      | code => simp at hr
    cases hpost with
    | null h same =>
      refine ⟨c', hs, none, M, hat, trivial, ?_⟩
      have harr : ArrAt M dp n f := fun j hj => by
        have e := bytesT4_of_getD (M := M) (m := m) (a := dp + 4 * j) (b := dp + 4 * j)
          (fun k hk => by rw [show dp + 4 * j + k = dp + (4 * j + k) by omega]; exact same _ (by dsimp only; omega))
        rw [e]; exact hd.arr j hj
      have hdM : Dig M dp n f := ⟨hd.ram, hd.al, harr⟩
      exact { wit := fun r hr hrs => hstk r hr hrs none
              wsite := ⟨Iv.sub_self _, hdM⟩
              place := .keep, frame := HFrm.ofKeep h.keep hW
              heap := ⟨h.heap, ImpureAt.of_keep h.keep (fun a h1 h2 => himp a ⟨h1, h2⟩) hH.imp⟩
              foot := fun a ha => .inl ha, off := hoff .site }
    | @ok q h copy =>
      have hf := h.fresh
      have hn : 0 < 4 * n' := by omega
      let g : Nat → Nat := fun j => if j < n then f j else (bytesT4 M (q + 4 * j)).toNat
      refine ⟨c', hs, some (q, g), M, hat, fun j hj => by simp [g, hj], ?_⟩
      have harr : ArrAt M q n' g := fun j hj => by
          by_cases hjn : j < n
          · simp only [g, if_pos hjn]
            have e := bytesT4_of_getD (M := M) (m := m) (a := q + 4 * j) (b := dp + 4 * j)
              (fun k hk => by
                rw [show q + 4 * j + k = q + (4 * j + k) by omega, show dp + 4 * j + k = dp + (4 * j + k) by omega]
                exact copy _ (by dsimp only; omega))
            rw [e]; exact hd.arr j hjn
          · simp only [g, if_neg hjn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      have hdM : Dig M q n' g := ⟨(Place.fresh (I := Iv.nil) hf hn).ram Ram.nil, by have := hf.al; omega, harr⟩
      exact { wit := fun r hr hrs => hstk r hr hrs _
              wsite := ⟨Iv.sub_self _, hdM⟩
              place := .regrow hf hn rfl, frame := HFrm.ofKeep h.keep hW
              heap := ⟨h.heap, ImpureAt.of_keep h.keep (fun a h1 h2 => himp a ⟨h1, h2⟩) hH.imp⟩
              foot := fun a ha => foot_uncons (Foot.of_cons ha), off := off_blk hf hn }

/-! ## `mp_exch(a, b)` -/

structure ExP where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt

def mpExch : Contract where
  P := ExP
  X := Unit
  R := Two.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Two.all
  entry := Exch.entry
  args p := [(10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]
  rets _ ra := [(1, ra)]
  lay p := Exch.lay p.sp p.pa p.adp p.pb p.bdp p.a p.b
  kind := fun ⟨_, pa, adp, pb, bdp, a, b⟩ => Tom.Machine.Two.kind pa adp pb bdp a b
  out := fun ⟨_, pa, adp, pb, bdp, a, b⟩ _ r => match r with
    | .aS => .mpS pa bdp b
    | .bS => .mpS pb adp a
    | r => Tom.Machine.Two.kind pa adp pb bdp a b r
  isW := Two.isW2
  ws := [.aS, .bS]
  Res p := p.a.sign < 2 ^ 31
  Q _ _ := True
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r hr h := by cases p; cases r <;> simp_all [Kind.isRam]
  out_ind p x r hr h := by cases p; cases r <;> simp_all [Kind.isRam, Kind.indep]
  spec := by
    intro p m v outp ra hra hres hS hB
    obtain ⟨sp, pa, adp, pb, bdp, a, b⟩ := p
    have ga : MpGeom pa adp a.alloc := Hdr.geom (hB .aS).2
    have gb : MpGeom pb bdp b.alloc := Hdr.geom (hB .bS).2
    have hpre : Exch.Pre m sp pa adp pb bdp a b ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2, ga := ga, gb := gb
        sgn := hres, ra_al := hra, img := (hB .code).2, lay := hS }
    refine Triple.rmap (fun cf ⟨M, hat, hpost⟩ => ?_) (Fn.Exch.correct (v := v) (outp := outp) hpre)
    have d1 := hS .aS .bD (by decide); have d2 := hS .bS .aD (by decide)
    simp only [Exch.lay, Two.lay, Iv.Disj, Disj] at d1 d2
    refine ⟨(), M, hat.sub rfl rfl, trivial, ?_, hpost.frame⟩
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact ⟨Iv.sub_self _, Hdr.of_mpAt hpost.ra_
        { st := ga.st, st_al := ga.st_al, ds := gb.ds, ds_al := gb.ds_al, disj := by
            simp only [Layout.sizeofMpInt, Layout.sizeofDigit]; omega }⟩
    · exact hB.keep hS hpost.frame Two.R.aD
    · exact ⟨Iv.sub_self _, Hdr.of_mpAt hpost.rb
        { st := gb.st, st_al := gb.st_al, ds := ga.ds, ds_al := ga.ds_al, disj := by
            simp only [Layout.sizeofMpInt, Layout.sizeofDigit]; omega }⟩
    · exact hB.keep hS hpost.frame Two.R.bD
    · exact hB.keep hS hpost.frame Two.R.code

end Tom.Machine.Std
