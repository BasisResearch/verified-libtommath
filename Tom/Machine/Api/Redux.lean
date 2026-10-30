import Tom.Machine.Api.Std_exf

/-!
# `redux(x, n, mp)`: `s_mp_exptmod_fast`'s reduction through a function pointer

`s_mp_exptmod_fast` calls its reduction indirectly (`jalr s8`), `s8` set by the setup branch:
`s_mp_montgomery_reduce_fast` (`redmode == 0`, `2 P->used + 1 < MP_WARRAY`), `mp_dr_reduce` (`1`),
`mp_reduce_2k` (else). The three take `(x, n, rho)` in `a0`–`a2` and leave `x` reduced in place (no
`mp_grow`, D5), `mp_reduce_2k` with a temporary (`MP_MEM` possible). `reduxH k` is the one allocating
contract of the three, by mode `k`: the regions and parameters of `Api/MpReduce2k.lean` (`a` is `x`)
on the deepest stack (`s_mp_montgomery_reduce_fast`'s 4256 bytes), entry `reduxE k`, the residue and
the result relation `RPK k` of the routine that mode calls. The site is `x`'s digit array, kept.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Mont
open Tom.Machine.Api.MpReduce2k (P R)

/-- The routine `redux` points to in mode `k`. -/
def reduxE : Nat → BitVec 64
  | 0 => MontRedFast.entry
  | 1 => DrReduce.entry
  | _ => MpReduce2k.entry

/-- The stack depth: `s_mp_montgomery_reduce_fast`'s (`mp_dr_reduce` 176, `mp_reduce_2k` 656). -/
abbrev Fred : Nat := 4256

def layR (p : P) : R → Iv
  | .stk => ⟨p.sp - Fred, Fred⟩
  | r => MpReduce2k.lay p r

/-- `s_mp_montgomery_reduce_fast(x, n, rho)`'s needs (`Std.RedFRes` without the stack). -/
structure ResMont (p : P) : Prop where
  va : p.a.Valid
  vn : p.n.Valid
  rho_ok : (p.n.mag * p.d + 1) % radix = 0
  rho_lt : p.d < radix
  x_lt : p.a.mag < p.n.mag * radix ^ p.n.used
  nu_pos : 1 ≤ p.n.used
  nu_le : p.n.used ≤ 255
  room : p.n.used < p.a.alloc

/-- `mp_dr_reduce(x, n, k)`'s needs (`Std.DrRedRes` without the stack). -/
structure ResDr (p : P) : Prop where
  va : p.a.Valid
  vn : p.n.Valid
  n_pos : 0 < p.n.mag
  k_lt : p.d < radix
  x_lt : p.a.mag < radix ^ (2 * p.n.used)
  room : 2 * p.n.used ≤ p.a.alloc

/-- `mp_reduce_2k(a, n, d)`'s needs (`Api.MpReduce2k.Res` without the stack and the structs). -/
structure Res2k (p : P) : Prop where
  va : p.a.Valid
  vn : p.n.Valid
  npos : 0 < p.n.mag
  d_lt : p.d < radix
  hd : p.n.mag + p.d = 2 ^ nbits p.n.mag
  bits : Layout.digitBits * p.n.used < 2 ^ 31
  aroom : p.a.used + 1 ≤ p.a.alloc
  qroom : p.a.used + 1 ≤ defPrec

/-- What mode `k`'s routine needs beyond the stack and the structs off the arena. -/
def ResK : Nat → P → Prop
  | 0, p => ResMont p
  | 1, p => ResDr p
  | _, p => Res2k p

structure RedRes (k : Nat) (p : P) : Prop where
  stk : StkRes p.sp Fred
  aoff : OffHeap p.pa 24
  noff : OffHeap p.pn 24
  k : ResK k p

/-- What mode `k`'s routine leaves in `x` (`a`). -/
def RPK : Nat → MpInt → MpInt → Nat → MpInt → Prop
  | 0, x, n, d, x' => Mont.RedcPost x n d x'
  | 1, x, n, d, x' => Reduce.DrReducePost x n d x'
  | _, x, n, d, x' => Reduce.Reduce2kPost x n d x'

/-- `MP_MEM` (`x` as it was), or `x` reduced in place. -/
def RQK (k : Nat) (p : P) : Option MpInt → Prop
  | none => True
  | some a' => RPK k p.a p.n p.d a' ∧ a'.alloc = p.a.alloc

theorem stkR {sp F : Nat} (h : StkRes sp Fred) (hF : F ≤ Fred) : StkRes sp F :=
  ⟨h.al, Nat.le_trans (Nat.add_le_add_left hF _) h.lo, h.hi⟩

/-- The `Two` contracts' regions in `mp_reduce_2k`'s (`n` read is Two's `a`, `x` Two's `b`). -/
def σT : Two.R → R
  | .stk => .stk | .aS => .nS | .aD => .nD | .bS => .aS | .bD => .aD | .code => .code

theorem redux_two (k : Nat) (F : Nat) (hF : F ≤ 4256)
    {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}
    (hsp : 4256 ≤ p.sp) (hS : Sound (layR p) MpReduce2k.isW) (hB : Bundle (layR p) (MpReduce2k.kind p) m)
    (hH : AHeap m p.H) (hoff : ∀ r, Off (layR p r) p.H)
    (hrun : Triple (At (reduxE k) ((1, ra) :: MpReduce2k.args p) m v.keep outp)
      (fun cf => ∃ x' M, At ra [(1, ra), (10, 0#64)] M v.keep outp cf ∧ RPK k p.a p.n p.d x' ∧
        x'.alloc = p.a.alloc ∧ Bundle (Two.lay F p.sp p.pn p.ndp p.pa p.adp p.n p.a)
          (Tom.Machine.Two.kind p.pn p.ndp p.pa p.adp p.n x') M ∧
        Frm (Two.lay F p.sp p.pn p.ndp p.pa p.adp p.n p.a) Two.ws m M)) :
    Triple (At (reduxE k) ((1, ra) :: MpReduce2k.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (MpReduce2k.rets p x ra) M v.keep outp cf ∧ RQK k p x ∧
        HPost (layR p) MpReduce2k.ws .aD (MpReduce2k.out p x) (layR p .aD) p.H p.H m M) := by
  refine Triple.rmap (fun cf ⟨x', M, hat, hq, hal, hb, hF'⟩ => ?_) hrun
  have hsub : ∀ k, (Two.lay F p.sp p.pn p.ndp p.pa p.adp p.n p.a k).Sub (layR p (σT k)) := by
    intro k; cases k
    · show Iv.Sub ⟨p.sp - F, F⟩ ⟨p.sp - 4256, 4256⟩
      unfold Iv.Sub; dsimp only; omega
    all_goals exact Iv.sub_self _
  have hfr : Frm (layR p) MpReduce2k.ws m M := Frm.push σT hsub hF'
  have hst : St (layR p) MpReduce2k.isW MpReduce2k.ws (MpReduce2k.out p (some x')) m M := by
    refine ⟨hS, fun r => ?_, hfr⟩
    cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact ⟨Iv.sub_self _, by
        have := (hb .bS).2; simp only [Tom.Machine.Two.kind, Two.lay] at this
        show Hdr M p.pa p.adp x'; exact this⟩
    · refine ⟨by show Iv.Sub ⟨p.adp, 4 * p.a.alloc⟩ _; exact Iv.sub_self _, ?_⟩
      have := (hb .bD).2; simp only [Tom.Machine.Two.kind, Two.lay] at this
      show Dig M p.adp p.a.alloc x'.digit
      rw [← hal]; exact this
    · exact hB.keep hS hfr MpReduce2k.R.nS
    · exact hB.keep hS hfr MpReduce2k.R.nD
    · exact hB.keep hS hfr MpReduce2k.R.code
  exact ⟨some x', M, hat, ⟨hq, hal⟩, HPost.inplace hst hH hoff rfl rfl (fun r _ _ => hst.wit r) (hst.wit .aD)⟩

theorem sub2k (p : P) (r : R) : (MpReduce2k.lay p r).Sub (layR p r) := by
  cases r
  · show Iv.Sub ⟨p.sp - MpReduce2k.F, MpReduce2k.F⟩ ⟨p.sp - 4256, 4256⟩
    have e : MpReduce2k.F = 656 := rfl
    unfold Iv.Sub; dsimp only; rw [e]; omega
  all_goals exact Iv.sub_self _

/-- `mp_reduce_2k`'s post over the deeper stack. -/
theorem HPost.widen2k {p : P} {x : Option MpInt} {m M : Mem}
    (hB : Bundle (layR p) (MpReduce2k.kind p) m)
    (h : HPost (MpReduce2k.lay p) MpReduce2k.ws .aD (MpReduce2k.out p x) (MpReduce2k.site' p x) p.H p.H m M) :
    HPost (layR p) MpReduce2k.ws .aD (MpReduce2k.out p x) (layR p .aD) p.H p.H m M where
  wit r hr hrs := by
    cases r
    · cases x <;> exact ⟨trivial, (hB .stk).2⟩
    · exact h.wit .aS hr hrs
    · exact absurd rfl hrs
    all_goals simp [MpReduce2k.ws] at hr
  wsite := h.wsite
  place := h.place
  frame a ha := h.frame a fun h' => ha (h'.imp (fun hi => by
    obtain ⟨w, hw, hx⟩ := hi.exists
    have := sub2k p w
    exact InAny.of_mem hw (by unfold Iv.Sub Iv.In at *; omega)) id)
  heap := h.heap
  foot := h.foot
  off := h.off

theorem used_pos_of_mag {x : MpInt} (h : 0 < x.mag) : 0 < x.used :=
  Nat.pos_of_ne_zero fun h0 => by rw [MpInt.mag_used_zero h0] at h; exact absurd h (by decide)

theorem subT (p : P) (F : Nat) (hF : F ≤ 4256) (k : Two.R) :
    (Two.lay F p.sp p.pn p.ndp p.pa p.adp p.n p.a k).Sub (layR p (σT k)) := by
  cases k
  · show Iv.Sub ⟨p.sp - F, F⟩ ⟨p.sp - 4256, 4256⟩
    unfold Iv.Sub; dsimp only; omega
  all_goals exact Iv.sub_self _

/-- The `Two` contracts' parameters from `mp_reduce_2k`'s. -/
def toRF (p : P) : RedFP := ⟨p.sp, p.pa, p.adp, p.pn, p.ndp, p.a, p.n, p.d⟩

/-- **`redux` in mode `k`** as an allocating contract (`Api/MpReduce2k.lean`'s regions). -/
def reduxH (k : Nat) : HContract where
  P := P
  X := Option MpInt
  R := R
  all := [.stk, .aS, .aD, .nS, .nD, .code]
  hall := MpReduce2k.all
  entry := reduxE k
  args := MpReduce2k.args
  rets := MpReduce2k.rets
  lay := layR
  kind := MpReduce2k.kind
  out := MpReduce2k.out
  isW := MpReduce2k.isW
  ws := MpReduce2k.ws
  site := .aD
  site' p _ := layR p .aD
  hin p := p.H
  hout p _ := p.H
  Res := RedRes k
  Q := RQK k
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | _ <;> cases r <;> simp_all [MpReduce2k.out, MpReduce2k.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have hal : 0 < p.a.alloc := by
      rcases k with _ | _ | k
      · have h' : ResMont p := h.k; have := h'.room; omega
      · have h' : ResDr p := h.k; have := h'.room; have := used_pos_of_mag h'.n_pos; omega
      · have h' : Res2k p := h.k; have := h'.aroom; omega
    have hnl : 0 < p.n.alloc := by
      rcases k with _ | _ | k
      · have h' : ResMont p := h.k; have := h'.nu_pos; have := h'.vn.used_le; omega
      · have h' : ResDr p := h.k; exact Tom.Machine.MpInt.alloc_pos_of_mag h'.vn h'.n_pos
      · have h' : Res2k p := h.k; exact Tom.Machine.MpInt.alloc_pos_of_mag h'.vn h'.npos
    cases r with
    | stk => left; show 0 < Fred; decide
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | nD => exact .inl (show 0 < 4 * p.n.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | aS | nS => exact .inl (show 0 < 24 by decide)
  spec := by
    intro p m v outp ra hra hres hS hB hH hoff c hc
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 p.sp) rfl
    have hgp := At.gp_eq hc (x := gpV) rfl
    simp only at he hgp; subst he hgp
    have hlo := hres.stk.lo
    rw [show heapEnd = 0x87800000 from rfl, show Fred = 4256 from rfl] at hlo
    have hal := hres.stk.al
    have hsp : 4256 ≤ p.sp := by omega
    rcases k with _ | _ | k
    · -- `s_mp_montgomery_reduce_fast`
      have hk : ResMont p := hres.k
      obtain ⟨va, vn, ho, hl, hx, h1, h2, hr⟩ := hk
      have hS' : Sound (montRedF.lay (toRF p)) Two.isW :=
        hS.pull σT [.stk, .aS, .aD, .bS, .bD, .code] Two.all (subT p 4256 (Nat.le_refl _))
      have hB' : Bundle (montRedF.lay (toRF p)) (montRedF.kind (toRF p)) m :=
        hB.pull σT (subT p 4256 (Nat.le_refl _)) (fun k => by cases k <;> rfl)
          (fun k => by cases k <;> first | trivial | exact Iv.sub_self _)
      have hr' : montRedF.Res (toRF p) := ⟨va, vn, ho, hl, hx, h1, h2, hr, hal, hsp⟩
      have hrun := montRedF.spec (v := ⟨BitVec.ofNat 64 p.sp, gpV, tp, s0, s⟩) (outp := outp) hra hr' hS' hB'
      have hrun' : Triple (At (reduxE 0) ((1, ra) :: MpReduce2k.args p) m
          (⟨BitVec.ofNat 64 p.sp, gpV, tp, s0, s⟩ : Abi).keep outp) _ :=
        Triple.lmap (fun _ h => by exact At.sub h rfl rfl) hrun
      refine redux_two 0 4256 (Nat.le_refl _) hsp hS hB hH hoff
        (Triple.rmap (fun cf ⟨x', M, hat, hq, hb, hF⟩ => ⟨x', M, hat, hq, hq.alloc, hb, hF⟩)
          hrun') c hc
    · -- `mp_dr_reduce`
      have hk : ResDr p := hres.k
      obtain ⟨va, vn, hn, hl, hx, hr⟩ := hk
      have hS' : Sound (drRedC.lay (toRF p)) Two.isW :=
        hS.pull σT [.stk, .aS, .aD, .bS, .bD, .code] Two.all (subT p 176 (by decide))
      have hB' : Bundle (drRedC.lay (toRF p)) (drRedC.kind (toRF p)) m :=
        hB.pull σT (subT p 176 (by decide)) (fun k => by cases k <;> rfl)
          (fun k => by cases k <;> first | trivial | exact Iv.sub_self _)
      have hr' : drRedC.Res (toRF p) := ⟨va, vn, hn, hl, hx, hr, hal, show 176 ≤ p.sp by omega⟩
      have hrun := drRedC.spec (v := ⟨BitVec.ofNat 64 p.sp, gpV, tp, s0, s⟩) (outp := outp) hra hr' hS' hB'
      have hrun' : Triple (At (reduxE 1) ((1, ra) :: MpReduce2k.args p) m
          (⟨BitVec.ofNat 64 p.sp, gpV, tp, s0, s⟩ : Abi).keep outp) _ :=
        Triple.lmap (fun _ h => by exact At.sub h rfl rfl) hrun
      refine redux_two 1 176 (by decide) hsp hS hB hH hoff
        (Triple.rmap (fun cf ⟨x', M, hat, hq, hb, hF⟩ => ⟨x', M, hat, hq.1, hq.2, hb, hF⟩)
          hrun') c hc
    · -- `mp_reduce_2k`
      have hk : Res2k p := hres.k
      obtain ⟨va, vn, hn, hl, hd, hb, ha, hq⟩ := hk
      have hnl := Tom.Machine.MpInt.alloc_pos_of_mag vn hn
      have hS' : Sound (MpReduce2k.lay p) MpReduce2k.isW :=
        hS.pull id [.stk, .aS, .aD, .nS, .nD, .code] MpReduce2k.all (sub2k p)
      have hB' : Bundle (MpReduce2k.lay p) (MpReduce2k.kind p) m :=
        hB.pull id (sub2k p) (fun k => rfl) (fun k => by cases k <;> first | trivial | exact Iv.sub_self _)
      have hoff' : ∀ r, Off (MpReduce2k.lay p r) (MpReduce2k.hin p) := fun r => (hoff r).sub (sub2k p r) (by
        cases r
        · exact .inl (show 0 < MpReduce2k.F by decide)
        · exact .inl (show 0 < 24 by decide)
        · exact .inl (show 0 < 4 * p.a.alloc by omega)
        · exact .inl (show 0 < 24 by decide)
        · exact .inl (show 0 < 4 * p.n.alloc by omega)
        · exact .inl (show 0 < textLen by decide))
      have hr' : MpReduce2k.Res p :=
        ⟨stkR hres.stk (by decide), va, vn, hn, hl, hd, hb, ha, hq, hres.aoff, hres.noff⟩
      refine Triple.rmap (fun cf ⟨x, M, hat, hq', hpo⟩ => ⟨x, M, hat, ?_, HPost.widen2k hB hpo⟩)
        (Fn.MpReduce2kG5.correct (p := p) (v := ⟨BitVec.ofNat 64 p.sp, gpV, tp, s0, s⟩) (outp := outp) hra hr' hS' hB' hH hoff') c hc
      cases x with
      | none => trivial
      | some a' => exact ⟨hq'.red, hq'.alloc⟩

end Tom.Machine.Std
