import Tom.Machine.Api.MpReduce
import Tom.Machine.Api.Std_red2f
import Tom.Machine.Fn.MpReduceMainG
import Tom.Machine.Kit.Widen
import Tom.Machine.Kit.CallR
import Tom.Spec.SMpExptmodMode

/-!
# `redux(x, n, mu)`: `s_mp_exptmod`'s reduction through a function pointer

`s_mp_exptmod` calls its reduction indirectly (`jalr s6`), `s6` set by the setup branch:
`mp_reduce` (`redmode == 0`, Barrett, `mu` from `mp_reduce_setup`) or `mp_reduce_2k_l` (else, `mu`
from `mp_reduce_2k_setup_l`). Both take `(x, n, mu)` in `a0`–`a2`, `mu` an `mp_int`, and grow `x`
(its digits re-placed). `reduxS k` is the allocating contract of the routine of mode `k`: the regions and parameters of `Api/MpReduce2kL.lean` (`a` is
`x`, `d` is `mu`; mode 0 maps `mp_reduce`'s `xS xD nS nD uS uD`), the growing contract's stack
`2872 + 8 (x->used + n->used)` (`mp_reduce`'s 2816 below it), entry `reduxSE k`, `x`'s block in
front of the heap, the result `(ok, q, x')` with `x` re-placed in both modes, the residue and the
result relation `RP k` of the routine that mode calls.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Reduce
open Tom.Machine.Api.MpReduce2kL (P R)

/-- The routine `redux` points to in mode `k`. -/
def reduxSE : Nat → BitVec 64
  | 0 => MpReduce.entry
  | _ => MpReduce2kL.entry

/-- `mp_reduce`'s parameters from `mp_reduce_2k_l`'s (`mu` is `d`). -/
def toRB (p : P) : MpReduce.P := ⟨p.sp, p.pa, p.adp, p.pn, p.ndp, p.pd, p.ddp, p.a, p.n, p.d, p.H⟩

/-- `mp_reduce`'s regions among `mp_reduce_2k_l`'s. -/
def σB : MpReduce.R → R
  | .stk => .stk | .xS => .aS | .xD => .aD | .nS => .nS | .nD => .nD | .uS => .dS | .uD => .dD
  | .code => .code

/-- What mode `k`'s routine needs (its contract's residue). -/
def ResS : Nat → P → Prop
  | 0, p => MpReduce.Res (toRB p)
  | _, p => MpReduce2kLG.Res p

structure RedSRes (k : Nat) (p : P) : Prop where
  stk : StkRes p.sp (MpReduce2kLG.F (p := p))
  k : ResS k p

/-- What mode `k`'s routine leaves in `x` (`SMpExptmodStep.rxRP`). -/
abbrev RP : Nat → MpInt → MpInt → MpInt → MpInt → Prop := SMpExptmodStep.rxRP

/-- What `x` holds after: shaped, live, placed; on `MP_OKAY` the reduction of mode `k`. -/
structure RQ (k : Nat) (p : P) (x : MpReduce2kLG.X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (MpReduce2kLG.hin p) (MpReduce2kLG.lay p .aD) (MpReduce2kLG.site' p x)
  post : x.1 = true → RP k p.a p.n p.d x.2.2

/-- `mp_reduce`'s layout over `mp_reduce_2k_l`'s names (its own stack). -/
def layB (p : P) : R → Iv
  | .stk => ⟨p.sp - MpReduce.F, MpReduce.F⟩
  | r => MpReduce2kL.lay p r

theorem stkS_le {p : P} : MpReduce.F ≤ MpReduce2kLG.F (p := p) := by
  show 2816 ≤ 2872 + 8 * (p.a.used + p.n.used); omega

/-- `mp_reduce`'s regions inside `mp_reduce_2k_l`'s growing layout. -/
theorem subB {p : P} (hF : MpReduce2kLG.F (p := p) ≤ p.sp) (r : MpReduce.R) :
    (MpReduce.lay (toRB p) r).Sub (MpReduce2kLG.lay p (σB r)) := by
  have := stkS_le (p := p)
  cases r
  · show Iv.Sub ⟨p.sp - MpReduce.F, MpReduce.F⟩ ⟨p.sp - MpReduce2kLG.F (p := p), MpReduce2kLG.F (p := p)⟩
    unfold Iv.Sub; dsimp only; omega
  all_goals exact Iv.sub_self _

/-- **`redux` in mode `k`** as an allocating contract (`Api/MpReduce2kL.lean`'s regions). -/
def reduxS (k : Nat) : HContract where
  P := P
  X := MpReduce2kLG.X
  R := R
  all := [.stk, .aS, .aD, .nS, .nD, .dS, .dD, .kc, .tc, .code]
  hall := MpReduce2kL.all
  entry := reduxSE k
  args := MpReduce2kL.args
  rets := MpReduce2kLG.rets
  lay := MpReduce2kLG.lay
  kind := MpReduce2kL.kind
  out := MpReduce2kLG.out
  isW := MpReduce2kL.isW
  ws := MpReduce2kL.ws
  site := .aD
  site' := MpReduce2kLG.site'
  hin := MpReduce2kLG.hin
  hout := MpReduce2kLG.hout
  Res := RedSRes k
  Q := RQ k
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    obtain ⟨ok, q, a'⟩ := x
    cases r <;> simp_all [MpReduce2kLG.out, MpReduce2kL.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have hal : 0 < p.a.alloc ∧ 0 < p.n.alloc ∧ 0 < p.d.alloc := by
      rcases k with _ | k
      · have h' : MpReduce.Res (toRB p) := h.k; exact ⟨h'.xpos, h'.npos, h'.upos⟩
      · have h' : MpReduce2kLG.Res p := h.k
        exact ⟨h'.apos, MpInt.alloc_pos_of_mag h'.vn h'.npos, h'.dpos⟩
    obtain ⟨h1, h2, h3⟩ := hal
    cases r with
    | stk => exact .inl (show 0 < MpReduce2kLG.F (p := p) by unfold MpReduce2kLG.F; omega)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | nD => exact .inl (show 0 < 4 * p.n.alloc by omega)
    | dD => exact .inl (show 0 < 4 * p.d.alloc by omega)
    | kc | tc => exact .inl (show 0 < 4 by decide)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (show 0 < 24 by decide)
  spec := by
    intro p m v outp ra hra hres hS hB hH hoff
    rcases k with _ | k
    · -- `mp_reduce`
      have hk : MpReduce.Res (toRB p) := hres.k
      have hF : MpReduce2kLG.F (p := p) ≤ p.sp := by
        have := hres.stk.lo; rw [show heapEnd = 0x87800000 from rfl] at this; omega
      have hsub := subB hF
      have hS' : Sound (MpReduce.lay (toRB p)) MpReduce.isW :=
        hS.pull σB [.stk, .xS, .xD, .nS, .nD, .uS, .uD, .code] MpReduce.all hsub
      have hB' : Bundle (MpReduce.lay (toRB p)) (MpReduce.kind (toRB p)) m :=
        hB.pull σB hsub (fun r => by cases r <;> rfl) (fun r => by cases r <;> first | trivial | exact Iv.sub_self _)
      have hoff' : ∀ r, Off (MpReduce.lay (toRB p) r) (MpReduce.hin (toRB p)) := fun r =>
        (hoff (σB r)).sub (hsub r) (by
          cases r
          · exact .inl (show 0 < MpReduce.F by decide)
          · exact .inl (show 0 < 24 by decide)
          · exact .inl (show 0 < 4 * p.a.alloc by have : 0 < p.a.alloc := hk.xpos; omega)
          · exact .inl (show 0 < 24 by decide)
          · exact .inl (show 0 < 4 * p.n.alloc by have : 0 < p.n.alloc := hk.npos; omega)
          · exact .inl (show 0 < 24 by decide)
          · exact .inl (show 0 < 4 * p.d.alloc by have : 0 < p.d.alloc := hk.upos; omega)
          · exact .inl (show 0 < textLen by decide))
      refine Triple.rmap (fun cf ⟨x, M, hat, hq, hpo⟩ => ⟨x, M, hat, ⟨hq.shape, hq.pos, hq.place, hq.post⟩, ?_⟩)
        (Fn.MpReduceG5.correct (p := toRB p) (v := v) (outp := outp) hra hk hS' hB' hH hoff')
      have h1 : HPost (layB p) MpReduce2kL.ws .aD (MpReduce2kLG.out p x) (MpReduce2kLG.site' p x)
          (MpReduce2kLG.hin p) (MpReduce2kLG.hout p x) m M :=
        HPost.rename (lay := layB p) σB (fun r => by cases r <;> rfl) rfl
          (fun r => by obtain ⟨_, _, _⟩ := x; cases r <;> rfl)
          (fun r hr => by
            simp only [MpReduce.ws, List.mem_cons, List.mem_nil_iff, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> decide)
          (fun r hr hne => by
            simp only [MpReduce2kL.ws, List.mem_cons, List.mem_nil_iff, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact ⟨.stk, by decide, by decide, rfl⟩
            · exact ⟨.xS, by decide, by decide, rfl⟩
            · exact absurd rfl hne) hpo
      exact HPost.widen .stk (by decide) (fun r hr => by cases r <;> first | exact absurd rfl hr | rfl)
        (by show Iv.Sub ⟨p.sp - MpReduce.F, MpReduce.F⟩ ⟨p.sp - MpReduce2kLG.F (p := p), MpReduce2kLG.F (p := p)⟩
            have := stkS_le (p := p); unfold Iv.Sub; dsimp only; omega)
        (by obtain ⟨_, _, _⟩ := x; exact ⟨trivial, (hB .stk).2⟩) h1
    · -- `mp_reduce_2k_l`
      have hk : MpReduce2kLG.Res p := hres.k
      exact Triple.rmap (fun cf ⟨x, M, hat, hq, hpo⟩ => ⟨x, M, hat, ⟨hq.shape, hq.pos, hq.place, hq.post⟩, hpo⟩)
        (Fn.MpReduce2kLGG5.correct (p := p) (v := v) (outp := outp) hra hk hS hB hH hoff)

/-! The record's fields that do not depend on the mode (for the caller's checks, without unfolding the
record and its proofs). -/
theorem reduxS_ws (k : Nat) : (reduxS k).ws = MpReduce2kL.ws := rfl
theorem reduxS_out (k : Nat) : (reduxS k).out = MpReduce2kLG.out := rfl
theorem reduxS_kind (k : Nat) : (reduxS k).kind = MpReduce2kL.kind := rfl
theorem reduxS_lay (k : Nat) : (reduxS k).lay = MpReduce2kLG.lay := rfl
theorem reduxS_isW (k : Nat) : (reduxS k).isW = MpReduce2kL.isW := rfl

/-- The residue of mode `md < 2` from the two modes' residues. -/
theorem reduxS_res {md : Nat} {p : P} (hmd : md < 2) (hstk : StkRes p.sp (MpReduce2kLG.F (p := p)))
    (h0 : md = 0 → MpReduce.Res (toRB p)) (h1 : md = 1 → MpReduce2kLG.Res p) : RedSRes md p := by
  rcases md with _ | _ | md
  · exact ⟨hstk, h0 rfl⟩
  · exact ⟨hstk, h1 rfl⟩
  · omega

/-- `redux`'s value in mode `k` (the register `s6`). -/
def reduxSA : Nat → Nat
  | 0 => 2147508748
  | _ => 2147508080

open Sail LeanRV64DExecutable.Functions in
/-- **`jalr s6` reaches mode `md`'s routine** (`call_heapR`'s `htgt`). -/
theorem reduxS_tgt {md re : Nat} (hmd : md < 2) (hre : re = reduxSA md) :
    BitVec.update (BitVec.ofNat 64 re + sign_extend (m := 64) (0#12 : BitVec 12)) 0 0#1 = (reduxS md).entry := by
  subst hre
  rcases md with _ | _ | md
  · decide
  · decide
  · omega

/-- **`redux`'s residue at `s_mp_exptmod`'s calls**: `x` a nonnegative product of residues (at most
`2 P->used` digits), `P` positive with the C's `int` arithmetic on such a product, `mu` from the mode's setup. -/
theorem reduxS_resS {md : Nat} {p : P} (hmd : md < 2) (hmu : SMpExptmodStep.MuOk p.n md p.d)
    (hstk : StkRes p.sp (MpReduce2kLG.F (p := p))) (va : p.a.Valid) (az : p.a.sign = Layout.mpZpos)
    (vn : p.n.Valid) (nz : p.n.sign = Layout.mpZpos) (hn0 : 0 < p.n.mag)
    (hbits : Layout.digitBits * (2 * p.n.used + 1) < 2 ^ 31)
    (hxu : p.a.used ≤ 2 * p.n.used) (apos : 0 < p.a.alloc) (dpos : 0 < p.d.alloc)
    (aoff : OffHeap p.pa 24) (noff : OffHeap p.pn 24) (doff : OffHeap p.pd 24) : RedSRes md p := by
  have hk1 : 0 < p.n.used := WindowStep.used_pos hn0
  have npos : 0 < p.n.alloc := MpInt.alloc_pos_of_mag vn hn0
  have hvd := hmu.valid
  have := va.used_le; have := vn.used_le
  have hb : 28 * (2 * p.n.used + 1) < 2 ^ 31 := hbits
  rcases md with _ | _ | md
  · have hs := hmu.b0 rfl
    have hu := SMpExptmodStep.mu_used vn hn0 hs
    exact ⟨hstk, (⟨⟨hstk.al, Nat.le_trans (Nat.add_le_add_left (stkS_le (p := p)) _) hstk.lo, hstk.hi⟩,
      va, az, vn, nz, hvd, hs.sign, hk1, (show 28 * (p.n.used + 1) < 2 ^ 31 by omega), (show 28 * p.a.used < 2 ^ 31 by omega), hxu, hu.1, hu.2, apos, npos, dpos, aoff, noff, doff⟩ :
        MpReduce.Res (toRB p))⟩
  · have hs := hmu.b1 (by decide)
    exact ⟨hstk, (⟨hstk, va, vn, hvd, hn0, hs.spec, by show 28 * p.n.used < 2 ^ 31; omega,
      by show 28 * p.a.used < 2 ^ 31; omega, by omega, apos, dpos, aoff, noff, doff⟩ :
        MpReduce2kLG.Res p)⟩
  · omega

/-- Mode `md`'s entry is word-aligned (`call_heapR`'s `hal`). -/
theorem reduxS_al {md : Nat} (hmd : md < 2) : (reduxS md).entry.toNat % 4 = 0 := by
  rcases md with _ | _ | md
  · decide
  · decide
  · omega

end Tom.Machine.Std
