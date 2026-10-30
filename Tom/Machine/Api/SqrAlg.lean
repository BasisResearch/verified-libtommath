import Tom.Machine.Api.SqrRec
import Tom.Machine.Kit.DOut

/-!
# The algorithms `mp_sqr` dispatches to: their common contract shape

`s_mp_karatsuba_sqr` and `s_mp_toom_sqr` take `mp_sqr`'s parameters, regions, results and
heap (`Api.MpSqr.P`, or `Api.MpSqrA.P` for `b = a`), and differ in their entry, their residue
(the dispatch facts the code relies on, and the induction hypothesis `ih : SqrBelow a->used`)
and in nothing else: `MP_OKAY` promises `|b'| = |a|²`, `b'` valid (the sign is `mp_sqr`'s to
set). On `MP_MEM` `b'` is only shaped, with a live block.

The stack depth is `mp_sqr`'s minus its 16-byte frame: `F = 2208 + 8 a->used`. Karatsuba's
frame (192) and a recursive `mp_sqr` at `a->used - 59` or less fit, toom's (160) likewise,
and so do the non-recursive callees (all below 2000 bytes).
-/

namespace Tom.Machine.Api.SqrAlg

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

/-- The algorithms' stack depth. -/
def Fa (n : Nat) : Nat := 2208 + 8 * n

/-- What the destination holds after an algorithm (`x = (ok, q, b')`), its digits re-placed
from `I` (the old digit array, `n0` digits) for the blocks `H`: `DOut` (Kit/DOut.lean) at `|a|²` (on
`MP_OKAY` valid with magnitude `|a|²`; where `b'`'s digits are, `HPost.place` restated for `mp_sqr`,
which passes the site on; the digits only grow). -/
abbrev Out (a : MpInt) (n0 : Nat) (H : List (Nat × Nat)) (I : Iv) (x : MpSqr.X) : Prop :=
  DOut (a.mag * a.mag) n0 I H x

/-! ## `b` distinct from `a` -/

section
open Tom.Machine.Api.MpSqr (P R X)

def F (p : P) : Nat := Fa p.a.used

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - (2208 + 8 * p.a.used), 2208 + 8 * p.a.used⟩
  | r => MpSqr.lay p r

def Q (p : P) (x : X) : Prop := Out p.a p.b.alloc (MpSqr.hin p) (lay p .bD) x

/-- The contract of an algorithm at `entry` with residue `Rs`, at one `p`. -/
def SpecR (entry : BitVec 64) (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (lay p) MpSqr.isW → Bundle (lay p) (MpSqr.kind p) m → AHeap m (MpSqr.hin p) →
    (∀ r, Off (lay p r) (MpSqr.hin p)) →
    Triple (At entry ((1, ra) :: MpSqr.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (MpSqr.rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) MpSqr.ws .bD (MpSqr.out p x) (MpSqr.site' p x) (MpSqr.hin p) (MpSqr.hout p x) m M)

/-- The residue every algorithm shares (`Api.MpSqr.Res` at the depth `F`, without the comba
path's room). -/
structure Base (p : P) : Prop where
  stk : StkRes p.sp (F p)
  va : p.a.Valid
  sb : p.b.Shape
  bsign : p.b.sign = Layout.mpZpos ∨ p.b.sign = Layout.mpNeg
  au : p.a.used < 2 ^ 29
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

end

/-! ## In place, `b = a` -/

section
open Tom.Machine.Api.MpSqrA (P R)

def FA (p : P) : Nat := Fa p.a.used

def layA (p : P) : R → Iv
  | .stk => ⟨p.sp - (2208 + 8 * p.a.used), 2208 + 8 * p.a.used⟩
  | r => MpSqrA.lay p r

def QA (p : P) (x : MpSqr.X) : Prop := Out p.a p.a.alloc (MpSqrA.hin p) (layA p .aD) x

def SpecRA (entry : BitVec 64) (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (layA p) MpSqrA.isW → Bundle (layA p) (MpSqrA.kind p) m → AHeap m (MpSqrA.hin p) →
    (∀ r, Off (layA p r) (MpSqrA.hin p)) →
    Triple (At entry ((1, ra) :: MpSqrA.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (MpSqrA.rets p x ra) M v.keep outp cf ∧ QA p x ∧
        HPost (layA p) MpSqrA.ws .aD (MpSqrA.out p x) (MpSqrA.site' p x) (MpSqrA.hin p) (MpSqrA.hout p x) m M)

structure BaseA (p : P) : Prop where
  stk : StkRes p.sp (FA p)
  va : p.a.Valid
  au : p.a.used < 2 ^ 29
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

end

end Tom.Machine.Api.SqrAlg
