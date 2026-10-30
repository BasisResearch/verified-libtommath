import Tom.Machine.Api.KMul
import Tom.Machine.Api.BalMul
import Tom.Machine.Api.ToomMul
import Tom.Machine.Api.MpMulA

/-!
# The algorithms of `mp_mul(a, b, a)`: their in-place contracts

`Api/MulAlg.lean` with `c = a`: `mp_mul(a, b, a)` (`Api/MpMulA.lean`) dispatches to
`s_mp_karatsuba_mul(a, b, a)`, `s_mp_balance_mul(a, b, a)`, `s_mp_toom_mul(a, b, a)` at their
entries with the same arguments (`a2 = a0`). Regions `Api.MpMulA.R` (`stk aS aD bS bD kc tc code`,
written `stk aS aD`); the site is `a`'s digit array, at a block `q` after.

Why the code is right in place: every algorithm reads `a` before it writes the destination.
Karatsuba copies `a`'s digits into `x0`, `x1` first and writes `c` only by its last call
`mp_add(&t1, &x1y1, c)`; balance builds the product in its temporary `r` (`a0` the slices of the
longer operand, copied before) and ends by `mp_exch(&r, c)`; toom splits `a` into `a0 a1 a2`
(copies) before any write to `c`, and uses `c` only as a temporary after the split.

`MulAlg.Base`'s facts about `c` are `a`'s (`a` valid). The contracts are **not proved**: named
premises of `mp_mul(a, b, a)`'s proof (`Api/MpMulGA.lean`).
-/

namespace Tom.Machine.Api.MulAlgA

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpMulA (P R)
open Tom.Machine.Api.MpMul (X μ)

/-- The algorithms' stack depth (`MulAlg.F`). -/
def F (p : P) : Nat := 2736 + 8 * μ p.a p.b

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - (2736 + 8 * (p.a.used + p.b.used)), 2736 + 8 * (p.a.used + p.b.used)⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .kc => ⟨MpMul.kcAddr, 4⟩
  | .tc => ⟨MpMul.tcAddr, 4⟩
  | .code => textIv

/-- What `a` holds after an algorithm (`MulAlg.Out` over the operands' old values). -/
structure Out (p : P) (ok : Bool) (a' : MpInt) : Prop where
  shape : a'.Shape
  pos : 0 < a'.alloc
  /-- `MP_OKAY`: `a'` valid with magnitude `|a| |b|` (of the old `a`). -/
  valid : ok = true → a'.Valid
  mag : ok = true → a'.mag = p.a.mag * p.b.mag

def Q (p : P) : X → Prop
  | (ok, _, a') => Out p ok a'

/-- The contract of an in-place algorithm at `entry` with residue `Rs`, at one `p`. -/
def SpecR (entry : BitVec 64) (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (lay p) MpMulA.isW → Bundle (lay p) (MpMulA.kind p) m → AHeap m (MpMulA.hin p) →
    (∀ r, Off (lay p r) (MpMulA.hin p)) →
    Triple (At entry ((1, ra) :: MpMulA.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (MpMulA.rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) MpMulA.ws .aD (MpMulA.out p x) (MpMulA.site' p x) (MpMulA.hin p) (MpMulA.hout p x) m M)

/-- The residue every in-place algorithm shares (`Api.MpMulA.Res` at the depth `F`). -/
structure Base (p : P) : Prop where
  stk : StkRes p.sp (F p)
  va : p.a.Valid
  vb : p.b.Valid
  uab : μ p.a p.b < 2 ^ 30
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

end Tom.Machine.Api.MulAlgA

namespace Tom.Machine.Api.KMulA

open Tom.Machine Tom.Machine.Api
open Tom.Machine.Api.MpMulA (P)
open Tom.Machine.Api.MpMul (μ)

/-- What `s_mp_karatsuba_mul(a, b, a)` needs (`KMul.Res` in place). -/
structure Res (p : P) : Prop extends MulAlgA.Base p where
  /-- `mp_mul`'s dispatch: `min ≥ KARATSUBA_MUL_CUTOFF = 80`. -/
  kmin : 80 ≤ min p.a.used p.b.used
  /-- `mp_mul`'s dispatch: not the balanced case. -/
  kbal : max p.a.used p.b.used < 2 * min p.a.used p.b.used
  /-- The recursive `mp_mul`s below the measure. -/
  ih : MulRec.MulBelow (μ p.a p.b)

def Spec (p : P) : Prop := MulAlgA.SpecR KMul.entry Res p

/-- **`s_mp_karatsuba_mul(a, b, a)` on the machine** (not proved). -/
def Statement : Prop := ∀ p : P, Spec p

end Tom.Machine.Api.KMulA

namespace Tom.Machine.Api.BalMulA

open Tom.Machine Tom.Machine.Api
open Tom.Machine.Api.MpMulA (P)
open Tom.Machine.Api.MpMul (μ)

/-- What `s_mp_balance_mul(a, b, a)` needs (`BalMul.Res` in place). -/
structure Res (p : P) : Prop extends MulAlgA.Base p where
  /-- `mp_mul`'s dispatch (`18dc`, `18f4`, `197c`). -/
  bmin : 80 ≤ min p.a.used p.b.used
  bhalf : 80 ≤ max p.a.used p.b.used / 2
  bratio : 2 * min p.a.used p.b.used ≤ max p.a.used p.b.used
  /-- The recursive `mp_mul`s below the measure. -/
  ih : MulRec.MulBelow (μ p.a p.b)

def Spec (p : P) : Prop := MulAlgA.SpecR BalMul.entry Res p

/-- **`s_mp_balance_mul(a, b, a)` on the machine** (not proved). -/
def Statement : Prop := ∀ p : P, Spec p

end Tom.Machine.Api.BalMulA

namespace Tom.Machine.Api.ToomMulA

open Tom.Machine Tom.Machine.Api
open Tom.Machine.Api.MpMulA (P)
open Tom.Machine.Api.MpMul (μ)

/-- What `s_mp_toom_mul(a, b, a)` needs (`ToomMul.Res` in place). -/
structure Res (p : P) : Prop extends MulAlgA.Base p where
  /-- `mp_mul`'s dispatch (`18fc`). -/
  tmin : 350 ≤ min p.a.used p.b.used
  tbal : max p.a.used p.b.used < 2 * min p.a.used p.b.used
  /-- The recursive `mp_mul`s below the measure. -/
  ih : MulRec.MulBelow (μ p.a p.b)

def Spec (p : P) : Prop := MulAlgA.SpecR ToomMul.entry Res p

/-- **`s_mp_toom_mul(a, b, a)` on the machine** (not proved). -/
def Statement : Prop := ∀ p : P, Spec p

end Tom.Machine.Api.ToomMulA
