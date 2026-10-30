import Tom.Machine.Api.MpSqrA

/-!
# `mp_sqr` on a small operand, growing the destination (a named premise)

`Api.MpSqr.Res.room` (D5 for the comba path: `a->used < 120 → 2 a->used ≤ b->alloc`) is not
met inside `s_mp_toom_sqr`: `mp_sqr(&a0, &S0)` squares the clamped low third (any `used ≤ B`,
`S0` from `mp_init`: `MP_PREC = 32` digits) and `mp_sqr(b, b)` squares `a0 + a2 − a1` (any
size). Below `KARATSUBA_SQR_CUTOFF = 120` digits `mp_sqr` calls `s_mp_sqr_fast(a, b)`, which
grows `b` (`mp_grow(b, 2 a->used)`, not covered by `Api/SqrFast.lean`). This file states that
path: `mp_sqr(a, b)` and `mp_sqr(a, a)` with `a->used < 120` and no room, on a 4096-byte stack
(`mp_sqr`'s 16, `s_mp_sqr_fast`'s 2208, `mp_grow`'s 544 inside it), same regions, results,
`Out` and heap as `Api/MpSqr.lean` / `Api/MpSqrA.lean`. **Not proved**: a named premise.
-/

namespace Tom.Machine.Api.MpSqrS

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpSqr (P R X entry kind out isW ws site' hin hout args rets Q)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - 4096, 4096⟩
  | r => MpSqr.lay p r

/-- `Api.MpSqr.Res` on the small branch, without the room. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 4096
  small : p.a.used < 120
  va : p.a.Valid
  sb : p.b.Shape
  bsign : p.b.sign = Layout.mpZpos ∨ p.b.sign = Layout.mpNeg
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

def Spec (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .bD (out p x) (site' p x) (hin p) (hout p x) m M)

/-- **`mp_sqr(a, b)`, `a->used < 120`, growing `b`** (named premise, not proved). -/
def Statement : Prop := ∀ p : P, Spec p

end Tom.Machine.Api.MpSqrS

namespace Tom.Machine.Api.MpSqrSA

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpSqrA (P R kind out isW ws site' hin hout args rets Q)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - 4096, 4096⟩
  | r => MpSqrA.lay p r

structure Res (p : P) : Prop where
  stk : StkRes p.sp 4096
  small : p.a.used < 120
  va : p.a.Valid
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

def Spec (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At MpSqr.entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

/-- **`mp_sqr(a, a)`, `a->used < 120`, growing `a`** (named premise, not proved). -/
def Statement : Prop := ∀ p : P, Spec p

end Tom.Machine.Api.MpSqrSA
