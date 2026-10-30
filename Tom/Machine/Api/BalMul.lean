import Tom.Machine.Api.MulAlg

/-!
# `s_mp_balance_mul(a, b, c)`, `c` distinct: the contract

`vendor/libtommath/bn_s_mp_balance_mul.c`, compiled at `0x8000234c` (frame 208): the longer
operand cut into `nblocks = max / min` slices of `bsize = min` digits (`__divdi3`), each
multiplied by the shorter one (`mp_mul(&a0, &B, &tmp)`, `B` a struct copy of the shorter
operand), shifted (`mp_lshd(&tmp, bsize * i)`, `__muldi3`) and added (`mp_add(&r, &tmp, &r)`);
the left-over slice likewise; `mp_exch(&r, c)`, `mp_clear_multi`. `mp_mul` calls it with
`min ≥ KARATSUBA_MUL_CUTOFF`, `max / 2 ≥ KARATSUBA_MUL_CUTOFF`, `max ≥ 2 min`; each
recursive `mp_mul` is on `μ' ≤ 2 min ≤ μ - 80`. Proved by `Fn.BalMulG5.correct`
(`Fn/BalMulMainG.lean`).
-/

namespace Tom.Machine.Api.BalMul

open Tom.Machine Tom.Machine.Api
open Tom.Machine.Api.MpMul (P μ)

def entry : BitVec 64 := 0x8000234c#64

structure Res (p : P) : Prop extends MulAlg.Base p where
  /-- `mp_mul`'s dispatch (`18dc`, `18f4`, `197c`). -/
  bmin : 80 ≤ min p.a.used p.b.used
  bhalf : 80 ≤ max p.a.used p.b.used / 2
  bratio : 2 * min p.a.used p.b.used ≤ max p.a.used p.b.used
  ih : MulRec.MulBelow (μ p.a p.b)

def Spec (p : P) : Prop := MulAlg.SpecR entry Res p

/-- **`s_mp_balance_mul(a, b, c)` on the machine** (proved: `Fn.BalMulG5.correct`). -/
def Statement : Prop := ∀ p : P, Spec p

end Tom.Machine.Api.BalMul
