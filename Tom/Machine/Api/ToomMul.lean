import Tom.Machine.Api.MulAlg

/-!
# `s_mp_toom_mul(a, b, c)`, `c` distinct: the contract

`vendor/libtommath/bn_s_mp_toom_mul.c`, compiled at `0x800046e0` (frame 336): Bodrato's
Toom-3 (`Tom/Spec/MulAlgo.lean`, `toom3_*`): five products by `mp_mul` (three of them in place,
`c = a`: `Api/MpMulA.lean`), the interpolation by `mp_sub`, `mp_mul_2`, `mp_div_2`,
`s_mp_div_3`, the recomposition by `mp_lshd`, `mp_add`. `mp_mul` calls it with
`min ≥ TOOM_MUL_CUTOFF = 350` and not balanced (`max < 2 min`). Statement only.
-/

namespace Tom.Machine.Api.ToomMul

open Tom.Machine Tom.Machine.Api
open Tom.Machine.Api.MpMul (P μ)

def entry : BitVec 64 := 0x800046e0#64

structure Res (p : P) : Prop extends MulAlg.Base p where
  /-- `mp_mul`'s dispatch (`18fc`). -/
  tmin : 350 ≤ min p.a.used p.b.used
  tbal : max p.a.used p.b.used < 2 * min p.a.used p.b.used
  ih : MulRec.MulBelow (μ p.a p.b)

def Spec (p : P) : Prop := MulAlg.SpecR entry Res p

/-- **`s_mp_toom_mul(a, b, c)` on the machine** (not proved). -/
def Statement : Prop := ∀ p : P, Spec p

end Tom.Machine.Api.ToomMul
