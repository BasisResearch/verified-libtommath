import Tom.Machine.Api.BalMul

/-!
# The gap in `s_mp_balance_mul`: `mp_mul` on a slice with stale digits

`s_mp_balance_mul`'s left-over slice is copied into `a0` over the last full slice: only
`rem = A.used - bsize · nblocks < bsize` digits are written, `a0.dp[rem .. bsize)` keep the last
slice's digits (`Tom/Spec/BalMulStep.lean`, `leftover_not_shape`; disassembly `800024e0`–`80002510`:
`a0.used := 0`, then `a0.dp[count] = A.dp[j++]` while `j < A.used`, no zeroing), and
`mp_mul(&a0, &B, &tmp)` runs on it, so `a0` is only `MpInt.ValidU` (`Valid` without `high_zero`).

The statement holds by `MulRec.MulBelow.mulU`
(`Fn.MulGroupB.leftoverMul`).
-/

namespace Tom.Machine.Api.BalMulGap

open Tom.Machine Tom.Machine.Api
open Tom.Machine.Api.MpMul (P μ)

/-- `mp_mul(a, b, c)` below measure `n`, the operands with stale digits. -/
def MulBelowU (n : Nat) : Prop := ∀ p : P, μ p.a p.b < n → MpMul.SpecR MpMul.ResU p

/-- **The gap** (proved: `Fn.MulGroupB.leftoverMul`): the recursion hypothesis covers operands with
stale digits. -/
def LeftoverMul_Statement : Prop := ∀ n, MulRec.MulBelow n → MulBelowU n

end Tom.Machine.Api.BalMulGap
