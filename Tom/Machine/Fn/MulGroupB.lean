import Tom.Machine.Fn.MulGroupT
import Tom.Machine.Fn.BalMulMainG
import Tom.Machine.Fn.BalMulAMainG
import Tom.Machine.Api.BalMulGap

/-!
# The multiplication and squaring groups closed

`s_mp_balance_mul(a, b, c)` and `s_mp_balance_mul(a, b, a)` on the machine (`Fn.BalMulG5.correct`,
`Fn.BalMulAG5.correct`; `experiments/asm/bal.asm.json`, `balA.asm.json`) discharge the last premises
of `Fn/MulGroupT.lean`'s closures. Their left-over `mp_mul(&a0, &B, &tmp)` runs on a slice with
stale digits above `used`: the group's recursion is stated over `ValidU` operands
(`Api.MulRec.MulAt`, `Api.MpMul.ResU`), so it is covered.

* `mulCorrect`, `sqrCorrect`: `mp_mul` (both shapes) and `mp_sqr` (both shapes), no premises;
* `mulCorrectU`: `mp_mul(a, b, c)` over operands with stale digits above `used`;
* `mulBelow`, `sqrBelow`: the recursion hypotheses at every bound, so the algorithms' contracts
  (`KMul`, `ToomMul`, `BalMul` and the squaring ones, whose residues carry them) hold outright;
-/

namespace Tom.Machine.Fn.MulGroupB

open Tom.Machine.Api

/-- The closures' premises: balance mul in both shapes. -/
theorem gaps : MulGroupT.GapsFull := ⟨BalMulG5.correct, BalMulAG5.correct⟩

/-- **`mp_mul(a, b, c)` and `mp_mul(a, b, a)` on the machine**, no premises. -/
theorem mulCorrect : MpMul.Statement ∧ MpMulA.Statement := MulGroupT.mulCorrectFull gaps

/-- **`mp_sqr(a, b)` and `mp_sqr(a, a)` on the machine**, no premises. -/
theorem sqrCorrect : MpSqr.Statement ∧ MpSqrA.Statement := MulGroupT.sqrCorrectFull gaps

/-- **`mp_mul(a, b, c)` with operands only `ValidU`** (digits at and above `used` arbitrary). -/
theorem mulCorrectU : MpMul.StatementU :=
  (MulRec.closeU (MulGroupK.correctI ⟨BalMulG5.correct, ToomMulG5.correct⟩)
    (MpMulAG5I.correctAI' ⟨BalMulAG5.correct, ToomMulAG5.correct⟩)).1

/-- The multiplication group's recursion hypothesis at every bound. -/
theorem mulBelow (n : Nat) : MulRec.MulBelow n :=
  fun _ _ => ⟨fun p _ => mulCorrectU p, fun p _ => mulCorrect.2 p⟩

/-- The squaring group's recursion hypothesis at every bound. -/
theorem sqrBelow (n : Nat) : SqrRec.SqrBelow n :=
  fun _ _ => ⟨fun p _ => sqrCorrect.1 p, fun p _ => sqrCorrect.2 p⟩

/-- The gap (`Api/BalMulGap.lean`), proved. -/
theorem leftoverMul : BalMulGap.LeftoverMul_Statement := fun n h p hp => h.mulU hp

end Tom.Machine.Fn.MulGroupB
