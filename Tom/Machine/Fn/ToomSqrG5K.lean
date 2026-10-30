import Tom.Machine.Kit.DOut
import Tom.Machine.Api.ToomSqrI
import Tom.Machine.Api.Std_t7
import Tom.Machine.Kit.Run
import Tom.Spec.ToomSqrStep
import Tom.Machine.Fn.ToomSqrG
import Tom.Machine.Fn.KSqrG5K

/-!
# Toom-3 squaring's assembly: helpers

`s_mp_toom_sqr` allocates four temporaries (`S0`, `a0`, `a1`, `a2`) and uses `b` as a fifth.
The assembly (`Fn/ToomSqrMainG.lean`, annotation `tsqr.asm.json`, style `"pre"`) runs over the
contract's regions plus the four digit arrays `dZ dU dV dW` (the region type, `soundG` and `GPre`,
with the named premises `Api.ToomSqrI.Gaps`, generated from the annotation's `"region"`).
`b`'s digits are re-placed by many calls: the placement the contract's `Q` asks for is carried
along by `DOut.next` (Kit/DOut.lean).
-/

namespace Tom.Machine.Fn.ToomSqrG5K

open Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpSqr (P kind hin)

/-! ## The failure paths before a call into `b` keep it -/

/-- `b` as it was (before any call into it). -/
theorem outKeep {p : P} (h : ToomSqr.Res p) : SqrAlg.Q p (false, p.bdp, p.b) :=
  ⟨h.sb, h.bpos, (fun e => nomatch e), (fun e => nomatch e), Place.keep, Nat.le_refl _⟩

end Tom.Machine.Fn.ToomSqrG5K
