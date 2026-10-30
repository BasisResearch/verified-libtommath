import Tom.Machine.Api.SMpMulDigsAG
import Tom.Machine.Fn.SMpMulDigsAFMainG
import Tom.Machine.Fn.SMpMulDigsAMainG
import Tom.Machine.Fn.SMpMulHighDigsAFMainG
import Tom.Machine.Fn.SMpMulHighDigsMainG

/-!
# `s_mp_mul_digs(a, b, a, digs)` and `s_mp_mul_high_digs(a, b, a, digs)` on both paths

By cases on the C's fast test: the fast path's growing contracts (`Fn.SMpMulDigsAFG5.correct`,
`Fn.SMpMulHighDigsAFG5.correct`), or the slow path's (`Fn.SMpMulDigsAG5.correct`,
`Fn.SMpMulHighDigsG5.correct`), through the contract bridges `Spec.ofFast`/`Spec.ofSlow` of `Api/SMpMulDigsAG.lean`.
-/

namespace Tom.Machine.Fn.SMpMulDigsAGClosed

open Tom.Machine.Api

/-- **`s_mp_mul_digs(a, b, a, digs)` on either path.** -/
theorem digsCorrect : SMpMulDigsAG.Statement := fun {p} => if hf : SMpMulDigs.Fast p.a p.b p.digs
  then SMpMulDigsAG.Spec.ofFast hf SMpMulDigsAFG5.correct
  else SMpMulDigsAG.Spec.ofSlow hf SMpMulDigsAG5.correct

/-- **`s_mp_mul_high_digs(a, b, a, digs)` on either path.** -/
theorem highCorrect : SMpMulHighDigsG.Statement := fun {p} => if hf : SMpMulHighDigs.Fast p.a p.b
  then SMpMulHighDigsG.Spec.ofFast hf SMpMulHighDigsAFG5.correct
  else SMpMulHighDigsG.Spec.ofSlow hf SMpMulHighDigsG5.correct

end Tom.Machine.Fn.SMpMulDigsAGClosed
