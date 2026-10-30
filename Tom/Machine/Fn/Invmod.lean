import Tom.Machine.Fn.MpInvmodMainG
import Tom.Machine.Fn.InvmodFastMainG
import Tom.Machine.Fn.InvmodSlowMainG

/-!
# `mp_invmod` on the machine, closed

`Fn/MpInvmodMainG.lean` proves `mp_invmod`'s assembly with its workers' contracts as premises
(`Api.MpInvmodOf.Res`); the workers' generated assemblies discharge them. The workers grow every
temporary they copy into, so `b` is of any size (`MpInvmodG`); the D5 statements follow
(`Statement.d5`: `correctG.d5`, `Fn.InvmodFastG5.correct.d5`, `Fn.InvmodSlowG5.correct.d5`).
-/

namespace Tom.Machine.Fn.Invmod

/-- **`mp_invmod` on the machine, `b` of any size.** -/
theorem correctG : Api.MpInvmodG.Statement := fun hra hres =>
  Fn.MpInvmodG5.correct hra ⟨hres, Fn.InvmodFastG5.correct, Fn.InvmodSlowG5.correct⟩

/-- **`mp_invmod` on the machine.** -/
theorem correct : Api.MpInvmod.Statement := correctG.d5

end Tom.Machine.Fn.Invmod
