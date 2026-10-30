import Tom.Machine.Fn.MpExptmodMainG
import Tom.Machine.Fn.SExptFastMainG
import Tom.Machine.Fn.SExptMainG
import Tom.Machine.Fn.Invmod

/-!
# `mp_exptmod` on the machine, closed

`Fn/MpExptmodMainG.lean` proves `mp_exptmod`'s assembly with its workers' contracts as premises
(`Api.MpExptmod.ResOf`), including the recursive call's contract for a nonnegative exponent.
The workers' assemblies discharge the first three. The recursion is closed in two steps: with a
nonnegative exponent the recursive branch is dead, which gives `correct_nn`; `correct_nn` then
discharges the recursive premise for every exponent.
-/

namespace Tom.Machine.Fn.MpExptmod

/-- `mp_exptmod` for a nonnegative exponent (the recursive call's contract). -/
theorem correct_nn : Api.MpExptmod.StatementNN := by
  intro p m v outp ra hra hres
  exact Fn.MpExptmodG5.correct hra ⟨hres.1, Fn.SExptFastG5.correct, Fn.SExptG5.correct,
    Fn.Invmod.correctG, fun h => absurd h hres.2⟩

/-- **`mp_exptmod` on the machine.** -/
theorem correct : Api.MpExptmod.Statement := by
  intro p m v outp ra hra hres
  exact Fn.MpExptmodG5.correct hra ⟨hres, Fn.SExptFastG5.correct, Fn.SExptG5.correct,
    Fn.Invmod.correctG, fun _ => correct_nn⟩

end Tom.Machine.Fn.MpExptmod
