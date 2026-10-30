import Tom.Machine.Kit.Run
import Tom.Machine.Kit.StackCall

/-!
# A contract region re-placed by a growing callee

`mp_lshd(a, k)`, `mp_mul_2d(a, b, a)` and `mp_mul_d(a, b, c)` call `mp_grow` on their own
destination: `call_heap` re-places the caller's region `r` (its digit array) at the callee's
`site'` (`Iv.upd ρ r J`), and the paths that need no growth keep `ρ`. A cut after the growth
takes one layout `Iv.upd ρ r J` for both: on the path without the call `J = ρ r`, and
`Iv.upd_eq_self` gives the state over it (`St.congrL`, `HP.congrL`).

`rd_out`: a cut's frame snapshot `writeLog m0 log` (callee-saved registers spilled on one path
only) read outside `log`, by the premise's fact about `m0` (`load_fwd`).
-/

namespace Tom.Machine

section
variable {ι : Type} [DecidableEq ι]

/-- Re-placing a region at its own interval changes nothing. -/
theorem Iv.upd_eq_self (ρ : ι → Iv) (r : ι) {J : Iv} (h : ρ r = J) : ∀ r', ρ r' = Iv.upd ρ r J r' := fun r' => by
  unfold Iv.upd; split
  · subst_vars; rfl
  · rfl

end

/-- A read of `writeLog m0 log` that misses `log`, by a fact about `m0` in context. -/
macro "rd_out" : tactic => `(tactic| (rw [Tom.Machine.Api.Two.bytesT8_log_out _ _ _
  (by simp only [Vsa.Sim.OutLRange, and_true, true_and]; omega)]; load_fwd; try rfl))

end Tom.Machine
