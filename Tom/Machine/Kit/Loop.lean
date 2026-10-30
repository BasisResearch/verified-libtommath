import Vsa.Triple

/-!
# Counted loops

`Triple.countdown`: a loop whose state at its head is indexed by a counter
`k` (a digit index, a remaining length). Each iteration from `P (k+1)`
either leaves the loop (`Q`) or comes back to the head at `P k`; from `P 0`
the loop leaves. Then every `P n` reaches `Q`. This is `Vsa.Logic.Triple.loop`
with the measure the counter itself and the exit folded into the step,
which is the shape libtommath's digit loops have (the guard is data the
iteration reads, not a register predicate).
-/

namespace Vsa.Logic.Triple

open Vsa.Machine (Config)

theorem countdown {P : Nat → Config → Prop} {Q : Config → Prop}
    (step : ∀ k, Triple (P (k + 1)) (fun c => Q c ∨ P k c)) (base : Triple (P 0) Q) :
    ∀ n, Triple (P n) Q
  | 0 => base
  | n + 1 => Triple.seq (step n) (Triple.cases (Triple.rfl) (countdown step base n))

/-- A pure fact in the precondition. -/
theorem of_pure {H : Prop} {P Q : Config → Prop} (h : H → Triple P Q) :
    Triple (fun c => H ∧ P c) Q :=
  fun c hc => h hc.1 c hc.2

/-- A pure fact in the precondition, on the right. -/
theorem of_pure' {H : Prop} {P Q : Config → Prop} (h : H → Triple P Q) :
    Triple (fun c => P c ∧ H) Q :=
  fun c hc => h hc.2 c hc.1

/-- A loop counting up to `n`: each iteration from `P i` with `i + 1 < n`
reaches `P (i + 1)`, the last one (`P (n - 1)`) reaches `Q`. -/
theorem countup {P : Nat → Config → Prop} {Q : Config → Prop} {n : Nat}
    (step : ∀ i, i + 1 < n → Triple (P i) (P (i + 1))) (last : Triple (P (n - 1)) Q) :
    ∀ i, i < n → Triple (P i) Q := by
  suffices h : ∀ k i, i + k + 1 = n → Triple (P i) Q from fun i hi => h (n - 1 - i) i (by omega)
  intro k
  induction k with
  | zero => intro i hi; rw [show i = n - 1 by omega]; exact last
  | succ k ih => intro i hi; exact Triple.seq (step i (by omega)) (ih (i + 1) (by omega))

end Vsa.Logic.Triple
