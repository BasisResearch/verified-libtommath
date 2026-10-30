import Tom.Machine.Kit.Meet
import Tom.Machine.Kit.StackCall

/-!
# `s_mp_sqr_fast` with growth: reading the spilled slots

The set-up spills `a->used`, `a->used - 1`, `4 (a->used - 1)` and `2 a->used` one store per row
(a row that stores and reloads a slot overran the memory cap), so the frame snapshot at the
join is a nest of one-entry write logs. `rd_peel h` (`h : 2208 ≤ sp`) reads a slot from such a nest: the outer logs
that miss it by `bytesT8_log_out` (`rd_miss`) (`out_sp1`: literal offsets, no `omega` in the edge's large context), the one that writes it by `bytesT8_log''`; `rd_base h e` a slot no log writes, by the fact `e`. (`rd_log` first merges the nest by `writeLog_append`; on these
nests its proof overran the kernel's budget.)
-/

namespace Tom.Machine

/-- Two frame slots `c1`, `c2` bytes below `sp`, eight bytes apart: the read misses the store. -/
theorem out_sp1 {sp c1 c2 : Nat} (v : BitVec 64) (hc : c2 + 8 ≤ c1 ∨ c1 + 8 ≤ c2) (h1 : c1 ≤ sp) (h2 : c2 ≤ sp) :
    Vsa.Sim.OutLRange [(sp - c1, 8, v)] (sp - c2) 8 := by
  simp only [Vsa.Sim.OutLRange, and_true]; omega

/-- The outer logs that miss the slot. -/
macro "rd_miss " h:term : tactic => `(tactic|
  (repeat (rw [Tom.Machine.Api.Two.bytesT8_log_out _ _ _ (out_sp1 _ (by decide) (Nat.le_trans (by decide) $h)
    (Nat.le_trans (by decide) $h))])))

/-- A slot written by one of the nest's one-entry logs. -/
macro "rd_peel " h:term : tactic => `(tactic| (rd_miss $h; exact bytesT8_log'' _ [] [] _ _ _ rfl (by simp only [Vsa.Sim.OutLRange])))

/-- A slot no log writes: the fact `e` about the nest's base. -/
macro "rd_base " h:term:max e:term : tactic => `(tactic| (rd_miss $h; exact $e))

end Tom.Machine
