import Tom.Machine.Kit.Sites
import Tom.Spec.Div2d

/-!
# Placement and allocation facts for loops around re-placing calls

* `MpInt.alloc_pos_of_mag`: a valid integer with a nonzero magnitude has a nonempty digit block (a
  contract region's `Off` positivity at the entry; `MpReduce2kG5.nalloc_pos`'s statement, generic).
(A re-placed block's freshness is `Kit/Sites.lean`'s `fresh_of_place`.)
* `Div2dPost.alloc_eq`: `mp_div_2d` keeps the quotient's block.
-/

namespace Tom.Machine

open Tom Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

theorem MpInt.alloc_pos_of_mag {x : MpInt} (hv : x.Valid) (h : 0 < x.mag) : 0 < x.alloc := by
  have hu : 0 < x.used := by
    rcases Nat.eq_zero_or_pos x.used with h0 | h0
    · simp [MpInt.mag, h0, natUpTo] at h
    · exact h0
  exact Nat.lt_of_lt_of_le hu hv.used_le

theorem Div2dPost.alloc_eq {a c c' : MpInt} {sh : Nat} (h : Div2dPost a sh c c') : c'.alloc = c.alloc := h.alloc

end Tom.Machine
