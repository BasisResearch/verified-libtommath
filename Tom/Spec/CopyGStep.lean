import Tom.Spec.Grow6Step

/-!
# `mp_copy(a, b)` growing `b`

`mp_copy` calls `mp_grow(b, a->used)` when `b->alloc < a->used`: the copy then runs over the grown
`copyIn a b` (`a.used` digits when it had to grow, else `b`), which has room (`copyIn_room`), so
`CopyPost a (copyIn a b)` and `CopyPost.spec` apply.
-/

namespace Tom

open MpInt

/-- `b` after `mp_copy`'s `mp_grow(b, a->used)`. -/
def copyIn (a b : MpInt) : MpInt := if b.alloc < a.used then b.growTo a.used else b

theorem copyIn_grown {a b : MpInt} (hb : b.Shape) (h31 : a.used < 2 ^ 31) : GrownOf b (copyIn a b) :=
  GrownOf.ite hb id h31

theorem copyIn_room (a b : MpInt) : a.used ≤ (copyIn a b).alloc := by
  unfold copyIn; split
  · simp [MpInt.growTo, MpInt.ofDigits]
  · omega

/-- **`mp_copy(a, b)` growing**: `b'` valid with `a`'s value. -/
theorem CopyPost.specG {a b b' : MpInt} (ha : a.Valid) (hb : b.Shape) (h : CopyPost a (copyIn a b) b') :
    b'.Valid ∧ b'.mag = a.mag ∧ b'.val = a.val :=
  CopyPost.spec ha (copyIn_grown hb (Nat.lt_of_le_of_lt ha.used_le ha.alloc_lt)).shape (copyIn_room a b) h

end Tom
