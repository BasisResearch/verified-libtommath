/-!
# `s_mp_reverse`: reversing a byte array in place

`s_mp_reverse(s, len)` (`vendor/libtommath/bn_s_mp_reverse.c`) swaps
`s[ix]` and `s[iy]` from both ends inwards. Its contract is over byte lists:
the array that held `l` holds `l.reverse`. `revPart f n k` is the array after
`k` swaps (positions below `k` and above `n - 1 - k` exchanged), the loop's
invariant; `revPart_done` says that when the ends meet it is the reverse.
-/

namespace Tom

variable {α : Type}

/-- The array `f` of `n` elements after `k` swaps from both ends. -/
def revPart (f : Nat → α) (n k i : Nat) : α := if i < k ∨ n - 1 - k < i then f (n - 1 - i) else f i

theorem revPart_zero (f : Nat → α) (n i : Nat) (hi : i < n) : revPart f n 0 i = f i := by
  unfold revPart; split <;> first | rfl | omega

/-- One swap: position `k` gets `f (n-1-k)`, position `n-1-k` gets `f k`. -/
theorem revPart_step (f : Nat → α) (n k i : Nat) (hk : k < n - 1 - k) :
    revPart f n (k + 1) i =
      if i = n - 1 - k then f k else if i = k then f (n - 1 - k) else revPart f n k i := by
  unfold revPart
  (repeat' split) <;> first | rfl | omega | (congr 1; omega)

/-- When the ends meet, all positions are swapped. -/
theorem revPart_done (f : Nat → α) (n k i : Nat) (hk1 : ¬ k + 1 < n - 1 - (k + 1))
    (hi : i < n) : revPart f n (k + 1) i = f (n - 1 - i) := by
  unfold revPart
  split
  · rfl
  · congr 1; omega

theorem reverse_getD (l : List α) (d : α) (i : Nat) (hi : i < l.length) :
    l.reverse.getD i d = l.getD (l.length - 1 - i) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse hi]

end Tom
