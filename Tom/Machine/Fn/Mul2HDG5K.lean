import Tom.Machine.Api.Mul2HD
import Tom.Machine.Kit.Run
import Tom.Machine.Kit.AnnFacts
import Tom.Spec.Mul2HDStep

/-!
# `mp_mul_2(a, b)` distinct: `b`'s digit function at the tail

The loop leaves `b`'s array (`A`, grown from `b`) as the overlay `ovl (m2g a) A.digit a->used`,
the carry store `Mont.upd … a->used 1` on top; the tail cut `T` carries it as `g` with
`g j = if j < n then addDigits a a j else A.digit j` (`n = a->used + carry`). With `memset` of
`[n, oldused)` (`zfill`) or without it (`oldused ≤ n`), `A`'s digits above `oldused = A->used`
being zero, the array is `m2outD a A n`'s (`m2d_tn`, `m2d_tm`; the loop's exits by Kit/AnnFacts.lean's
`ovl_ite`, `upd_ovl_ite`).
-/

namespace Tom.Machine.Fn.Mul2HDG5K

open Tom Tom.Machine Tom.Machine.Std

theorem m2d_tn {a A : MpInt} {n : Nat} {g : Nat → Nat} (ha : a.Shape) (hA : A.Shape) (hou : A.used ≤ n)
    (hn : n = a.used + addCarryAt a a a.used) (hgd : ∀ j, g j = if j < n then addDigits a a j else A.digit j) :
    ∀ j, j < A.alloc → (m2outD a A n).digit j = g j := by
  intro j hj
  rw [m2outD, MpInt.ofDigits_digit, if_pos hj, hgd]; split
  · rfl
  · rw [m2d_high ha hn (by omega), hA.high_zero j (by omega)]

theorem m2d_tm {a A : MpInt} {n : Nat} {g : Nat → Nat} (ha : a.Shape) (hA : A.Shape)
    (hn : n = a.used + addCarryAt a a a.used) (hgd : ∀ j, g j = if j < n then addDigits a a j else A.digit j) :
    ∀ j, j < A.alloc → (m2outD a A n).digit j = zfill g n A.used j := by
  intro j hj
  rw [m2outD, MpInt.ofDigits_digit, if_pos hj]; simp only [zfill]; split
  · exact m2d_high ha hn (by omega)
  · rw [hgd]; split
    · rfl
    · rw [m2d_high ha hn (by omega), hA.high_zero j (by omega)]

end Tom.Machine.Fn.Mul2HDG5K
