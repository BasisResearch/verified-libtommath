import Tom.Spec.Div
import Tom.Spec.DivD
import Tom.Spec.Set

/-!
# `mp_div` with `c` or `d` NULL: the halves of its post

`Api/MpDivR.lean` (`mp_div(a, b, NULL, d)`) and `Api/MpDivQ.lean` (`mp_div(a, b, a, NULL)`) state
`DivRem` and `DivQuot` alone; their cases from the callees' posts (`mp_copy(a, d)`, `mp_zero(c)`, the
long division's `DivBigRem`/`DivBigQuot`).
-/

namespace Tom

variable {a b c c' d d' : MpInt}

/-- `|a| < |b|`: `mp_copy(a, d)` (`d`'s digits above its old `used` zero: `d` shaped). -/
theorem DivRem.of_small (ha : a.Valid) (hd : d.Shape) (hlt : a.mag < b.mag) (hcp : CopyPost a d d') :
    DivRem a b d d' := by
  refine ⟨fun _ => ClampedTo.of_copy ha hcp.alloc hcp.len (funext fun i => ?_) hcp.used hcp.sign,
    fun h => absurd h (Nat.not_le.2 hlt)⟩
  rw [hcp.digit i]
  by_cases h1 : i < a.used
  · rw [if_pos h1]
  · rw [if_neg h1, ha.high_zero i (by omega)]
    by_cases h2 : i < d.used
    · rw [if_pos h2]
    · rw [if_neg h2, hd.high_zero i (by omega)]

theorem DivRem.of_big (hge : b.mag ≤ a.mag) (hr : DivBigRem a b d') : DivRem a b d d' :=
  ⟨fun h => absurd hge (Nat.not_le.2 h), fun _ => hr⟩

/-- `|a| < |b|`: `mp_zero(c)`. -/
theorem DivQuot.of_small (hlt : a.mag < b.mag) (hz : ZeroPost c c') : DivQuot a b c c' :=
  ⟨fun _ => ⟨hz.alloc, hz.len, funext hz.digit, by rw [hz.used]; rfl, by rw [hz.sign]; split <;> rfl⟩,
    fun h => absurd h (Nat.not_le.2 hlt)⟩

theorem DivQuot.of_big (hge : b.mag ≤ a.mag) (hq : DivBigQuot a b c') : DivQuot a b c c' :=
  ⟨fun h => absurd hge (Nat.not_le.2 h), fun _ => hq⟩

end Tom
