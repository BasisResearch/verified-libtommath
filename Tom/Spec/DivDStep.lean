import Tom.Spec.DivD
import Tom.Spec.Canon
import Tom.Spec.Mont
import Tom.Spec.Init

/-!
# `mp_div_d`'s model steps

The value premises of `mp_div_d`'s generated assembly (`experiments/asm/mdivd.asm.json`) and
the lemmas that carry them along its edges, over `Tom/Spec/DivD.lean`'s long division
(`ldR`, `ldQ`, `divDDigit`) and its contracts (`DivDQuot`, `DivDRem`):

* `PW b ix`: the power-of-two scan at `ix` (`b = 2^k`, `1 ≤ ix ≤ k < 28`);
* `LH da b n f ix w`: the long division's head at `ix` (`w` the remainder carried in, `f` the
  quotient digits above `ix`), `LH.start` (`ix = n - 1`, `w = 0`, `q`'s zero digits),
  `LH.step` (`t = w / b`, `w - t b`, one digit stored) and `LH.fin` (after `ix = 0`);
* `ZH a b f w`: after the loop (`w = |a| mod b`, the digits `divDDigit`); `long_fin` turns
  `mp_clamp`'s post into `DivLongQuot`;
* the `DivDQuot`/remainder facts per path (`quot_copy`, `quot_pow2`, `quot_long`, `rem_*`).
-/

namespace Tom.DivDStep

open MpInt

/-! ## The power-of-two scan -/

/-- The scan at `ix`: `b = 2^(log2 b)`, `1 ≤ ix ≤ log2 b < 28`. -/
structure PW (b ix : Nat) : Prop where
  pow : b = 2 ^ Nat.log2 b
  pos : 1 ≤ ix
  le : ix ≤ Nat.log2 b
  lt : Nat.log2 b < 28

theorem log2_lt {b : Nat} (hb : b < 268435456) : Nat.log2 b < 28 := by
  rcases Nat.eq_zero_or_pos b with rfl | h
  · decide
  · exact (Nat.log2_lt (by omega)).2 hb

/-- The scan's start: `b` a power of two, `b ≠ 1`. -/
theorem PW.start {b : Nat} (h0 : 0 < b) (h1 : b ≠ 1) (hb : b < 268435456) (hp : (b - 1) &&& b = 0) : PW b 1 := by
  have hp' : b &&& (b - 1) = 0 := by rw [Nat.and_comm]; exact hp
  have e := pow2_of_and h0 hp'
  refine ⟨e, Nat.le_refl _, ?_, log2_lt hb⟩
  rcases Nat.eq_zero_or_pos (Nat.log2 b) with h | h
  · rw [h] at e; simp at e; omega
  · exact h

theorem PW.bound {b ix : Nat} (h : PW b ix) : 2 ^ ix < 268435456 :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (show ix ≤ 27 by have := h.le; have := h.lt; omega))
    (by decide)

/-- `b != 1 << ix`: the scan goes on. -/
theorem PW.next {b ix : Nat} (h : PW b ix) (hne : 2 ^ ix ≠ b) : ix + 1 < 28 := by
  have : ix ≠ Nat.log2 b := fun e => hne (by rw [e]; exact h.pow.symm)
  have := h.le; have := h.lt; omega

theorem PW.step {b ix : Nat} (h : PW b ix) (hne : 2 ^ ix ≠ b) : PW b (ix + 1) := by
  have : ix ≠ Nat.log2 b := fun e => hne (by rw [e]; exact h.pow.symm)
  exact ⟨h.pow, by have := h.pos; omega, by have := h.le; omega, h.lt⟩

/-- `b == 1 << ix`: `ix = log2 b`. -/
theorem PW.log {b ix : Nat} (heq : 2 ^ ix = b) : Nat.log2 b = ix := by
  rw [← heq]; exact Nat.log2_two_pow

/-! ## The long division's loop -/

/-- The head at `ix`: `w` is the remainder carried into `ix`, `f` holds the quotient
digits above `ix` (and zeros elsewhere). -/
structure LH (da : Nat → Nat) (b n : Nat) (f : Nat → Nat) (ix w : Nat) : Prop where
  w_eq : w = ldR da b n (ix + 1)
  f_eq : ∀ j, f j = if ix < j ∧ j < n then ldQ da b n j else 0

theorem LH.start {da : Nat → Nat} {b n N : Nat} (hn : 0 < n) : LH da b n (MpInt.zeroN N).digit (n - 1) 0 := by
  refine ⟨?_, fun j => ?_⟩
  · rw [show n - 1 + 1 = n by omega, ldR_top]
  · rw [MpInt.zeroN_digit, if_neg (by omega)]

theorem LH.w_lt {da : Nat → Nat} {b n ix w : Nat} {f : Nat → Nat} (h : LH da b n f ix w) (hb : 0 < b) : w < b := by
  rw [h.w_eq]; exact ldR_lt da hb n _

/-- One iteration (either branch: `t = W / b`, `w := W - t b`). -/
theorem LH.step {da : Nat → Nat} {b n ix w : Nat} {f : Nat → Nat} (h : LH da b n f ix w) (hix : ix < n) :
    LH da b n (Mont.upd f ix ((w * 268435456 + da ix) / b)) (ix - 1)
      (w * 268435456 + da ix - (w * 268435456 + da ix) / b * b) ∨ ix = 0 := by
  rcases Nat.eq_zero_or_pos ix with h0 | h0
  · exact .inr h0
  refine .inl ⟨?_, fun j => ?_⟩
  · rw [show ix - 1 + 1 = ix by omega, ldR_step da b hix, ← h.w_eq, (ldStep_sub_c _ b).2]; rfl
  · unfold Mont.upd
    by_cases hj : j = ix
    · subst hj; rw [if_pos rfl, if_pos ⟨by omega, hix⟩]; unfold ldQ; rw [← h.w_eq]; rfl
    · rw [if_neg hj, h.f_eq j]
      by_cases h1 : ix < j ∧ j < n
      · rw [if_pos h1, if_pos ⟨by omega, h1.2⟩]
      · rw [if_neg h1, if_neg (by omega)]

theorem LH.next {da : Nat → Nat} {b n ix w : Nat} {f : Nat → Nat} (h : LH da b n f ix w) (hix : ix < n) (h0 : 0 < ix) :
    LH da b n (Mont.upd f ix ((w * 268435456 + da ix) / b)) (ix - 1)
      (w * 268435456 + da ix - (w * 268435456 + da ix) / b * b) := by
  rcases h.step hix with h' | h'
  · exact h'
  · omega

/-- The `w < b` branch stores `t = 0` and keeps `W`: the same step. -/
theorem small_eq {W b : Nat} (h : W < b) : W / b = 0 ∧ W - W / b * b = W := by
  rw [Nat.div_eq_of_lt h]; omega

/-- After the loop: the remainder is `|a| mod b`, the digits are the quotient's. -/
structure ZH (a : MpInt) (b : Nat) (f : Nat → Nat) (w : Nat) : Prop where
  w_eq : w = a.mag % b
  f_eq : ∀ j, f j = divDDigit a b j

/-- The last iteration (`ix = 0`). -/
theorem LH.fin {a : MpInt} {b w : Nat} {f : Nat → Nat} (h : LH a.digit b a.used f 0 w) (hu : 0 < a.used) :
    ZH a b (Mont.upd f 0 ((w * 268435456 + a.digit 0) / b))
      (w * 268435456 + a.digit 0 - (w * 268435456 + a.digit 0) / b * b) := by
  refine ⟨?_, fun j => ?_⟩
  · rw [(ldStep_sub_c _ b).2, ← ldR_mag, ldR_step _ b hu, ← h.w_eq]; rfl
  · unfold Mont.upd divDDigit
    by_cases hj : j = 0
    · subst hj; rw [if_pos rfl, if_pos hu]; unfold ldQ; rw [← h.w_eq]; rfl
    · rw [if_neg hj, h.f_eq j]
      by_cases h1 : j < a.used
      · rw [if_pos ⟨by omega, h1⟩, if_pos h1]
      · rw [if_neg (by omega), if_neg h1]

/-- The `w < b` branch at `ix > 0`: `t = 0`, `w` kept. -/
theorem LH.next0 {da : Nat → Nat} {b n ix w : Nat} {f : Nat → Nat} (h : LH da b n f ix w) (hix : ix < n) (h0 : 0 < ix)
    (hW : w * 268435456 + da ix < b) : LH da b n (Mont.upd f ix 0) (ix - 1) (w * 268435456 + da ix) := by
  have h' := h.next hix h0
  rwa [(small_eq hW).1, Nat.zero_mul, Nat.sub_zero] at h'

/-- The last iteration at `ix = 0` (the cut's `ix`). -/
theorem LH.fin' {a : MpInt} {b ix w : Nat} {f : Nat → Nat} (h : LH a.digit b a.used f ix w) (hix : ix = 0)
    (hu : 0 < a.used) :
    ZH a b (Mont.upd f ix ((w * 268435456 + a.digit ix) / b))
      (w * 268435456 + a.digit ix - (w * 268435456 + a.digit ix) / b * b) := by
  subst hix; exact h.fin hu

theorem LH.fin0' {a : MpInt} {b ix w : Nat} {f : Nat → Nat} (h : LH a.digit b a.used f ix w) (hix : ix = 0)
    (hu : 0 < a.used) (hW : w * 268435456 + a.digit ix < b) :
    ZH a b (Mont.upd f ix 0) (w * 268435456 + a.digit ix) := by
  have h' := h.fin' hix hu
  rwa [(small_eq hW).1, Nat.zero_mul, Nat.sub_zero] at h'

/-- The quotient record before `mp_clamp`: `used = a->used`, `a`'s sign, `N` digits `f`. -/
abbrev qOf (a : MpInt) (N : Nat) (f : Nat → Nat) : MpInt := MpInt.ofDigits a.used N a.sign f

theorem qOf_shape {a : MpInt} {b N w : Nat} {f : Nat → Nat} (hz : ZH a b f w) (ha : a.Shape) (hb : 0 < b)
    (hN : a.used ≤ N) (hN' : N < 2 ^ 31) : (qOf a N f).Shape :=
  MpInt.ofDigits_shape hN hN' (fun j _ => by rw [hz.f_eq j]; exact divDDigit_lt a ha hb j)
    (fun j h1 _ => by rw [hz.f_eq j]; unfold divDDigit; rw [if_neg (by omega)])

/-- **The long division's result**: after `mp_clamp(&q)`. -/
theorem long_fin {a t1 : MpInt} {b N w : Nat} {f : Nat → Nat} (hz : ZH a b f w) (hN : N = initPrec a.used)
    (hc : ClampPost (qOf a N f) t1) : DivLongQuot a b t1 ∧ t1.alloc = N := by
  have hN3 : max 3 a.used = N := by rw [hN]; unfold initPrec; rw [minPrec_eq]
  have hdig : (qOf a N f).digit = divDDigit a b := by
    funext j
    rw [MpInt.ofDigits_digit, hz.f_eq j]
    split
    · rfl
    · unfold divDDigit; rw [if_neg (by have := Nat.le_max_right 3 a.used; omega)]
  have hal : t1.alloc = N := by rw [hc.alloc]; rfl
  refine ⟨{ alloc := hal.trans hN3.symm, len := ?_, digit := ?_, used := ?_, sign := ?_ }, hal⟩
  · rw [hc.digits, MpInt.ofDigits_len, hN3]
  · rw [hc.digit, hdig]
  · rw [hc.used, hdig]; rfl
  · rw [hc.sign]; rfl

/-! ## `c` and `*d` per path -/

theorem quot_long {a c c' : MpInt} {b : Nat} (hb1 : b ≠ 1) (hu : 0 < a.used) (hp : (b - 1) &&& b ≠ 0)
    (h : DivLongQuot a b c') : DivDQuot a b c c' where
  copy h1 := by omega
  pow2 _ _ h2 := absurd (by rw [Nat.and_comm]; exact h2) hp
  long _ _ _ := h

theorem quot_div3 {a c c' : MpInt} (hu : 0 < a.used) (h : Div3Quot a c') : DivDQuot a 3 c c' :=
  quot_long (by decide) hu (by decide) h

theorem quot_pow2 {a c c' : MpInt} {b ix : Nat} (hb1 : b ≠ 1) (hu : 0 < a.used) (hp : (b - 1) &&& b = 0)
    (heq : 2 ^ ix = b) (h : Div2dPost a ix c c') : DivDQuot a b c c' where
  copy h1 := by omega
  pow2 _ _ _ := by rw [PW.log heq]; exact h
  long _ _ h2 := absurd (by rw [Nat.and_comm]; exact hp) h2

/-- `mp_copy(a, c)` of valid `a` into shaped `c`: `c' = a` in `c`'s digits. -/
theorem quot_copy {a c c' : MpInt} {b : Nat} (ha : a.Valid) (hc : c.Shape) (h1 : b = 1 ∨ a.used = 0)
    (h : CopyPost a c c') : DivDQuot a b c c' where
  copy _ := ClampedTo.of_copy ha h.alloc (by rw [h.len]) (funext fun i => by
      rw [h.digit i]
      split
      · rfl
      · split
        · rw [ha.high_zero i (by omega)]
        · rw [hc.high_zero i (by omega), ha.high_zero i (by omega)])
    h.used h.sign
  pow2 hb hu _ := by omega
  long hb hu _ := by omega

theorem rem_copy {a : MpInt} {b : Nat} (h1 : b = 1 ∨ a.used = 0) : 0 = a.mag % b := by
  rcases h1 with h1 | h1
  · rw [h1, Nat.mod_one]
  · rw [MpInt.mag_used_zero h1, Nat.zero_mod]

theorem rem_pow2 {a : MpInt} {b ix : Nat} (ha : a.Shape) (heq : 2 ^ ix = b) (hix : ix < 28) :
    a.digit 0 % 2 ^ ix = a.mag % b := by
  rw [← heq, ← mag_mod_pow2 ha (k := ix) (by rw [digitBits_eq]; omega), Nat.and_two_pow_sub_one_eq_mod]

theorem rem_div3 (a : MpInt) : ldR a.digit 3 a.used 0 = a.mag % 3 := ldR_mag a 3

end Tom.DivDStep
