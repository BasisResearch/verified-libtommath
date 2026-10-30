import Tom.Spec.KSqrStep
import Tom.Spec.Mul
import Tom.Spec.Ledger

/-!
# `s_mp_balance_mul`'s model steps: the slices and their sum

`vendor/libtommath/bn_s_mp_balance_mul.c`: the longer operand `A` is cut into `nblocks` slices
of `bsize = k` digits; slice `i` is copied into `a0` (`a0.dp[count] = A.dp[j++]`), multiplied by
the shorter `B`, shifted by `k i` digits and added to `r`; then the left-over slice
`A.dp[k nblocks ..]`.

* `slice A o k n`: the digits `o, …, o + k - 1` of `A` (`alloc n`, before `mp_clamp`);
  `slice_mag`: `|slice| = |A| / R^o mod R^k` (`R = radix`);
* `acc`: after slice `i` the sum is `|A| mod R^(k (i + 1)) · |B|` (`Nat.mod_mul`);
* `fin`: the left-over slice (`|A| / R^(k nb)`) closes it to `|A| · |B|`.

**The left-over slice is not `Shape`** (`leftover_not_shape`): its copy writes only
`rem = A.used - k nb < k` digits, so `a0.dp[rem .. k)` still hold the last full slice's digits,
and `MpInt.Shape.high_zero` fails as soon as one of them is nonzero. The multiplication group's
contracts are stated over `ValidU` operands (`Tom/Spec/MpIntU.lean`), so the code's `a0`
is modelled as it is: its digits `slc f A t c` (the copied window of `A` over whatever `a0` held),
`mp_clamp`ed into a `ValidU` value (`clamp_specU`), the window's magnitude (`win_mag`, `rest_mag`).

The accumulator is signed: `B` is a struct copy of the shorter operand, sign included, so every
product `a0 · B` carries `B`'s sign and `r` holds `B.val · (|A| mod R^(k i))` (`acc_val`, `fin_val`).
-/

namespace Tom.BalMul

open MpInt KSqr

/-- Digits `o, …, o + k - 1` of `A` as an `mp_int` with `alloc n` (zero above `k`). -/
def slice (A : MpInt) (o k n : Nat) : MpInt := MpInt.ofDigits k n Layout.mpZpos (highF A o k)

/-- `|A| / R^o` as the digits above `o`. -/
theorem div_pow {A : MpInt} (ha : A.ShapeU) {o : Nat} (ho : o ≤ A.used) :
    A.mag / radix ^ o = natUpTo (fun i => A.digit (o + i)) (A.used - o) := by
  rw [mag_split ho, Nat.add_mul_div_left _ _ (Nat.pow_pos radix_pos),
    Nat.div_eq_of_lt (natUpTo_lt _ ha.digit_lt o), Nat.zero_add]

/-- **A window's magnitude**: the digits `o, …, o + k - 1` of `A`. -/
theorem win_mag {A : MpInt} (ha : A.ShapeU) {o k : Nat} (hk : o + k ≤ A.used) :
    natUpTo (fun i => A.digit (o + i)) k = A.mag / radix ^ o % radix ^ k := by
  rw [div_pow ha (by omega), show A.used - o = k + (A.used - o - k) by omega, natUpTo_split,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (natUpTo_lt _ (fun i => ha.digit_lt _) k)]

/-- **A slice's magnitude.** -/
theorem slice_mag {A : MpInt} (ha : A.ShapeU) {o k n : Nat} (hk : o + k ≤ A.used) (hkn : k ≤ n) :
    (slice A o k n).mag = A.mag / radix ^ o % radix ^ k := by
  have h1 : (slice A o k n).mag = natUpTo (fun i => A.digit (o + i)) k := by
    show natUpTo (slice A o k n).digit k = _
    exact natUpTo_congr k fun i hi => by
      rw [slice, MpInt.ofDigits_digit, if_pos (by omega)]; simp [highF, hi]
  rw [h1, win_mag ha hk]

/-- The slice is shaped (and, after `mp_clamp`, valid: `ClampPost.spec`). -/
theorem slice_shape {A : MpInt} (ha : A.ShapeU) {o k n : Nat} (hkn : k ≤ n) (hn : n < 2 ^ 31) :
    (slice A o k n).Shape where
  len := MpInt.ofDigits_len _ _ _ _
  used_le := hkn
  alloc_lt := hn
  digit_lt i := by
    rw [slice, MpInt.ofDigits_digit]; unfold highF
    split
    · split
      · exact ha.digit_lt _
      · exact radix_pos
    · exact radix_pos
  high_zero i hi := by
    rw [slice, MpInt.ofDigits_digit]; unfold highF
    simp only [slice, MpInt.ofDigits] at hi
    split
    · rw [if_neg (by omega)]
    · rfl

/-- **One slice added**: `|A| mod R^(k i) + (|A| / R^(k i) mod R^k) R^(k i) = |A| mod R^(k (i + 1))`. -/
theorem acc (A k i : Nat) :
    A % radix ^ (k * i) + A / radix ^ (k * i) % radix ^ k * radix ^ (k * i) = A % radix ^ (k * (i + 1)) := by
  rw [show k * (i + 1) = k * i + k by rw [Nat.mul_add, Nat.mul_one], Nat.pow_add, Nat.mod_mul, Nat.mul_comm _ (radix ^ (k * i))]

/-- The sum of products after slice `i`, shifted: `r = (|A| mod R^(k i)) |B|`. -/
theorem acc_mul (A Bm k i : Nat) :
    A % radix ^ (k * i) * Bm + A / radix ^ (k * i) % radix ^ k * Bm * radix ^ (k * i) =
      A % radix ^ (k * (i + 1)) * Bm := by
  rw [← acc A k i, Nat.add_mul, Nat.mul_right_comm (A / radix ^ (k * i) % radix ^ k) Bm]

/-- **The left-over slice closes the sum**: `(|A| mod R^o) |B| + (|A| / R^o) |B| R^o = |A| |B|`. -/
theorem fin (A Bm o : Nat) : A % radix ^ o * Bm + A / radix ^ o * Bm * radix ^ o = A * Bm := by
  rw [Nat.mul_right_comm (A / radix ^ o) Bm, ← Nat.add_mul, Nat.mul_comm (A / radix ^ o), Nat.mod_add_div]

/-- The left-over slice's magnitude (all of `A` above `o`). -/
theorem left_mag {A : MpInt} (ha : A.ShapeU) {o n : Nat} (ho : o ≤ A.used) (hn : A.used - o ≤ n) :
    (slice A o (A.used - o) n).mag = A.mag / radix ^ o := by
  rw [slice_mag ha (by omega) hn, Nat.mod_eq_of_lt (hi_lt ha ho)]

/-! ## The left-over copy keeps stale digits -/

/-- `a0`'s digits after the left-over copy over the previous slice `prev`: the `rem` digits of
`A` from `o`, then `prev`'s. -/
def leftF (prev : Nat → Nat) (A : MpInt) (o rem : Nat) : Nat → Nat :=
  fun j => if j < rem then A.digit (o + j) else prev j

/-- An `mp_int` with a nonzero digit at or above `used` is not `Shape`. -/
theorem not_shape_of_stale {t : MpInt} {j : Nat} (hj : t.used ≤ j) (hf : t.digit j ≠ 0) : ¬ t.Shape :=
  fun h => hf (h.high_zero j hj)

/-- **The left-over `a0` is not `Shape`** when the previous slice has a nonzero digit at or above
`rem` (inside `a0`'s `alloc n`), whatever its `used` after `mp_clamp` (at most `rem`). -/
theorem leftover_not_shape {A : MpInt} {o k rem n u s : Nat} {j : Nat} (hu : u ≤ rem) (hj : rem ≤ j)
    (hjk : j < k) (hkn : k ≤ n) (hnz : A.digit (o - k + j) ≠ 0) :
    ¬ (MpInt.ofDigits u n s (leftF (highF A (o - k) k) A o rem)).Shape := by
  refine not_shape_of_stale (j := j) (by simp only [MpInt.ofDigits]; omega) ?_
  rw [MpInt.ofDigits_digit, if_pos (by omega)]
  simp only [leftF, highF, if_neg (show ¬ j < rem by omega), if_pos hjk]
  exact hnz

/-! ## The copy as the code runs it

`a0` holds digits `f` (zeros after `mp_init_size`, the previous slice after that); the copy loop
writes `c` digits of `A` from `t` over them (`slc`), one `Mont.upd` per store (`slc_upd`), and
stores `a0.used := c` each time. -/

/-- `a0`'s digits after `c` stores of `A`'s digits from `t` over `f`. -/
def slc (f : Nat → Nat) (A : MpInt) (t c : Nat) : Nat → Nat := fun x => if x < c then A.digit (t + x) else f x

theorem slc_zero (f : Nat → Nat) (A : MpInt) (t : Nat) : slc f A t 0 = f := by
  funext x; simp [slc]

theorem slc_upd (f : Nat → Nat) (A : MpInt) (t c : Nat) :
    Mont.upd (slc f A t c) c (A.digit (t + c)) = slc f A t (c + 1) := by
  funext x; unfold Mont.upd slc
  by_cases h : x = c
  · subst h; simp
  · by_cases h' : x < c
    · simp [h, h', show x < c + 1 by omega]
    · simp [h, h', show ¬ x < c + 1 by omega]

theorem slc_lt {f : Nat → Nat} {A : MpInt} (hA : A.ShapeU) (hf : ∀ x, f x < radix) (t c x : Nat) :
    slc f A t c x < radix := by
  unfold slc; split
  · exact hA.digit_lt _
  · exact hf x

/-- `a0` handed to `mp_clamp`: `used = c`, `alloc n`, the copied digits. -/
def a0r (f : Nat → Nat) (A : MpInt) (t c n : Nat) : MpInt := MpInt.ofDigits c n Layout.mpZpos (slc f A t c)

theorem a0r_shapeU {f : Nat → Nat} {A : MpInt} (hA : A.ShapeU) (hf : ∀ x, f x < radix) {t c n : Nat}
    (hc : c ≤ n) (hn : n < 2 ^ 31) : (a0r f A t c n).ShapeU where
  len := MpInt.ofDigits_len _ _ _ _
  used_le := hc
  alloc_lt := hn
  digit_lt i := by
    rw [a0r, MpInt.ofDigits_digit]; split
    · exact slc_lt hA hf t c i
    · exact radix_pos

theorem a0r_mag (f : Nat → Nat) (A : MpInt) {t c n : Nat} (hc : c ≤ n) :
    (a0r f A t c n).mag = natUpTo (fun i => A.digit (t + i)) c := by
  show natUpTo (a0r f A t c n).digit c = _
  exact natUpTo_congr c fun i hi => by rw [a0r, MpInt.ofDigits_digit, if_pos (by omega)]; simp [slc, hi]

/-- **`mp_clamp` of an `mp_int` with stale digits**: `ValidU`, the same magnitude. -/
theorem clamp_specU {a a' : MpInt} (hs : a.ShapeU) (hsign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg)
    (h : ClampPost a a') : a'.ValidU ∧ a'.mag = a.mag := by
  have hd := h.digit
  have hle := clampUsed_le a.digit a.used
  refine ⟨{ len := ?_, used_le := ?_, alloc_lt := ?_, digit_lt := ?_, top := ?_, sign_ok := ?_,
            zero_pos := ?_ }, ?_⟩
  · rw [h.digits, h.alloc]; exact hs.len
  · rw [h.used, h.alloc]; exact Nat.le_trans hle hs.used_le
  · rw [h.alloc]; exact hs.alloc_lt
  · rw [hd]; exact hs.digit_lt
  · intro hu; rw [hd, h.used]; exact clampUsed_top a.digit a.used (h.used ▸ hu)
  · rw [h.sign]; split
    · exact Or.inl rfl
    · exact hsign
  · intro hu; rw [h.sign, ite_eq_left_iff.2 (fun h => absurd hu h)]
  · unfold MpInt.mag; rw [hd, h.used]; exact natUpTo_clampUsed a.digit a.used

/-- A clamped `a0` slice: `ValidU`, value `v`, at most `c` digits used, `n` allocated, positive. -/
structure A0 (a' : MpInt) (v c n : Nat) : Prop where
  valid : a'.ValidU
  val : a'.val = (v : Int)
  used : a'.used ≤ c
  alloc : a'.alloc = n
  sign : a'.sign = Layout.mpZpos

/-- The clamped `a0` of a full slice: `ValidU`, nonnegative, the window `|A| / R^t mod R^c`. -/
theorem a0_full {f : Nat → Nat} {A a' : MpInt} (hA : A.ShapeU) (hf : ∀ x, f x < radix) {t c n : Nat}
    (hc : c ≤ n) (hn : n < 2 ^ 31) (ht : t + c ≤ A.used) (h : ClampPost (a0r f A t c n) a') :
    A0 a' (A.mag / radix ^ t % radix ^ c) c n := by
  obtain ⟨hv, hm⟩ := clamp_specU (a0r_shapeU hA hf hc hn) (.inl rfl) h
  have hs : a'.sign = Layout.mpZpos := by rw [h.sign]; split <;> rfl
  exact { valid := hv, val := by rw [Ledger.val_zpos hs, hm, a0r_mag f A hc, win_mag hA ht],
          used := by rw [h.used]; exact clampUsed_le _ _, alloc := h.alloc, sign := hs }

/-- The clamped `a0` of the left-over slice: the rest `|A| / R^t`. -/
theorem a0_rest {f : Nat → Nat} {A a' : MpInt} (hA : A.ShapeU) (hf : ∀ x, f x < radix) {t n : Nat}
    (hc : A.used - t ≤ n) (hn : n < 2 ^ 31) (ht : t ≤ A.used) (h : ClampPost (a0r f A t (A.used - t) n) a') :
    A0 a' (A.mag / radix ^ t) (A.used - t) n := by
  obtain ⟨hv, hm⟩ := clamp_specU (a0r_shapeU hA hf hc hn) (.inl rfl) h
  have hs : a'.sign = Layout.mpZpos := by rw [h.sign]; split <;> rfl
  exact { valid := hv, val := by rw [Ledger.val_zpos hs, hm, a0r_mag f A hc, div_pow hA ht],
          used := by rw [h.used]; exact clampUsed_le _ _, alloc := h.alloc, sign := hs }

/-! ## The accumulator `r` -/

/-- **One block at offset `t`**: `|A| mod R^t + (|A| / R^t mod R^k) R^t = |A| mod R^(t + k)`. -/
theorem acc_at (A t k : Nat) :
    A % radix ^ t + A / radix ^ t % radix ^ k * radix ^ t = A % radix ^ (t + k) := by
  rw [Nat.pow_add, Nat.mod_mul, Nat.mul_comm _ (radix ^ t)]

/-- `r` after the blocks below digit `t`: valid, `B.val · (|A| mod R^t)`, at most `t + B.used` digits,
a live array. -/
structure Acc (A B r : MpInt) (t : Nat) : Prop where
  valid : r.Valid
  val : r.val = B.val * ((A.mag % radix ^ t : Nat) : Int)
  used : r.used ≤ t + B.used
  pos : 0 < r.alloc

/-- `r = 0` (`mp_init_multi`). -/
theorem acc_zero {A B r : MpInt} (hz : r.used = 0) (hv : r.Valid) (hp : 0 < r.alloc) : Acc A B r 0 where
  valid := hv
  val := by
    have hm : r.mag = 0 := by unfold MpInt.mag; rw [hz]; rfl
    have : r.val = 0 := by unfold MpInt.val; split <;> simp [hm]
    rw [this, Nat.pow_zero, Nat.mod_one]; simp
  used := by omega
  pos := hp

/-- `0` as `mp_init` leaves it. -/
theorem acc_init {A B : MpInt} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 31) : Acc A B (MpInt.zeroN n) 0 :=
  acc_zero rfl (MpInt.zeroN_valid hn') hn

/-- The product `a0 · B` (`MulPost`) of a slice with value `S ≥ 0`. -/
theorem prod_val {a0 B t1 : MpInt} {S : Nat} (ha : a0.val = S) (h : MulPost a0 B t1) :
    t1.val = (S : Int) * B.val := by rw [h.val, ha]

/-- Its size: at most `a0.used + B.used` digits. -/
theorem prod_used {a0 B t1 : MpInt} (ha : a0.ValidU) (hb : B.ValidU) (h : MulPost a0 B t1) :
    t1.used ≤ a0.used + B.used := by
  refine Ledger.used_le_of_lt h.valid ?_
  have e : t1.mag = a0.mag * B.mag := by
    rw [← natAbs_val, h.val, Int.natAbs_mul, natAbs_val, natAbs_val]
  rw [e, Nat.pow_add]
  exact Nat.mul_lt_mul'' ha.mag_lt hb.mag_lt

/-- A shifted product (`mp_lshd(&tmp, t)`): the value times `R^t`. -/
theorem shift_val {x x' : MpInt} {t : Nat} (hm : x'.mag = x.mag * radix ^ t) (hs : x'.sign = x.sign) :
    x'.val = x.val * ((radix ^ t : Nat) : Int) := by
  unfold MpInt.val; rw [hs, hm]; split <;> simp [Int.natCast_mul, Int.neg_mul]

/-- Its size. -/
theorem shift_used {x x' : MpInt} {t : Nat} (hv : x'.Valid) (hx : x.ShapeU) (hm : x'.mag = x.mag * radix ^ t) :
    x'.used ≤ x.used + t :=
  Ledger.used_le_of_lt hv (by rw [hm, Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right hx.mag_lt (Nat.pow_pos radix_pos))

/-- The signed sum of one block: `B X + S B Y = B (X + S Y)`. -/
theorem blk_val (Bv : Int) (X S Y : Nat) : Bv * (X : Int) + (S : Int) * Bv * (Y : Int) = Bv * ((X + S * Y : Nat) : Int) := by
  rw [Int.natCast_add, Int.natCast_mul, Int.mul_add, Int.mul_comm (S : Int) Bv, Int.mul_assoc]

/-- **One block**: `r + (|A| / R^t mod R^k) B R^t`. -/
theorem acc_step {A B r r' : MpInt} {t k : Nat} (h : Acc A B r t) (hv : r'.Valid)
    (hval : r'.val = r.val + ((A.mag / radix ^ t % radix ^ k : Nat) : Int) * B.val * ((radix ^ t : Nat) : Int))
    (hp : 0 < r'.alloc) (hB : B.ShapeU) : Acc A B r' (t + k) where
  valid := hv
  val := by rw [hval, h.val, blk_val, acc_at]
  used := by
    refine Ledger.used_le_of_lt hv ?_
    rw [← natAbs_val, hval, h.val, blk_val, acc_at, Int.natAbs_mul, natAbs_val, Int.natAbs_natCast, Nat.mul_comm,
      Nat.pow_add radix (t + k) B.used]
    exact Nat.mul_lt_mul_of_lt_of_le (Nat.mod_lt _ (Nat.pow_pos radix_pos)) (Nat.le_of_lt hB.mag_lt)
      (Nat.pow_pos radix_pos)
  pos := hp

/-- **The left-over block closes it**: `r + (|A| / R^t) B R^t = B.val |A|`. -/
theorem fin_val {A B r r' : MpInt} {t : Nat} (h : Acc A B r t)
    (hval : r'.val = r.val + ((A.mag / radix ^ t : Nat) : Int) * B.val * ((radix ^ t : Nat) : Int)) :
    r'.val = B.val * (A.mag : Int) := by
  rw [hval, h.val, blk_val, Nat.mod_add_div' A.mag (radix ^ t)]

/-- No left-over: the blocks cover `A`. -/
theorem fin_none {A B r : MpInt} {t : Nat} (h : Acc A B r t) (hA : A.ShapeU) (hk : A.used ≤ t) :
    r.val = B.val * (A.mag : Int) := by
  rw [h.val, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hA.mag_lt (Nat.pow_le_pow_right radix_pos hk))]

/-- **The result**: valid with magnitude `|A| |B|`. -/
theorem out_mag {A B r : MpInt} (hv : r.Valid) (h : r.val = B.val * (A.mag : Int)) : r.mag = A.mag * B.mag := by
  rw [← natAbs_val, h, Int.natAbs_mul, natAbs_val, Int.natAbs_natCast, Nat.mul_comm]

/-- The left-over product, shifted back: at most `A.used + B.used` digits. -/
theorem rest_used {A B T : MpInt} {t : Nat} (hv : T.Valid)
    (hval : T.val = ((A.mag / radix ^ t : Nat) : Int) * B.val * ((radix ^ t : Nat) : Int))
    (hA : A.ShapeU) (hB : B.ShapeU) (ht : t ≤ A.used) : T.used ≤ A.used + B.used := by
  refine Ledger.used_le_of_lt hv ?_
  rw [← natAbs_val, hval, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast, natAbs_val,
    show A.used + B.used = (A.used - t + B.used) + t by omega, Nat.pow_add, Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_lt_of_le (hi_lt hA ht) (Nat.le_of_lt hB.mag_lt)
    (Nat.pow_pos radix_pos)) (Nat.pow_pos radix_pos)

/-- The result with the operands the other way round. -/
theorem out_mag' {A B r : MpInt} (hv : r.Valid) (h : r.val = B.val * (A.mag : Int)) : r.mag = B.mag * A.mag := by
  rw [out_mag hv h, Nat.mul_comm]

/-- `a0` handed to `mp_clamp`, its digits as the last copy store left them. -/
theorem a0r_fill {f : Nat → Nat} {A : MpInt} {t c k n : Nat} (hc : c + 1 = k) :
    ∀ x, x < n → (a0r f A t k n).digit x = Mont.upd (slc f A t c) c (A.digit (t + c)) x := by
  intro x hx
  rw [a0r, MpInt.ofDigits_digit, if_pos hx, slc_upd, hc]

/-- At least two blocks: `2 ≤ ⌊u / k⌋` for `2 k ≤ u`. -/
theorem nb_two {u k : Nat} (hk : 0 < k) (h : 2 * k ≤ u) : 2 ≤ u / k :=
  (Nat.le_div_iff_mul_le hk).2 (by omega)

/-! ## The other two temporaries -/

/-- `a0` between slices: digits below `radix` (stale above `used`), `alloc n`, nonnegative. -/
structure Slot (z : MpInt) (n : Nat) : Prop where
  shape : z.ShapeU
  alloc : z.alloc = n
  sign : z.sign = Layout.mpZpos

theorem Slot.init {n : Nat} (hn : n < 2 ^ 31) : Slot (MpInt.zeroN n) n where
  shape := (MpInt.zeroN_valid hn).toShape.toU
  alloc := rfl
  sign := rfl

/-- `tmp` between blocks: what `mp_mul`'s destination needs (shaped, a sign, a live array). -/
structure Tmp (t : MpInt) : Prop where
  shape : t.Shape
  sign : t.sign = Layout.mpZpos ∨ t.sign = Layout.mpNeg
  pos : 0 < t.alloc

theorem Tmp.init {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 31) : Tmp (MpInt.zeroN n) :=
  ⟨(MpInt.zeroN_valid hn').toShape, .inl rfl, hn⟩

theorem Tmp.ofValid {t : MpInt} (hv : t.Valid) (hp : 0 < t.alloc) : Tmp t := ⟨hv.toShape, hv.sign_ok, hp⟩

/-! ## The block arithmetic (`t = k i`, `j = t`) -/

/-- The block count's bounds: `k ⌊u / k⌋ ≤ u < k ⌊u / k⌋ + k`. -/
theorem nb_lo (u k : Nat) : k * (u / k) ≤ u := Nat.mul_div_le u k

theorem nb_hi {u k : Nat} (hk : 0 < k) : u < k * (u / k) + k := by
  have := Nat.lt_mul_div_succ u hk; rw [Nat.mul_succ] at this; exact this

/-- A block below the last one fits: `t + k + k ≤ u` for `t = k i`, `i + 1 < ⌊u / k⌋`. -/
theorem blk_fit {u k i t : Nat} (ht : t = k * i) (hi : i + 1 < u / k) : t + k + k ≤ u := by
  have h1 := nb_lo u k
  have h2 : k * (i + 2) ≤ k * (u / k) := Nat.mul_le_mul_left k (by omega)
  rw [Nat.mul_add, ← ht] at h2; omega

/-- The block `i < ⌊u / k⌋` fits: `t + k ≤ u`. -/
theorem blk_in {u k i t : Nat} (ht : t = k * i) (hi : i < u / k) : t + k ≤ u := by
  have h1 := nb_lo u k
  have h2 : k * (i + 1) ≤ k * (u / k) := Nat.mul_le_mul_left k (by omega)
  rw [Nat.mul_add, ← ht] at h2; omega

/-- After the last block: `t = k ⌊u / k⌋`, the rest below one block. -/
theorem blk_end {u k i t : Nat} (hk : 0 < k) (ht : t = k * i) (hi : i = u / k) : t ≤ u ∧ u < t + k := by
  subst hi; rw [ht]; exact ⟨nb_lo u k, nb_hi hk⟩

/-- The next offset. -/
theorem blk_next {k i t : Nat} (ht : t = k * i) : t + k = k * (i + 1) := by rw [ht, Nat.mul_succ]

end Tom.BalMul
