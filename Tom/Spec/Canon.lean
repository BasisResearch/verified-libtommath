import Tom.Spec.Set
import Tom.Spec.Div2d

/-!
# The record is the value

An `mp_int` result handed between calls is described by a field record (`used`, `alloc`,
`sign`, `digits.length`, `digit`); for a `Valid` result, by its value and `alloc` alone. This
file proves both halves once:

* **Digit records.** `MpInt.ext'` (the four fields), `MpInt.digits_ext` (digit-wise equal
  arrays of one length), `MpInt.eq_ofDigits` (a five-field record *is* `ofDigits u al s f`),
  `MpInt.ofDigits_shape` / `MpInt.ofDigits_valid` (the `Shape`/`Valid` records of an
  `ofDigits`, the obligations the Meet assemblies rebuild by hand).
* **Uniqueness of the digit expansion.** `natUpTo_inj` (equal values, digits below the radix:
  equal digits), `MpInt.used_eq_of_mag` (`used` of a `Valid` is fixed by `mag`),
  `MpInt.sign_eq_of_val`.
* **Value records.** `MpInt.canon_unique` (`Valid`, same `val`, same `alloc`: equal),
  `MpInt.canon_unique_mag` (the variant for sign-fixed callers), and the canonical
  representation `MpInt.canon n al` (the digits of `|n|`, zero-padded to `al`) with
  `canon_valid`, `canon_mag`, `canon_val`, `eq_canon`.
-/

namespace Tom

open MpInt

namespace MpInt

/-! ## Extensionality -/

/-- Two `mp_int`s with equal fields are equal. -/
theorem ext' {a b : MpInt} (hu : a.used = b.used) (hal : a.alloc = b.alloc) (hs : a.sign = b.sign)
    (hd : a.digits = b.digits) : a = b := by
  cases a; cases b; simp_all

/-- Digit arrays of one length with the same digits are equal. -/
theorem digits_eq_of_digit {a b : MpInt} (hl : a.digits.length = b.digits.length)
    (h : ∀ i, a.digit i = b.digit i) : a.digits = b.digits := by
  apply List.ext_getElem hl
  intro i h1 h2
  have := h i
  simp only [MpInt.digit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] at this
  exact this

/-- Shaped `mp_int`s with one `alloc` and the same digits have the same digit array. -/
theorem digits_ext {a b : MpInt} (ha : a.Shape) (hb : b.Shape) (hal : a.alloc = b.alloc)
    (h : ∀ i, a.digit i = b.digit i) : a.digits = b.digits :=
  digits_eq_of_digit (by rw [ha.len, hb.len, hal]) h

/-- Shaped `mp_int`s with equal `used`, `alloc`, `sign` and digits are equal. -/
theorem ext_digit {a b : MpInt} (ha : a.Shape) (hb : b.Shape) (hu : a.used = b.used)
    (hal : a.alloc = b.alloc) (hs : a.sign = b.sign) (h : ∀ i, a.digit i = b.digit i) : a = b :=
  ext' hu hal hs (digits_ext ha hb hal h)

/-! ## Digit records: `ofDigits` -/

/-- **A five-field record is the value**: an `mp_int` with `used = u`, `alloc = al`,
`sign = s`, `al` digits and digit `i` equal to `f i` below `al` is `ofDigits u al s f`. -/
theorem eq_ofDigits {a : MpInt} {u al s : Nat} {f : Nat → Nat} (hu : a.used = u) (hal : a.alloc = al)
    (hs : a.sign = s) (hlen : a.digits.length = al) (hd : ∀ i, i < al → a.digit i = f i) :
    a = ofDigits u al s f := by
  refine ext' hu hal hs (digits_eq_of_digit (by rw [hlen, ofDigits_len]) fun i => ?_)
  rw [ofDigits_digit]
  split
  · exact hd i ‹_›
  · simp only [MpInt.digit, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : a.digits.length ≤ i),
      Option.getD_none]

/-- The `Shape` of an `ofDigits`: digits below the radix and zero from `u` (both only
below `al`; `ofDigits` is zero above). -/
theorem ofDigits_shape {u al s : Nat} {f : Nat → Nat} (hu : u ≤ al) (hal : al < 2 ^ 31)
    (hf : ∀ j, j < al → f j < radix) (hz : ∀ j, u ≤ j → j < al → f j = 0) :
    (ofDigits u al s f).Shape :=
  { len := ofDigits_len .., used_le := hu, alloc_lt := hal
    digit_lt := fun i => by
      rw [ofDigits_digit]; split
      · exact hf i ‹_›
      · exact radix_pos
    high_zero := fun i hi => by
      rw [ofDigits_digit]; split
      · exact hz i hi ‹_›
      · rfl }

/-- The `Valid` record of an `ofDigits`: its `Shape`, a nonzero top digit, a sign, and zero
not negative. -/
theorem ofDigits_valid {u al s : Nat} {f : Nat → Nat} (hu : u ≤ al) (hal : al < 2 ^ 31)
    (hf : ∀ j, j < al → f j < radix) (hz : ∀ j, u ≤ j → j < al → f j = 0)
    (htop : 0 < u → f (u - 1) ≠ 0) (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg)
    (hzs : u = 0 → s = Layout.mpZpos) : (ofDigits u al s f).Valid :=
  { ofDigits_shape hu hal hf hz with
    top := fun h => by
      have h' : 0 < u := h
      show (ofDigits u al s f).digit (u - 1) ≠ 0
      rw [ofDigits_digit, ite_eq_left (by omega)]; exact htop h'
    sign_ok := hs, zero_pos := hzs }

end MpInt

/-! ## Uniqueness of the digit expansion -/

/-- Equal values of `u` digits below the radix: equal digits. -/
theorem natUpTo_inj {f g : Nat → Nat} {u : Nat} (hf : ∀ i, i < u → f i < radix)
    (hg : ∀ i, i < u → g i < radix) (h : natUpTo f u = natUpTo g u) : ∀ i, i < u → f i = g i := by
  intro i hi
  have key : ∀ d : Nat → Nat, (∀ i, i < u → d i < radix) → natDigit (natUpTo d u) i = d i := by
    intro d hd
    rw [natUpTo_congr u (e := fun j => if j < u then d j else 0) (fun j hj => by simp [hj]),
      natDigit_natUpTo _ (fun j => by
        split
        · exact hd j ‹_›
        · exact radix_pos), ite_eq_left hi, ite_eq_left hi]
  rw [← key f hf, ← key g hg, h]

namespace MpInt

/-- A `Valid` `mp_int` of magnitude zero has `used = 0`. -/
theorem Valid.used_zero {a : MpInt} (ha : a.Valid) (h : a.mag = 0) : a.used = 0 := by
  refine Nat.eq_zero_of_not_pos fun hu => ?_
  have := mag_ge ha hu
  have := Nat.pow_pos (n := a.used - 1) radix_pos
  omega

/-- `used` of a `Valid` `mp_int` is determined by its magnitude. -/
theorem used_eq_of_mag {a b : MpInt} (ha : a.Valid) (hb : b.Valid) (h : a.mag = b.mag) :
    a.used = b.used :=
  Nat.le_antisymm (used_le_of_mag_le hb.toShape ha (Nat.le_of_eq h))
    (used_le_of_mag_le ha.toShape hb (Nat.le_of_eq h.symm))

/-- `|val| = mag`. -/
theorem natAbs_val (a : MpInt) : a.val.natAbs = a.mag := by
  unfold MpInt.val; split <;> simp

theorem mag_eq_of_val {a b : MpInt} (h : a.val = b.val) : a.mag = b.mag := by
  rw [← natAbs_val, h, natAbs_val]

/-- The sign of a `Valid` `mp_int` is determined by its value. -/
theorem sign_eq_of_val {a b : MpInt} (ha : a.Valid) (hb : b.Valid) (h : a.val = b.val) :
    a.sign = b.sign := by
  have hm := mag_eq_of_val h
  have hz : ∀ {x : MpInt}, x.Valid → x.sign = Layout.mpNeg → x.mag = 0 → False := fun hx hs h0 => by
    have := hx.zero_pos (hx.used_zero h0)
    rw [hs] at this; exact absurd this (by decide)
  rcases ha.sign_ok with hsa | hsa <;> rcases hb.sign_ok with hsb | hsb
  · rw [hsa, hsb]
  · simp [MpInt.val, hsa, hsb, Layout.mpZpos, Layout.mpNeg] at h
    exact (hz hb hsb (by omega)).elim
  · simp [MpInt.val, hsa, hsb, Layout.mpZpos, Layout.mpNeg] at h
    exact (hz ha hsa (by omega)).elim
  · rw [hsa, hsb]

/-! ## Value records -/

/-- **Uniqueness, sign-fixed form**: `Valid`, the same magnitude, sign and `alloc`: equal. -/
theorem canon_unique_mag {a b : MpInt} (ha : a.Valid) (hb : b.Valid) (hm : a.mag = b.mag)
    (hs : a.sign = b.sign) (hal : a.alloc = b.alloc) : a = b :=
  ext_digit ha.toShape hb.toShape (used_eq_of_mag ha hb hm) hal hs fun i => by
    rw [ha.toShape.digit_eq, hb.toShape.digit_eq, hm]

/-- **Uniqueness**: `Valid`, the same value and `alloc`: equal. -/
theorem canon_unique {a b : MpInt} (ha : a.Valid) (hb : b.Valid) (hv : a.val = b.val)
    (hal : a.alloc = b.alloc) : a = b :=
  canon_unique_mag ha hb (mag_eq_of_val hv) (sign_eq_of_val ha hb hv) hal

/-- The canonical `mp_int` of value `n` with `al` digits allocated: the digits of `|n|` in
base `radix`, zero from `al` (the representation is meant for `|n| < radix ^ al`), `used`
clamped, `MP_NEG` exactly when `n < 0`. -/
def canon (n : Int) (al : Nat) : MpInt :=
  ofDigits (clampUsed (natDigit n.natAbs) al) al (if n < 0 then Layout.mpNeg else Layout.mpZpos)
    (natDigit n.natAbs)

theorem canon_digit (n : Int) (al i : Nat) :
    (canon n al).digit i = if i < al then natDigit n.natAbs i else 0 :=
  ofDigits_digit ..

theorem canon_clamped {n : Int} {al : Nat} (h : n.natAbs < radix ^ al) :
    ClampedTo (canon n al) al (natDigit n.natAbs) al (if n < 0 then Layout.mpNeg else Layout.mpZpos) := by
  have hd : (canon n al).digit = natDigit n.natAbs := funext fun i => by
    rw [canon_digit]; split
    · rfl
    · exact (natDigit_high h (by omega)).symm
  refine { alloc := rfl, len := ofDigits_len .., digit := hd, used := rfl, sign := ?_ }
  show (if n < 0 then Layout.mpNeg else Layout.mpZpos) = _
  by_cases hu : (canon n al).used = 0
  · have h0 : natUpTo (natDigit n.natAbs) (clampUsed (natDigit n.natAbs) al) = 0 := by
      rw [show clampUsed (natDigit n.natAbs) al = (canon n al).used from rfl, hu]; rfl
    rw [natUpTo_clampUsed, natUpTo_natDigit, Nat.mod_eq_of_lt h] at h0
    have : ¬ n < 0 := by omega
    simp [this, hu]
  · simp [hu]

theorem canon_spec {n : Int} {al : Nat} (h : n.natAbs < radix ^ al) (hal : al < 2 ^ 31) :
    (canon n al).Valid ∧ (canon n al).mag = n.natAbs ∧ (canon n al).val = n := by
  have := (canon_clamped h).spec_natDigit h (Nat.le_refl _) hal (by split <;> simp)
  refine ⟨this.1, this.2.1, ?_⟩
  rw [this.2.2]
  split
  · rename_i hn; rw [ite_eq_left (by decide)]; omega
  · rename_i hn; rw [ite_eq_right (by decide)]; omega

theorem canon_valid {n : Int} {al : Nat} (h : n.natAbs < radix ^ al) (hal : al < 2 ^ 31) :
    (canon n al).Valid := (canon_spec h hal).1

theorem canon_mag {n : Int} {al : Nat} (h : n.natAbs < radix ^ al) : (canon n al).mag = n.natAbs := by
  unfold MpInt.mag
  rw [show (canon n al).used = clampUsed (natDigit n.natAbs) al from rfl,
    natUpTo_congr _ (e := natDigit n.natAbs) (fun i hi => by
      rw [canon_digit, ite_eq_left (Nat.lt_of_lt_of_le hi (clampUsed_le _ _))]),
    natUpTo_clampUsed, natUpTo_natDigit, Nat.mod_eq_of_lt h]

theorem canon_val {n : Int} {al : Nat} (h : n.natAbs < radix ^ al) (hal : al < 2 ^ 31) :
    (canon n al).val = n := (canon_spec h hal).2.2

/-- A `Valid` `mp_int` is the canonical representation of its value. -/
theorem eq_canon {a : MpInt} (ha : a.Valid) : a = canon a.val a.alloc := by
  have h : a.val.natAbs < radix ^ a.alloc := by
    rw [natAbs_val]
    exact Nat.lt_of_lt_of_le (mag_lt ha.toShape) (Nat.pow_le_pow_right radix_pos ha.used_le)
  exact canon_unique ha (canon_valid h ha.alloc_lt) (canon_val h ha.alloc_lt).symm rfl

/-- A `Valid` `mp_int` of value `n` and `alloc = al` is `canon n al`. -/
theorem eq_canon_of {a : MpInt} {n : Int} {al : Nat} (ha : a.Valid) (hv : a.val = n) (hal : a.alloc = al) :
    a = canon n al := by
  subst hv hal; exact eq_canon ha

end MpInt

end Tom
