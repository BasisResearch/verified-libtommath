import Tom.Spec.Mul

/-!
# Shifts by a bit count: `mp_mod_2d`, `mp_div_2d`, `mp_mul_2d`

`natDigit N j = N / radix ^ j % radix` is digit `j` of a number; a shaped `mp_int`'s
digits are the digits of its magnitude (`MpInt.Shape.digit_eq`), and
`natUpTo (natDigit N) n = N % radix ^ n` (`natUpTo_natDigit`).

The shift count `sh = 28 * D + d` (`D = sh / MP_DIGIT_BIT`, `d = sh % MP_DIGIT_BIT`):

* `mp_mod_2d(a, sh, c)` (`bn_mp_mod_2d.c`) copies `a`, zeroes the digits from
  `⌈sh / 28⌉` and masks digit `D` with `2^d - 1`: `mod2dDigit`;
  `mod2dDigit_eq`: digit `j` of `|a| mod 2^sh`.
* `mp_div_2d(a, sh, c, NULL)` (`bn_mp_div_2d.c`) copies `a`, drops `D` digits
  (`mp_rshd`), and shifts the rest right by `d` bits from the top, carrying the low
  `d` bits of each digit into the digit below: `div2dDigit`; `div2dDigit_eq`: digit
  `j` of `|a| / 2^sh`.
* `mp_mul_2d(a, sh, c)` (`bn_mp_mul_2d.c`) copies `a`, adds `D` zero digits below
  (`mp_lshd`), and shifts left by `d` bits from the bottom, carrying the top `d`
  bits of each digit into the digit above, the last carry into a new top digit:
  `mul2dDigit`; `natUpTo_mul2dDigit`: the digits are `|a| * 2^sh`.

The C formulas of the loop bodies (in `mp_digit` arithmetic) are `mod2dMask_c`,
`div2dDigit_c`, `mul2dDigit_c`, `mul2dCarry_c`. Each `…Post` is the case where the
destination has room (`c->alloc ≥ a->used` for `mp_copy`, `≥ a->used + D + 1` for
`mp_mul_2d`'s `mp_grow`, D5) and `sh ≥ 0` (a negative count makes `mp_mod_2d` zero,
`mp_div_2d` a copy, and `mp_mul_2d` fail with `MP_VAL`).

`ClampedTo c' al f n s` is the common shape of a result: digit function `f`, `used`
clamped from `n`, sign `s` unless zero; `ClampedTo.spec` makes it `Valid` with
magnitude `natUpTo f n`.
-/

namespace Tom

open MpInt

/-! ## Digits of a number -/

theorem radix_pow_pos (j : Nat) : 0 < radix ^ j := Nat.pow_pos radix_pos

/-- Digit `j` of `N` in base `radix`. -/
def natDigit (N j : Nat) : Nat := N / radix ^ j % radix

theorem natDigit_lt (N j : Nat) : natDigit N j < radix := Nat.mod_lt _ radix_pos

theorem natUpTo_natDigit (N : Nat) : ∀ n, natUpTo (natDigit N) n = N % radix ^ n
  | 0 => by simp [natUpTo, Nat.mod_one]
  | n + 1 => by rw [natUpTo, natUpTo_natDigit N n, Nat.mod_pow_succ]; rfl

theorem natDigit_high {N n j : Nat} (h : N < radix ^ n) (hj : n ≤ j) : natDigit N j = 0 := by
  unfold natDigit
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right radix_pos hj)), Nat.zero_mod]

/-- `N / radix^j` is digit `j` plus `radix` times `N / radix^(j+1)`. -/
theorem div_pow_succ (N j : Nat) : N / radix ^ j = natDigit N j + radix * (N / radix ^ (j + 1)) := by
  unfold natDigit
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  exact (Nat.mod_add_div _ _).symm

/-- The digits of a digit sum. -/
theorem natDigit_natUpTo (dig : Nat → Nat) (h : ∀ i, dig i < radix) (n j : Nat) :
    natDigit (natUpTo dig n) j = if j < n then dig j else 0 := by
  split
  · rename_i hj
    obtain ⟨m, rfl⟩ : ∃ m, n = (j + 1) + m := ⟨n - (j + 1), by omega⟩
    rw [natUpTo_split dig (j + 1) m]
    unfold natDigit
    rw [natUpTo, Nat.pow_succ]
    have hl := natUpTo_lt dig h j
    rw [show natUpTo dig j + radix ^ j * dig j + radix ^ j * radix * natUpTo (fun i => dig (j + 1 + i)) m
        = natUpTo dig j + radix ^ j * (dig j + radix * natUpTo (fun i => dig (j + 1 + i)) m) by
        rw [Nat.mul_add, ← Nat.mul_assoc]; omega]
    rw [Nat.add_mul_div_left _ _ (radix_pow_pos j), Nat.div_eq_of_lt hl, Nat.zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h j)]
  · exact natDigit_high (natUpTo_lt dig h n) (by omega)

/-- A shaped `mp_int`'s digits are the digits of its magnitude. -/
theorem MpInt.Shape.digit_eq {a : MpInt} (ha : a.Shape) (j : Nat) : a.digit j = natDigit a.mag j := by
  unfold MpInt.mag
  rw [natDigit_natUpTo _ ha.digit_lt]
  split
  · rfl
  · exact ha.high_zero j (by omega)

/-- A valid `mp_int` is clamped at `used`. -/
theorem MpInt.Valid.clampUsed_self {a : MpInt} (ha : a.Valid) : clampUsed a.digit a.used = a.used :=
  clampUsed_eq a.digit a.used
    (by rcases Nat.eq_zero_or_pos a.used with h | h
        · exact Or.inl h
        · exact Or.inr (ha.top h))
    a.used (Nat.le_refl _) (fun _ h1 h2 => absurd h2 (by omega))

/-! ## Results with a digit function -/

/-- An `mp_int` with digit function `f`, `used` clamped from `n`, sign `s` unless it
is zero (`mp_clamp`), and `al` digits allocated. -/
structure ClampedTo (c' : MpInt) (al : Nat) (f : Nat → Nat) (n s : Nat) : Prop where
  alloc : c'.alloc = al
  len : c'.digits.length = al
  digit : c'.digit = f
  used : c'.used = clampUsed f n
  sign : c'.sign = if c'.used = 0 then Layout.mpZpos else s

/-- Such a result is valid, with magnitude `natUpTo f n` and the sign `s`. -/
theorem ClampedTo.spec {c' : MpInt} {al n s : Nat} {f : Nat → Nat} (h : ClampedTo c' al f n s)
    (hf : ∀ i, f i < radix) (hz : ∀ i, n ≤ i → f i = 0) (hn : n ≤ al) (hal : al < 2 ^ 31)
    (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg) :
    c'.Valid ∧ c'.mag = natUpTo f n ∧
      c'.val = if s = Layout.mpNeg then -(natUpTo f n : Int) else natUpTo f n := by
  have hle := clampUsed_le f n
  have hmag : c'.mag = natUpTo f n := by
    unfold MpInt.mag; rw [h.digit, h.used, natUpTo_clampUsed]
  refine ⟨{ len := ?_, used_le := ?_, alloc_lt := ?_, digit_lt := ?_, high_zero := ?_,
            top := ?_, sign_ok := ?_, zero_pos := ?_ }, hmag, val_of_post h.sign hmag⟩
  · rw [h.len, h.alloc]
  · rw [h.used, h.alloc]; omega
  · rw [h.alloc]; exact hal
  · rw [h.digit]; exact hf
  · intro i hi
    rw [h.digit]
    by_cases hlt : i < n
    · exact clampUsed_zero _ _ i (h.used ▸ hi) hlt
    · exact hz i (by omega)
  · intro hu; rw [h.digit, h.used]; exact clampUsed_top _ _ (h.used ▸ hu)
  · rw [h.sign]; split
    · exact Or.inl rfl
    · exact hs
  · intro hu; rw [h.sign, ite_eq_left_iff.2 (fun h => absurd hu h)]

/-- A result whose digits are the digits of `N < radix ^ n`. -/
theorem ClampedTo.spec_natDigit {c' : MpInt} {al n s N : Nat} (h : ClampedTo c' al (natDigit N) n s)
    (hN : N < radix ^ n) (hn : n ≤ al) (hal : al < 2 ^ 31) (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg) :
    c'.Valid ∧ c'.mag = N ∧ c'.val = if s = Layout.mpNeg then -(N : Int) else N := by
  have := h.spec (natDigit_lt N) (fun i hi => natDigit_high hN hi) hn hal hs
  rwa [natUpTo_natDigit, Nat.mod_eq_of_lt hN] at this

/-! ## Powers of two -/

theorem digitBits_eq : Layout.digitBits = 28 := rfl

/-- `2^sh = radix^D * 2^d`. -/
theorem two_pow_split (sh : Nat) :
    2 ^ sh = radix ^ (sh / Layout.digitBits) * 2 ^ (sh % Layout.digitBits) := by
  conv => lhs; rw [← Nat.div_add_mod sh Layout.digitBits]
  rw [Nat.pow_add, Nat.pow_mul]

/-- `2^d * 2^(28-d) = radix` for `d ≤ 28`. -/
theorem two_pow_mul_compl {d : Nat} (hd : d ≤ Layout.digitBits) :
    2 ^ d * 2 ^ (Layout.digitBits - d) = radix := by
  rw [← Nat.pow_add, Nat.add_sub_cancel' hd]

theorem two_pow_dvd_radix {d : Nat} (hd : d ≤ Layout.digitBits) : 2 ^ d ∣ radix :=
  Nat.pow_dvd_pow 2 hd

theorem radix_pow_eq (j : Nat) : radix ^ j = 2 ^ (Layout.digitBits * j) := by
  rw [Nat.pow_mul]

theorem two_pow_le_radix {d : Nat} (hd : d ≤ Layout.digitBits) : 2 ^ d ≤ radix :=
  Nat.pow_le_pow_right (by decide) hd

/-! ## `mp_mod_2d` -/

/-- Digit `j` of `mp_mod_2d(a, sh, c)`: `a`'s digits below `D`, digit `D` masked with
`2^d - 1`, zero above. -/
def mod2dDigit (a : MpInt) (sh j : Nat) : Nat :=
  if j < sh / Layout.digitBits then a.digit j
  else if j = sh / Layout.digitBits then a.digit j % 2 ^ (sh % Layout.digitBits) else 0

/-- `c->dp[D] &= (1 << d) - 1`. -/
theorem mod2dMask_c (e d : Nat) : e &&& ((1 <<< d) - 1) = e % 2 ^ d := by
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]

/-- `natDigit N j` reads `N` below `radix^(j+1)`. -/
theorem natDigit_eq_mod (N j : Nat) : natDigit N j = N % radix ^ (j + 1) / radix ^ j := by
  unfold natDigit
  rw [Nat.pow_succ', Nat.mod_mul_left_div_self]

theorem mod2dDigit_eq {a : MpInt} (ha : a.Shape) (sh j : Nat) :
    mod2dDigit a sh j = natDigit (a.mag % 2 ^ sh) j := by
  have hsp := two_pow_split sh
  have hd := Nat.mod_lt sh (show 0 < Layout.digitBits by decide)
  unfold mod2dDigit
  split
  · rename_i hj
    rw [ha.digit_eq, natDigit_eq_mod, natDigit_eq_mod, Nat.mod_mod_of_dvd]
    rw [radix_pow_eq]
    apply Nat.pow_dvd_pow
    have := Nat.div_add_mod sh Layout.digitBits
    have : Layout.digitBits * (j + 1) ≤ Layout.digitBits * (sh / Layout.digitBits) :=
      Nat.mul_le_mul_left _ hj
    omega
  · split
    · rename_i _ hj
      subst hj
      rw [ha.digit_eq]
      unfold natDigit
      rw [hsp, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (two_pow_dvd_radix (Nat.le_of_lt hd)),
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
          (two_pow_le_radix (Nat.le_of_lt hd)))]
    · rename_i h1 h2
      symm
      apply natDigit_high (n := sh / Layout.digitBits + 1) _ (by omega)
      refine Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) ?_
      rw [hsp, Nat.pow_succ]
      exact Nat.mul_le_mul_left _ (two_pow_le_radix (Nat.le_of_lt hd))

/-- What `mp_mod_2d(a, sh, c)` leaves in `c` when `c->alloc ≥ a->used` (D5): the
masked digits, `used` clamped from `a->used`, `a`'s sign unless zero. (For `sh = 0`
the C calls `mp_zero(c)`; for `sh ≥ 28 * a->used` it is `mp_copy(a, c)`: both are
this state.) -/
def Mod2dPost (a : MpInt) (sh : Nat) (c c' : MpInt) : Prop :=
  ClampedTo c' c.alloc (mod2dDigit a sh) a.used a.sign

/-- `mp_mod_2d` computes `|c| = |a| mod 2^sh` with the sign of `a`. -/
theorem Mod2dPost.spec {a c c' : MpInt} {sh : Nat} (ha : a.Valid) (hroom : a.used ≤ c.alloc)
    (hc : c.alloc < 2 ^ 31) (h : Mod2dPost a sh c c') :
    c'.Valid ∧ c'.mag = a.mag % 2 ^ sh ∧
      c'.val = if a.sign = Layout.mpNeg then -((a.mag % 2 ^ sh : Nat) : Int) else (a.mag % 2 ^ sh : Nat) := by
  have hf : mod2dDigit a sh = natDigit (a.mag % 2 ^ sh) := funext (mod2dDigit_eq ha.toShape sh)
  unfold Mod2dPost at h
  rw [hf] at h
  exact h.spec_natDigit (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (MpInt.mag_lt ha.toShape)) hroom hc ha.sign_ok

/-! ## `mp_div_2d` -/

/-- Digit `j` of `mp_div_2d(a, sh, c, NULL)`: after `mp_rshd(c, D)` digit `j` is
`a[j + D]`; the bit loop shifts it right by `d` and ORs in the low `d` bits of the
digit above, shifted up by `28 - d`. -/
def div2dDigit (a : MpInt) (sh j : Nat) : Nat :=
  a.digit (j + sh / Layout.digitBits) / 2 ^ (sh % Layout.digitBits) +
    a.digit (j + sh / Layout.digitBits + 1) % 2 ^ (sh % Layout.digitBits) *
      2 ^ (Layout.digitBits - sh % Layout.digitBits)

/-- The bit loop of `mp_div_2d`: `rr = *tmpc & mask` is `e % 2^d`, and
`(*tmpc >> D) | (r << shift)` is the model's digit (no `uint32_t` wrap). -/
theorem div2dDigit_c (e r d : Nat) (hd : d < Layout.digitBits) (he : e < radix) (hr : r < 2 ^ d) :
    (e >>> d) ||| (r <<< (Layout.digitBits - d)) = e / 2 ^ d + r * 2 ^ (Layout.digitBits - d) ∧
      e / 2 ^ d + r * 2 ^ (Layout.digitBits - d) < radix := by
  have hc := two_pow_mul_compl (Nat.le_of_lt hd)
  have hq : e / 2 ^ d < 2 ^ (Layout.digitBits - d) :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by rw [Nat.mul_comm, hc]; exact he)
  refine ⟨?_, ?_⟩
  · rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact hq),
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.add_comm]
  · have : (r + 1) * 2 ^ (Layout.digitBits - d) ≤ 2 ^ d * 2 ^ (Layout.digitBits - d) :=
      Nat.mul_le_mul_right _ hr
    rw [Nat.succ_mul, hc] at this
    omega

/-- `(x + radix * (y + radix * F)) / p % radix = x / p + (y % p) * s` for `p * s = radix`. -/
theorem div_digit_pair {p s x y F : Nat} (hps : p * s = radix) (hx : x < radix) :
    (x + radix * (y + radix * F)) / p % radix = x / p + y % p * s := by
  have hp : 0 < p := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0, Nat.zero_mul] at hps; exact absurd hps.symm (Nat.ne_of_gt radix_pos))
  have hy := Nat.mod_add_div y p
  have e : x + radix * (y + radix * F) = x + p * (s * (y % p) + radix * (y / p + s * F)) := by
    rw [← hps]
    conv => lhs; rw [← hy]
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm s p]
    omega
  rw [e, Nat.add_mul_div_left _ _ hp, ← Nat.add_assoc, Nat.add_mul_mod_self_left]
  have h1 : x / p < s := (Nat.div_lt_iff_lt_mul hp).2 (by rw [Nat.mul_comm s p, hps]; exact hx)
  have h2 : (y % p + 1) * s ≤ p * s := Nat.mul_le_mul_right _ (Nat.mod_lt _ hp)
  rw [Nat.succ_mul] at h2
  rw [Nat.mod_eq_of_lt (by rw [Nat.mul_comm s (y % p)]; omega), Nat.mul_comm s (y % p)]

theorem div2dDigit_eq {a : MpInt} (ha : a.Shape) (sh j : Nat) :
    div2dDigit a sh j = natDigit (a.mag / 2 ^ sh) j := by
  have hd := Nat.mod_lt sh (show 0 < Layout.digitBits by decide)
  have hsp := two_pow_split sh
  unfold div2dDigit natDigit
  generalize sh / Layout.digitBits = D at hsp ⊢
  generalize sh % Layout.digitBits = d at hsp hd ⊢
  have e1 : a.mag / 2 ^ sh / radix ^ j = a.mag / radix ^ (j + D) / 2 ^ d := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, hsp, Nat.pow_add]
    congr 1
    ac_rfl
  rw [e1, div_pow_succ a.mag (j + D), div_pow_succ a.mag (j + D + 1), ← ha.digit_eq, ← ha.digit_eq,
    div_digit_pair (two_pow_mul_compl (Nat.le_of_lt hd)) (ha.digit_lt _)]

/-- What `mp_div_2d(a, sh, c, NULL)` leaves in `c` when `c->alloc ≥ a->used` (D5):
the shifted digits, `used` clamped from `a->used - D`, `a`'s sign unless zero. (With
`d != NULL` it also leaves `Mod2dPost a sh d d'` in `d`.) The in-place call
`mp_div_2d(x, sh, x, NULL)` (in `mp_div`) leaves the same state with `c = a`. -/
def Div2dPost (a : MpInt) (sh : Nat) (c c' : MpInt) : Prop :=
  ClampedTo c' c.alloc (div2dDigit a sh) (a.used - sh / Layout.digitBits) a.sign

/-- `mp_div_2d` computes `|c| = |a| / 2^sh` with the sign of `a` (truncation). -/
theorem Div2dPost.spec {a c c' : MpInt} {sh : Nat} (ha : a.Valid) (hroom : a.used ≤ c.alloc)
    (hc : c.alloc < 2 ^ 31) (h : Div2dPost a sh c c') :
    c'.Valid ∧ c'.mag = a.mag / 2 ^ sh ∧
      c'.val = if a.sign = Layout.mpNeg then -((a.mag / 2 ^ sh : Nat) : Int) else (a.mag / 2 ^ sh : Nat) := by
  have hf : div2dDigit a sh = natDigit (a.mag / 2 ^ sh) := funext (div2dDigit_eq ha.toShape sh)
  unfold Div2dPost at h
  rw [hf] at h
  refine h.spec_natDigit ?_ (Nat.le_trans (Nat.sub_le _ _) hroom) hc ha.sign_ok
  have hm := MpInt.mag_lt ha.toShape
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), two_pow_split sh, ← Nat.mul_assoc, ← Nat.pow_add]
  generalize sh / Layout.digitBits = D
  calc a.mag < radix ^ a.used := hm
    _ ≤ radix ^ (a.used - D + D) := Nat.pow_le_pow_right radix_pos (by omega)
    _ ≤ radix ^ (a.used - D + D) * 2 ^ (sh % Layout.digitBits) := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)

/-! ## `mp_mul_2d` -/

/-- The low part of `e << d` kept in the digit (`(*tmpc << d) & MP_MASK`). -/
def shlLo (d e : Nat) : Nat := e * 2 ^ d % radix

/-- The carry `(*tmpc >> (28 - d)) & mask`: the top `d` bits of `e`. -/
def shlHi (d e : Nat) : Nat := e * 2 ^ d / radix

/-- Digit `j` of `mp_mul_2d(a, sh, c)`: after `mp_lshd(c, D)` digit `j` is
`a[j - D]` (zero below `D`); the bit loop keeps its low `28 - d` bits shifted up by `d`
and ORs in the carry from the digit below; the last carry is the digit at
`a->used + D`. -/
def mul2dDigit (a : MpInt) (sh j : Nat) : Nat :=
  (if sh / Layout.digitBits ≤ j then shlLo (sh % Layout.digitBits) (a.digit (j - sh / Layout.digitBits))
    else 0) +
  (if sh / Layout.digitBits < j then shlHi (sh % Layout.digitBits) (a.digit (j - sh / Layout.digitBits - 1))
    else 0)

theorem shlLo_eq {d e : Nat} (hd : d ≤ Layout.digitBits) :
    shlLo d e = e % 2 ^ (Layout.digitBits - d) * 2 ^ d := by
  unfold shlLo
  rw [← two_pow_mul_compl hd, Nat.mul_comm (2 ^ d), Nat.mul_mod_mul_right]

theorem shlHi_eq {d e : Nat} (hd : d ≤ Layout.digitBits) : shlHi d e = e / 2 ^ (Layout.digitBits - d) := by
  unfold shlHi
  rw [← two_pow_mul_compl hd, Nat.mul_comm (2 ^ d), Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)]

theorem shlHi_lt {d e : Nat} (hd : d ≤ Layout.digitBits) (he : e < radix) : shlHi d e < 2 ^ d := by
  rw [shlHi_eq hd, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), two_pow_mul_compl hd]
  exact he

/-- The kept part leaves the low `d` bits free. -/
theorem shlLo_add_lt {d e r : Nat} (hd : d ≤ Layout.digitBits) (hr : r < 2 ^ d) : shlLo d e + r < radix := by
  rw [shlLo_eq hd]
  have h := Nat.mul_le_mul_right (2 ^ d)
    (Nat.mod_lt e (Nat.two_pow_pos (Layout.digitBits - d)) : e % 2 ^ (Layout.digitBits - d) + 1 ≤ _)
  rw [Nat.succ_mul, Nat.mul_comm (2 ^ (Layout.digitBits - d)), two_pow_mul_compl hd] at h
  omega

/-- The bit loop of `mp_mul_2d`: `((*tmpc << d) | r) & MP_MASK`, with the shift done
in `W ≥ 28` bits, is the model's digit. -/
theorem mul2dDigit_c (e r d W : Nat) (hd : d ≤ Layout.digitBits) (hW : Layout.digitBits ≤ W)
    (hr : r < 2 ^ d) :
    ((e * 2 ^ d % 2 ^ W) ||| r) &&& Layout.mpMask = shlLo d e + r := by
  have hdW : 2 ^ d ∣ 2 ^ W := Nat.pow_dvd_pow 2 (Nat.le_trans hd hW)
  have hdiv : 2 ^ d ∣ e * 2 ^ d % 2 ^ W := (Nat.dvd_mod_iff hdW).2 (Nat.dvd_mul_left _ _)
  have hor : (e * 2 ^ d % 2 ^ W) ||| r = e * 2 ^ d % 2 ^ W + r := by
    obtain ⟨m, hm⟩ := hdiv
    rw [hm, Nat.mul_comm, ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt hr]
  rw [hor, and_mpMask, ← Nat.mod_add_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hW)]
  exact Nat.mod_eq_of_lt (shlLo_add_lt hd hr)

/-- The carry of `mp_mul_2d`'s loop: `(*tmpc >> (28 - d)) & ((1 << d) - 1)`. -/
theorem mul2dCarry_c (e d : Nat) (hd : d ≤ Layout.digitBits) (he : e < radix) :
    (e >>> (Layout.digitBits - d)) &&& ((1 <<< d) - 1) = shlHi d e := by
  rw [mod2dMask_c, Nat.shiftRight_eq_div_pow, ← shlHi_eq hd]
  exact Nat.mod_eq_of_lt (shlHi_lt hd he)

theorem mul2dDigit_lt {a : MpInt} (ha : a.Shape) (sh j : Nat) : mul2dDigit a sh j < radix := by
  have hd := Nat.le_of_lt (Nat.mod_lt sh (show 0 < Layout.digitBits by decide))
  unfold mul2dDigit
  have hhi : (if sh / Layout.digitBits < j then shlHi (sh % Layout.digitBits)
      (a.digit (j - sh / Layout.digitBits - 1)) else 0) < 2 ^ (sh % Layout.digitBits) := by
    split
    · exact shlHi_lt hd (ha.digit_lt _)
    · exact Nat.two_pow_pos _
  split
  · exact shlLo_add_lt hd hhi
  · have := shlLo_add_lt (e := 0) hd hhi
    omega

theorem mul2dDigit_high {a : MpInt} (ha : a.Shape) (sh j : Nat) (hj : a.used + sh / Layout.digitBits + 1 ≤ j) :
    mul2dDigit a sh j = 0 := by
  unfold mul2dDigit shlLo shlHi
  rw [ha.high_zero _ (by omega), ha.high_zero _ (by omega)]
  simp

/-- **The shift**: the digits of `mp_mul_2d` are `|a| * 2^sh`. -/
theorem natUpTo_mul2dDigit {a : MpInt} (ha : a.Shape) (sh : Nat) :
    natUpTo (mul2dDigit a sh) (a.used + sh / Layout.digitBits + 1) = a.mag * 2 ^ sh := by
  have hd := Nat.le_of_lt (Nat.mod_lt sh (show 0 < Layout.digitBits by decide))
  generalize hD : sh / Layout.digitBits = D
  generalize hdd : sh % Layout.digitBits = d at hd
  have hsp : 2 ^ sh = radix ^ D * 2 ^ d := by rw [two_pow_split, hD, hdd]
  let lo := fun m => shlLo d (a.digit m)
  let hi := fun m => shlHi d (a.digit m)
  let h : Nat → Nat := fun m => lo m + if 1 ≤ m then hi (m - 1) else 0
  have hm : ∀ j, mul2dDigit a sh j = if D ≤ j then h (j - D) else 0 := by
    intro j
    unfold mul2dDigit
    rw [hD, hdd]
    by_cases h1 : D ≤ j
    · by_cases h2 : D < j
      · simp only [h1, h2, ite_true, h, lo, hi, show 1 ≤ j - D by omega]
      · simp only [h1, h2, ite_true, ite_false, h, lo, show ¬ 1 ≤ j - D by omega]
    · simp only [h1, show ¬ D < j by omega, ite_false, Nat.add_zero]
  rw [natUpTo_congr _ (e := fun j => if D ≤ j then h (j - D) else 0) (fun j _ => hm j),
    show a.used + D + 1 = D + (a.used + 1) by omega, natUpTo_shift h D (a.used + 1)]
  have hsum : natUpTo h (a.used + 1) = natUpTo lo (a.used + 1) +
      natUpTo (fun m => if 1 ≤ m then hi (m - 1) else 0) (1 + a.used) := by
    rw [Nat.add_comm 1 a.used]; exact natUpTo_add _ _ _
  have hs1 : natUpTo (fun m => if 1 ≤ m then hi (m - 1) else 0) (1 + a.used) = radix ^ 1 * natUpTo hi a.used :=
    natUpTo_shift hi 1 a.used
  have hlo : natUpTo lo (a.used + 1) = natUpTo lo a.used := by
    rw [natUpTo]
    simp only [lo, ha.high_zero a.used (Nat.le_refl _), shlLo, Nat.zero_mul, Nat.zero_mod, Nat.mul_zero,
      Nat.add_zero]
  have hpair : natUpTo lo a.used + radix * natUpTo hi a.used = 2 ^ d * a.mag := by
    rw [← natUpTo_mul, ← natUpTo_add]
    unfold MpInt.mag
    rw [← natUpTo_mul]
    apply natUpTo_congr; intro i _
    simp only [lo, hi, shlLo, shlHi]
    rw [Nat.mod_add_div, Nat.mul_comm]
  rw [hsum, hs1, hlo, Nat.pow_one, hpair, hsp, Nat.mul_comm a.mag, Nat.mul_assoc]

/-- What `mp_mul_2d(a, sh, c)` leaves in `c` when `c->alloc ≥ a->used + D + 1` (no
`mp_grow`, D5): the shifted digits, `used` clamped from `a->used + D + 1`, `a`'s sign
unless zero. (The C's `used` is `a->used + D`, plus one if the last carry is
nonzero, then `mp_clamp`: the same.) The in-place call `mp_mul_2d(x, sh, x)` (in
`mp_div`) leaves the same state with `c = a`. -/
def Mul2dPost (a : MpInt) (sh : Nat) (c c' : MpInt) : Prop :=
  ClampedTo c' c.alloc (mul2dDigit a sh) (a.used + sh / Layout.digitBits + 1) a.sign

/-- `mp_mul_2d` computes `c = a * 2^sh`. -/
theorem Mul2dPost.spec {a c c' : MpInt} {sh : Nat} (ha : a.Valid)
    (hroom : a.used + sh / Layout.digitBits + 1 ≤ c.alloc) (hc : c.alloc < 2 ^ 31) (h : Mul2dPost a sh c c') :
    c'.Valid ∧ c'.mag = a.mag * 2 ^ sh ∧ c'.val = a.val * 2 ^ sh := by
  obtain ⟨hv, hm, hval⟩ := ClampedTo.spec h (mul2dDigit_lt ha.toShape sh)
    (fun i hi => mul2dDigit_high ha.toShape sh i hi) hroom hc ha.sign_ok
  rw [natUpTo_mul2dDigit ha.toShape] at hm hval
  refine ⟨hv, hm, ?_⟩
  rw [hval, MpInt.val_eq]
  split <;> push_cast <;> simp [Int.neg_mul]

end Tom
