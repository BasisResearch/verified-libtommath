import Tom.Spec.Indexed
import Tom.Spec.Signed

/-!
# `mp_add_d` and `mp_sub_d`: adding and subtracting one digit

`mp_add_d(a, b, c)` (`vendor/libtommath/bn_mp_add_d.c`) and
`mp_sub_d(a, b, c)` (`bn_mp_sub_d.c`) take a digit `b < 2^MP_DIGIT_BIT`. With
`c` having room for `a->used + 1` digits (no `mp_grow`, D5) they take one of
three branches each:

| call | `a` | then |
|---|---|---|
| `mp_add_d` | `MP_ZPOS` | `c[i] = (a[i] + mu) & MP_MASK`, `mu = … >> MP_DIGIT_BIT` from `mu = b`; `c[used] = mu`; `c->used = a->used + 1`; `MP_ZPOS` |
| `mp_add_d` | `MP_NEG`, `used > 1` or `a[0] ≥ b` | `mp_sub_d(|a|, b, c)`, then `c->sign = MP_NEG`, `mp_clamp` |
| `mp_add_d` | `MP_NEG`, `used ≤ 1`, `a[0] < b` | `c[0] = b - a[0]`, `c->used = 1`, `MP_ZPOS` |
| `mp_sub_d` | `MP_NEG` | `mp_add_d(|a|, b, c)`, then `c->sign = MP_NEG`, `mp_clamp` |
| `mp_sub_d` | `used = 1`, `a[0] ≤ b`, or `used = 0` | `c[0] = b - a[0]`, `c->used = 1`, `MP_NEG` |
| `mp_sub_d` | otherwise | `c[i] = (a[i] - mu) & MP_MASK`, `mu = … >> 31` from `mu = b`; `c->used = a->used`; `MP_ZPOS` |

Each branch zeroes the old excess digits and clamps. A branch's result is a
`DRes c c' dig n s`: the digits `dig` (zero from `n` on), `used` clamped
from `n`, the sign `s` reset when the result is zero (the same shape as
`SAddPost`). The recursive branches compose a callee's `DRes` with the sign
store and the `mp_clamp` (`DRes.resign`). The digit models are the C loops
by index: `addDCarry`/`addDDigits` (the carry chain of `a` with carry-in `b`,
`carryChain a.digit 0 b`), `subDBorrow`/`subDDigits` (the borrow chain).
-/

namespace Tom

open MpInt

/-! ## A branch's result -/

/-- What a branch leaves in `c`: the digits `dig`, `used` clamped from `n`,
the sign `s` unless the result is zero; `alloc` unchanged. -/
structure DRes (c c' : MpInt) (dig : Nat → Nat) (n s : Nat) : Prop where
  alloc : c'.alloc = c.alloc
  len : c'.digits.length = c.alloc
  digit : c'.digit = dig
  used : c'.used = clampUsed dig n
  sign : c'.sign = if c'.used = 0 then Layout.mpZpos else s

theorem clampUsed_idem (dig : Nat → Nat) (n : Nat) : clampUsed dig (clampUsed dig n) = clampUsed dig n :=
  clampUsed_eq dig _ (by
      rcases Nat.eq_zero_or_pos (clampUsed dig n) with h | h
      · exact Or.inl h
      · exact Or.inr (clampUsed_top dig n h))
    _ (Nat.le_refl _) (fun _ h1 h2 => absurd h2 (Nat.not_lt.2 h1))

/-- A result, its sign then set to `s'` and clamped again (the recursive
branches: `c->sign = MP_NEG; mp_clamp(c)`). -/
theorem DRes.resign {c c' c'' : MpInt} {dig : Nat → Nat} {n s : Nat} (h : DRes c c' dig n s) (s' : Nat)
    (hc : ClampPost (c'.withSign s') c'') : DRes c c'' dig n s' :=
  have hu : c''.used = clampUsed dig n := by
    rw [hc.used]
    show clampUsed c'.digit c'.used = clampUsed dig n
    rw [h.digit, h.used, clampUsed_idem]
  { alloc := by rw [hc.alloc]; exact h.alloc
    len := by rw [hc.digits]; exact h.len
    digit := by rw [hc.digit]; exact h.digit
    used := hu
    sign := by rw [hc.sign]; rfl }

theorem DRes.congr {c c' : MpInt} {dig dig' : Nat → Nat} {n s : Nat} (h : DRes c c' dig n s)
    (he : dig = dig') : DRes c c' dig' n s := he ▸ h

/-- A branch's result is valid, with magnitude `Σ_{i<n} dig i R^i` and the
sign `s`. -/
theorem DRes.spec {c c' : MpInt} {dig : Nat → Nat} {n s : Nat} (h : DRes c c' dig n s)
    (hlt : ∀ i, dig i < radix) (hhi : ∀ i, n ≤ i → dig i = 0) (hn : n ≤ c.alloc)
    (hc : c.alloc < 2 ^ 31) (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg) :
    c'.Valid ∧ c'.mag = natUpTo dig n ∧
      c'.val = if s = Layout.mpNeg then -(natUpTo dig n : Int) else natUpTo dig n := by
  have hle := clampUsed_le dig n
  have hmag : c'.mag = natUpTo dig n := by
    unfold MpInt.mag; rw [h.digit, h.used, natUpTo_clampUsed]
  refine ⟨{ len := ?_, used_le := ?_, alloc_lt := ?_, digit_lt := ?_, high_zero := ?_,
            top := ?_, sign_ok := ?_, zero_pos := ?_ }, hmag, ?_⟩
  · rw [h.len, h.alloc]
  · rw [h.used, h.alloc]; omega
  · rw [h.alloc]; exact hc
  · rw [h.digit]; exact hlt
  · intro i hi
    rw [h.digit]
    by_cases hi' : i < n
    · exact clampUsed_zero _ _ i (h.used ▸ hi) hi'
    · exact hhi i (by omega)
  · intro hu; rw [h.digit, h.used]; exact clampUsed_top _ _ (h.used ▸ hu)
  · rw [h.sign]; split
    · exact Or.inl rfl
    · exact hs
  · intro hu; rw [h.sign, ite_eq_left_iff.2 (fun h => absurd hu h)]
  · exact val_of_post h.sign hmag

/-- `c` as a branch hands it to `mp_clamp`: `used = n`, sign `s`, digits `dig`. -/
def dMid (c : MpInt) (dig : Nat → Nat) (n s : Nat) : MpInt :=
  { used := n, alloc := c.alloc, sign := s, digits := (List.range c.alloc).map dig }

theorem dMid_digit {c : MpInt} {dig : Nat → Nat} {n s : Nat} (hhi : ∀ i, n ≤ i → dig i = 0)
    (hn : n ≤ c.alloc) : (dMid c dig n s).digit = dig := by
  funext i
  unfold MpInt.digit dMid
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < c.alloc
  · rw [List.getElem?_range h, Option.map_some, Option.getD_some]
  · rw [List.getElem?_eq_none (by rw [List.length_range]; omega), Option.map_none, Option.getD_none,
      hhi i (by omega)]

theorem dMid_shape {c : MpInt} {dig : Nat → Nat} {n s : Nat} (hlt : ∀ i, dig i < radix)
    (hhi : ∀ i, n ≤ i → dig i = 0) (hn : n ≤ c.alloc) (hc : c.alloc < 2 ^ 31) : (dMid c dig n s).Shape :=
  have hd := dMid_digit (s := s) hhi hn
  { len := by simp [dMid]
    used_le := hn
    alloc_lt := hc
    digit_lt := fun i => by rw [hd]; exact hlt i
    high_zero := fun i hi => by rw [hd]; exact hhi i hi }

/-- A branch's `mp_clamp` of `dMid` is its result. -/
theorem DRes.of_clamp {c c' : MpInt} {dig : Nat → Nat} {n s : Nat} (hhi : ∀ i, n ≤ i → dig i = 0)
    (hn : n ≤ c.alloc) (h : ClampPost (dMid c dig n s) c') : DRes c c' dig n s :=
  have hd := dMid_digit (s := s) hhi hn
  { alloc := h.alloc
    len := by rw [h.digits]; simp [dMid]
    digit := by rw [h.digit, hd]
    used := by rw [h.used, hd]; rfl
    sign := by rw [h.sign]; rfl }

/-! ## The digit loops -/

/-- The carry into position `i` of `mp_add_d`'s loop (`mu`, from `mu = b`). -/
def addDCarry (a : MpInt) (b : Nat) : Nat → Nat := carryChain a.digit (fun _ => 0) b

theorem addDCarry_zero (a : MpInt) (b : Nat) : addDCarry a b 0 = b := rfl

theorem addDCarry_succ (a : MpInt) (b i : Nat) :
    addDCarry a b (i + 1) = (a.digit i + addDCarry a b i) / radix := by
  simp [addDCarry, carryChain]

/-- `mp_add_d`'s digits for `a ≥ 0`: the loop's sums below `a->used`, the
final carry at `a->used`, zero above. -/
def addDDigits (a : MpInt) (b : Nat) (i : Nat) : Nat :=
  if i < a.used then (a.digit i + addDCarry a b i) % radix
  else if i = a.used then addDCarry a b i else 0

/-- The borrow into position `i` of `mp_sub_d`'s loop (`mu`, from `mu = b`). -/
def subDBorrow (a : MpInt) (b : Nat) : Nat → Nat := borrowChain a.digit (fun _ => 0) b

theorem subDBorrow_zero (a : MpInt) (b : Nat) : subDBorrow a b 0 = b := rfl

theorem subDBorrow_succ (a : MpInt) (b i : Nat) :
    subDBorrow a b (i + 1) = if a.digit i < subDBorrow a b i then 1 else 0 := by
  unfold subDBorrow; rw [borrowChain, Nat.zero_add]

/-- `mp_sub_d`'s digits for `a ≥ b ≥ 0`: the loop's differences below
`a->used`, zero above. -/
def subDDigits (a : MpInt) (b : Nat) (i : Nat) : Nat :=
  if i < a.used then (a.digit i + radix - subDBorrow a b i) % radix else 0

/-- The single digit of the small branches: `b - a[0]`. -/
def smallDigits (a : MpInt) (b : Nat) (i : Nat) : Nat := if i = 0 then b - a.digit 0 else 0

theorem addDCarry_lt {a : MpInt} (ha : a.Shape) {b : Nat} (hb : b < radix) :
    ∀ i, addDCarry a b i < radix
  | 0 => hb
  | i + 1 => by
    rw [addDCarry_succ]
    have := addDCarry_lt ha hb i
    have := ha.digit_lt i
    rw [radix_eq] at *
    omega

theorem addDCarry_succ_le {a : MpInt} (ha : a.Shape) {b : Nat} (hb : b < radix) (i : Nat) :
    addDCarry a b (i + 1) ≤ 1 := by
  rw [addDCarry_succ]
  have := addDCarry_lt ha hb i
  have := ha.digit_lt i
  rw [radix_eq] at *
  omega

theorem subDBorrow_le {a : MpInt} {b : Nat} (hb : b < radix) : ∀ i, subDBorrow a b i < radix
  | 0 => hb
  | i + 1 => by
    rw [subDBorrow_succ]; have := radix_pos
    rw [radix_eq]; split <;> omega

theorem subDBorrow_succ_le (a : MpInt) (b i : Nat) : subDBorrow a b (i + 1) ≤ 1 := by
  rw [subDBorrow_succ]; split <;> omega

theorem addDDigits_lt {a : MpInt} (ha : a.Shape) {b : Nat} (hb : b < radix) (i : Nat) :
    addDDigits a b i < radix := by
  unfold addDDigits
  split
  · exact Nat.mod_lt _ radix_pos
  · split
    · exact addDCarry_lt ha hb i
    · exact radix_pos

theorem addDDigits_high (a : MpInt) (b : Nat) (i : Nat) (hi : a.used + 1 ≤ i) : addDDigits a b i = 0 := by
  unfold addDDigits; rw [if_neg (by omega), if_neg (by omega)]

theorem subDDigits_lt (a : MpInt) (b : Nat) (i : Nat) : subDDigits a b i < radix := by
  unfold subDDigits; split
  · exact Nat.mod_lt _ radix_pos
  · exact radix_pos

theorem subDDigits_high (a : MpInt) (b : Nat) (i : Nat) (hi : a.used ≤ i) : subDDigits a b i = 0 := by
  unfold subDDigits; rw [if_neg (by omega)]

theorem smallDigits_lt {a : MpInt} {b : Nat} (hb : b < radix) (i : Nat) : smallDigits a b i < radix := by
  unfold smallDigits; split <;> omega

theorem smallDigits_high (a : MpInt) (b : Nat) (i : Nat) (hi : 1 ≤ i) : smallDigits a b i = 0 := by
  unfold smallDigits; rw [if_neg (by omega)]

/-- The loop sums with carry: `Σ_{i<n} c_i R^i + R^n mu_n = Σ_{i<n} a_i R^i + b`. -/
theorem natUpTo_addD (a : MpInt) (b : Nat) : ∀ n,
    natUpTo (fun i => (a.digit i + addDCarry a b i) % radix) n + radix ^ n * addDCarry a b n =
      natUpTo a.digit n + b
  | 0 => by simp [natUpTo, addDCarry_zero]
  | n + 1 => by
    have ih := natUpTo_addD a b n
    simp only [natUpTo]
    rw [addDCarry_succ]
    have h1 := Nat.mod_add_div (a.digit n + addDCarry a b n) radix
    have e : radix ^ (n + 1) * ((a.digit n + addDCarry a b n) / radix) =
        radix ^ n * (radix * ((a.digit n + addDCarry a b n) / radix)) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    have e2 : radix ^ n * ((a.digit n + addDCarry a b n) % radix) +
        radix ^ n * (radix * ((a.digit n + addDCarry a b n) / radix)) =
        radix ^ n * a.digit n + radix ^ n * addDCarry a b n := by
      rw [← Nat.mul_add, h1, Nat.mul_add]
    rw [e]
    omega

/-- The loop differences with borrow: `Σ_{i<n} c_i R^i + b = Σ_{i<n} a_i R^i + R^n mu_n`. -/
theorem natUpTo_subD {a : MpInt} (ha : a.Shape) {b : Nat} (hb : b < radix) : ∀ n,
    natUpTo (fun i => (a.digit i + radix - subDBorrow a b i) % radix) n + b =
      natUpTo a.digit n + radix ^ n * subDBorrow a b n
  | 0 => by simp [natUpTo, subDBorrow_zero]
  | n + 1 => by
    have ih := natUpTo_subD ha hb n
    simp only [natUpTo]
    have hd := ha.digit_lt n
    have hu := subDBorrow_le (a := a) hb n
    have key : (a.digit n + radix - subDBorrow a b n) % radix + subDBorrow a b n =
        a.digit n + radix * subDBorrow a b (n + 1) := by
      rw [subDBorrow_succ]
      rw [radix_eq] at *
      split <;> omega
    have e : radix ^ (n + 1) * subDBorrow a b (n + 1) = radix ^ n * (radix * subDBorrow a b (n + 1)) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    have e2 : radix ^ n * ((a.digit n + radix - subDBorrow a b n) % radix) + radix ^ n * subDBorrow a b n =
        radix ^ n * a.digit n + radix ^ n * (radix * subDBorrow a b (n + 1)) := by
      rw [← Nat.mul_add, key, Nat.mul_add]
    rw [e]
    omega

theorem natUpTo_addDDigits {a : MpInt} (b : Nat) :
    natUpTo (addDDigits a b) (a.used + 1) = a.mag + b := by
  have h := natUpTo_addD a b a.used
  simp only [natUpTo]
  rw [natUpTo_congr (e := fun i => (a.digit i + addDCarry a b i) % radix) a.used
    (fun i hi => by simp [addDDigits, hi])]
  simp only [addDDigits, Nat.lt_irrefl, if_false, if_true]
  unfold MpInt.mag
  omega

theorem natUpTo_subDDigits {a : MpInt} (ha : a.Shape) {b : Nat} (hb : b < radix) (hab : b ≤ a.mag) :
    natUpTo (subDDigits a b) a.used = a.mag - b := by
  have h := natUpTo_subD ha hb a.used
  rw [natUpTo_congr (e := fun i => (a.digit i + radix - subDBorrow a b i) % radix) a.used
    (fun i hi => by simp [subDDigits, hi])]
  have hlt := natUpTo_lt _ (fun i => Nat.mod_lt (a.digit i + radix - subDBorrow a b i) radix_pos) a.used
  -- the final borrow is zero
  have h0 : subDBorrow a b a.used = 0 := by
    rcases Nat.eq_zero_or_pos (subDBorrow a b a.used) with h0 | hpos
    · exact h0
    · have : radix ^ a.used * 1 ≤ radix ^ a.used * subDBorrow a b a.used := Nat.mul_le_mul_left _ hpos
      unfold MpInt.mag at hab
      omega
  rw [h0, Nat.mul_zero, Nat.add_zero] at h
  unfold MpInt.mag at hab ⊢
  omega

theorem natUpTo_smallDigits (a : MpInt) (b : Nat) : natUpTo (smallDigits a b) 1 = b - a.digit 0 := by
  simp [natUpTo, smallDigits]

/-- A shaped `mp_int` with at most one digit has magnitude `a[0]`. -/
theorem MpInt.mag_le_one {a : MpInt} (ha : a.Shape) (hu : a.used ≤ 1) : a.mag = a.digit 0 := by
  unfold MpInt.mag
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu with h | h
  · rw [h, ha.high_zero 0 (by omega)]; rfl
  · rw [h]; simp [natUpTo]

/-- A valid `mp_int` with two digits or more is at least the radix. -/
theorem MpInt.radix_le_mag {a : MpInt} (ha : a.Valid) (hu : 2 ≤ a.used) : radix ≤ a.mag := by
  have h := MpInt.mag_ge ha (by omega)
  have : radix ^ 1 ≤ radix ^ (a.used - 1) := Nat.pow_le_pow_right radix_pos (by omega)
  simp only [Nat.pow_one] at this
  omega

/-! ## Contracts -/

/-- `mp_add_d`'s test for its negative small branch (`a < 0` and `|a| < b`). -/
def AddDSmall (a : MpInt) (b : Nat) : Prop := a.used ≤ 1 ∧ a.digit 0 < b

/-- `mp_sub_d`'s test for its small branch (`0 ≤ a ≤ b`). -/
def SubDSmall (a : MpInt) (b : Nat) : Prop := (a.used = 1 ∧ a.digit 0 ≤ b) ∨ a.used = 0

/-- What `mp_add_d(a, b, c)` leaves in `c`, by the branch it takes. -/
structure AddDPost (a : MpInt) (b : Nat) (c c' : MpInt) : Prop where
  pos : a.sign = Layout.mpZpos → DRes c c' (addDDigits a b) (a.used + 1) Layout.mpZpos
  big : a.sign = Layout.mpNeg → ¬ AddDSmall a b → DRes c c' (subDDigits a b) a.used Layout.mpNeg
  small : a.sign = Layout.mpNeg → AddDSmall a b → DRes c c' (smallDigits a b) 1 Layout.mpZpos

/-- What `mp_sub_d(a, b, c)` leaves in `c`, by the branch it takes. -/
structure SubDPost (a : MpInt) (b : Nat) (c c' : MpInt) : Prop where
  neg : a.sign = Layout.mpNeg → DRes c c' (addDDigits a b) (a.used + 1) Layout.mpNeg
  small : a.sign = Layout.mpZpos → SubDSmall a b → DRes c c' (smallDigits a b) 1 Layout.mpNeg
  big : a.sign = Layout.mpZpos → ¬ SubDSmall a b → DRes c c' (subDDigits a b) a.used Layout.mpZpos

/-- `mp_add_d` computes `c = a + b` and leaves `c` valid. -/
theorem AddDPost.spec {a c c' : MpInt} {b : Nat} (ha : a.Valid) (hb : b < radix)
    (hroom : a.used + 1 ≤ c.alloc) (hc : c.alloc < 2 ^ 31) (h : AddDPost a b c c') :
    c'.Valid ∧ c'.val = a.val + b := by
  have hs := ha.toShape
  rw [MpInt.val_eq (a := a)]
  rcases sign_cases ha.sign_ok with h0 | h1
  · obtain ⟨hv, -, hval⟩ := (h.pos h0).spec (addDDigits_lt hs hb) (addDDigits_high a b) hroom hc (Or.inl rfl)
    refine ⟨hv, ?_⟩
    rw [hval, natUpTo_addDDigits, h0]; simp [Layout.mpNeg, Layout.mpZpos]
  · by_cases hsm : AddDSmall a b
    · obtain ⟨hv, -, hval⟩ := (h.small h1 hsm).spec (smallDigits_lt hb) (smallDigits_high a b)
        (by omega) hc (Or.inl rfl)
      refine ⟨hv, ?_⟩
      rw [hval, natUpTo_smallDigits, h1, MpInt.mag_le_one hs hsm.1]
      have := hsm.2
      simp [Layout.mpNeg, Layout.mpZpos]; omega
    · have hab : b ≤ a.mag := by
        by_cases hu : 2 ≤ a.used
        · have := MpInt.radix_le_mag ha hu; omega
        · rw [MpInt.mag_le_one hs (by omega)]
          exact Nat.le_of_not_lt fun hlt => hsm ⟨by omega, hlt⟩
      obtain ⟨hv, -, hval⟩ := (h.big h1 hsm).spec (subDDigits_lt a b) (subDDigits_high a b)
        (by omega) hc (Or.inr rfl)
      refine ⟨hv, ?_⟩
      rw [hval, natUpTo_subDDigits hs hb hab, h1]; simp [Layout.mpNeg]; omega

/-- `mp_sub_d` computes `c = a - b` and leaves `c` valid. -/
theorem SubDPost.spec {a c c' : MpInt} {b : Nat} (ha : a.Valid) (hb : b < radix)
    (hroom : a.used + 1 ≤ c.alloc) (hc : c.alloc < 2 ^ 31) (h : SubDPost a b c c') :
    c'.Valid ∧ c'.val = a.val - b := by
  have hs := ha.toShape
  rw [MpInt.val_eq (a := a)]
  rcases sign_cases ha.sign_ok with h0 | h1
  · by_cases hsm : SubDSmall a b
    · obtain ⟨hv, -, hval⟩ := (h.small h0 hsm).spec (smallDigits_lt hb) (smallDigits_high a b)
        (by omega) hc (Or.inr rfl)
      refine ⟨hv, ?_⟩
      have hle : a.mag ≤ b := by
        rcases hsm with ⟨hu, hd⟩ | hu
        · rw [MpInt.mag_le_one hs (by omega)]; exact hd
        · rw [MpInt.mag_used_zero hu]; omega
      have hm : a.digit 0 = a.mag := by
        rcases hsm with ⟨hu, _⟩ | hu
        · rw [MpInt.mag_le_one hs (by omega)]
        · rw [MpInt.mag_used_zero hu, hs.high_zero 0 (by omega)]
      rw [hval, natUpTo_smallDigits, h0, hm]
      simp [Layout.mpNeg, Layout.mpZpos]; omega
    · have hab : b ≤ a.mag := by
        by_cases hu : 2 ≤ a.used
        · have := MpInt.radix_le_mag ha hu; omega
        · have hu1 : a.used = 1 := by
            rcases Nat.lt_or_ge a.used 1 with h' | h'
            · exact absurd (Or.inr (by omega)) hsm
            · omega
          rw [MpInt.mag_le_one hs (by omega)]
          exact Nat.le_of_lt (Nat.lt_of_not_le fun hle => hsm (Or.inl ⟨hu1, hle⟩))
      obtain ⟨hv, -, hval⟩ := (h.big h0 hsm).spec (subDDigits_lt a b) (subDDigits_high a b)
        (by omega) hc (Or.inl rfl)
      refine ⟨hv, ?_⟩
      rw [hval, natUpTo_subDDigits hs hb hab, h0]; simp [Layout.mpNeg, Layout.mpZpos]; omega
  · obtain ⟨hv, -, hval⟩ := (h.neg h1).spec (addDDigits_lt hs hb) (addDDigits_high a b) hroom hc (Or.inr rfl)
    refine ⟨hv, ?_⟩
    rw [hval, natUpTo_addDDigits, h1]; simp [Layout.mpNeg]; omega

end Tom
