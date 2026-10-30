import Tom.Spec.Gcd
import Tom.Spec.Bits
import Tom.Spec.Sub
import Tom.Spec.Div2d
import Tom.Spec.Init
import Tom.Spec.Set

/-!
# `mp_gcd`'s model steps

What the assembly (`Fn/MpGcdMainG.lean`) needs from `Tom/Spec`, once:

* `cntLsb_eq`: `mp_cnt_lsb(a)` (`Bits.lean`'s `cntLsb`, the C's nibble table) is
  `Gcd.lsb |a|`, the trailing zero bits of the magnitude; `lsb_lt`: it is below
  `28 used`.
* `Tmp x n v N`: a temporary of the loop: valid, nonnegative, magnitude `v`, `alloc = n`,
  `used ≤ N`. Its steps: `mp_init_copy` and `sign := MP_ZPOS` (`Tmp.init`),
  `mp_div_2d` in place (`Tmp.div`), `s_mp_sub(&v, &u, &v)` (`Tmp.sub`).
* `GLoop`: the loop invariant at `11c8` (`Gcd.GcdInv` and `gcdLoop` on the two magnitudes),
  its one pass (`GLoop.next`), its exit (`GLoop.fin`: the result and the room of
  `mp_mul_2d(&u, k, c)`).
-/

namespace Tom

open MpInt Gcd

namespace GcdStep

/-! ## Trailing zero bits -/

theorem lsb_eq_of : ∀ (k : Nat) {n o : Nat}, n = 2 ^ k * o → o % 2 = 1 → lsb n = k
  | 0, n, o, h, ho => by
    rw [lsb]; simp only [Nat.pow_zero, Nat.one_mul] at h; subst h
    rw [dite_eq_right_iff.2 (fun h => absurd h.2 (by omega))]
  | k + 1, n, o, h, ho => by
    have hk : 0 < 2 ^ k := Nat.two_pow_pos k
    have hn : n ≠ 0 ∧ n % 2 = 0 := by
      subst h; rw [Nat.pow_succ]
      refine ⟨Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos hk (by decide)) (by omega)), ?_⟩
      rw [Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]; exact Nat.mul_mod_right _ _
    rw [lsb, dite_eq_left_of_eq_true (eq_true hn), lsb_eq_of k (o := o) (by
      subst h; rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]) ho]

theorem lsb_mul_pow (k : Nat) {n : Nat} (hn : n ≠ 0) : lsb (2 ^ k * n) = k + lsb n :=
  lsb_eq_of _ (o := oddPart n) (by rw [Nat.pow_add, Nat.mul_assoc, oddPart_mul]) (oddPart_odd n hn)

/-- The nibble table: `lnz[j]` is the number of trailing zeros of `j ≠ 0`. -/
theorem lnzTab_spec : ∀ j, j < 16 → j ≠ 0 → j % 2 ^ lnzTab j = 0 ∧ (j / 2 ^ lnzTab j) % 2 = 1 ∧ lnzTab j ≤ 3 := by
  decide

theorem lsbInner_eq (q : Nat) (hq : q ≠ 0) : lsbInner q = lsb q := by
  by_cases h0 : q % 16 = 0
  · rw [lsbInner_step h0 hq, lsbInner_eq (q / 16) (by omega)]
    have : q = 2 ^ 4 * (q / 16) := by omega
    conv => rhs; rw [this]
    rw [lsb_mul_pow 4 (by omega)]
  · rw [lsbInner_stop h0]
    obtain ⟨h1, h2, h3⟩ := lnzTab_spec (q % 16) (Nat.mod_lt _ (by decide)) h0
    generalize lnzTab (q % 16) = t at h1 h2 h3 ⊢
    have h16 : 2 ^ t ∣ 16 := by
      rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl <;> decide
    have hd : 2 ^ t ∣ q := by
      have e := Nat.div_add_mod q 16
      have : 2 ^ t ∣ 16 * (q / 16) + q % 16 :=
        Nat.dvd_add (Nat.dvd_trans h16 (Nat.dvd_mul_right _ _)) (Nat.dvd_of_mod_eq_zero h1)
      rwa [e] at this
    symm
    apply lsb_eq_of _ (o := q / 2 ^ t) (Nat.mul_div_cancel' hd).symm
    have e : q = 16 * (q / 16) + q % 16 := (Nat.div_add_mod q 16).symm
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp only [Nat.pow_zero, Nat.pow_succ, Nat.one_mul, Nat.div_one] at h1 h2 ⊢ <;> omega
termination_by q
decreasing_by omega

/-- The lowest nonzero digit below `n`, when there is one. -/
theorem firstNz_spec (dig : Nat → Nat) : ∀ n, (∃ j, j < n ∧ dig j ≠ 0) →
    firstNz dig n < n ∧ dig (firstNz dig n) ≠ 0 ∧ ∀ j, j < firstNz dig n → dig j = 0
  | 0, ⟨j, hj, _⟩ => absurd hj (by omega)
  | n + 1, hex => by
    by_cases hlo : ∃ j, j < n ∧ dig j ≠ 0
    · obtain ⟨h1, h2, h3⟩ := firstNz_spec dig n hlo
      simp only [firstNz, h1, ↓reduceIte]
      exact ⟨by omega, h2, h3⟩
    · have hz : ∀ j, j < n → dig j = 0 := fun j hj => Classical.byContradiction fun h => hlo ⟨j, hj, h⟩
      have hn : dig n ≠ 0 := by
        obtain ⟨j, hj, hne⟩ := hex
        rcases Nat.lt_or_ge j n with h | h
        · exact absurd (hz j h) hne
        · rwa [show j = n by omega] at hne
      simp only [firstNz, firstNz_zeros dig n hz, Nat.lt_irrefl, ↓reduceIte, ne_eq, hn, not_false_eq_true]
      exact ⟨by omega, trivial, hz⟩

/-! ## `mp_cnt_lsb` -/

theorem natUpTo_split (dig : Nat → Nat) (x : Nat) :
    ∀ n, x < n → ∃ r, natUpTo dig n = natUpTo dig x + radix ^ x * (dig x + radix * r)
  | 0, h => absurd h (by omega)
  | n + 1, h => by
    rcases Nat.lt_or_ge x n with hx | hx
    · obtain ⟨r, hr⟩ := natUpTo_split dig x n hx
      refine ⟨r + radix ^ (n - x - 1) * dig n, ?_⟩
      have e : radix ^ n = radix ^ x * (radix * radix ^ (n - x - 1)) := by
        rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
      simp only [natUpTo, hr, e, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]
    · have : x = n := by omega
      subst this
      exact ⟨0, by simp [natUpTo]⟩

theorem natUpTo_low_zero (dig : Nat → Nat) : ∀ x, (∀ j, j < x → dig j = 0) → natUpTo dig x = 0
  | 0, _ => rfl
  | x + 1, h => by simp only [natUpTo, natUpTo_low_zero dig x (fun j hj => h j (by omega)), h x (by omega)]; simp

/-- **`mp_cnt_lsb` is the number of trailing zero bits of the magnitude**, and it lies
below `28 used`. -/
theorem cntLsb_eq {a : MpInt} (ha : a.Valid) : cntLsb a = lsb a.mag ∧ (a.used ≠ 0 → lsb a.mag < Layout.digitBits * a.used) := by
  unfold cntLsb
  by_cases hu : a.used = 0
  · simp only [hu, ↓reduceIte, MpInt.mag, natUpTo]; exact ⟨by rw [lsb]; simp, fun h => absurd rfl h⟩
  simp only [hu, ↓reduceIte]
  have hex : ∃ j, j < a.used ∧ a.digit j ≠ 0 := ⟨a.used - 1, by omega, ha.top (by omega)⟩
  obtain ⟨hx1, hx2, hz⟩ := firstNz_spec a.digit a.used hex
  generalize firstNz a.digit a.used = x at hx1 hx2 hz ⊢
  have hxs : x < a.used ∧ a.digit x ≠ 0 := ⟨hx1, hx2⟩
  obtain ⟨r, hr⟩ := natUpTo_split a.digit x a.used hxs.1
  rw [natUpTo_low_zero a.digit x hz, Nat.zero_add] at hr
  have hd := ha.digit_lt x
  have hdl : lsb (a.digit x) < Layout.digitBits := by
    have h1 := oddPart_mul (a.digit x)
    have h2 := oddPart_pos hxs.2
    refine Nat.lt_of_not_le fun hle => ?_
    have : 2 ^ Layout.digitBits ≤ 2 ^ lsb (a.digit x) := Nat.pow_le_pow_right (by decide) hle
    have : 2 ^ lsb (a.digit x) ≤ a.digit x := by
      calc 2 ^ lsb (a.digit x) = 2 ^ lsb (a.digit x) * 1 := (Nat.mul_one _).symm
        _ ≤ 2 ^ lsb (a.digit x) * oddPart (a.digit x) := Nat.mul_le_mul_left _ h2
        _ = a.digit x := h1
    have : radix = 2 ^ Layout.digitBits := rfl
    omega
  have hm : lsb (MpInt.mag a) = Layout.digitBits * x + lsb (a.digit x) := by
    unfold MpInt.mag; rw [hr]
    have hR : radix ^ x = 2 ^ (Layout.digitBits * x) := by simp only [radix]; rw [Nat.pow_mul]
    rw [hR]
    apply lsb_eq_of _ (o := oddPart (a.digit x) + 2 ^ (Layout.digitBits - lsb (a.digit x)) * r)
    · rw [Nat.pow_add, Nat.mul_assoc]; congr 1
      have e : radix = 2 ^ lsb (a.digit x) * 2 ^ (Layout.digitBits - lsb (a.digit x)) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hdl)]
      conv => lhs; rw [← oddPart_mul (a.digit x), e]
      rw [Nat.mul_add, Nat.mul_assoc]
    · have := oddPart_odd (a.digit x) hxs.2
      have h2 : 2 ^ (Layout.digitBits - lsb (a.digit x)) * r % 2 = 0 := by
        obtain ⟨m', hm'⟩ : ∃ m', Layout.digitBits - lsb (a.digit x) = m' + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
        rw [hm', Nat.pow_succ, Nat.mul_comm (2 ^ m') 2, Nat.mul_assoc]; exact Nat.mul_mod_right _ _
      omega
  refine ⟨?_, fun _ => ?_⟩
  · rw [hm]; split
    · rename_i hodd
      rw [lsb_eq_of 0 (o := a.digit x) (by simp) hodd]
    · rw [lsbInner_eq _ hxs.2]
  · rw [hm]
    have : Layout.digitBits * x + Layout.digitBits ≤ Layout.digitBits * a.used := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hxs.1
    omega


/-! ## The temporaries `u`, `v` -/

theorem initPrec_pos (n : Nat) : 0 < initPrec n := by
  unfold initPrec; rw [minPrec_eq]; omega


/-- A temporary of the loop: valid, nonnegative, magnitude `v`, `n` digits allocated,
`used ≤ N`. -/
structure Tmp (x : MpInt) (n v N : Nat) : Prop where
  valid : x.Valid
  mag : x.mag = v
  zpos : x.sign = Layout.mpZpos
  alloc : x.alloc = n
  used_le : x.used ≤ N

theorem _root_.Tom.MpInt.Valid.setSign0 {x : MpInt} (h : x.Valid) : ({ x with sign := 0 } : MpInt).Valid :=
  { h.toShape with top := h.top, sign_ok := Or.inl rfl, zero_pos := fun _ => rfl }

/-- `mp_init_copy(&u, a)`, then `u.sign := MP_ZPOS`. -/
theorem Tmp.init {a u : MpInt} {N : Nat} (ha : a.Valid) (hc : CopyPost a (MpInt.zeroN (initPrec a.used)) u)
    (hN : a.used ≤ N) : Tmp { u with sign := 0 } (initPrec a.used) a.mag N := by
  have hn : initPrec a.used < 2 ^ 31 := by
    have := ha.used_le; have := ha.alloc_lt; unfold initPrec; rw [minPrec_eq]; omega
  have hz := MpInt.zeroN_valid hn
  have ⟨hv, hm, _⟩ := hc.spec ha hz.toShape (Nat.le_max_right _ _)
  exact { valid := hv.setSign0, mag := hm, zpos := rfl, alloc := hc.alloc
          used_le := by show u.used ≤ N; rw [hc.used]; exact hN }

theorem Tmp.shape {x : MpInt} {n v N : Nat} (h : Tmp x n v N) : x.Shape := h.valid.toShape

theorem Tmp.bits {x : MpInt} {n v N : Nat} (h : Tmp x n v N) (hN : Layout.digitBits * N < 2 ^ 31) :
    Layout.digitBits * x.used < 2 ^ 31 := by have := Nat.mul_le_mul_left Layout.digitBits h.used_le; omega

/-- `mp_cnt_lsb(x)`. -/
theorem Tmp.lsb {x : MpInt} {n v N : Nat} (h : Tmp x n v N) : cntLsb x = Gcd.lsb v := by
  rw [(cntLsb_eq h.valid).1, h.mag]

theorem Tmp.lsb_lt {x : MpInt} {n v N : Nat} (h : Tmp x n v N) (hv : v ≠ 0) : Gcd.lsb v < Layout.digitBits * N := by
  have hu : x.used ≠ 0 := fun hu => hv (by rw [← h.mag]; simp [MpInt.mag, hu, natUpTo])
  have h2 := (cntLsb_eq h.valid).2 hu; rw [h.mag] at h2
  have h3 := Nat.mul_le_mul_left Layout.digitBits h.used_le
  omega

/-- `mp_div_2d(x, s, x, NULL)`. -/
theorem Tmp.div {x y : MpInt} {n v N s : Nat} (h : Tmp x n v N) (hd : Div2dPost x s x y) :
    Tmp y n (v / 2 ^ s) N := by
  have hc : ClampedTo y x.alloc _ _ _ := hd
  have ⟨hv, hm, _⟩ := Div2dPost.spec h.valid h.valid.used_le h.valid.alloc_lt hd
  refine { valid := hv, mag := by rw [hm, h.mag], zpos := ?_, alloc := by rw [hc.alloc, h.alloc], used_le := ?_ }
  · rw [hc.sign]; split
    · rfl
    · exact h.zpos
  · have := MpInt.used_le_of_mag_le h.shape hv (by rw [hm]; exact Nat.div_le_self _ _)
    have := h.used_le; omega

/-- `s_mp_sub(&v, &u, &v)` with `|u| ≤ |v|`. -/
theorem Tmp.sub {V U W : MpInt} {nv nu a b N : Nat} (hv : Tmp V nv a N) (hu : Tmp U nu b N) (hle : b ≤ a)
    (hs : SSubPost V U V W) : Tmp W nv (a - b) N := by
  have ⟨hw, hm⟩ := SSubPost.spec hv.shape hu.shape (by rw [hv.mag, hu.mag]; exact hle) hv.valid.used_le
    hv.valid.alloc_lt (.inl hv.zpos) hs
  refine { valid := hw, mag := by rw [hm, hv.mag, hu.mag], zpos := ?_, alloc := by rw [hs.alloc, hv.alloc], used_le := ?_ }
  · rw [hs.sign]; split
    · rfl
    · exact hv.zpos
  · have := MpInt.used_le_of_mag_le hv.shape hw (by rw [hm]; exact Nat.sub_le _ _)
    have := hv.used_le; omega

/-- `s_mp_sub`'s `b->used ≤ a->used`. -/
theorem Tmp.ge {V U : MpInt} {nv nu a b N : Nat} (hv : Tmp V nv a N) (hu : Tmp U nu b N) (hle : b ≤ a) :
    U.used ≤ V.used :=
  MpInt.used_le_of_mag_le hv.shape hu.valid (by rw [hv.mag, hu.mag]; exact hle)

/-- A value that lies below an operand's magnitude: `used` below `N`. -/
theorem Tmp.re {x : MpInt} {n v v' N : Nat} (h : Tmp x n v N) (e : v = v') : Tmp x n v' N := e ▸ h


/-- The magnitude as the value. -/
theorem Tmp.self {x : MpInt} {n v N : Nat} (h : Tmp x n v N) : Tmp x n x.mag N := { h with mag := rfl }

/-- `mp_cnt_lsb`'s count is an `int` (for `mp_div_2d`'s `b`). -/
theorem Tmp.lsb_lt' {x : MpInt} {n v N : Nat} (h : Tmp x n v N) (hN : Layout.digitBits * N < 2 ^ 31) :
    cntLsb x < 2 ^ 31 := by
  rw [h.lsb]
  by_cases hv : v = 0
  · subst hv; rw [Gcd.lsb]; simp
  · have := h.lsb_lt hv; omega

/-- The value after `mp_div_2d(x, lsb x)`: the odd part. -/
theorem Tmp.odd {x y : MpInt} {n v N : Nat} (h : Tmp x n v N) (hd : Div2dPost x (cntLsb x) x y) :
    Tmp y n (oddPart v) N := by
  have := h.div hd; rw [h.lsb] at this; exact this

/-! ## The loop -/

/-- The C's pass when `|u| > |v|`: exchange, subtract, halve. -/
theorem inv_gt {G u v : Nat} (h : GcdInv G u v) (hv : v ≠ 0) (hlt : v < u) :
    GcdInv G v (oddPart (u - v)) ∧ v + oddPart (u - v) < u + v := by
  have hs := h.step hv
  have hl := gcdStep_lt (u := u) (v := v) (by have := h.u_odd; omega) hv
  unfold gcdStep at hs hl; rw [if_pos hlt] at hs hl
  exact ⟨hs, hl⟩

/-- The C's pass when `|u| ≤ |v|`: subtract, halve. -/
theorem inv_le {G u v : Nat} (h : GcdInv G u v) (hv : v ≠ 0) (hle : u ≤ v) :
    GcdInv G u (oddPart (v - u)) ∧ u + oddPart (v - u) < u + v := by
  have hs := h.step hv
  have hl := gcdStep_lt (u := u) (v := v) (by have := h.u_odd; omega) hv
  unfold gcdStep at hs hl; rw [if_neg (by omega)] at hs hl
  exact ⟨hs, hl⟩

/-- The loop's entry: the odd parts. -/
theorem inv_init {A B : Nat} (hA : A ≠ 0) (hB : B ≠ 0) :
    GcdInv (Nat.gcd (oddPart A) (oddPart B)) (oddPart A) (oddPart B) :=
  ⟨oddPart_odd A hA, fun _ => oddPart_odd B hB, rfl⟩

/-- `mp_cmp_mag(u, v) == MP_GT` for valid operands. -/
theorem cmp_gt {U V : MpInt} : compare U.mag V.mag = .gt ↔ V.mag < U.mag := Nat.compare_eq_gt

/-- The answer: `gcdC A B = gcd (odd A) (odd B) * 2 ^ k`. -/
theorem gcdC_split {A B k : Nat} (hA : A ≠ 0) (hB : B ≠ 0) (hk : k = min (Gcd.lsb A) (Gcd.lsb B)) :
    gcdC A B = Nat.gcd (oddPart A) (oddPart B) * 2 ^ k := by
  rw [gcdC_eq, gcd_split hA hB, hk]

/-- `|u| 2^k ≤ |a|` at the exit. -/
theorem gcd_shift_le {A B k : Nat} (hA : A ≠ 0) (hk : k ≤ Gcd.lsb A) :
    Nat.gcd (oddPart A) (oddPart B) * 2 ^ k ≤ A := by
  have h1 : Nat.gcd (oddPart A) (oddPart B) ≤ oddPart A :=
    Nat.le_of_dvd (oddPart_pos hA) (Nat.gcd_dvd_left _ _)
  have h2 : 2 ^ k ≤ 2 ^ Gcd.lsb A := Nat.pow_le_pow_right (by decide) hk
  calc Nat.gcd (oddPart A) (oddPart B) * 2 ^ k ≤ oddPart A * 2 ^ Gcd.lsb A := Nat.mul_le_mul h1 h2
    _ = A := by rw [Nat.mul_comm]; exact oddPart_mul A

/-- The room of `mp_mul_2d(&u, k, c)`: `u->used + k / 28 ≤ a->used` when `|u| 2^k ≤ |a|`. -/
theorem used_shift_le {U a : MpInt} {k : Nat} (hU : U.Valid) (hu0 : U.mag ≠ 0) (ha : a.Shape)
    (hle : U.mag * 2 ^ k ≤ a.mag) : U.used + k / Layout.digitBits ≤ a.used := by
  have hu : 0 < U.used := by
    refine Nat.pos_of_ne_zero fun h => hu0 ?_; simp [MpInt.mag, h, natUpTo]
  have h1 := MpInt.mag_ge hU hu
  have h2 := MpInt.mag_lt ha
  have h3 : radix ^ (k / Layout.digitBits) ≤ 2 ^ k := by
    show (2 ^ Layout.digitBits) ^ (k / Layout.digitBits) ≤ 2 ^ k
    rw [← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (Nat.mul_div_le k _)
  have h4 : radix ^ (U.used - 1 + k / Layout.digitBits) < radix ^ a.used := by
    rw [Nat.pow_add]
    calc radix ^ (U.used - 1) * radix ^ (k / Layout.digitBits) ≤ U.mag * 2 ^ k := Nat.mul_le_mul h1 h3
      _ ≤ a.mag := hle
      _ < radix ^ a.used := h2
  have := (Nat.pow_lt_pow_iff_right (by decide : 1 < radix)).1 h4
  omega

/-- **The result**: `mp_mul_2d(&u, k, c)` then `c->sign := MP_ZPOS`. -/
theorem fin_post {a b U c c' : MpInt} {k : Nat} (hA : a.mag ≠ 0) (hB : b.mag ≠ 0)
    (hk : k = min (Gcd.lsb a.mag) (Gcd.lsb b.mag)) (hU : U.Valid)
    (hUm : U.mag = Nat.gcd (oddPart a.mag) (oddPart b.mag))
    (hroom : U.used + k / Layout.digitBits + 1 ≤ c.alloc) (hc : c.alloc < 2 ^ 31) (hm : Mul2dPost U k c c') :
    GcdPost a b { c' with sign := 0 } ∧ ({ c' with sign := 0 } : MpInt).alloc = c.alloc := by
  have ⟨hv, hmag, _⟩ := Mul2dPost.spec hU hroom hc hm
  have hcl : ClampedTo c' c.alloc _ _ _ := hm
  refine ⟨{ valid := hv.setSign0, mag := ?_, sign := rfl }, hcl.alloc⟩
  show c'.mag = _
  rw [hmag, hUm, gcdC_split hA hB hk]

/-- `mp_gcd`'s room for `mp_mul_2d` from `Res.room`. -/
theorem fin_room {a b U : MpInt} {k n : Nat} (ha : a.Valid) (hA : a.mag ≠ 0)
    (hk : k = min (Gcd.lsb a.mag) (Gcd.lsb b.mag)) (hU : U.Valid)
    (hUm : U.mag = Nat.gcd (oddPart a.mag) (oddPart b.mag)) (hroom : max a.used b.used + 1 ≤ n) :
    U.used + k / Layout.digitBits + 1 ≤ n := by
  have hu0 : U.mag ≠ 0 := by
    rw [hUm]; exact Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ (oddPart_pos hA))
  have := used_shift_le hU hu0 ha.toShape (by rw [hUm]; exact gcd_shift_le (B := b.mag) (k := k) hA (by omega))
  omega

/-- `a = 0`: `mp_abs(b, c)`. -/
theorem abs_b {a b c c' : MpInt} (ha : a.used = 0) (hb : b.Valid) (hc : c.Shape) (hroom : b.used ≤ c.alloc)
    (h : AbsPost b c c') : GcdPost a b c' ∧ c'.alloc = c.alloc := by
  have ⟨hv, hm, _⟩ := h.spec hb hc hroom
  refine ⟨{ valid := hv, mag := ?_, sign := h.sign }, h.alloc⟩
  have : a.mag = 0 := by simp [MpInt.mag, ha, natUpTo]
  rw [hm, this]; simp [gcdC]

/-- `b = 0`: `mp_abs(a, c)`. -/
theorem abs_a {a b c c' : MpInt} (hb : b.used = 0) (ha : a.Valid) (hc : c.Shape) (hroom : a.used ≤ c.alloc)
    (h : AbsPost a c c') : GcdPost a b c' ∧ c'.alloc = c.alloc := by
  have ⟨hv, hm, _⟩ := h.spec ha hc hroom
  refine ⟨{ valid := hv, mag := ?_, sign := h.sign }, h.alloc⟩
  have : b.mag = 0 := by simp [MpInt.mag, hb, natUpTo]
  rw [hm, this]; unfold gcdC; split <;> simp_all

theorem mag_zero_of_used {a : MpInt} (h : a.used = 0) : a.mag = 0 := by
  simp [MpInt.mag, h, natUpTo]

/-- A nonzero `used` is a nonzero magnitude. -/
theorem mag_ne_zero {a : MpInt} (ha : a.Valid) (hu : a.used ≠ 0) : a.mag ≠ 0 := by
  have := MpInt.mag_ge ha (by omega); have : 0 < radix ^ (a.used - 1) := Nat.pow_pos radix_pos
  omega

end GcdStep

end Tom
