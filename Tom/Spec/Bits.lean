import Tom.Spec.Algo

/-!
# `mp_count_bits`: bit lengths

`mp_count_bits(a)` (`vendor/libtommath/bn_mp_count_bits.c`) returns `0` for
zero, otherwise `(used - 1) * MP_DIGIT_BIT` plus the number of shifts that
empty the top digit. `bitLen q` is that number of shifts (`0` for `0`);
`countBits` is the C's formula; `countBits_spec` says it is the bit length
of the magnitude.
-/

namespace Tom

open MpInt

/-- The number of bits of `q`: how often `q >>= 1` runs before `q = 0`. -/
def bitLen (q : Nat) : Nat := if q = 0 then 0 else Nat.log2 q + 1

theorem bitLen_zero : bitLen 0 = 0 := rfl

/-- One shift of the C's loop. -/
theorem bitLen_step {q : Nat} (h : q ≠ 0) : bitLen q = bitLen (q / 2) + 1 := by
  unfold bitLen
  simp only [h, ↓reduceIte]
  by_cases h2 : q / 2 = 0
  · simp only [h2, ↓reduceIte]; rw [Nat.log2_def]; simp only [show ¬ 2 ≤ q by omega, ↓reduceIte]
  · simp only [h2, ↓reduceIte]; rw [Nat.log2_def q]; simp only [show 2 ≤ q by omega, ↓reduceIte]

theorem lt_two_pow_bitLen (q : Nat) : q < 2 ^ bitLen q := by
  unfold bitLen
  by_cases h : q = 0
  · subst h; decide
  · simp only [h, ↓reduceIte]; exact Nat.lt_log2_self

theorem two_pow_bitLen_le {q : Nat} (h : q ≠ 0) : 2 ^ (bitLen q - 1) ≤ q := by
  unfold bitLen
  simp only [h, ↓reduceIte, Nat.add_sub_cancel]
  exact Nat.log2_self_le h

theorem bitLen_le {q k : Nat} (h : q < 2 ^ k) : bitLen q ≤ k := by
  unfold bitLen
  by_cases hq : q = 0
  · simp [hq]
  · simp only [hq, ↓reduceIte]; have := (Nat.log2_lt hq).2 h; omega

/-- `bitLen` from bounds: `2^(k-1) ≤ n < 2^k` with `k ≥ 1`. -/
theorem bitLen_eq {n k : Nat} (hk : 1 ≤ k) (h1 : n < 2 ^ k) (h2 : 2 ^ (k - 1) ≤ n) : bitLen n = k := by
  have hn : n ≠ 0 := by have := Nat.one_le_two_pow (n := k - 1); omega
  unfold bitLen
  simp only [hn, ↓reduceIte]
  have a1 : n.log2 < k := (Nat.log2_lt hn).2 h1
  have a2 : ¬ n.log2 < k - 1 := fun h => by have := (Nat.log2_lt hn).1 h; omega
  omega

/-- `mp_count_bits(a)` as the C states it. -/
def countBits (a : MpInt) : Nat :=
  if a.used = 0 then 0 else Layout.digitBits * (a.used - 1) + bitLen (a.digit (a.used - 1))

/-- **`mp_count_bits` is the bit length of the magnitude.** -/
theorem countBits_spec {a : MpInt} (ha : a.Valid) : countBits a = bitLen a.mag := by
  unfold countBits
  by_cases hu : a.used = 0
  · simp only [hu, ↓reduceIte, MpInt.mag, natUpTo]; rfl
  simp only [hu, ↓reduceIte]
  obtain ⟨u, hu'⟩ : ∃ u, a.used = u + 1 := ⟨a.used - 1, by omega⟩
  have ht := ha.top (by omega)
  rw [hu', Nat.add_sub_cancel] at ht ⊢
  have hlo := natUpTo_lt a.digit ha.digit_lt u
  have htl := ha.digit_lt u
  have hb1 := lt_two_pow_bitLen (a.digit u)
  have hb2 := two_pow_bitLen_le ht
  have hbl : 1 ≤ bitLen (a.digit u) := by
    unfold bitLen; simp only [ht, ↓reduceIte]; omega
  have hr : radix ^ u = 2 ^ (Layout.digitBits * u) := by
    simp only [radix]; rw [Nat.pow_mul]
  have hmag : a.mag = natUpTo a.digit u + radix ^ u * (a.digit u) := by
    simp only [MpInt.mag, hu', natUpTo]
  symm
  apply bitLen_eq (by omega)
  · rw [hmag, Nat.pow_add, ← hr]
    have : radix ^ u * ((a.digit u) + 1) ≤ radix ^ u * 2 ^ bitLen (a.digit u) := Nat.mul_le_mul_left _ hb1
    rw [Nat.mul_succ] at this
    omega
  · rw [hmag, show Layout.digitBits * u + bitLen (a.digit u) - 1 = Layout.digitBits * u + (bitLen (a.digit u) - 1) by omega,
      Nat.pow_add, ← hr]
    have : radix ^ u * 2 ^ (bitLen (a.digit u) - 1) ≤ radix ^ u * (a.digit u) := Nat.mul_le_mul_left _ hb2
    omega

/-- `mp_count_bits` is at most `MP_DIGIT_BIT * used`. -/
theorem countBits_le {a : MpInt} (ha : a.Shape) : countBits a ≤ Layout.digitBits * a.used := by
  unfold countBits
  split
  · omega
  · have := bitLen_le (k := Layout.digitBits) (ha.digit_lt (a.used - 1))
    have : Layout.digitBits * (a.used - 1) + Layout.digitBits = Layout.digitBits * a.used := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega

/-! ## `mp_cnt_lsb` -/

/-- `lnz` of `bn_mp_cnt_lsb.c`: the trailing zeros of a nibble (`4` for `0`). -/
def lnzTab (j : Nat) : Nat := [4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0].getD j 0

theorem lnzTab_le (j : Nat) (hj : j < 16) : lnzTab j ≤ 4 := by
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals first | omega | decide

theorem lnzTab_le3 (j : Nat) (hj : j < 16) (h0 : j ≠ 0) : lnzTab j ≤ 3 := by
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals first | omega | decide

/-- The C's nibble loop: `x += lnz[q & 15]; q >>= 4` while the nibble was zero. -/
def lsbInner (q : Nat) : Nat :=
  if q % 16 = 0 ∧ q ≠ 0 then 4 + lsbInner (q / 16) else lnzTab (q % 16)
termination_by q
decreasing_by omega

theorem lsbInner_step {q : Nat} (h0 : q % 16 = 0) (hq : q ≠ 0) : lsbInner q = 4 + lsbInner (q / 16) := by
  rw [lsbInner]; simp [h0, hq]

theorem lsbInner_stop {q : Nat} (h0 : q % 16 ≠ 0) : lsbInner q = lnzTab (q % 16) := by
  rw [lsbInner]; simp [h0]

/-- A nonzero `q` below `16^n` has fewer than `4 n` trailing zeros. -/
theorem lsbInner_lt : ∀ n q, q ≠ 0 → q < 16 ^ n → lsbInner q < 4 * n
  | 0, q, hq, h => by simp at h; omega
  | n + 1, q, hq, h => by
    by_cases h0 : q % 16 = 0
    · rw [lsbInner_step h0 hq]
      have := lsbInner_lt n (q / 16) (by omega) (by rw [Nat.pow_succ] at h; omega)
      omega
    · rw [lsbInner_stop h0]
      have := lnzTab_le3 (q % 16) (Nat.mod_lt _ (by decide)) h0
      omega

/-- The index of the lowest nonzero digit below `n` (`n` if none). -/
def firstNz (dig : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if firstNz dig n < n then firstNz dig n else if dig n ≠ 0 then n else n + 1

theorem firstNz_zeros (dig : Nat → Nat) : ∀ n, (∀ j, j < n → dig j = 0) → firstNz dig n = n
  | 0, _ => rfl
  | n + 1, h => by
    have ih := firstNz_zeros dig n (fun j hj => h j (by omega))
    simp only [firstNz, ih, Nat.lt_irrefl, ↓reduceIte, h n (by omega), ne_eq, not_true_eq_false]

theorem firstNz_eq (dig : Nat → Nat) (x : Nat) (hz : ∀ j, j < x → dig j = 0) (hx : dig x ≠ 0) :
    ∀ n, x < n → firstNz dig n = x
  | 0, h => absurd h (by omega)
  | n + 1, h => by
    rcases Nat.lt_or_ge x n with hn | hn
    · have ih := firstNz_eq dig x hz hx n hn
      simp only [firstNz, ih, hn, ↓reduceIte]
    · have hxn : x = n := by omega
      subst hxn
      simp only [firstNz, firstNz_zeros dig x hz, Nat.lt_irrefl, ↓reduceIte, ne_eq, hx, not_false_eq_true]

/-- `mp_cnt_lsb(a)` as the C states it. -/
def cntLsb (a : MpInt) : Nat :=
  if a.used = 0 then 0
  else Layout.digitBits * firstNz a.digit a.used +
    (if a.digit (firstNz a.digit a.used) % 2 = 1 then 0 else lsbInner (a.digit (firstNz a.digit a.used)))

end Tom
