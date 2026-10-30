import Tom.Spec.Div
import Tom.Spec.Signed
import Tom.Spec.Set
import Tom.Spec.Cmp

/-!
# `mp_div`'s model steps: the callees' results as the long division's quantities

`Tom/Spec/DivKnuth.lean` has the arithmetic (`DivInv`, `knuth_step`, `knuth_skip`, the C's
`mp_word` steps);

* `sub_pos`, `add_negpos`: `mp_sub(&x, &y, &x)` of two nonnegative integers and
  `mp_add(&x, &t1, &x)` of a negative and a nonnegative one, with the room the code has
  (`max(used) ≤ alloc`: both take a `s_mp_sub` branch, which does not grow; `SubPost.spec`
  and `AddPost.spec` assume one digit more, for the `s_mp_add` branches);
* step 2 (`S2`): `x + j D = A` with `x ≥ 0`; `S2.step` (`mp_cmp ≠ MP_LT`, `++q[n-t]`,
  `mp_sub`), `S2.exit` (`j = A / D`, `x = A % D`);
* step 3.2 (`Fix`): the do-while's stored digit `qv` with `fixDown p q̂₀ = fixDown p (dec qv)`;
* step 3.3/3.4 (`step3`): `mp_mul_d`, `mp_lshd`, `mp_sub` and the add-back leave
  `knuthXn` and write `knuthQd`, so `DivInv` steps (`DivInv.step` by `knuth_step`).
-/

namespace Tom.DivStep

open MpInt

/-! ## Signs -/

theorem val_zpos {x : MpInt} (h : x.sign = Layout.mpZpos) : x.val = x.mag := by
  simp [MpInt.val, h, Layout.mpZpos, Layout.mpNeg]

theorem val_neg {x : MpInt} (h : x.sign = Layout.mpNeg) : x.val = -(x.mag : Int) := by
  simp [MpInt.val, h]

theorem mag_pos_of_used {x : MpInt} (hx : x.Valid) (hu : x.used ≠ 0) : 0 < x.mag :=
  Nat.lt_of_lt_of_le (radix_pow_pos _) (MpInt.mag_ge hx (by omega))

theorem used_zero_of_mag {x : MpInt} (hx : x.Valid) (hm : x.mag = 0) : x.used = 0 := by
  rcases Nat.eq_zero_or_pos x.used with h | h
  · exact h
  · have := mag_pos_of_used hx (by omega); omega

/-- `s_mp_sub(a, b, c)` with `|b| ≤ |a|` and the sign `s` written before: valid,
`|c'| = |a| - |b|`, the sign `s` unless zero. -/
theorem ssub_val {a b c c' : MpInt} (ha : a.Valid) (hb : b.Valid) (hmag : b.mag ≤ a.mag)
    (hroom : a.used ≤ c.alloc) (hc : c.alloc < 2 ^ 31) {s : Nat} (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg)
    (h : SSubPost a b (c.withSign s) c') : c'.Valid ∧ c'.val = sval s (a.mag - b.mag) := by
  obtain ⟨hv, hm⟩ := SSubPost.spec (c := c.withSign s) ha.toShape hb.toShape hmag hroom hc hs h
  refine ⟨hv, ?_⟩
  rw [MpInt.val_sval, hm]
  have hsg : c'.sign = if c'.used = 0 then Layout.mpZpos else s := h.sign
  by_cases hu : c'.used = 0
  · rw [hsg, if_pos hu]
    have : a.mag - b.mag = 0 := by rw [← hm]; exact MpInt.mag_used_zero hu
    rw [this, sval_mag_zero, sval_mag_zero]
  · rw [hsg, if_neg hu]

/-- **`mp_sub(&x, &y, &x)`**, `x`, `y` nonnegative (steps 2 and 3.3). -/
theorem sub_pos {x y x' : MpInt} (hx : x.Valid) (hy : y.Valid) (hxs : x.sign = Layout.mpZpos)
    (hys : y.sign = Layout.mpZpos) (hroom : max x.used y.used ≤ x.alloc) (h : SubPost x y x x') :
    x'.Valid ∧ x'.val = x.val - y.val := by
  have hss : x.sign = y.sign := by rw [hxs, hys]
  have hal := hx.alloc_lt
  rw [val_zpos hxs, val_zpos hys]
  by_cases hlt : x.mag < y.mag
  · have hc : cmpMag x y = .lt := by rw [cmpMag_eq hx hy]; exact Nat.compare_eq_lt.2 hlt
    have h2 := h.lt hss hc
    rw [if_pos hxs] at h2
    obtain ⟨hv, hval⟩ := ssub_val hy hx (Nat.le_of_lt hlt) (by omega) hal (Or.inr rfl) h2
    refine ⟨hv, ?_⟩
    rw [hval, sval_neg]; omega
  · have hc : cmpMag x y ≠ .lt := by
      rw [cmpMag_eq hx hy]; intro h'; exact hlt (Nat.compare_eq_lt.1 h')
    have h2 := h.ge hss hc
    rw [hxs] at h2
    obtain ⟨hv, hval⟩ := ssub_val hx hy (Nat.le_of_not_lt hlt) (by omega) hal (Or.inl rfl) h2
    refine ⟨hv, ?_⟩
    rw [hval, sval_zero]; omega

/-- **`mp_add(&x, &t1, &x)`**, `x` negative, `t1` nonnegative (the add-back, step 3.4). -/
theorem add_negpos {x y x' : MpInt} (hx : x.Valid) (hy : y.Valid) (hxs : x.sign = Layout.mpNeg)
    (hys : y.sign = Layout.mpZpos) (hroom : max x.used y.used ≤ x.alloc) (h : AddPost x y x x') :
    x'.Valid ∧ x'.val = x.val + y.val := by
  have hss : x.sign ≠ y.sign := by rw [hxs, hys]; decide
  have hal := hx.alloc_lt
  rw [val_neg hxs, val_zpos hys]
  by_cases hlt : x.mag < y.mag
  · have hc : cmpMag x y = .lt := by rw [cmpMag_eq hx hy]; exact Nat.compare_eq_lt.2 hlt
    have h2 := h.lt hss hc
    rw [hys] at h2
    obtain ⟨hv, hval⟩ := ssub_val hy hx (Nat.le_of_lt hlt) (by omega) hal (Or.inl rfl) h2
    refine ⟨hv, ?_⟩
    rw [hval, sval_zero]; omega
  · have hc : cmpMag x y ≠ .lt := by
      rw [cmpMag_eq hx hy]; intro h'; exact hlt (Nat.compare_eq_lt.1 h')
    have h2 := h.ge hss hc
    rw [hxs] at h2
    obtain ⟨hv, hval⟩ := ssub_val hx hy (Nat.le_of_not_lt hlt) (by omega) hal (Or.inr rfl) h2
    refine ⟨hv, ?_⟩
    rw [hval, sval_neg]; omega

/-- A valid integer with a nonnegative value has the sign `MP_ZPOS`. -/
theorem sign_of_val_nonneg {x : MpInt} (hx : x.Valid) (h : 0 ≤ x.val) : x.sign = Layout.mpZpos := by
  rcases sign_cases hx.sign_ok with hs | hs
  · exact hs
  · have hn : x.sign = Layout.mpNeg := hs
    rw [val_neg hn] at h
    have hm : x.mag = 0 := by omega
    exact hx.zero_pos (used_zero_of_mag hx hm)

/-- A valid integer with a negative value has the sign `MP_NEG`. -/
theorem sign_of_val_neg {x : MpInt} (hx : x.Valid) (h : x.val < 0) : x.sign = Layout.mpNeg := by
  rcases sign_cases hx.sign_ok with hs | hs
  · have hz : x.sign = Layout.mpZpos := hs
    rw [val_zpos hz] at h; omega
  · exact hs

/-! ## Step 2: `while (x ≥ y b^(n-t)) { ++q[n-t]; x -= y b^(n-t) }` -/

/-- Before step 2's test: `x + j D = A`, `x ≥ 0`. -/
structure S2 (A D : Nat) (x : MpInt) (j : Nat) : Prop where
  valid : x.Valid
  pos : x.sign = Layout.mpZpos
  sum : x.mag + j * D = A

theorem S2.init {x : MpInt} {D : Nat} (hx : x.Valid) (hp : x.sign = Layout.mpZpos) : S2 x.mag D x 0 :=
  ⟨hx, hp, by simp⟩

/-- `mp_cmp(&x, &y)` of two nonnegative integers compares their magnitudes. -/
theorem cmpS_pos {x y : MpInt} (hx : x.Valid) (hy : y.Valid) (hxs : x.sign = Layout.mpZpos)
    (hys : y.sign = Layout.mpZpos) : cmpS x y = compare x.mag y.mag := by
  rw [cmpS_spec hx hy, val_zpos hxs, val_zpos hys]
  rcases Nat.lt_trichotomy x.mag y.mag with h | h | h
  · rw [Nat.compare_eq_lt.2 h]; exact Int.compare_eq_lt.2 (by omega)
  · rw [h, Nat.compare_eq_eq.2 rfl]; exact Int.compare_eq_eq.2 rfl
  · rw [Nat.compare_eq_gt.2 h]; exact Int.compare_eq_gt.2 (by omega)

/-- `x ≥ D`: one more subtraction. -/
theorem S2.step {A D j : Nat} {x y x' : MpInt} (h : S2 A D x j) (hy : y.Valid) (hys : y.sign = Layout.mpZpos)
    (hym : y.mag = D) (hge : D ≤ x.mag) (hroom : max x.used y.used ≤ x.alloc) (hs : SubPost x y x x') :
    S2 A D x' (j + 1) := by
  obtain ⟨hv, hval⟩ := sub_pos h.valid hy h.pos hys hroom hs
  rw [val_zpos h.pos, val_zpos hys] at hval
  have hnn : 0 ≤ x'.val := by rw [hval]; omega
  have hp := sign_of_val_nonneg hv hnn
  rw [val_zpos hp] at hval
  refine ⟨hv, hp, ?_⟩
  have := h.sum
  rw [Nat.succ_mul]; omega

/-- `x < D`: step 2 is done, `j = A / D`, `x = A % D`. -/
theorem S2.exit {A D j : Nat} {x : MpInt} (h : S2 A D x j) (hlt : x.mag < D) : j = A / D ∧ x.mag = A % D := by
  have hD : 0 < D := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
  have hs := h.sum
  have hq : A / D = j := by
    rw [← hs, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hlt, Nat.zero_add]
  refine ⟨hq.symm, ?_⟩
  rw [← hs, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

/-- Step 2 subtracts at most `A / D` times: the measure `A / D - j` falls. -/
theorem S2.le {A D j : Nat} {x : MpInt} (h : S2 A D x j) (hD : 0 < D) : j ≤ A / D := by
  have hs := h.sum
  rw [← hs, Nat.add_mul_div_right _ _ hD]; exact Nat.le_add_left _ _

/-! ## Step 3.2: the do-while on the stored digit -/

/-- `q = (q - 1) & MP_MASK` on a digit: `q - 1`, or `MP_MASK` from `0`. -/
def dec (q : Nat) : Nat := (q + (radix - 1)) % radix

theorem dec_pos {q : Nat} (h0 : 0 < q) (hq : q < radix) : dec q = q - 1 := by
  unfold dec; rw [radix_eq] at hq ⊢; omega

theorem dec_start {q : Nat} (hq : q < radix) : dec ((q + 1) % radix) = q := by
  unfold dec; rw [radix_eq] at hq ⊢; omega

/-- At the do-body (`cf0`): the stored digit `qv` decrements to the candidate `dec qv`, whose
`fixDown` is `q̂`. -/
structure Fix (p : Nat → Bool) (q0 qv : Nat) : Prop where
  lt : qv < radix
  fix : fixDown p q0 = fixDown p (dec qv)

/-- Entry from step 3.1: `q.dp[k] = (q̂₀ + 1) & MP_MASK` (`x[i] = y[t]` stores `0`, the
same value for `q̂₀ = MP_MASK`). -/
theorem Fix.start (p : Nat → Bool) {q0 : Nat} (hq : q0 < radix) : Fix p q0 ((q0 + 1) % radix) :=
  ⟨Nat.mod_lt _ radix_pos, by rw [dec_start hq]⟩

/-- The test held (`MP_GT`): once more, with the candidate stored. -/
theorem Fix.again {p : Nat → Bool} {q0 qv : Nat} (h : Fix p q0 qv) (ht : p (dec qv) = true) (h0 : 0 < dec qv) :
    Fix p q0 (dec qv) :=
  ⟨Nat.mod_lt _ radix_pos, by rw [h.fix, fixDown_dec ht h0, dec_pos h0 (Nat.mod_lt _ radix_pos)]⟩

/-- The test failed: the candidate is `q̂`. -/
theorem Fix.done {p : Nat → Bool} {q0 qv : Nat} (h : Fix p q0 qv) (ht : p (dec qv) = false) :
    fixDown p q0 = dec qv := by rw [h.fix, fixDown_stop ht]

/-- The do-while's measure: the candidate falls. -/
theorem dec_lt {q : Nat} (h0 : 0 < dec q) (hq : q < radix) : dec (dec q) < dec q := by
  rw [dec_pos h0 (Nat.mod_lt _ radix_pos)]; omega

/-! ## Steps 3.3–3.4: the subtraction and the add-back -/

/-- `x - q̂ y b^k` (`mp_mul_d(&y, q̂, &t1)`, `mp_lshd(&t1, k)`, `mp_sub(&x, &t1, &x)`), as
values: `t1 = q̂ y b^k`, `x' = x - t1`. -/
structure Sub3 (X D q : Nat) (x' : MpInt) : Prop where
  valid : x'.Valid
  val : x'.val = (X : Int) - ((q * D : Nat) : Int)

/-- The add-back (`mp_copy(&y, &t1)`, `mp_lshd(&t1, k)`, `mp_add(&x, &t1, &x)`):
`x'' = x' + y b^k`. -/
theorem Sub3.addBack {X D q : Nat} {x' t x'' : MpInt} (h : Sub3 X D q x') (hneg : x'.sign = Layout.mpNeg)
    (ht : t.Valid) (hts : t.sign = Layout.mpZpos) (htm : t.mag = D) (hroom : max x'.used t.used ≤ x'.alloc)
    (ha : AddPost x' t x' x'') : x''.Valid ∧ x''.val = (X : Int) - ((q * D : Nat) : Int) + (D : Int) := by
  obtain ⟨hv, hval⟩ := add_negpos h.valid ht hneg hts hroom ha
  refine ⟨hv, ?_⟩
  rw [hval, h.val, val_zpos hts, htm]

/-- **One iteration of step 3** on the callees' results: with `x = X` before (`DivInv`'s
remainder at `i`), `q̂` from step 3.2 and `x'` from `mp_sub` (and `x''` from the add-back when
`x' < 0`), the digit the code writes (`q̂`, or `q̂ - 1` after the add-back) and the new `x` are
`knuthQd`, `knuthXn` (`knuth_step`: `X / (B b^k)` and `X % (B b^k)`). -/
theorem step3_keep {X B t k : Nat} {x' : MpInt} (h : Sub3 X (B * radix ^ k) (knuthQhat X B t (t + k + 1)) x')
    (hpos : x'.sign = Layout.mpZpos) :
    knuthQd X B t (t + k + 1) = knuthQhat X B t (t + k + 1) ∧ x'.val = knuthXn X B t (t + k + 1) := by
  have hv := h.val
  rw [val_zpos hpos] at hv
  have hi : t + k + 1 - t - 1 = k := by omega
  have hnn : ¬ ((X : Int) - ((knuthQhat X B t (t + k + 1) * (B * radix ^ (t + k + 1 - t - 1)) : Nat) : Int) < 0) := by
    rw [hi]; omega
  unfold knuthQd knuthXn
  rw [if_neg hnn, if_neg hnn, val_zpos hpos, hv, hi]
  exact ⟨rfl, rfl⟩

theorem step3_back {X B t k : Nat} {x' : MpInt} {v : Int} (h : Sub3 X (B * radix ^ k) (knuthQhat X B t (t + k + 1)) x')
    (hneg : x'.sign = Layout.mpNeg) (hv : v = (X : Int) - ((knuthQhat X B t (t + k + 1) * (B * radix ^ k) : Nat) : Int)
      + ((B * radix ^ k : Nat) : Int)) :
    knuthQd X B t (t + k + 1) = knuthQhat X B t (t + k + 1) - 1 ∧ v = knuthXn X B t (t + k + 1) := by
  have hval := h.val
  have hi : t + k + 1 - t - 1 = k := by omega
  have hlt0 : x'.val < 0 := by
    rw [val_neg hneg]
    have hm : x'.mag ≠ 0 := fun h0 => by
      have := h.valid.zero_pos (used_zero_of_mag h.valid h0); rw [this] at hneg; exact absurd hneg (by decide)
    omega
  have hn : (X : Int) - ((knuthQhat X B t (t + k + 1) * (B * radix ^ (t + k + 1 - t - 1)) : Nat) : Int) < 0 := by
    rw [hi, ← hval]; exact hlt0
  unfold knuthQd knuthXn
  rw [if_pos hn, if_pos hn, hv, hi]
  exact ⟨rfl, rfl⟩

/-- The new remainder is a valid nonnegative integer with magnitude `X % (B b^k)`, and the digit
is `X / (B b^k)`: `DivInv` steps (`DivInv.step`). -/
theorem step3_inv {A B t i X : Nat} {qd : Nat → Nat} {x : MpInt} (hinv : DivInv A B t i X qd)
    (hB : B < radix ^ (t + 1)) (hyt : 2 ^ 26 ≤ natDigit B t) (hti : t + 1 ≤ i) (hx : x.Valid)
    (hval : x.val = knuthXn X B t i) :
    x.sign = Layout.mpZpos ∧ DivInv A B t (i - 1) x.mag (setDigit qd (i - t - 1) (knuthQd X B t i)) := by
  have hBpos : 0 < B := Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.two_pow_pos 26) (radix_pow_pos t))
    (Nat.le_trans (Nat.mul_le_mul_right _ hyt) natDigit_top_le)
  obtain ⟨k, rfl⟩ : ∃ k, i = t + k + 1 := ⟨i - t - 1, by omega⟩
  have hlt := hinv.rem_lt hBpos hti
  rw [show t + k + 1 - t - 1 = k by omega] at hlt ⊢
  obtain ⟨hq, hn⟩ := knuth_step hB hyt hlt
  rw [hn] at hval
  have hp := sign_of_val_nonneg hx (by rw [hval]; exact Int.natCast_nonneg _)
  refine ⟨hp, ?_⟩
  rw [val_zpos hp] at hval
  have hm : x.mag = X % (B * radix ^ k) := by exact_mod_cast hval
  have := hinv.step hti
  rw [show t + k + 1 - t - 1 = k by omega] at this
  rw [hm, hq]; exact this

end Tom.DivStep
