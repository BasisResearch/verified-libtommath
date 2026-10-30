import Tom.Spec.KMulStepG
import Tom.Spec.Expt2G
import Tom.Spec.Bits

/-!
# `mp_montgomery_calc_normalization`'s model steps on the growing callees

`Fn/MontNormMain.lean`'s invariant `NI` (the value after `j` passes of `Mont.normLoop`) without
`alloc`: `mp_2expt` (`Expt2Post (expt2In a e) e`) and `mp_mul_2(a, a)` (`Api/Mul2H.lean`'s
value) may re-place `a`, so nothing about its allocation is carried.

* the start: `start2` (`b->used > 1`, `a = 2^normE0 b` by the growing `mp_2expt`), `start1` (`mp_set(a, 1)`);
* one pass: the doubling `NIG.dbl` (`a' = 2 a` as values, valid) to `DB`, then `DB.lt` (`MP_LT`) or
  `DB.ge` (`s_mp_sub(a, b, a)` in place: `|a| ≥ |b|` leaves room);
* the end: `NIG.fin` after `normCnt b` passes is `Mont.NormPost`.

The loop counter `k` of the C (`x = k - 1`) runs from `k0` to `28` with `k0 + normCnt b = 29`
(`k0 = mp_count_bits(b) % 28`, or `1`): `start2_cnt`, `start1_cnt`.
-/

namespace Tom.MontNormGStep

open Tom.Mont

theorem normLoop_succ (b : Nat) : ∀ j x, normLoop b x (j + 1) = normStep b (normLoop b x j)
  | 0, _ => rfl
  | j + 1, x => by
    show normLoop b (normStep b x) (j + 1) = _
    rw [normLoop_succ b j (normStep b x)]; rfl

/-- The value after `j` passes. -/
structure NIG (b ai : MpInt) (j : Nat) : Prop where
  valid : ai.Valid
  mag : ai.mag = normLoop b.mag (2 ^ normE0 b) j
  sign : ai.sign = Layout.mpZpos
  lt : ai.mag < b.mag

/-- After the doubling of pass `j + 1`. -/
structure DB (b a1 : MpInt) (j : Nat) : Prop where
  valid : a1.Valid
  mag : a1.mag = 2 * normLoop b.mag (2 ^ normE0 b) j
  sign : a1.sign = Layout.mpZpos
  lt2 : a1.mag < 2 * b.mag

theorem NIG.used_le {b ai : MpInt} {j : Nat} (h : NIG b ai j) (hb : b.Valid) : ai.used ≤ b.used :=
  MpInt.used_le_of_mag_le hb.toShape h.valid (Nat.le_of_lt h.lt)

/-- `mp_mul_2(a, a)`: valid, twice the value. -/
theorem NIG.dbl {b ai a1 : MpInt} {j : Nat} (h : NIG b ai j) (hv : a1.Valid) (hval : a1.val = 2 * ai.val) :
    DB b a1 j := by
  have hv0 : ai.val = (ai.mag : Int) := by unfold MpInt.val; rw [h.sign]; simp [Layout.mpZpos, Layout.mpNeg]
  rw [hv0] at hval
  have hs : a1.sign = Layout.mpZpos := KMul.sign_of_val hv (n := 2 * ai.mag) (by rw [hval]; push_cast; rfl)
  have hm : a1.mag = 2 * ai.mag := by
    have : a1.val = (a1.mag : Int) := by unfold MpInt.val; rw [hs]; simp [Layout.mpZpos, Layout.mpNeg]
    omega
  exact ⟨hv, by rw [hm, h.mag], hs, by have := h.lt; omega⟩

/-- `MP_LT`: the pass keeps `2 ai`. -/
theorem DB.lt {b a1 : MpInt} {j : Nat} (h : DB b a1 j) (hlt : a1.mag < b.mag) : NIG b a1 (j + 1) :=
  { valid := h.valid, sign := h.sign, lt := hlt
    mag := by rw [normLoop_succ, normStep, if_neg (by have := h.mag; omega), ← h.mag] }

/-- Not `MP_LT`: `b->used ≤ a->used` (`s_mp_sub`'s order). -/
theorem DB.used_ge {b a1 : MpInt} {j : Nat} (h : DB b a1 j) (hb : b.Valid) (hge : b.mag ≤ a1.mag) :
    b.used ≤ a1.used :=
  MpInt.used_le_of_mag_le h.valid.toShape hb hge

/-- Not `MP_LT`: `s_mp_sub(a, b, a)` subtracts `b`. -/
theorem DB.ge {b a1 a2 : MpInt} {j : Nat} (h : DB b a1 j) (hb : b.Valid) (hge : b.mag ≤ a1.mag)
    (hsub : SSubPost a1 b a1 a2) : NIG b a2 (j + 1) := by
  obtain ⟨hv2, hm2⟩ := SSubPost.spec h.valid.toShape hb.toShape hge h.valid.used_le h.valid.alloc_lt
    (Or.inl h.sign) hsub
  exact { valid := hv2, lt := by have := h.lt2; omega
          sign := by rw [hsub.sign, h.sign]; split <;> rfl
          mag := by rw [normLoop_succ, normStep, if_pos (by have := h.mag; omega), hm2, h.mag] }

/-- After `normCnt b` passes. -/
theorem NIG.fin {b a : MpInt} {j : Nat} (h : NIG b a j) (hj : j = normCnt b) : NormPost b a :=
  ⟨h.valid, by rw [h.mag, hj], h.sign⟩

/-- `mp_2expt(a, 28 (b->used - 1) + bits - 1)` with `bits = mp_count_bits(b) % 28`, `b->used > 1`. -/
theorem start2 {a a1 b : MpInt} (hb : b.Valid) (hodd : b.mag % 2 = 1) (h1 : 1 < b.mag) (hu : 1 < b.used)
    (hal : a.alloc < 2 ^ 31) (he : 28 * (b.used - 1) + countBits b % 28 - 1 < 2 ^ 31)
    (h : Expt2Post (expt2In a (28 * (b.used - 1) + countBits b % 28 - 1)) (28 * (b.used - 1) + countBits b % 28 - 1) a1) :
    NIG b a1 0 := by
  have hcs := countBits_spec hb
  have hee : 28 * (b.used - 1) + countBits b % 28 - 1 = normE0 b := by
    simp only [normE0, if_pos hu, hcs, Layout.digitBits, Nat.mul_comm 28]; rfl
  obtain ⟨hv1, hm1, _⟩ := Expt2Post.specG hal he h
  have hE := normE0_lt b hb hodd h1
  exact ⟨hv1, by rw [hm1, hee]; rfl, h.sign, by rw [hm1, hee]; exact hE⟩

theorem start2_cnt {b : MpInt} (hb : b.Valid) (hu : 1 < b.used) : countBits b % 28 + normCnt b = 0 + 29 := by
  have hcs := countBits_spec hb
  have : countBits b % 28 < 28 := Nat.mod_lt _ (by decide)
  simp only [normCnt, if_pos hu, Layout.digitBits]; rw [hcs]; show _ = 29; unfold nbits bitLen at *; omega

/-- `mp_set(a, 1)`, `b->used ≤ 1`. -/
theorem start1 {a a1 b : MpInt} (hb : b.Valid) (hodd : b.mag % 2 = 1) (h1 : 1 < b.mag) (hu : ¬ 1 < b.used)
    (sa : a.Shape) (hal : 0 < a.alloc) (h : SetPost a 1 a1) : NIG b a1 0 := by
  obtain ⟨hv1, hm1, _⟩ := SetPost.spec sa hal (by decide) h
  have hE := normE0_lt b hb hodd h1
  have h0e : normE0 b = 0 := by simp only [normE0, if_neg hu]
  exact ⟨hv1, by rw [hm1, h0e]; rfl, h.sign, by rw [hm1]; rw [h0e] at hE; exact hE⟩

theorem start1_cnt {b : MpInt} (hu : ¬ 1 < b.used) : 1 + normCnt b = 0 + 29 := by
  simp only [normCnt, if_neg hu]; rfl

end Tom.MontNormGStep
