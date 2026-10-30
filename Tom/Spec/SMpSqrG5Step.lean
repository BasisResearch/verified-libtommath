import Tom.Spec.Canon
import Tom.Spec.Mont
import Tom.Spec.MulAlgo
import Tom.Spec.Init

/-!
# `s_mp_sqr`'s loops: the model steps (case cost of H2)

The schoolbook square (`bn_s_mp_sqr.c`) over `t`'s digit function `f` (`N` digits),
`a`'s digits `d` (`u` of them). After the rows `< i` the value of `t` is
`V i = A² + 2·A·T` (`A` the digits below `i`, `T` the digits from `i`); row `i`
adds the diagonal `d i² R^{2i}` and the doubled cross products, then propagates
its carry. The three cuts' value premises (`OH`, `IH`, `PH`) and one lemma per
segment that stores a digit, stated in the forms the rows (`smsqrg.rows.json`) write.
-/

namespace Tom.SqrStepG5

open MpInt
open Mont (upd natUpTo_upd)

/-- `Σ_{lo ≤ j < hi} d j · radix^j`. -/
def rs (d : Nat → Nat) (lo hi : Nat) : Nat := natUpTo (fun j => if lo ≤ j then d j else 0) hi

theorem rs_succ (d : Nat → Nat) (lo hi : Nat) :
    rs d lo (hi + 1) = rs d lo hi + (if lo ≤ hi then radix ^ hi * d hi else 0) := by
  unfold rs; simp only [natUpTo]; split <;> simp

theorem rs_le (d : Nat → Nat) {lo : Nat} : ∀ {hi}, hi ≤ lo → rs d lo hi = 0
  | 0, _ => rfl
  | n + 1, h => by rw [rs_succ, rs_le d (by omega), if_neg (by omega)]

theorem rs_head (d : Nat → Nat) {i : Nat} : ∀ {hi}, i < hi → rs d i hi = radix ^ i * d i + rs d (i + 1) hi
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [rs_succ, rs_succ d (i + 1)]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h' | rfl
    · rw [rs_head d h', if_pos (by omega), if_pos (by omega)]; omega
    · rw [rs_le d (Nat.le_refl _), rs_le d (Nat.le_succ _), if_pos (Nat.le_refl _), if_neg (by omega)]
      omega

theorem rs_zero (d : Nat → Nat) (n : Nat) : rs d 0 n = natUpTo d n :=
  natUpTo_congr n fun j _ => if_pos (Nat.zero_le j)

theorem rs_split (d : Nat → Nat) {i : Nat} : ∀ {u}, i ≤ u → rs d 0 u = rs d 0 i + rs d i u
  | 0, h => by rw [show i = 0 by omega]; rfl
  | n + 1, h => by
    rcases Nat.lt_or_eq_of_le h with h' | rfl
    · rw [rs_succ, rs_succ d i, rs_split d (by omega : i ≤ n), if_pos (Nat.zero_le _), if_pos (by omega)]
      omega
    · rw [rs_le d (Nat.le_refl _)]; rfl

/-- The value after the rows below `i`. -/
def V (d : Nat → Nat) (u i : Nat) : Nat := rs d 0 i * rs d 0 i + 2 * rs d 0 i * rs d i u

/-- Row `i`'s partial value after its diagonal and the cross products below `iy`. -/
def W (d : Nat → Nat) (u i iy : Nat) : Nat :=
  V d u i + radix ^ i * d i * (radix ^ i * d i + 2 * rs d (i + 1) iy)

theorem V_zero (d : Nat → Nat) (u : Nat) : V d u 0 = 0 := by simp [V, rs, natUpTo]

theorem W_start (d : Nat → Nat) (u i : Nat) :
    W d u i (i + 1) = V d u i + radix ^ (2 * i) * (d i * d i) := by
  rw [W, rs_le d (Nat.le_refl _), show 2 * i = i + i by omega, Nat.pow_add]; grind

theorem W_step (d : Nat → Nat) (u i iy : Nat) (h : i + 1 ≤ iy) :
    W d u i (iy + 1) = W d u i iy + 2 * (d iy * d i) * radix ^ (i + iy) := by
  simp only [W, rs_succ d (i + 1) iy, if_pos h, Nat.pow_add]; grind

theorem W_end (d : Nat → Nat) {u i : Nat} (h : i < u) : W d u i u = V d u (i + 1) := by
  simp only [W, V, rs_succ d 0 i, if_pos (Nat.zero_le i), rs_head d h]; grind

theorem V_le (d : Nat → Nat) {u i : Nat} (h : i ≤ u) : V d u i ≤ natUpTo d u * natUpTo d u := by
  rw [← rs_zero, rs_split d h]
  unfold V
  generalize rs d 0 i = A; generalize rs d i u = T
  have : (A + T) * (A + T) = A * A + 2 * A * T + T * T := by grind
  omega

/-- **A digit store with carry out**: `t[k] := (t[k] + y) mod R`, carry `(t[k] + y) / R`. -/
theorem store (f : Nat → Nat) {k N : Nat} (hk : k < N) (y : Nat) :
    natUpTo (upd f k ((f k + y) % radix)) N + (f k + y) / radix * radix ^ (k + 1) =
      natUpTo f N + radix ^ k * y := by
  have h1 := natUpTo_upd f k ((f k + y) % radix) N hk
  have h2 : radix ^ k * ((f k + y) % radix) + radix ^ k * (radix * ((f k + y) / radix)) =
      radix ^ k * f k + radix ^ k * y := by rw [← Nat.mul_add, Nat.mod_add_div, Nat.mul_add]
  have h3 : (f k + y) / radix * radix ^ (k + 1) = radix ^ k * (radix * ((f k + y) / radix)) := by
    rw [Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc]
  rw [h3]
  generalize natUpTo (upd f k ((f k + y) % radix)) N = X at *
  generalize radix ^ k * (radix * ((f k + y) / radix)) = Y at *
  generalize radix ^ k * ((f k + y) % radix) = Z at *
  omega

theorem upd_lt {f : Nat → Nat} {N k v : Nat} (hf : ∀ j, j < N → f j < radix) (hv : v < radix) :
    ∀ j, j < N → upd f k v j < radix := fun j hj => by
  unfold upd; split
  · exact hv
  · exact hf j hj

theorem natUpTo_mono (f : Nat → Nat) (n : Nat) : ∀ k, natUpTo f n ≤ natUpTo f (n + k)
  | 0 => Nat.le_refl _
  | k + 1 => Nat.le_trans (natUpTo_mono f n k) (by rw [← Nat.add_assoc]; simp only [natUpTo]; omega)

/-- Digits of a value below `R^m` are zero from `m`. -/
theorem high_zero {f : Nat → Nat} {N m : Nat} (h : natUpTo f N < radix ^ m) :
    ∀ j, m ≤ j → j < N → f j = 0 := fun j h1 h2 => by
  refine Classical.byContradiction fun hj => ?_
  have e1 := natUpTo_ge_top f j hj
  have e2 := natUpTo_mono f (j + 1) (N - (j + 1))
  rw [show j + 1 + (N - (j + 1)) = N by omega] at e2
  have e3 := Nat.pow_le_pow_right radix_pos h1
  omega

/-! ## The cuts' value premises -/

/-- At the outer head (`ix`): rows below `ix` added. -/
structure OH (d : Nat → Nat) (u N : Nat) (f : Nat → Nat) (ix : Nat) : Prop where
  dig : ∀ j, j < N → f j < radix
  val : natUpTo f N = V d u ix

/-- At the inner head (`ix`, `iy`, carry `c` into digit `ix + iy`). -/
structure IH (d : Nat → Nat) (u N : Nat) (f : Nat → Nat) (ix iy c : Nat) : Prop where
  dig : ∀ j, j < N → f j < radix
  val : natUpTo f N + c * radix ^ (ix + iy) = W d u ix iy
  c_lt : c < 2 * radix

/-- In the carry loop (row `ix` done but for the carry `c` into digit `k`). -/
structure PH (d : Nat → Nat) (u N : Nat) (f : Nat → Nat) (ix k c : Nat) : Prop where
  dig : ∀ j, j < N → f j < radix
  val : natUpTo f N + c * radix ^ k = V d u (ix + 1)
  c_lt : c < 2 * radix

section
variable {d : Nat → Nat} {u N : Nat} {f : Nat → Nat}

theorem eR : radix = 268435456 := rfl

theorem OH.zero : OH d u N (MpInt.zeroN N).digit 0 :=
  { dig := fun j _ => by rw [MpInt.zeroN_digit]; exact radix_pos
    val := by rw [V_zero, natUpTo_congr N (e := fun _ => 0) (fun j _ => MpInt.zeroN_digit N j), natUpTo_zero_fun] }

/-- The diagonal (`ms`). -/
theorem OH.ms {ix : Nat} (h : OH d u N f ix) (hd : ∀ j, d j < radix) (hk : 2 * ix < N) :
    IH d u N (upd f (2 * ix) ((f (2 * ix) + d ix * d ix) % 268435456)) ix (ix + 1)
      ((f (2 * ix) + d ix * d ix) / 268435456) :=
  { dig := upd_lt h.dig (Nat.mod_lt _ (by decide))
    val := by
      have := store f hk (d ix * d ix)
      rw [show ix + (ix + 1) = 2 * ix + 1 by omega, W_start, ← h.val]
      rw [eR] at this ⊢; omega
    c_lt := by
      have e1 := hd ix; have e2 := h.dig (2 * ix) hk
      have e3 : d ix * d ix ≤ 268435455 * 268435455 := Nat.mul_le_mul (by rw [eR] at e1; omega) (by rw [eR] at e1; omega)
      rw [eR] at e2 ⊢; exact (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega) }

/-- One cross product (`il`). -/
theorem IH.step {ix iy c : Nat} (h : IH d u N f ix iy c) (hd : ∀ j, d j < radix) (h1 : ix < iy)
    (hk : ix + iy < N) :
    IH d u N (upd f (ix + iy) ((2 * (d iy * d ix) + f (ix + iy) + c) % 268435456)) ix (iy + 1)
      ((2 * (d iy * d ix) + f (ix + iy) + c) / 268435456) :=
  { dig := upd_lt h.dig (Nat.mod_lt _ (by decide))
    val := by
      have := store f hk (2 * (d iy * d ix) + c)
      rw [show 2 * (d iy * d ix) + f (ix + iy) + c = f (ix + iy) + (2 * (d iy * d ix) + c) by omega,
        show ix + (iy + 1) = ix + iy + 1 by omega, W_step d u ix iy (by omega), ← h.val]
      rw [eR] at this ⊢; rw [Nat.mul_add] at this
      have : 268435456 ^ (ix + iy) * (2 * (d iy * d ix)) = 2 * (d iy * d ix) * 268435456 ^ (ix + iy) :=
        Nat.mul_comm _ _
      have : 268435456 ^ (ix + iy) * c = c * 268435456 ^ (ix + iy) := Nat.mul_comm _ _
      omega
    c_lt := by
      have e1 := hd ix; have e1' := hd iy; have e2 := h.dig (ix + iy) hk; have e4 := h.c_lt
      rw [eR] at e1 e1' e2 e4 ⊢
      have e3 : d iy * d ix ≤ 268435455 * 268435455 := Nat.mul_le_mul (by omega) (by omega)
      exact (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega) }

/-- The row's last product done (`ix`, `sk`). -/
theorem IH.exit {ix iy c k : Nat} (h : IH d u N f ix iy c) (hiy : iy = u) (hix : ix < u) (hk : k = ix + iy) :
    PH d u N f ix k c :=
  { dig := h.dig, c_lt := h.c_lt, val := by subst hiy hk; rw [h.val, W_end d hix] }

/-- A carry is left only below `2u`. -/
theorem PH.k_lt {ix k c : Nat} (h : PH d u N f ix k c) (hd : ∀ j, d j < radix) (hc : c ≠ 0) (hix : ix < u) :
    k < 2 * u := by
  have e1 := V_le d (show ix + 1 ≤ u by omega)
  have e2 := natUpTo_lt d hd u
  have e3 : natUpTo d u * natUpTo d u < radix ^ u * radix ^ u :=
    Nat.mul_lt_mul_of_lt_of_le e2 (Nat.le_of_lt e2) (Nat.pos_of_ne_zero (by omega))
  rw [← Nat.pow_add, ← Nat.two_mul] at e3
  have e4 : radix ^ k ≤ c * radix ^ k := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hc)
  have e5 := h.val
  have : radix ^ k < radix ^ (2 * u) := by omega
  exact (Nat.pow_lt_pow_iff_right (by decide)).1 this

/-- One carry step (`pl`, `pe`, `pd`). -/
theorem PH.carry {ix k c : Nat} (h : PH d u N f ix k c) (hk : k < N) :
    PH d u N (upd f k ((f k + c) % 268435456)) ix (k + 1) ((f k + c) / 268435456) :=
  { dig := upd_lt h.dig (Nat.mod_lt _ (by decide))
    val := by
      have := store f hk c
      rw [← h.val]; rw [eR] at this ⊢
      have : 268435456 ^ k * c = c * 268435456 ^ k := Nat.mul_comm _ _
      omega
    c_lt := by
      have e2 := h.dig k hk; have e4 := h.c_lt
      rw [eR] at e2 e4 ⊢
      exact (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega) }

theorem OH.cast {i j : Nat} (h : OH d u N f i) (e : i = j) : OH d u N f j := e ▸ h

/-- No carry left: the next row. -/
theorem PH.done {ix k c : Nat} (h : PH d u N f ix k c) (hc : c = 0) : OH d u N f (ix + 1) :=
  { dig := h.dig, val := by have := h.val; subst hc; simpa using this }

end

/-! ## The result -/

/-- `t` as `mp_clamp` is handed it: `used = 2u + 1`, the digits `f`. -/
def tOf (u N : Nat) (f : Nat → Nat) : MpInt := MpInt.ofDigits (2 * u + 1) N Layout.mpZpos f

theorem tOf_shape {a : MpInt} {N : Nat} {f : Nat → Nat} (ha : a.Shape) (h : OH a.digit a.used N f a.used)
    (hN : 2 * a.used + 1 ≤ N) (hN' : N < 2 ^ 31) : (tOf a.used N f).Shape := by
  have hv : natUpTo f N < radix ^ (2 * a.used) := by
    rw [h.val]; have := V_le a.digit (Nat.le_refl a.used); have e2 := natUpTo_lt a.digit ha.digit_lt a.used
    rw [Nat.two_mul, Nat.pow_add]
    exact Nat.lt_of_le_of_lt this (Nat.mul_lt_mul_of_lt_of_le e2 (Nat.le_of_lt e2) (Nat.pos_of_ne_zero (by
      intro e; rw [e] at e2; omega)))
  exact ofDigits_shape hN hN' h.dig fun j h1 h2 => high_zero hv j (by omega) h2

/-- **The square**: after the last row and `mp_clamp`. -/
theorem sqr_fin {a t' : MpInt} {N : Nat} {f : Nat → Nat} (ha : a.Shape) (h : OH a.digit a.used N f a.used)
    (hN : 2 * a.used + 1 ≤ N) (hN' : N < 2 ^ 31) (hc : ClampPost (tOf a.used N f) t') :
    SqrPost a t' ∧ t'.alloc = N := by
  have hs := tOf_shape ha h hN hN'
  obtain ⟨hv, hm⟩ := hc.spec hs (Or.inl rfl)
  have hmag : (tOf a.used N f).mag = a.mag * a.mag := by
    show natUpTo (tOf a.used N f).digit (2 * a.used + 1) = _
    rw [natUpTo_congr (2 * a.used + 1) (e := f) (fun j hj => by
        show (MpInt.ofDigits _ N _ f).digit j = f j; rw [MpInt.ofDigits_digit, if_pos (by omega)])]
    have hv' : natUpTo f N < radix ^ (2 * a.used) := by
      rw [h.val]; have := V_le a.digit (Nat.le_refl a.used); have e2 := natUpTo_lt a.digit ha.digit_lt a.used
      rw [Nat.two_mul, Nat.pow_add]
      exact Nat.lt_of_le_of_lt this (Nat.mul_lt_mul_of_lt_of_le e2 (Nat.le_of_lt e2) (Nat.pos_of_ne_zero (by
        intro e; rw [e] at e2; omega)))
    rw [← natUpTo_zeros f (2 * a.used + 1) N hN (fun j h1 h2 => high_zero hv' j (by omega) h2), h.val]
    have := V_le a.digit (Nat.le_refl a.used)
    simp only [V, rs_le a.digit (Nat.le_refl a.used), Nat.mul_zero, Nat.add_zero, rs_zero]; rfl
  refine ⟨⟨hv, ?_⟩, by rw [hc.alloc]; rfl⟩
  have hsg : t'.sign = Layout.mpZpos := by rw [hc.sign]; split <;> rfl
  have e1 : t'.val = (t'.mag : Int) := by simp [MpInt.val, hsg, Layout.mpZpos, Layout.mpNeg]
  rw [e1, hm, hmag]
  unfold MpInt.val; split
  · rw [Int.neg_mul_neg]; push_cast; rfl
  · push_cast; rfl

end Tom.SqrStepG5
