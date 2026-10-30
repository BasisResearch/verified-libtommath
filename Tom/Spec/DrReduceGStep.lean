import Tom.Spec.Reduce
import Tom.Spec.Sub
import Tom.Spec.Grow6Step

/-!
# `mp_dr_reduce` growing `x`: the model steps of its assembly

The loop of `Api/DrReduceG.lean` (`Fn/DrReduceGMainG.lean`) over `Tom.Reduce`'s model: at `top`
the value `xc` with fuel `F` (`DT`: `redLoop`'s target kept), in the digit loop `drRow`'s digits and
carry after `i` steps (`IR`, in the machine's literal store forms), after a pass the value `pv`
(`x->used`, `x->sign` as they were, the digits `drPass`), after `mp_clamp` `PC` (the fold of `xc`),
then the exit (`PC.fin`) or `s_mp_sub` and `goto top` (`PC.sub`). The pass's value lemmas are the
ones of the room contract's proof (`Fn/DrReduceMain.lean`), stated here over the Spec only.
-/

namespace Tom

namespace DrReduceGStep

open MpInt Reduce Mont

theorem eR : radix = 268435456 := rfl

/-! ## The pass's value -/

section value
variable {f : Nat → Nat} {m k u : Nat}

theorem upd_self (f : Nat → Nat) (i : Nat) : upd f i (f i) = f := by
  funext j; unfold upd; split <;> simp_all

/-- Above `x->used ≤ m` a pass changes nothing. -/
theorem drRow_zero (hf : ∀ i, f i < radix) (hz : ∀ j, u ≤ j → f j = 0) (hu : u ≤ m) :
    ∀ i, drRow f m k i = ⟨f, 0⟩
  | 0 => rfl
  | i + 1 => by
    simp only [drRow, drRow_zero hf hz hu i, hz (m + i) (by omega), Nat.mul_zero, cstep, Nat.zero_add,
      Nat.add_zero, Nat.mod_eq_of_lt (hf i), Nat.div_eq_of_lt (hf i), upd_self]

theorem drPass_high (hf : ∀ i, f i < radix) (hz : ∀ j, u ≤ j → f j = 0) : ∀ i, u ≤ i → drPass f m k i = 0 := by
  intro i hi
  unfold drPass
  by_cases h1 : i < m
  · rw [if_pos h1, drRow_zero hf hz (by omega) m]; exact hz i hi
  · rw [if_neg h1]
    by_cases h2 : i = m
    · rw [if_pos h2, drRow_zero hf hz (by omega) m]
    · rw [if_neg h2]

theorem pass_mag (hf : ∀ i, f i < radix) (hz : ∀ j, u ≤ j → f j = 0) (hu : u ≤ 2 * m) :
    natUpTo (drPass f m k) u = drFold m k (natUpTo f u) := by
  have hN1 : natUpTo (drPass f m k) (max u (m + 1)) = natUpTo (drPass f m k) u :=
    natUpTo_zeros _ _ _ (Nat.le_max_left _ _) fun i h1 _ => drPass_high hf hz i h1
  have hN2 : natUpTo (drPass f m k) (max u (m + 1)) = natUpTo (drPass f m k) (m + 1) :=
    natUpTo_zeros _ _ _ (Nat.le_max_right _ _) fun i h1 _ => by
      unfold drPass; rw [if_neg (by omega), if_neg (by omega)]
  have h2m : natUpTo f (2 * m) = natUpTo f u := natUpTo_zeros _ _ _ hu fun i h1 _ => hz i h1
  rw [← hN1, hN2, drPass_val f m k hf, h2m]

/-- The pass's digits: the loop's, `x[m] = mu`, zero on `[m + 1, x->used)` (`MP_ZERO_DIGITS`). -/
theorem pass_digit (hz : ∀ j, u ≤ j → f j = 0) (j : Nat) :
    (if m + 1 ≤ j ∧ j < u then 0 else upd (drRow f m k m).dig m (drRow f m k m).u j) = drPass f m k j := by
  unfold drPass upd
  by_cases h1 : j < m
  · simp only [show ¬ (m + 1 ≤ j ∧ j < u) by omega, show ¬ j = m by omega, h1, if_false, if_true]
  · by_cases h2 : j = m
    · subst h2; simp only [show ¬ (j + 1 ≤ j ∧ j < u) by omega, h1, if_false, if_true]
    · by_cases h3 : m + 1 ≤ j ∧ j < u
      · rw [if_pos h3, if_neg h1, if_neg h2]
      · simp only [h3, h1, h2, if_false]
        rw [drRow_out f m k m j (by omega)]; exact hz j (by omega)

theorem drPass_lt (hf : ∀ i, f i < radix) (hk : k < radix) (i : Nat) : drPass f m k i < radix := by
  have hb := drRow_bound f m k hf hk m
  unfold drPass; split
  · exact hb.1 i
  · split
    · exact hb.2
    · exact radix_pos

/-- The fold does not grow the value (`k < radix ≤ radix^m`). -/
theorem drFold_le (hm : 1 ≤ m) (hk : k < radix) {a0 a : Nat} (ha0 : a0 < radix ^ (2 * m)) (ha : a ≤ a0) :
    drFold m k a ≤ a := by
  have hR : radix ≤ radix ^ m := by
    calc radix = radix ^ 1 := (Nat.pow_one _).symm
      _ ≤ radix ^ m := Nat.pow_le_pow_right radix_pos hm
  exact (drFold_ok m k (radix ^ m - k) a0 (by omega) ha0).le a ha

theorem drFold_zero : drFold m k 0 = 0 := by simp [drFold]

end value

theorem used_le_of_lt {a : MpInt} (ha : a.Valid) {j : Nat} (h : a.mag < radix ^ j) : a.used ≤ j := by
  rcases Nat.eq_zero_or_pos a.used with h0 | h0
  · omega
  · have := MpInt.mag_ge ha h0
    have : radix ^ (a.used - 1) < radix ^ j := Nat.lt_of_le_of_lt this h
    have := (Nat.pow_lt_pow_iff_right (by simp only [radix, Layout.digitBits]; decide)).1 this
    omega

theorem mag_zero_of_used {a : MpInt} (h : a.used = 0) : a.mag = 0 := by
  unfold MpInt.mag; rw [h]; rfl

/-! ## `top` -/

/-- At `top`: the value `xc` with fuel `F` left, the loop's target kept. -/
structure DT (x n : MpInt) (k F : Nat) (xc : MpInt) : Prop where
  valid : xc.Valid
  le : xc.mag ≤ x.mag
  lt : xc.mag < F
  tgt : redLoop (drFold n.used k) n.mag F xc.mag = redLoop (drFold n.used k) n.mag (x.mag + 1) x.mag
  sign : xc.sign = if xc.used = 0 then Layout.mpZpos else x.sign

theorem DT.start {x n : MpInt} {k : Nat} (hx : x.Valid) : DT x n k (x.mag + 1) x :=
  ⟨hx, Nat.le_refl _, Nat.lt_succ_self _, rfl, by
    split
    · exact hx.zero_pos ‹_›
    · rfl⟩

theorem growTo_mag {x : MpInt} {N : Nat} (hx : x.Shape) (hN : x.alloc ≤ N) : (x.growTo N).mag = x.mag := by
  show natUpTo (x.growTo N).digit x.used = natUpTo x.digit x.used
  rw [MpInt.growTo_digit hx hN]

/-- After `mp_grow(x, N)`: the same value in a longer block. -/
theorem DT.grow {x n : MpInt} {k N : Nat} (hx : x.Valid) (hN : x.alloc ≤ N) (h31 : N < 2 ^ 31) :
    DT x n k (x.mag + 1) (x.growTo N) := by
  have e : (x.growTo N).mag = x.mag := growTo_mag hx.toShape hN
  refine ⟨MpInt.growTo_valid hx hN h31, by rw [e]; exact Nat.le_refl _, by rw [e]; omega, by rw [e], ?_⟩
  show x.sign = if x.used = 0 then _ else _
  split
  · exact hx.zero_pos ‹_›
  · rfl

/-! ## The digit loop -/

/-- The digit loop after `i` steps: `drRow`'s digits and carry. -/
structure IR (xc : MpInt) (m k : Nat) (f : Nat → Nat) (i c : Nat) : Prop where
  f : f = (drRow xc.digit m k i).dig
  c : c = (drRow xc.digit m k i).u

theorem IR.start {xc : MpInt} {m k : Nat} : IR xc m k xc.digit 0 0 := ⟨rfl, rfl⟩

/-- One step: `r = x[m + i] k + x[i] + mu`, `x[i] := r & MP_MASK`, `mu := r >> 28`. -/
theorem IR.step {xc : MpInt} {m k i c : Nat} {f : Nat → Nat} (h : IR xc m k f i c) (hi : i < m) :
    IR xc m k (upd f i ((f (m + i) * k + f i + c) % 268435456)) (i + 1) ((f (m + i) * k + f i + c) / 268435456) := by
  obtain ⟨rfl, rfl⟩ := h
  have e : (drRow xc.digit m k i).dig (m + i) * k + (drRow xc.digit m k i).dig i + (drRow xc.digit m k i).u =
      k * xc.digit (m + i) + (drRow xc.digit m k i).u + (drRow xc.digit m k i).dig i := by
    rw [drRow_out _ m k i (m + i) (by omega), Nat.mul_comm]; omega
  constructor
  · simp only [drRow, cstep]; rw [e]; rfl
  · simp only [drRow, cstep]; rw [e]; rfl

theorem IR.dig_lt {xc : MpInt} {m k i c : Nat} {f : Nat → Nat} (h : IR xc m k f i c) (hx : xc.Shape)
    (hk : k < radix) (j : Nat) : f j < 268435456 := by
  rw [h.f]; exact (drRow_bound _ m k hx.digit_lt hk i).1 j

theorem IR.c_lt {xc : MpInt} {m k i c : Nat} {f : Nat → Nat} (h : IR xc m k f i c) (hx : xc.Shape)
    (hk : k < radix) : c < 268435456 := by
  rw [h.c]; exact (drRow_bound _ m k hx.digit_lt hk i).2

/-! ## After a pass -/

/-- The value a pass leaves before `mp_clamp`: `x->used`, `x->sign` as they were, the digits
`drPass` on `al` digits. -/
def pv (xc : MpInt) (al m k : Nat) : MpInt := MpInt.ofDigits xc.used al xc.sign (drPass xc.digit m k)

/-- `x[m] := mu` with no `MP_ZERO_DIGITS` (`x->used ≤ m + 1`). -/
theorem pv_digit_s {xc : MpInt} {al m k : Nat} (hx : xc.Shape) (hu : xc.used ≤ m + 1) (j : Nat) (hj : j < al) :
    (pv xc al m k).digit j = upd (drRow xc.digit m k m).dig m (drRow xc.digit m k m).u j := by
  rw [pv, MpInt.ofDigits_digit, if_pos hj, ← pass_digit hx.high_zero, if_neg (by omega)]

/-- `x[m] := mu`, then `MP_ZERO_DIGITS` on `[m + 1, x->used)`. -/
theorem pv_digit_z {xc : MpInt} {al m k : Nat} (hx : xc.Shape) (j : Nat) (hj : j < al) :
    (pv xc al m k).digit j =
      (if m + 1 ≤ j ∧ j < xc.used then 0 else upd (drRow xc.digit m k m).dig m (drRow xc.digit m k m).u j) := by
  rw [pv, MpInt.ofDigits_digit, if_pos hj, ← pass_digit hx.high_zero]

theorem pv_shape {x n xc : MpInt} {k F al : Nat} (h : DT x n k F xc) (hal : xc.alloc = al) (hk : k < radix) :
    (pv xc al n.used k).Shape where
  len := MpInt.ofDigits_len _ _ _ _
  used_le := by show xc.used ≤ al; rw [← hal]; exact h.valid.used_le
  alloc_lt := by show al < 2 ^ 31; rw [← hal]; exact h.valid.alloc_lt
  digit_lt := fun i => by
    rw [pv, MpInt.ofDigits_digit]; split
    · exact drPass_lt h.valid.digit_lt hk i
    · exact radix_pos
  high_zero := fun i hi => by
    rw [pv, MpInt.ofDigits_digit]; split
    · exact drPass_high h.valid.digit_lt h.valid.high_zero i hi
    · rfl

theorem pv_sign {xc : MpInt} {al m k : Nat} (hx : xc.Valid) :
    (pv xc al m k).sign = Layout.mpZpos ∨ (pv xc al m k).sign = Layout.mpNeg := hx.sign_ok

/-- After `mp_clamp`: valid, the fold of `xc`, the sign rule, `x`'s block. -/
structure PC (x n : MpInt) (k F : Nat) (xc x2 : MpInt) : Prop where
  dt : DT x n k F xc
  valid : x2.Valid
  mag : x2.mag = drFold n.used k xc.mag
  sign : x2.sign = if x2.used = 0 then Layout.mpZpos else x.sign
  alloc : x2.alloc = xc.alloc

theorem PC.of {x n xc x2 : MpInt} {k F al : Nat} (h : DT x n k F xc) (hal : xc.alloc = al)
    (hx : x.mag < radix ^ (2 * n.used)) (hk : k < radix) (hcl : ClampPost (pv xc al n.used k) x2) :
    PC x n k F xc x2 := by
  have hs := pv_shape h hal hk
  have hcs := ClampPost.spec hs (pv_sign h.valid) hcl
  have hz := h.valid.high_zero
  have hu2 : xc.used ≤ 2 * n.used := used_le_of_lt h.valid (Nat.lt_of_le_of_lt h.le hx)
  have hmag : (pv xc al n.used k).mag = drFold n.used k xc.mag := by
    show natUpTo (pv xc al n.used k).digit xc.used = drFold n.used k (natUpTo xc.digit xc.used)
    rw [← pass_mag h.valid.digit_lt hz hu2]
    exact natUpTo_congr _ (fun j hj => by rw [pv, MpInt.ofDigits_digit, if_pos (by have := h.valid.used_le; omega)])
  refine ⟨h, hcs.1, by rw [hcs.2, hmag], ?_, by rw [hcl.alloc, hal]; rfl⟩
  rw [hcl.sign]; split
  · rfl
  · rename_i hne
    have hpos : 0 < x2.mag := by
      have := MpInt.mag_ge hcs.1 (by omega); have := Nat.pow_pos (n := x2.used - 1) radix_pos; omega
    have hu0 : xc.used ≠ 0 := fun h0 => by
      have : xc.mag = 0 := mag_zero_of_used h0
      rw [hcs.2, hmag, this, drFold_zero] at hpos; omega
    show xc.sign = _; rw [h.sign, if_neg hu0]

/-- `|x| < |n|` after a pass: the loop's result. -/
theorem PC.fin {x n xc x2 : MpInt} {k F : Nat} (h : PC x n k F xc x2) (hlt : x2.mag < n.mag) :
    DrReducePost x n k x2 where
  valid := h.valid
  mag := by
    have hF : F = (F - 1) + 1 := by have := h.dt.lt; omega
    rw [← h.dt.tgt, hF, redLoop, if_neg (by rw [← h.mag]; omega), h.mag]
  sign := h.sign

/-- `|x| ≥ |n|`: `s_mp_sub(x, n, x)`'s operand order (`n->used ≤ x->used`). -/
theorem PC.ge {x n xc x2 : MpInt} {k F : Nat} (h : PC x n k F xc x2) (hn : n.Valid) (hge : ¬ x2.mag < n.mag) :
    n.used ≤ x2.used :=
  MpInt.used_le_of_mag_le h.valid.toShape hn (Nat.le_of_not_lt hge)

/-- `|x| ≥ |n|`: `s_mp_sub(x, n, x)` and `goto top` with one fuel less; the value falls. -/
theorem PC.sub {x n xc x2 x3 : MpInt} {k F : Nat} (h : PC x n k F xc x2) (hx : x.mag < radix ^ (2 * n.used))
    (hk : k < radix) (hn : n.Valid) (hnp : 0 < n.mag) (hge : ¬ x2.mag < n.mag)
    (hss : SSubPost x2 n x2 x3) : DT x n k (F - 1) x3 ∧ x3.alloc = xc.alloc ∧ x3.mag < xc.mag := by
  have hs2 := SSubPost.spec h.valid.toShape hn.toShape (Nat.le_of_not_lt hge) h.valid.used_le h.valid.alloc_lt
    h.valid.sign_ok hss
  have hm : 1 ≤ n.used := by
    rcases Nat.eq_zero_or_pos n.used with h0 | h0
    · have := mag_zero_of_used h0; omega
    · exact h0
  have hfold := drFold_le (m := n.used) (k := k) hm hk hx h.dt.le
  have hlt := h.dt.lt
  have hF : F = (F - 1) + 1 := by omega
  have e3 : x3.mag = drFold n.used k xc.mag - n.mag := by rw [hs2.2, h.mag]
  have hge' : n.mag ≤ drFold n.used k xc.mag := by rw [← h.mag]; omega
  have hle := h.dt.le
  refine ⟨⟨hs2.1, by omega, by omega, ?_, ?_⟩, by rw [hss.alloc, h.alloc], by omega⟩
  · rw [← h.dt.tgt, hF, redLoop, if_pos hge', e3, Nat.add_sub_cancel]
  · rw [hss.sign]; split
    · rfl
    · rename_i hne
      have hpos : 0 < x2.used := by
        rcases Nat.eq_zero_or_pos x2.used with h0 | h0
        · have := mag_zero_of_used h0; omega
        · exact h0
      rw [h.sign, if_neg (by omega)]

end DrReduceGStep

end Tom
