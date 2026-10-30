import Tom.Spec.MpDivStep
import Tom.Spec.Grow6Step
import Tom.Spec.Bits
import Tom.Spec.DigitShift

/-!
# `mp_div`'s cuts as model quantities

The value premises of the cuts of `experiments/asm/mdiv.asm.json` (`Fn/MpDivMainG.lean`) and
the steps between them, over `Tom/Spec/DivKnuth.lean` and `Tom/Spec/MpDivStep.lean`:

* `Half a X nm`: an operand after `mp_init_copy`, `sign := MP_ZPOS` and `mp_mul_2d(x, nm, x)`
  (`half_copy`, `Half.mul2d`); `Norm B t`: the divisor's normalisation (`norm_of`);
* `YB Y B t`: `y` during step 3 (after `mp_rshd`); `XI A B t i X qf`: `x` and `q`'s digits
  before iteration `i` (`DivInv`); the step-2 exits (`exit_O`, `exit_Z`), the skip (`XI.skip`);
* step 3.1/3.2: the stored candidate (`Fix`), `t1 = q * Y2` and `t2 = X3` (`TC`), the test;
* step 3.3/3.4 (`Sub3`) and the next invariant (`XI.next_keep`, `XI.next_back`);
* the end: the quotient's digits (`quot_shape`) and the signs.
-/

namespace Tom.DivStep

open MpInt

/-! ## The operands after the normalisation -/

/-- One normalised operand: `x` (or `y`) after `mp_mul_2d(x, nm, x)` or the copy when `nm = 0`. -/
structure Half (a X : MpInt) (nm : Nat) : Prop where
  valid : X.Valid
  mag : X.mag = a.mag * 2 ^ nm
  sign : X.sign = Layout.mpZpos
  used : X.used ≤ a.used + 1

/-- `mp_init_copy(&x, a)` then `x.sign := MP_ZPOS`: the copy, `nm = 0`. -/
theorem half_copy {a X0 : MpInt} (ha : a.Valid) (hc : CopyPost a (MpInt.zeroN (initPrec a.used)) X0) :
    Half a { X0 with sign := 0 } 0 ∧ X0.alloc = initPrec a.used ∧ X0.used = a.used := by
  have hn : initPrec a.used < 2 ^ 31 := by
    have := ha.used_le; have := ha.alloc_lt; unfold initPrec; rw [minPrec_eq]; omega
  have hz := MpInt.zeroN_valid hn
  have ⟨hv, hm, _⟩ := hc.spec ha hz.toShape (Nat.le_max_right _ _)
  refine ⟨⟨{ hv.toShape with top := hv.top, sign_ok := Or.inl rfl, zero_pos := fun _ => rfl }, ?_, rfl, ?_⟩,
    hc.alloc, hc.used⟩
  · show X0.mag = _; rw [hm, Nat.pow_zero, Nat.mul_one]
  · show X0.used ≤ _; rw [hc.used]; omega

/-- `mp_count_bits` of the copy is `b`'s. -/
theorem countBits_copy {b Y0 : MpInt} (hc : CopyPost b (MpInt.zeroN (initPrec b.used)) Y0) :
    countBits { Y0 with sign := 0 } = countBits b := by
  unfold countBits
  simp only [hc.used]
  split
  · rfl
  · show _ + bitLen (Y0.digit _) = _
    rw [hc.digit, if_pos (by omega)]

theorem Half.shape {a X : MpInt} {nm : Nat} (h : Half a X nm) : X.Shape := h.valid.toShape

/-- `mp_mul_2d(x, nm, x)` of the copy (`nm < 28`). -/
theorem Half.mul2d {a Xs X1 : MpInt} {nm : Nat} (h : Half a Xs 0) (hnm : nm < 28) (hu : Xs.used = a.used)
    (h31 : a.used + 2 < 2 ^ 31) (hp : Mul2dPost Xs nm (mul2dIn Xs nm) X1) : Half a X1 nm ∧ Xs.used + 1 ≤ X1.alloc := by
  have hg := mul2dIn_grown h.shape (b := nm) (by rw [show nm / 28 = 0 by omega]; omega)
  have hroom := mul2dIn_room Xs nm
  obtain ⟨hv, hm, _⟩ := Mul2dPost.spec h.valid hroom hg.shape.alloc_lt hp
  have hd : nm / Layout.digitBits = 0 := by simp only [Layout.digitBits]; omega
  refine ⟨⟨hv, by rw [hm, h.mag, Nat.pow_zero, Nat.mul_one], ?_, ?_⟩, ?_⟩
  · have hs := hp.sign; split at hs
    · exact hs
    · rw [hs]; exact h.sign
  · have := hp.used; have := clampUsed_le (mul2dDigit Xs nm) (Xs.used + nm / Layout.digitBits + 1)
    rw [hd] at *; omega
  · rw [hp.alloc]; have := hroom; simp only [Layout.digitBits] at hd this; omega

/-- The divisor's normalisation: `B` has `t + 1` digits, the top one at least `2^26`. -/
structure Norm (B t : Nat) : Prop where
  lo : radix ^ t ≤ B
  hi : B < radix ^ (t + 1)
  top : 2 ^ 26 ≤ natDigit B t

/-- The normalisation `nm = divNorm (mp_count_bits(b))` puts `y`'s top digit in `[2^26, 2^27)`. -/
theorem norm_of {b Y : MpInt} (hb : b.Valid) (hb0 : 0 < b.used) (h : Half b Y (divNorm (countBits b))) :
    Norm (b.mag * 2 ^ divNorm (countBits b)) (Y.used - 1) ∧ 0 < Y.used := by
  have hbm : 0 < b.mag := Nat.lt_of_lt_of_le (radix_pow_pos _) (MpInt.mag_ge hb hb0)
  have hcb : countBits b = bitLen b.mag := countBits_spec hb
  have hY0 : 0 < Y.used := by
    rcases Nat.eq_zero_or_pos Y.used with h0 | h0
    · have := h.mag; rw [MpInt.mag_used_zero h0] at this
      have := Nat.mul_pos hbm (Nat.two_pow_pos (divNorm (countBits b))); omega
    · exact h0
  have hlo := MpInt.mag_ge h.valid hY0
  have hhi := MpInt.mag_lt h.shape
  rw [h.mag] at hlo hhi
  have hb1 : 1 ≤ countBits b := by
    rw [hcb]; unfold bitLen; rw [if_neg (by omega)]; omega
  have e1 : b.mag < 2 ^ countBits b := by rw [hcb]; exact lt_two_pow_bitLen _
  have e2 : 2 ^ (countBits b - 1) ≤ b.mag := by rw [hcb]; exact two_pow_bitLen_le (by omega)
  have ht := divNorm_top hb1 e1 e2 hlo (by rw [show Y.used - 1 + 1 = Y.used by omega]; exact hhi)
  exact ⟨⟨hlo, by rw [show Y.used - 1 + 1 = Y.used by omega]; exact hhi, ht.1⟩, hY0⟩

/-- `|b| ≤ |a|` after the normalisation: `y.used ≤ x.used`. -/
theorem used_le_of {X Y : MpInt} (hx : X.Valid) (hy : Y.Valid) (hle : Y.mag ≤ X.mag) : Y.used ≤ X.used := by
  rcases Nat.lt_or_ge X.used Y.used with h | h
  · have h1 := MpInt.mag_lt hx.toShape
    have h2 := MpInt.mag_ge hy (by omega)
    have : radix ^ X.used ≤ radix ^ (Y.used - 1) := Nat.pow_le_pow_right radix_pos (by omega)
    omega
  · exact h

/-! ## `y` shifted for step 2 and back -/

/-- What a growing `mp_lshd(&y, k)` leaves. -/
structure LshdR (Y Y2 : MpInt) (k : Nat) : Prop where
  valid : Y2.Valid
  mag : Y2.mag = Y.mag * radix ^ k
  used : Y2.used = Y.used + k
  sign : Y2.sign = Y.sign
  alloc : Y.alloc ≤ Y2.alloc

/-- `mp_lshd(&y, k)` (growing): `y b^k`, `used + k` digits. -/
theorem lshd_y {Y Y2 : MpInt} {k : Nat} (hy : Y.Valid) (hy0 : 0 < Y.used) (h31 : Y.used + k < 2 ^ 31)
    (h : LshdPost (lshdIn Y k) k Y2) : LshdR Y Y2 k := by
  have hg := lshdIn_grown hy.toShape h31
  have hv : (lshdIn Y k).Valid :=
    { hg.shape with top := fun h0 => by rw [hg.digit, hg.used]; exact hy.top (by rw [hg.used] at h0; exact h0)
                    sign_ok := by rw [hg.sign]; exact hy.sign_ok
                    zero_pos := fun h0 => by rw [hg.sign]; exact hy.zero_pos (by rw [hg.used] at h0; exact h0) }
  have hmag : (lshdIn Y k).mag = Y.mag := by unfold MpInt.mag; rw [hg.digit, hg.used]
  by_cases hk : k = 0
  · subst hk
    have e := h.noop (.inl rfl)
    refine ⟨e ▸ hv, by rw [e, hmag]; simp, by rw [e, hg.used]; simp, by rw [e, hg.sign], by rw [e]; exact hg.alloc⟩
  · have hr := lshdIn_room Y (k := k) (by omega) hy0
    obtain ⟨hv2, hm2⟩ := LshdPost.spec hv hr h
    have hs := h.shift (by omega) (by rw [hg.used]; exact hy0)
    exact ⟨hv2, by rw [hm2, hmag], by rw [hs.used, hg.used], by rw [hs.sign, hg.sign], by rw [hs.alloc]; exact hg.alloc⟩

/-- What `mp_rshd(&y, n - t)` leaves of the shifted divisor. -/
structure RshdR (Y2 Y3 : MpInt) (B t : Nat) : Prop where
  valid : Y3.Valid
  mag : Y3.mag = B
  used : Y3.used = t + 1
  sign : Y3.sign = Y2.sign
  alloc : Y3.alloc = Y2.alloc

/-- `mp_rshd(&y, k)` after step 2: `y` back. -/
theorem rshd_y {Y2 Y3 : MpInt} {B k t : Nat} (hv : Y2.Valid) (hm : Y2.mag = B * radix ^ k) (hu : Y2.used = t + 1 + k)
    (h : RshdPost Y2 k Y3) : RshdR Y2 Y3 B t := by
  obtain ⟨hv3, hm3⟩ := RshdPost.spec hv h
  rw [hm, Nat.mul_div_cancel _ (radix_pow_pos k)] at hm3
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · have e := h.noop h0; subst e; subst h0; exact ⟨hv3, hm3, by omega, rfl, rfl⟩
  · have hs := h.shift h0 (by omega)
    exact ⟨hv3, hm3, by rw [hs.used, hu]; omega, hs.sign, hs.alloc⟩

/-! ## Step 2's exits: the invariant of step 3 -/

theorem _root_.Tom.DivInv.congr {A B t i x : Nat} {qd qd' : Nat → Nat} (h : DivInv A B t i x qd) (hq : ∀ j, qd j = qd' j) :
    DivInv A B t i x qd' :=
  ⟨h.rem, fun k hk => (hq k).symm.trans (h.done k hk), fun k hk => (hq k).symm.trans (h.todo k hk)⟩

theorem _root_.Tom.DivInv.lt {A B t i x : Nat} {qd : Nat → Nat} (h : DivInv A B t i x qd) (j : Nat) : qd j < radix := by
  rcases Nat.lt_or_ge j (i - t) with hj | hj
  · rw [h.todo j hj]; exact radix_pos
  · rw [h.done j hj]; exact natDigit_lt _ _

/-- `y` during step 3: `B`, `t + 1` digits, normalised. -/
structure YB (Y : MpInt) (B t : Nat) : Prop where
  valid : Y.Valid
  sign : Y.sign = Layout.mpZpos
  mag : Y.mag = B
  used : Y.used = t + 1
  norm : Norm B t

theorem YB.digit {Y : MpInt} {B t : Nat} (h : YB Y B t) (j : Nat) : Y.digit j = natDigit B j := by
  rw [h.valid.toShape.digit_eq, h.mag]

/-- `x` and `q`'s digits before iteration `i` of step 3 (`x.dp[i]` readable). -/
structure XI (A B t i : Nat) (X : MpInt) (qf : Nat → Nat) : Prop where
  valid : X.Valid
  sign : X.sign = Layout.mpZpos
  room : i + 1 ≤ X.alloc
  inv : DivInv A B t i X.mag qf

theorem XI.cast {A B t i i' : Nat} {X : MpInt} {qf : Nat → Nat} (h : XI A B t i X qf) (e : i = i') : XI A B t i' X qf :=
  e ▸ h

theorem XI.digit {A B t i : Nat} {X : MpInt} {qf : Nat → Nat} (h : XI A B t i X qf) (j : Nat) :
    X.digit j = natDigit X.mag j := h.valid.toShape.digit_eq j

/-- Step 2 done, `x < y b^(n-t)` with `t < n`: the invariant at `i = n`. -/
theorem exit_O {A B ux uy j : Nat} {X : MpInt} {qf : Nat → Nat} (h : S2 A (B * radix ^ (ux - uy)) X j)
    (hlt : X.mag < B * radix ^ (ux - uy)) (hN : Norm B (uy - 1)) (hA : A < radix ^ ux) (hu : 0 < uy) (huu : uy < ux)
    (hxa : ux ≤ X.alloc) (hqf : ∀ i, qf i = if i = ux - uy then j else 0) :
    XI A B (uy - 1) (ux - uy - 1 + (uy - 1) + 1) X qf := by
  obtain ⟨hj, hx⟩ := h.exit hlt
  have e1 : ux - uy - 1 + (uy - 1) + 1 = ux - 1 := by omega
  rw [e1]
  have hd := DivInv.init (A := A) (B := B) (n := ux - 1) (t := uy - 1) (by rw [show ux - 1 + 1 = ux by omega]; exact hA)
    hN.lo (by omega) (by
      rw [show ux - 1 - (uy - 1) = ux - uy by omega]
      exact Nat.lt_of_lt_of_le (step2_lt (n := ux - 1) (by rw [show ux - 1 + 1 = ux by omega]; exact hA) hN.top (by omega)
        |> fun h4 => by rw [show ux - 1 - (uy - 1) = ux - uy by omega] at h4; exact h4) (by decide))
  rw [show ux - 1 - (uy - 1) = ux - uy by omega] at hd
  refine ⟨h.valid, h.pos, by omega, ?_⟩
  rw [hx]; refine hd.congr fun i => ?_
  rw [hqf, hj]

/-- Step 2 done with `n = t` (`x.used = y.used`): the invariant at `i = t`, the loop not run. -/
theorem exit_Z {A B ux j : Nat} {X : MpInt} {qf : Nat → Nat} (h : S2 A (B * radix ^ (ux - ux)) X j)
    (hlt : X.mag < B * radix ^ (ux - ux)) (hN : Norm B (ux - 1)) (hA : A < radix ^ ux) (hu : 0 < ux)
    (hqf : ∀ i, qf i = if i = ux - ux then j else 0) : DivInv A B (ux - 1) (ux - 1) X.mag qf := by
  obtain ⟨hj, hx⟩ := h.exit hlt
  have hd := DivInv.init (A := A) (B := B) (n := ux - 1) (t := ux - 1) (by rw [show ux - 1 + 1 = ux by omega]; exact hA)
    hN.lo (Nat.le_refl _) (by
      have h4 := step2_lt (n := ux - 1) (t := ux - 1) (B := B) (by rw [show ux - 1 + 1 = ux by omega]; exact hA) hN.top (Nat.le_refl _)
      exact Nat.lt_of_lt_of_le h4 (by decide))
  simp only [Nat.sub_self] at hd hx hj hqf
  rw [hx]; refine hd.congr fun i => ?_
  rw [hqf, hj]

/-- Step 3 skips `i > x.used`: digit `k` stays `0`, `x` stays. -/
theorem XI.skip {A B t k : Nat} {X : MpInt} {qf : Nat → Nat} (h : XI A B t (k + t + 1) X qf) (hB : radix ^ t ≤ B)
    (hu : X.used < k + t + 1) : XI A B t (k + t) X qf := by
  have hd := h.inv.step (by omega)
  rw [show k + t + 1 - 1 = k + t by omega, show k + t + 1 - t - 1 = k by omega] at hd
  have hx : X.mag < radix ^ (t + k) :=
    Nat.lt_of_lt_of_le (MpInt.mag_lt h.valid.toShape) (Nat.pow_le_pow_right radix_pos (by omega))
  obtain ⟨h0, h1⟩ := knuth_skip hB hx
  rw [h0, h1, setDigit_self (h.inv.todo k (by omega))] at hd
  exact ⟨h.valid, h.sign, by have := h.room; omega, hd⟩

/-- The two temporaries `t1`, `t2` between iterations. -/
structure TT (T1 T2 : MpInt) : Prop where
  s1 : T1.Shape
  a1 : 3 ≤ T1.alloc
  s2 : T2.Shape
  a2 : 3 ≤ T2.alloc
  u2 : T2.used ≤ 3

theorem TT.zero : TT (MpInt.zeroN defPrec) (MpInt.zeroN defPrec) :=
  ⟨(MpInt.zeroN_valid (by decide)).toShape, by decide, (MpInt.zeroN_valid (by decide)).toShape, by decide, by decide⟩

/-! ## Step 3.1–3.2: the candidate -/

/-- The three-digit test and the estimate of iteration `i`. -/
abbrev kP (B t x i : Nat) : Nat → Bool := knuthTest (knuthY2 B t) (knuthX3 x i)
abbrev kQ0 (B t x i : Nat) : Nat := knuthEst (natDigit x i) (natDigit x (i - 1)) (natDigit B t)

/-- 3.1, `x[i] = y[t]`: the stored `(MP_MASK + 1) & MP_MASK = 0`. -/
theorem fix_eq {B t x i : Nat} (he : natDigit x i = natDigit B t) : Fix (kP B t x i) (kQ0 B t x i) 0 := by
  have := Fix.start (kP B t x i) (q0 := radix - 1) (by have := radix_pos; omega)
  rw [show radix - 1 + 1 = radix by have := radix_pos; omega, Nat.mod_self] at this
  simp only [kQ0, knuthEst, he, if_true]; exact this

/-- 3.1, `x[i] ≠ y[t]`, `w = (x[i] b + x[i-1]) / y[t] < b`: the stored `(w + 1) & MP_MASK`. -/
theorem fix_lt {B t x i w : Nat} (hne : natDigit x i ≠ natDigit B t)
    (hw : w = (natDigit x i * 268435456 + natDigit x (i - 1)) / natDigit B t) (hlt : w < 268435456) :
    Fix (kP B t x i) (kQ0 B t x i) ((w + 1) % 268435456) := by
  have h := Fix.start (kP B t x i) (q0 := w) (by rw [radix_eq]; exact hlt)
  have e : kQ0 B t x i = w := by
    simp only [kQ0, knuthEst, hne, if_false, radix_eq]; rw [← hw]; exact Nat.min_eq_left (by omega)
  rw [e]; rw [radix_eq] at h; exact h

/-- 3.1, `w ≥ b`: clipped to `MP_MASK`, the stored `0`. -/
theorem fix_ge {B t x i w : Nat} (hne : natDigit x i ≠ natDigit B t)
    (hw : w = (natDigit x i * 268435456 + natDigit x (i - 1)) / natDigit B t) (hge : 268435456 ≤ w) :
    Fix (kP B t x i) (kQ0 B t x i) 0 := by
  have h := Fix.start (kP B t x i) (q0 := radix - 1) (by have := radix_pos; omega)
  rw [show radix - 1 + 1 = radix by have := radix_pos; omega, Nat.mod_self] at h
  have e : kQ0 B t x i = radix - 1 := by
    simp only [kQ0, knuthEst, hne, if_false, radix_eq]; rw [← hw]; exact Nat.min_eq_right (by omega)
  rw [e]; exact h

/-- At the test (`cdc`): the stored candidate `c`, whose `fixDown` is `q̂`. -/
structure FixT (p : Nat → Bool) (q0 c : Nat) : Prop where
  lt : c < radix
  fix : fixDown p q0 = fixDown p c

/-- The do-body's decrement: `(q - 1) & MP_MASK` in the machine's form. -/
theorem Fix.dec {p : Nat → Bool} {q0 qv : Nat} (h : Fix p q0 qv) : FixT p q0 ((qv + 268435455) % 268435456) :=
  ⟨Nat.mod_lt _ (by decide), by rw [h.fix]; rfl⟩

/-- The test held: once more. -/
theorem FixT.again {p : Nat → Bool} {q0 c : Nat} (h : FixT p q0 c) (ht : p c = true) (h0 : 0 < c) : Fix p q0 c :=
  ⟨h.lt, by rw [h.fix, fixDown_dec ht h0, dec_pos h0 h.lt]⟩

/-- The test failed: `c` is `q̂`. -/
theorem FixT.done {p : Nat → Bool} {q0 c : Nat} (h : FixT p q0 c) (ht : p c = false) : fixDown p q0 = c := by
  rw [h.fix, fixDown_stop ht]

/-! ## `t1 = q * Y2`, `t2 = X3` -/

/-- `t1` after `mp_zero(&t1)`, `t1.dp[0] := y0`, `t1.dp[1] := y1`, `t1.used := 2`. -/
def t1Of (T : MpInt) (y1 y0 : Nat) : MpInt :=
  MpInt.ofDigits 2 T.alloc T.sign (fun j => if j = 1 then y1 else if j = 0 then y0 else 0)

/-- `t2` after `t2.dp[0..2] := x0, x1, x2`, `t2.used := 3`. -/
def t2Of (T : MpInt) (x2 x1 x0 : Nat) : MpInt :=
  MpInt.ofDigits 3 T.alloc T.sign (fun j => if j = 2 then x2 else if j = 1 then x1 else if j = 0 then x0 else 0)

theorem t1Of_digit {T : MpInt} (hz : ∀ j, T.digit j = 0) (y1 y0 j : Nat) (hj : j < T.alloc) :
    (t1Of T y1 y0).digit j = if j = 1 then y1 else if j = 0 then y0 else T.digit j := by
  rw [t1Of, MpInt.ofDigits_digit, if_pos hj, hz]

theorem t2Of_digit {T : MpInt} (hs : T.Shape) (hu : T.used ≤ 3) (x2 x1 x0 j : Nat) (hj : j < T.alloc) :
    (t2Of T x2 x1 x0).digit j = if j = 2 then x2 else if j = 1 then x1 else if j = 0 then x0 else T.digit j := by
  rw [t2Of, MpInt.ofDigits_digit, if_pos hj]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rw [hs.high_zero j (by omega)]

/-- The low part of `y`'s top two digits. -/
abbrev yLo (B t : Nat) : Nat := if 1 ≤ t then natDigit B (t - 1) else 0
/-- The low digit of `x`'s top three. -/
abbrev xLo (x i : Nat) : Nat := if 2 ≤ i then natDigit x (i - 2) else 0

theorem yLo_lt (B t : Nat) : yLo B t < 2 ^ 32 := by
  unfold yLo; split
  · exact Nat.lt_trans (natDigit_lt _ _) (by decide)
  · decide

theorem xLo_lt (x i : Nat) : xLo x i < 2 ^ 32 := by
  unfold xLo; split
  · exact Nat.lt_trans (natDigit_lt _ _) (by decide)
  · decide

/-- **`t1 = q * Y2`** (`mp_mul_d(&t1, q, &t1)`): valid, below `b^3`, `alloc` kept. -/
theorem t1_mul {T Tz T1m : MpInt} {B t c : Nat} (hT : T.Shape) (ha : 3 ≤ T.alloc) (hz : ZeroPost T Tz)
    (hN : Norm B t) (hc : c < radix)
    (h : MulDPost (t1Of Tz (natDigit B t) (yLo B t)) c (t1Of Tz (natDigit B t) (yLo B t)) T1m) :
    T1m.Valid ∧ T1m.mag = c * knuthY2 B t ∧ T1m.mag < radix ^ 3 ∧ T1m.alloc = T.alloc := by
  have hal : Tz.alloc = T.alloc := hz.alloc
  have hyt : natDigit B t ≠ 0 := by have := hN.top; omega
  have hlo : yLo B t < radix := by unfold yLo; split <;> first | exact natDigit_lt _ _ | exact radix_pos
  have hv : (t1Of Tz (natDigit B t) (yLo B t)).Valid :=
    { len := MpInt.ofDigits_len _ _ _ _
      used_le := by show 2 ≤ Tz.alloc; omega
      alloc_lt := by show Tz.alloc < 2 ^ 31; rw [hal]; exact hT.alloc_lt
      digit_lt := fun j => by
        rw [t1Of, MpInt.ofDigits_digit]
        split
        · split
          · exact natDigit_lt _ _
          · split
            · exact hlo
            · exact radix_pos
        · exact radix_pos
      high_zero := fun j hj => by
        rw [t1Of, MpInt.ofDigits_digit]; simp only [t1Of, MpInt.ofDigits] at hj
        split
        · rw [if_neg (by omega), if_neg (by omega)]
        · rfl
      top := fun _ => by
        show (t1Of Tz (natDigit B t) (yLo B t)).digit 1 ≠ 0
        rw [t1Of, MpInt.ofDigits_digit, if_pos (by omega), if_pos rfl]; exact hyt
      sign_ok := by show Tz.sign = _ ∨ _; rw [hz.sign]; exact .inl rfl
      zero_pos := fun h0 => by simp [t1Of, MpInt.ofDigits] at h0 }
  have hm : (t1Of Tz (natDigit B t) (yLo B t)).mag = knuthY2 B t := by
    show natUpTo _ 2 = _
    rw [natUpTo_two]
    simp only [t1Of, MpInt.ofDigits_digit, show 1 < Tz.alloc by omega, show 0 < Tz.alloc by omega, if_true,
      if_false, show (0 : Nat) ≠ 1 by decide, knuthY2]
  obtain ⟨hv', hm', _⟩ := MulDPost.spec hv hc (by show 3 ≤ Tz.alloc; omega) (by show Tz.alloc < 2 ^ 31; rw [hal]; exact hT.alloc_lt) h
  refine ⟨hv', by rw [hm', hm, Nat.mul_comm], ?_, by rw [h.alloc]; exact hal⟩
  rw [hm', hm, Nat.mul_comm]; exact knuthT1_lt B t hc

/-- **`t2 = X3`**: shaped, `used = 3`, not clamped. -/
theorem t2_mk {T : MpInt} {x i : Nat} (hT : T.Shape) (ha : 3 ≤ T.alloc) :
    (t2Of T (natDigit x i) (natDigit x (i - 1)) (xLo x i)).Shape ∧ (t2Of T (natDigit x i) (natDigit x (i - 1)) (xLo x i)).used = 3 ∧
      (t2Of T (natDigit x i) (natDigit x (i - 1)) (xLo x i)).mag = knuthX3 x i := by
  have hlo : xLo x i < radix := by unfold xLo; split <;> first | exact natDigit_lt _ _ | exact radix_pos
  refine ⟨{ len := MpInt.ofDigits_len _ _ _ _, used_le := by show 3 ≤ T.alloc; omega, alloc_lt := hT.alloc_lt,
             digit_lt := fun j => ?_, high_zero := fun j hj => ?_ }, rfl, ?_⟩
  · rw [t2Of, MpInt.ofDigits_digit]
    split
    · split
      · exact natDigit_lt _ _
      · split
        · exact natDigit_lt _ _
        · split
          · exact hlo
          · exact radix_pos
    · exact radix_pos
  · simp only [t2Of, MpInt.ofDigits] at hj
    rw [t2Of, MpInt.ofDigits_digit]
    split
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · rfl
  · show natUpTo _ 3 = _
    rw [natUpTo_three]
    simp only [t2Of, MpInt.ofDigits_digit, show 2 < T.alloc by omega, show 1 < T.alloc by omega,
      show 0 < T.alloc by omega, if_true, if_false, show (1 : Nat) ≠ 2 by decide, show (0 : Nat) ≠ 2 by decide,
      show (0 : Nat) ≠ 1 by decide, knuthX3, xLo]

/-- The do-while's test: `mp_cmp_mag(&t1, &t2) == MP_GT` is `knuthTest`. -/
theorem test_gt {T1 T2 : MpInt} {B t x i c : Nat} (h1 : T1.Valid) (hm1 : T1.mag = c * knuthY2 B t)
    (hl1 : T1.mag < radix ^ 3) (h2 : T2.Shape) (hu2 : T2.used = 3) (hm2 : T2.mag = knuthX3 x i) :
    cmpMag T1 T2 = .gt ↔ kP B t x i c = true := by
  rw [cmpMag_three h1 hl1 h2 hu2, hm1, hm2]
  simp only [kP, knuthTest, Bool.and_eq_true, decide_eq_true_eq]

/-! ## Steps 3.3–3.4 -/

/-- `t1 = q̂ y` after the growing `mp_mul_d(&y, q̂, &t1)`. -/
structure MulDY (T1 T1a : MpInt) (B t c : Nat) : Prop where
  valid : T1a.Valid
  mag : T1a.mag = B * c
  sign : T1a.sign = Layout.mpZpos
  room : t + 2 ≤ T1a.alloc
  used : T1a.used ≤ t + 2
  alloc : T1.alloc ≤ T1a.alloc

/-- `t1 = q̂ y` (a cut's premise). -/
structure T1M (T1 : MpInt) (B c t : Nat) : Prop where
  valid : T1.Valid
  mag : T1.mag = B * c
  sign : T1.sign = Layout.mpZpos
  room : t + 2 ≤ T1.alloc
  used : T1.used ≤ t + 2

/-- `t1 = y` after `mp_copy(&y, &t1)` (a cut's premise). -/
structure TCp (T Y : MpInt) : Prop where
  valid : T.Valid
  mag : T.mag = Y.mag
  used : T.used = Y.used
  sign : T.sign = Y.sign
  a3 : 3 ≤ T.alloc

/-- `t1 = y b^k` after `mp_lshd(&t1, k)` (a cut's premise). -/
structure TSh (T Y : MpInt) (k : Nat) : Prop where
  valid : T.Valid
  mag : T.mag = Y.mag * radix ^ k
  used : T.used = Y.used + k
  sign : T.sign = Y.sign
  a3 : 3 ≤ T.alloc

/-- Step 2's bounds (a cut's premise): the normalised divisor, `t ≤ n`, `x < b^(n+1)`. -/
structure N2 (A B ux uy au : Nat) : Prop where
  norm : Norm B (uy - 1)
  uy0 : 0 < uy
  uyx : uy ≤ ux
  alt : A < radix ^ ux
  uxa : ux ≤ au + 1

/-- `mp_mul_d(&y, q, &t1)` (growing `t1`). -/
theorem muld_y {Y T1 T1a : MpInt} {B t c : Nat} (hY : YB Y B t) (hT : T1.Shape) (hc : c < radix)
    (h31 : t + 2 < 2 ^ 31) (h : MulDPost Y c (mulDIn Y T1) T1a) : MulDY T1 T1a B t c := by
  have hg := mulDIn_grown (a := Y) hT (by rw [hY.used]; omega)
  have hr := mulDIn_room Y T1
  obtain ⟨hv, hm, _⟩ := MulDPost.spec hY.valid hc hr hg.shape.alloc_lt h
  refine ⟨hv, by rw [hm, hY.mag], ?_, by rw [h.alloc]; rw [hY.used] at hr; omega,
    by rw [h.used]; have := clampUsed_le (mulDDigit Y c) (Y.used + 1); rw [hY.used] at this ⊢; omega,
    by rw [h.alloc]; exact hg.alloc⟩
  have := h.sign; split at this
  · exact this
  · rw [this, hY.sign]

/-- A valid integer below `b^n` has at most `n` digits. -/
theorem used_le_of_lt {x : MpInt} (hx : x.Valid) {n : Nat} (h : x.mag < radix ^ n) : x.used ≤ n := by
  rcases Nat.lt_or_ge n x.used with h1 | h1
  · have := MpInt.mag_ge hx (by omega)
    have : radix ^ n ≤ radix ^ (x.used - 1) := Nat.pow_le_pow_right radix_pos (by omega)
    omega
  · exact h1

/-- `t1 = q̂ y_t… b^k` after the growing `mp_lshd(&t1, k)`. -/
structure LshT1 (T1a T1b : MpInt) (B t c k : Nat) : Prop where
  valid : T1b.Valid
  mag : T1b.mag = c * (B * radix ^ k)
  sign : T1b.sign = Layout.mpZpos
  alloc : T1a.alloc ≤ T1b.alloc
  used : T1b.used ≤ k + t + 2

/-- `mp_lshd(&t1, k)` (growing): `q B b^k`. -/
theorem lshd_t1 {T1a T1b : MpInt} {B t c k : Nat} (hv : T1a.Valid) (hm : T1a.mag = B * c) (hs : T1a.sign = Layout.mpZpos)
    (hu : T1a.used ≤ t + 2) (h31 : t + 2 + k < 2 ^ 31) (hB : B < radix ^ (t + 1)) (hc : c < radix)
    (h : LshdPost (lshdIn T1a k) k T1b) : LshT1 T1a T1b B t c k := by
  have hg := lshdIn_grown hv.toShape (k := k) (by omega)
  have hvi : (lshdIn T1a k).Valid :=
    { hg.shape with top := fun h0 => by rw [hg.digit, hg.used]; exact hv.top (by rw [hg.used] at h0; exact h0)
                    sign_ok := by rw [hg.sign]; exact hv.sign_ok
                    zero_pos := fun h0 => by rw [hg.sign]; exact hv.zero_pos (by rw [hg.used] at h0; exact h0) }
  have hmi : (lshdIn T1a k).mag = T1a.mag := by unfold MpInt.mag; rw [hg.digit, hg.used]
  have hmag : T1b.mag = c * (B * radix ^ k) ∧ T1b.Valid ∧ T1b.sign = Layout.mpZpos ∧ (lshdIn T1a k).alloc ≤ T1b.alloc := by
    by_cases h0 : k = 0 ∨ (lshdIn T1a k).used = 0
    · have e := h.noop h0
      rw [e, hmi, hm]
      refine ⟨?_, hvi, by rw [hg.sign]; exact hs, Nat.le_refl _⟩
      rcases h0 with h0 | h0
      · subst h0; simp [Nat.mul_comm]
      · rw [hg.used] at h0; rw [MpInt.mag_used_zero h0] at hm
        rcases Nat.mul_eq_zero.1 hm.symm with h1 | h1 <;> simp [h1]
    · have hr := lshdIn_room T1a (k := k) (by omega) (by rw [hg.used] at h0; omega)
      obtain ⟨hv2, hm2⟩ := LshdPost.spec hvi hr h
      have hsh := h.shift (by omega) (by omega)
      refine ⟨by rw [hm2, hmi, hm, Nat.mul_comm B c, Nat.mul_assoc], hv2, by rw [hsh.sign, hg.sign]; exact hs, by rw [hsh.alloc]; exact Nat.le_refl _⟩
  obtain ⟨hm2, hv2, hs2, ha2⟩ := hmag
  refine ⟨hv2, hm2, hs2, Nat.le_trans hg.alloc ha2, used_le_of_lt hv2 ?_⟩
  rw [hm2]
  calc c * (B * radix ^ k) < radix * (radix ^ (t + 1) * radix ^ k) :=
        Nat.mul_lt_mul_of_lt_of_le hc (Nat.mul_le_mul_right _ (Nat.le_of_lt hB)) (Nat.mul_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hB) (radix_pow_pos _))
    _ = radix ^ (k + t + 2) := by rw [← Nat.pow_add, ← Nat.pow_succ']; congr 1; omega

/-- `mp_sub(&x, &t1, &x)`: `x - q B b^k`. -/
theorem sub3_mk {X T X' : MpInt} {D c : Nat} (hX : X.Valid) (hXs : X.sign = Layout.mpZpos) (hT : T.Valid)
    (hTs : T.sign = Layout.mpZpos) (hTm : T.mag = c * D) (hroom : max X.used T.used ≤ X.alloc)
    (h : SubPost X T X X') : Sub3 X.mag D c X' := by
  obtain ⟨hv, hval⟩ := sub_pos hX hT hXs hTs hroom h
  exact ⟨hv, by rw [hval, val_zpos hXs, val_zpos hTs, hTm]⟩

theorem Sub3.qpos {X D q : Nat} {x' : MpInt} (h : Sub3 X D q x') (hneg : x'.sign = Layout.mpNeg) : 0 < q := by
  have hv := h.val
  have hm : x'.mag ≠ 0 := fun h0 => by
    have := h.valid.zero_pos (used_zero_of_mag h.valid h0); rw [this] at hneg; exact absurd hneg (by decide)
  rw [val_neg hneg] at hv
  rcases Nat.eq_zero_or_pos q with h0 | h0
  · subst h0; simp at hv; omega
  · exact h0

/-- **3.3 without the add-back** (`x ≥ 0`): the next invariant, `q.dp[k] = q̂`. -/
theorem XI.next_keep {A B t k : Nat} {X X' : MpInt} {qf g : Nat → Nat} (hx : XI A B t (k + t + 1) X qf)
    (hN : Norm B t) (hs : Sub3 X.mag (B * radix ^ k) (knuthQhat X.mag B t (k + t + 1)) X')
    (hpos : X'.sign = Layout.mpZpos) (hg : ∀ j, j ≠ k → g j = qf j) (hgk : g k = knuthQhat X.mag B t (k + t + 1))
    (hal : X'.alloc = X.alloc) : XI A B t (k + t) X' g := by
  have e : k + t + 1 = t + k + 1 := by omega
  rw [e] at hs hgk hx
  obtain ⟨hq, hv⟩ := step3_keep hs hpos
  obtain ⟨hp, hd⟩ := step3_inv hx.inv hN.hi hN.top (by omega) hs.valid hv
  rw [show t + k + 1 - 1 = k + t by omega, show t + k + 1 - t - 1 = k by omega, hq] at hd
  refine ⟨hs.valid, hp, by rw [hal]; have := hx.room; omega, hd.congr fun j => ?_⟩
  unfold setDigit; split
  · subst_vars; exact hgk.symm
  · exact (hg j (by assumption)).symm

/-- **3.4, the add-back** (`x < 0`): `x += y b^k`, `q.dp[k] = q̂ - 1`, the next invariant. -/
theorem XI.next_back {A B t k : Nat} {X X' T X'' : MpInt} {qf g : Nat → Nat} (hx : XI A B t (k + t + 1) X qf)
    (hN : Norm B t) (hs : Sub3 X.mag (B * radix ^ k) (knuthQhat X.mag B t (k + t + 1)) X')
    (hneg : X'.sign = Layout.mpNeg) (hT : T.Valid) (hTs : T.sign = Layout.mpZpos) (hTm : T.mag = B * radix ^ k)
    (hroom : max X'.used T.used ≤ X'.alloc) (ha : AddPost X' T X' X'')
    (hg : ∀ j, j ≠ k → g j = qf j) (hgk : g k = knuthQhat X.mag B t (k + t + 1)) (hal : X''.alloc = X.alloc) :
    XI A B t (k + t) X'' (fun j => if j = k then g k - 1 else g j) := by
  have e : k + t + 1 = t + k + 1 := by omega
  rw [e] at hs hgk hx
  obtain ⟨hv2, hval2⟩ := hs.addBack hneg hT hTs hTm hroom ha
  obtain ⟨hq, hv⟩ := step3_back hs hneg hval2
  obtain ⟨hp, hd⟩ := step3_inv hx.inv hN.hi hN.top (by omega) hv2 hv
  rw [show t + k + 1 - 1 = k + t by omega, show t + k + 1 - t - 1 = k by omega, hq] at hd
  refine ⟨hv2, hp, by rw [hal]; have := hx.room; omega, hd.congr fun j => ?_⟩
  unfold setDigit; by_cases hj : j = k
  · subst hj; simp [hgk]
  · simp [hj, hg j hj]

/-! ## The end -/

/-- `q` before `mp_clamp(&q)`: `a->used + 2` digits of `|a| / |b|`. -/
theorem quot_shape {a : MpInt} {Q : Nat} {qf : Nat → Nat} (hqf : qf = natDigit Q) (hQ : Q < radix ^ a.used)
    (hau : a.used + 3 < 2 ^ 30) : (MpInt.ofDigits (a.used + 2) (initPrec (a.used + 2)) 0 qf).Shape := by
  have hp : initPrec (a.used + 2) = max 3 (a.used + 2) := by unfold initPrec; rw [minPrec_eq]
  subst hqf
  exact { len := MpInt.ofDigits_len _ _ _ _
          used_le := by show a.used + 2 ≤ initPrec (a.used + 2); omega
          alloc_lt := by show initPrec (a.used + 2) < 2 ^ 31; omega
          digit_lt := fun j => by rw [MpInt.ofDigits_digit]; split; exact natDigit_lt _ _; exact radix_pos
          high_zero := fun j hj => by
            have hj' : a.used + 2 ≤ j := hj
            rw [MpInt.ofDigits_digit]; split
            · exact natDigit_high hQ (by omega)
            · rfl }

/-- `c->sign := neg` with `neg = (a->sign != b->sign)` as the `snez` word leaves it. -/
theorem sign_word {sa sb : Nat} (ha : sa = 0 ∨ sa = 1) (hb : sb = 0 ∨ sb = 1) :
    (if BitVec.ofNat 64 sa - BitVec.ofNat 64 sb = 0#64 then 0 else 1) = divSign sa sb := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- **The quotient** (`mp_clamp(&q)`, `mp_exch(&q, c)`, `c->sign := neg`). -/
theorem quot_big {a b Qc : MpInt} {nm : Nat} {qf : Nat → Nat} (ha : a.Valid) (hb : b.Valid) (hb0 : 0 < b.used)
    (hqf : qf = natDigit (a.mag * 2 ^ nm / (b.mag * 2 ^ nm))) (hau : a.used + 3 < 2 ^ 30)
    (hcl : ClampPost (MpInt.ofDigits (a.used + 2) (initPrec (a.used + 2)) 0 qf) Qc) :
    DivBigQuot a b { Qc with sign := divSign a.sign b.sign } := by
  rw [norm_quot _ _ _ (Nat.two_pow_pos nm)] at hqf
  have hbm : 0 < b.mag := Nat.lt_of_lt_of_le (radix_pow_pos _) (MpInt.mag_ge hb hb0)
  have hQ : a.mag / b.mag < radix ^ a.used :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (MpInt.mag_lt ha.toShape)
  have hp : initPrec (a.used + 2) = max 3 (a.used + 2) := by unfold initPrec; rw [minPrec_eq]
  have hd : (MpInt.ofDigits (a.used + 2) (initPrec (a.used + 2)) 0 qf).digit = natDigit (a.mag / b.mag) := by
    funext j; rw [MpInt.ofDigits_digit, hqf]; split
    · rfl
    · exact (natDigit_high hQ (by rw [hp] at *; omega)).symm
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · show Qc.alloc = _; rw [hcl.alloc, ← hp]; rfl
  · show Qc.digits.length = _; rw [hcl.digits, ← hp]; exact MpInt.ofDigits_len _ _ _ _
  · show Qc.digit = _; rw [hcl.digit, hd]
  · show Qc.used = _; rw [hcl.used, hd]; rfl

/-- Step 2 subtracts at most three times. -/
theorem S2.lt4 {A B ux uy j : Nat} {X : MpInt} (h : S2 A (B * radix ^ (ux - uy)) X j) (hN : Norm B (uy - 1))
    (hA : A < radix ^ ux) (hu : 0 < uy) (huu : uy ≤ ux) : j < 4 := by
  have hB : 0 < B * radix ^ (ux - uy) := Nat.mul_pos (Nat.lt_of_lt_of_le (radix_pow_pos _) hN.lo) (radix_pow_pos _)
  have h4 := step2_lt (A := A) (B := B) (n := ux - 1) (t := uy - 1) (by rw [show ux - 1 + 1 = ux by omega]; exact hA)
    hN.top (by omega)
  rw [show ux - 1 - (uy - 1) = ux - uy by omega] at h4
  exact Nat.lt_of_le_of_lt (h.le hB) h4

/-- `exit_Z` with `uy = ux`. -/
theorem exit_Z' {A B ux uy j : Nat} {X : MpInt} {qf : Nat → Nat} (h : S2 A (B * radix ^ (ux - uy)) X j)
    (hlt : X.mag < B * radix ^ (ux - uy)) (hN : Norm B (uy - 1)) (hA : A < radix ^ ux) (hu : 0 < ux) (he : uy = ux)
    (hqf : ∀ i, qf i = if i = ux - uy then j else 0) : DivInv A B (uy - 1) (uy - 1) X.mag qf := by
  subst he; exact exit_Z h hlt hN hA hu hqf

/-- The candidates of the test: `t1 = c * Y2` and `t2 = X3`. -/
structure TC (B t x i c : Nat) (T1 T2 : MpInt) : Prop where
  v1 : T1.Valid
  m1 : T1.mag = c * knuthY2 B t
  l1 : T1.mag < radix ^ 3
  a1 : 3 ≤ T1.alloc
  s2 : T2.Shape
  u2 : T2.used = 3
  m2 : T2.mag = knuthX3 x i
  a2 : 3 ≤ T2.alloc

theorem TC.gt {B t x i c : Nat} {T1 T2 : MpInt} (h : TC B t x i c T1 T2) : cmpMag T1 T2 = .gt ↔ kP B t x i c = true :=
  test_gt h.v1 h.m1 h.l1 h.s2 h.u2 h.m2

theorem TC.stop {B t x i c : Nat} {T1 T2 : MpInt} (h : TC B t x i c T1 T2) (hc : cmpMag T1 T2 ≠ .gt) :
    kP B t x i c = false := by
  cases hk : kP B t x i c
  · rfl
  · exact absurd (h.gt.2 hk) hc

/-! ## 3.1 in the machine's digits -/

theorem fix_eqM {A B t k : Nat} {X Y : MpInt} {qf : Nat → Nat} (hx : XI A B t (k + t + 1) X qf) (hy : YB Y B t)
    (he : X.digit (k + t + 1) = Y.digit t) : Fix (kP B t X.mag (k + t + 1)) (kQ0 B t X.mag (k + t + 1)) 0 :=
  fix_eq (by rw [← hx.digit, ← hy.digit]; exact he)

theorem fix_ltM {A B t k : Nat} {X Y : MpInt} {qf : Nat → Nat} (hx : XI A B t (k + t + 1) X qf) (hy : YB Y B t)
    (hne : X.digit (k + t + 1) ≠ Y.digit t)
    (hlt : (X.digit (k + t + 1) * 268435456 + X.digit (k + t)) / Y.digit t < 268435456) :
    Fix (kP B t X.mag (k + t + 1)) (kQ0 B t X.mag (k + t + 1))
      (((X.digit (k + t + 1) * 268435456 + X.digit (k + t)) / Y.digit t + 1) % 268435456) :=
  fix_lt (by rw [← hx.digit, ← hy.digit]; exact hne)
    (by rw [show k + t + 1 - 1 = k + t by omega, ← hx.digit, ← hx.digit, ← hy.digit]) hlt

theorem fix_geM {A B t k : Nat} {X Y : MpInt} {qf : Nat → Nat} (hx : XI A B t (k + t + 1) X qf) (hy : YB Y B t)
    (hne : X.digit (k + t + 1) ≠ Y.digit t)
    (hge : 268435456 ≤ (X.digit (k + t + 1) * 268435456 + X.digit (k + t)) / Y.digit t) :
    Fix (kP B t X.mag (k + t + 1)) (kQ0 B t X.mag (k + t + 1)) 0 :=
  fix_ge (by rw [← hx.digit, ← hy.digit]; exact hne)
    (by rw [show k + t + 1 - 1 = k + t by omega, ← hx.digit, ← hx.digit, ← hy.digit]) hge

/-! ## `t1`'s and `t2`'s digits as the stores leave them -/

theorem t1_kind {T Y : MpInt} {B t : Nat} (hz : ∀ j, T.digit j = 0) (hy : YB Y B t) (y0 : Nat)
    (hy0 : y0 = yLo B t) (j : Nat) (hj : j < T.alloc) :
    (t1Of T (natDigit B t) (yLo B t)).digit j = if j = 1 then Y.digit t else if j = 0 then y0 else T.digit j := by
  rw [t1Of_digit hz _ _ j hj, hy.digit, hy0]

theorem t2_kind {T X : MpInt} {x i : Nat} (hs : T.Shape) (hu : T.used ≤ 3) (hX : X.Shape) (hx : X.mag = x) (x0 : Nat)
    (hx0 : x0 = xLo x i) (j : Nat) (hj : j < T.alloc) :
    (t2Of T (natDigit x i) (natDigit x (i - 1)) (xLo x i)).digit j =
      if j = 2 then X.digit i else if j = 1 then X.digit (i - 1) else if j = 0 then x0 else T.digit j := by
  rw [t2Of_digit hs hu _ _ _ j hj, hX.digit_eq, hX.digit_eq, hx, hx0]

theorem t1Of_valid {T Tz : MpInt} {B t : Nat} (hT : T.Shape) (ha : 3 ≤ T.alloc) (hz : ZeroPost T Tz) (hN : Norm B t) :
    (t1Of Tz (natDigit B t) (yLo B t)).Valid ∧ 3 ≤ (t1Of Tz (natDigit B t) (yLo B t)).alloc := by
  have := t1_mul (c := 0) (T1m := t1Of Tz (natDigit B t) (yLo B t)) hT ha hz hN radix_pos
  refine ⟨?_, by show 3 ≤ Tz.alloc; rw [hz.alloc]; exact ha⟩
  have hal : Tz.alloc = T.alloc := hz.alloc
  have hyt : natDigit B t ≠ 0 := by have := hN.top; omega
  have hlo : yLo B t < radix := by unfold yLo; split <;> first | exact natDigit_lt _ _ | exact radix_pos
  exact { len := MpInt.ofDigits_len _ _ _ _
          used_le := by show 2 ≤ Tz.alloc; omega
          alloc_lt := by show Tz.alloc < 2 ^ 31; rw [hal]; exact hT.alloc_lt
          digit_lt := fun j => by
            rw [t1Of, MpInt.ofDigits_digit]
            split
            · split
              · exact natDigit_lt _ _
              · split
                · exact hlo
                · exact radix_pos
            · exact radix_pos
          high_zero := fun j hj => by
            rw [t1Of, MpInt.ofDigits_digit]; simp only [t1Of, MpInt.ofDigits] at hj
            split
            · rw [if_neg (by omega), if_neg (by omega)]
            · rfl
          top := fun _ => by
            show (t1Of Tz (natDigit B t) (yLo B t)).digit 1 ≠ 0
            rw [t1Of, MpInt.ofDigits_digit, if_pos (by omega), if_pos rfl]; exact hyt
          sign_ok := by show Tz.sign = _ ∨ _; rw [hz.sign]; exact .inl rfl
          zero_pos := fun h0 => by simp [t1Of, MpInt.ofDigits] at h0 }

theorem divNorm_27 {cb : Nat} (h : cb % 28 = 27) : 0 = divNorm cb := by
  unfold divNorm; split <;> simp only [Layout.digitBits] at * <;> omega

theorem divNorm_lt27 {cb : Nat} (h : cb % 28 < 27) : 27 - cb % 28 = divNorm cb := by
  unfold divNorm; split <;> simp only [Layout.digitBits] at * <;> omega

/-- The running remainder of iteration `i` has at most `i + 1` digits. -/
theorem XI.used_le {A B t i : Nat} {X : MpInt} {qf : Nat → Nat} (h : XI A B t i X qf) (hN : Norm B t)
    (hti : t + 1 ≤ i) : X.used ≤ i + 1 := by
  apply used_le_of_lt h.valid
  have h1 := h.inv.rem_lt (Nat.lt_of_lt_of_le (radix_pow_pos _) hN.lo) hti
  have h2 : B * radix ^ (i - t - 1 + 1) ≤ radix ^ (t + 1) * radix ^ (i - t) := by
    rw [show i - t - 1 + 1 = i - t by omega]; exact Nat.mul_le_mul_right _ (Nat.le_of_lt hN.hi)
  rw [← Nat.pow_add, show t + 1 + (i - t) = i + 1 by omega] at h2
  exact Nat.lt_of_lt_of_le h1 h2

/-- The running remainder of iteration `i ≥ t` has at most `i + 1` digits. -/
theorem XI.used_le2 {A B t i : Nat} {X : MpInt} {qf : Nat → Nat} (h : XI A B t i X qf) (hN : Norm B t)
    (hti : t ≤ i) : X.used ≤ i + 1 := by
  apply used_le_of_lt h.valid
  have hB : 0 < B := Nat.lt_of_lt_of_le (radix_pow_pos _) hN.lo
  have h1 : X.mag < B * radix ^ (i - t) := by
    rw [h.inv.rem]; exact Nat.mod_lt _ (Nat.mul_pos hB (radix_pow_pos _))
  have h2 : B * radix ^ (i - t) ≤ radix ^ (t + 1) * radix ^ (i - t) := Nat.mul_le_mul_right _ (Nat.le_of_lt hN.hi)
  rw [← Nat.pow_add, show t + 1 + (i - t) = i + 1 by omega] at h2
  exact Nat.lt_of_lt_of_le h1 h2

/-- `x - q̂ y b^k` below `b^n` when both terms are. -/
theorem Sub3.used_le {X D q n : Nat} {x' : MpInt} (h : Sub3 X D q x') (hX : X < radix ^ n) (hq : q * D < radix ^ n) :
    x'.used ≤ n := by
  apply used_le_of_lt h.valid
  have hv := h.val
  unfold MpInt.val at hv
  split at hv <;> omega

/-- After `x -= q̂ y b^k` (either sign), `x` has at most `k + t + 2` digits. -/
theorem Sub3.used_kt {A B t k q : Nat} {Xo X : MpInt} {qf : Nat → Nat} (hx : XI A B t (k + t + 1) Xo qf)
    (hN : Norm B t) (hs : Sub3 Xo.mag (B * radix ^ k) q X) (hq : q < radix) : X.used ≤ k + t + 2 := by
  have hB : 0 < B := Nat.lt_of_lt_of_le (radix_pow_pos _) hN.lo
  have hP : radix ^ (t + 1) * radix ^ (k + 1) = radix ^ (k + t + 2) := by
    rw [← Nat.pow_add]; congr 1; omega
  apply hs.used_le
  · have h1 : Xo.mag < B * radix ^ (k + t + 1 - t) := by
      rw [hx.inv.rem]; exact Nat.mod_lt _ (Nat.mul_pos hB (radix_pow_pos _))
    rw [show k + t + 1 - t = k + 1 by omega] at h1
    rw [← hP]; exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ (Nat.le_of_lt hN.hi))
  · have hBk : B * radix ^ k ≤ radix ^ (t + 1) * radix ^ k := Nat.mul_le_mul_right _ (Nat.le_of_lt hN.hi)
    have hpos : 0 < radix ^ (t + 1) * radix ^ k := Nat.mul_pos (radix_pow_pos _) (radix_pow_pos _)
    calc q * (B * radix ^ k) ≤ q * (radix ^ (t + 1) * radix ^ k) := Nat.mul_le_mul_left _ hBk
      _ < radix * (radix ^ (t + 1) * radix ^ k) := Nat.mul_lt_mul_of_pos_right hq hpos
      _ = radix ^ (k + t + 2) := by
        rw [← hP, Nat.pow_succ radix k]; ac_rfl

end Tom.DivStep
