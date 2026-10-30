import Tom.Spec.Window
import Tom.Spec.Reduce
import Tom.Spec.Gcd

/-!
# `mp_exptmod`, `s_mp_exptmod`, `s_mp_exptmod_fast`

The window loop (`Tom.Window`) composed with the concrete reductions:

* `s_mp_exptmod(G, X, P, Y, redmode)`: `M[1] = G mod P` (`mp_mod`), `res = 1`, every
  product reduced modulo `P` (Barrett `mp_reduce` for `redmode = 0`, `mp_reduce_2k_l` for
  `redmode = 1`; both give `v mod P` on the loop's products, `ReducePost.spec`,
  `Reduce2kPost.spec`). `SExptmodPost.spec`: `Y = G^X mod P` for `P > 1`.
* `s_mp_exptmod_fast(G, X, P, Y, redmode)`: Montgomery (`redmode = 0`; `res = R mod P` from
  `mp_montgomery_calc_normalization`, `M[1] = G R mod P` from `mp_mulmod`, a final
  `redux(res)`), diminished radix (`1`) or `mp_reduce_2k` (`2`). `SExptmodFastPost.spec_*`.
* `mp_exptmod(G, X, P, Y)`: `MP_VAL` for `P < 0`; for `X < 0` the inverse (`mp_invmod`) to
  the power `|X|`; then the dispatch on `mp_reduce_is_2k_l`, `mp_dr_is_modulus`,
  `mp_reduce_is_2k` and the parity of `P` (`ExptmodPost`).

`ExptmodPost.spec_nonneg`: for `P > 1` and `X ≥ 0`, `Y = G^X mod P` — except for the
moduli where `mp_reduce_2k_setup` is lossy (`Lossy2k`, see `Reduce.setup2k_lossy`).
`ExptmodPost.spec_neg`: for `X < 0`, `Y * G^|X| ≡ 1 (mod P)` when `G` is invertible and
`G ≥ 0` or `P` is even; `ExptmodPost.spec_neg_odd`: for `G < 0` and odd `P` the C returns
the inverse of `(-G)^|X|` instead (`s_mp_invmod_fast` gives `-G^-1`).
-/

namespace Tom

open MpInt

namespace Exptmod

open Window Mont Reduce

/-! ## Integer helpers -/

theorem int_pow_emod (a P : Int) : ∀ n : Nat, a ^ n % P = (a % P) ^ n % P
  | 0 => by simp
  | n + 1 => by
    rw [Int.pow_succ, Int.pow_succ, Int.mul_emod, int_pow_emod a P n, Int.mul_emod ((a % P) ^ n), Int.emod_emod]

/-- The base of the window: `G mod P` (`mp_mod(G, P, &M[1])`), as a `Nat`. -/
def base (G P : MpInt) : Nat := (G.val % P.val).toNat

theorem base_cast (G P : MpInt) (hP : 0 < P.val) : (base G P : Int) = G.val % P.val :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

theorem MpInt.val_pos_of_sign {P : MpInt} (hs : P.sign ≠ Layout.mpNeg) : P.val = P.mag := by
  unfold MpInt.val; simp [hs]

/-- `(G mod P)^X mod P` in `Nat` is `G^X mod P` in `Int`. -/
theorem base_pow (G P : MpInt) (hs : P.sign ≠ Layout.mpNeg) (hP : 0 < P.mag) (n : Nat) :
    (((base G P) ^ n % P.mag : Nat) : Int) = G.val ^ n % P.val := by
  have hv := MpInt.val_pos_of_sign hs
  rw [Int.natCast_emod, Int.natCast_pow, base_cast G P (by omega), ← hv, ← int_pow_emod]

/-! ## The reductions as the window loop sees them -/

/-- Reduction modulo `P`: what `mp_reduce`, `mp_reduce_2k_l`, `mp_dr_reduce` and a non-lossy
`mp_reduce_2k` compute on the loop's products. -/
def redP (P : Nat) : Nat → Nat := fun v => v % P

theorem red_modP {P : Nat} (hP : 0 < P) : Red (redP P) P 1 where
  lt := fun x _ => Nat.mod_lt _ hP
  mod := fun x _ => by simp [redP]
  coprime := Nat.coprime_one_right P

/-- `mp_reduce_2k` with `d` from `mp_reduce_2k_setup`. -/
def red2kC (P : MpInt) : Nat → Nat := fun v =>
  redLoop (fold2k (nbits P.mag) ((2 ^ nbits P.mag - P.mag) % radix)) P.mag (v + 1) v

/-- `mp_dr_reduce` with `k` from `mp_dr_setup`. -/
def redDrC (P : MpInt) : Nat → Nat := fun v => redLoop (drFold P.used (radix - P.digit 0)) P.mag (v + 1) v

/-- Montgomery reduction with `rho` from `mp_montgomery_setup`. -/
def redMont (P : MpInt) : Nat → Nat := fun v => redc v P.mag (setupRho (P.digit 0)) P.used

theorem red_2k {P : MpInt} (hP : 0 < P.mag) (hd : P.mag + (2 ^ nbits P.mag - P.mag) % radix = 2 ^ nbits P.mag) :
    Red (red2kC P) P.mag 1 := by
  have h := red_modP hP
  refine ⟨fun x hx => ?_, fun x hx => ?_, h.coprime⟩ <;>
    (have e : red2kC P x = x % P.mag :=
      redLoop_spec _ _ hP _ x x (fold2k_ok _ _ _ _ hd) (Nat.le_refl _) (Nat.lt_succ_self _)
     rw [e])
  · exact h.lt x hx
  · exact h.mod x hx

theorem sq_lt_pow {P : MpInt} (hP : P.Shape) (x : Nat) (hx : x ≤ (P.mag - 1) * (P.mag - 1)) :
    x < radix ^ (2 * P.used) := by
  have h := MpInt.mag_lt hP
  rw [Nat.two_mul, Nat.pow_add]
  have : (P.mag - 1) * (P.mag - 1) < radix ^ P.used * radix ^ P.used :=
    Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) (Nat.pow_pos radix_pos)
  omega

theorem red_dr {P : MpInt} (hPs : P.Shape) (hP : 0 < P.mag) (hk : P.mag + (radix - P.digit 0) = radix ^ P.used) :
    Red (redDrC P) P.mag 1 := by
  have h := red_modP hP
  refine ⟨fun x hx => ?_, fun x hx => ?_, h.coprime⟩ <;>
    (have e : redDrC P x = x % P.mag :=
      redLoop_spec _ _ hP _ x x (drFold_ok _ _ _ _ hk (sq_lt_pow hPs x hx)) (Nat.le_refl _) (Nat.lt_succ_self _)
     rw [e])
  · exact h.lt x hx
  · exact h.mod x hx

theorem red_mont {P : MpInt} (hPs : P.Shape) (hodd : P.mag % 2 = 1) :
    Red (redMont P) P.mag (radix ^ P.used) := by
  have hm := MpInt.mag_mod_radix hPs
  have h0 : P.digit 0 % 2 = 1 := by
    rw [← hm, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ radix)]; exact hodd
  have hrho : (P.mag % radix * setupRho (P.digit 0) + 1) % radix = 0 := by rw [hm]; exact setupRho_spec _ h0
  have hP : 0 < P.mag := by omega
  have hlt := MpInt.mag_lt hPs
  exact ⟨fun x hx => (redc_red _ _ _ hrho hP (Nat.le_of_lt hlt) x hx).1,
    fun x hx => (redc_red _ _ _ hrho hP (Nat.le_of_lt hlt) x hx).2, coprime_odd_radix_pow hodd _⟩

/-! ## `s_mp_exptmod` -/

/-- The window size from `mp_count_bits(X)`. -/
def wsize (X : MpInt) : Nat := winSize (nbits X.mag)

/-- The window loop of `s_mp_exptmod(_fast)` over the digits of `X`, with the table built from
`m1` by `red` and the result register starting at `res0`. -/
def winRes (red : Nat → Nat) (X : MpInt) (m1 res0 : Nat) : Nat :=
  finish red (table red m1 (wsize X)) (wsize X)
    (runDigits red (table red m1 (wsize X)) (wsize X) X.digit X.used (start res0))

theorem winRes_spec {red : Nat → Nat} {P R g : Nat} (hr : Red red P R) (hP : 0 < P) (X : MpInt) (hX : X.Shape) :
    winRes red X (enc P R g 1) (enc P R g 0) = enc P R g X.mag := by
  unfold winRes MpInt.mag
  exact window_correct ⟨hr, hP, two_le_winSize _, table_ok hr hP (two_le_winSize _), rfl⟩ hX.digit_lt X.used

/-- What `s_mp_exptmod(G, X, P, Y, redmode)` leaves in `Y` (`redmode` 0 or 1, `X ≥ 0`,
`P > 0`, allocations not failing): the window loop with every product reduced modulo `P`,
`M[1] = G mod P`, `res = 1`. -/
structure SExptmodPost (G X P Y' : MpInt) : Prop where
  valid : Y'.Valid
  mag : Y'.mag = winRes (redP P.mag) X (base G P) 1
  sign : Y'.sign = Layout.mpZpos

/-- **`s_mp_exptmod`**: `Y = G^X mod P` for `P > 1`. -/
theorem SExptmodPost.spec {G X P Y' : MpInt} (hX : X.Shape) (hPs : P.sign ≠ Layout.mpNeg) (hP : 1 < P.mag)
    (h : SExptmodPost G X P Y') :
    Y'.Valid ∧ Y'.mag = base G P ^ X.mag % P.mag ∧ Y'.val = G.val ^ X.mag % P.val := by
  have hb : base G P < P.mag := by
    have := Int.emod_lt_of_pos G.val (b := P.val) (by rw [MpInt.val_pos_of_sign hPs]; omega)
    have h2 := base_cast G P (by rw [MpInt.val_pos_of_sign hPs]; omega)
    rw [MpInt.val_pos_of_sign hPs] at this h2; omega
  have hm : Y'.mag = base G P ^ X.mag % P.mag := by
    rw [h.mag]
    have := winRes_spec (red_modP (P := P.mag) (by omega)) (g := base G P) (by omega) X hX
    simp only [enc, Nat.pow_one, Nat.mul_one, Nat.pow_zero, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hP] at this
    exact this
  refine ⟨h.valid, hm, ?_⟩
  rw [MpInt.val_pos_of_sign (by rw [h.sign]; decide), hm, base_pow G P hPs (by omega)]

/-! ## `s_mp_exptmod_fast` -/

/-- What `s_mp_exptmod_fast(G, X, P, Y, redmode)` leaves in `Y` (`X ≥ 0`, `P > 0`,
allocations not failing), by `redmode`. -/
structure SExptmodFastPost (G X P Y' : MpInt) (redmode : Nat) : Prop where
  valid : Y'.Valid
  sign : Y'.sign = Layout.mpZpos
  mont : redmode = 0 → Y'.mag =
    redMont P (winRes (redMont P) X ((base G P * (radix ^ P.used % P.mag)) % P.mag) (radix ^ P.used % P.mag))
  dr : redmode = 1 → Y'.mag = winRes (redDrC P) X (base G P) 1
  r2k : redmode = 2 → Y'.mag = winRes (red2kC P) X (base G P) 1

theorem base_lt {G P : MpInt} (hPs : P.sign ≠ Layout.mpNeg) (hP : 0 < P.mag) : base G P < P.mag := by
  have := Int.emod_lt_of_pos G.val (b := P.val) (by rw [MpInt.val_pos_of_sign hPs]; omega)
  have h2 := base_cast G P (by rw [MpInt.val_pos_of_sign hPs]; omega)
  rw [MpInt.val_pos_of_sign hPs] at this h2; omega

theorem val_of_zpos {Y : MpInt} {n : Nat} (hs : Y.sign = Layout.mpZpos) (hm : Y.mag = n) : Y.val = n := by
  rw [MpInt.val_pos_of_sign (by rw [hs]; decide), hm]

/-- Montgomery (`redmode = 0`): `Y = G^X mod P` for odd `P > 1`. -/
theorem SExptmodFastPost.spec_mont {G X P Y' : MpInt} (hX : X.Shape) (hP : P.Shape) (hPs : P.sign ≠ Layout.mpNeg)
    (hodd : P.mag % 2 = 1) (hP1 : 1 < P.mag) (h : SExptmodFastPost G X P Y' 0) :
    Y'.Valid ∧ Y'.val = G.val ^ X.mag % P.val := by
  have hr := red_mont hP hodd
  have hb := base_lt (G := G) hPs (by omega)
  have e1 : (base G P * (radix ^ P.used % P.mag)) % P.mag = enc P.mag (radix ^ P.used) (base G P) 1 := by
    unfold enc; rw [Nat.pow_one, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  have e0 : radix ^ P.used % P.mag = enc P.mag (radix ^ P.used) (base G P) 0 := by
    unfold enc; rw [Nat.pow_zero, Nat.one_mul]
  have hm := h.mont rfl
  rw [e1, e0, winRes_spec hr (by omega) X hX, red_enc hr (by omega)] at hm
  exact ⟨h.valid, by rw [val_of_zpos h.sign hm, base_pow G P hPs (by omega)]⟩

/-- Diminished radix (`redmode = 1`): `Y = G^X mod P` for `P = radix^m - k`, `k = mp_dr_setup(P)`. -/
theorem SExptmodFastPost.spec_dr {G X P Y' : MpInt} (hX : X.Shape) (hP : P.Shape) (hPs : P.sign ≠ Layout.mpNeg)
    (hP1 : 1 < P.mag) (hk : P.mag + (radix - P.digit 0) = radix ^ P.used) (h : SExptmodFastPost G X P Y' 1) :
    Y'.Valid ∧ Y'.val = G.val ^ X.mag % P.val := by
  have hr := red_dr hP (by omega) hk
  have hb := base_lt (G := G) hPs (by omega)
  have hm := h.dr rfl
  have := winRes_spec hr (g := base G P) (by omega) X hX
  simp only [enc, Nat.pow_one, Nat.mul_one, Nat.pow_zero, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hP1] at this
  rw [this] at hm
  exact ⟨h.valid, by rw [val_of_zpos h.sign hm, base_pow G P hPs (by omega)]⟩

/-- `2^p - d` (`redmode = 2`): `Y = G^X mod P` when the setup's digit is the true `d`. -/
theorem SExptmodFastPost.spec_2k {G X P Y' : MpInt} (hX : X.Shape) (hPs : P.sign ≠ Layout.mpNeg)
    (hP1 : 1 < P.mag) (hd : P.mag + (2 ^ nbits P.mag - P.mag) % radix = 2 ^ nbits P.mag)
    (h : SExptmodFastPost G X P Y' 2) : Y'.Valid ∧ Y'.val = G.val ^ X.mag % P.val := by
  have hr := red_2k (by omega) hd
  have hb := base_lt (G := G) hPs (by omega)
  have hm := h.r2k rfl
  have := winRes_spec hr (g := base G P) (by omega) X hX
  simp only [enc, Nat.pow_one, Nat.mul_one, Nat.pow_zero, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hP1] at this
  rw [this] at hm
  exact ⟨h.valid, by rw [val_of_zpos h.sign hm, base_pow G P hPs (by omega)]⟩

/-! ## The modulus predicates -/

/-- `mp_reduce_is_2k_l(a)`: one digit, or at least half of the digits are `MP_MASK`. -/
def is2kL (a : MpInt) : Bool :=
  a.used != 0 && (a.used == 1 || decide ((List.range a.used).countP (fun i => a.digit i == radix - 1) ≥ a.used / 2))

/-- `mp_dr_is_modulus(a)`: at least two digits, all above the lowest `MP_MASK`. -/
def drIsMod (a : MpInt) : Bool :=
  decide (2 ≤ a.used) && (List.range a.used).all (fun i => i == 0 || a.digit i == radix - 1)

/-- `mp_reduce_is_2k(a)`: one digit, or every bit from `MP_DIGIT_BIT` up to the top is set. -/
def is2k (a : MpInt) : Bool :=
  a.used != 0 && (a.used == 1 ||
    (List.range (nbits a.mag)).all (fun i => decide (i < Layout.digitBits) || a.mag.testBit i))

/-- `s_mp_exptmod_fast`'s `redmode` as `mp_exptmod` picks it. -/
def drMode (a : MpInt) : Nat := if drIsMod a then 1 else if is2k a then 2 else 0

/-- The moduli where `mp_exptmod` uses `mp_reduce_2k` with a lossy setup. -/
def Lossy2k (P : MpInt) : Prop :=
  is2kL P = false ∧ drIsMod P = false ∧ is2k P = true ∧ radix ≤ 2 ^ nbits P.mag - P.mag

theorem drIsMod_digits {a : MpInt} (h : drIsMod a = true) :
    2 ≤ a.used ∧ ∀ i, 1 ≤ i → i < a.used → a.digit i = radix - 1 := by
  unfold drIsMod at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq] at h
  exact ⟨h.1, fun i h1 h2 => (h.2 i h2).resolve_left (by omega)⟩

/-! ## `mp_exptmod` -/

/-- The nonnegative-exponent part of `mp_exptmod(G, X, P, Y)` (`P ≥ 0`, `X ≥ 0`): the
dispatch, by branch. Errors leave `Y` as it was. -/
structure ExptmodNNPost (G X P Y Y' : MpInt) (ret : Int) : Prop where
  l2k : is2kL P = true → ret = Layout.mpOkay ∧ SExptmodPost G X P Y'
  fast : is2kL P = false → (P.mag % 2 = 1 ∨ drMode P ≠ 0) →
    ret = Layout.mpOkay ∧ SExptmodFastPost G X P Y' (drMode P)
  zero : is2kL P = false → P.mag % 2 = 0 → drMode P = 0 → P.mag = 0 → ret = Layout.mpVal ∧ Y' = Y
  barrett : is2kL P = false → P.mag % 2 = 0 → drMode P = 0 → 0 < P.mag →
    ret = Layout.mpOkay ∧ SExptmodPost G X P Y'

/-- What `mp_exptmod(G, X, P, Y)` leaves (allocations not failing): `MP_VAL` for a negative
modulus; for a negative exponent, `mp_invmod(G, P, &tmpG)` and then the nonnegative case for
`tmpG` and `|X|` (`mp_abs`); otherwise the nonnegative case. -/
structure ExptmodPost (G X P Y Y' : MpInt) (ret : Int) : Prop where
  pneg : P.sign = Layout.mpNeg → ret = Layout.mpVal ∧ Y' = Y
  xpos : P.sign ≠ Layout.mpNeg → X.sign ≠ Layout.mpNeg → ExptmodNNPost G X P Y Y' ret
  xneg : P.sign ≠ Layout.mpNeg → X.sign = Layout.mpNeg →
    ∃ Gi0 Gi : MpInt, ∃ r1 : Int, InvmodPost G P Gi0 Gi r1 ∧ (r1 ≠ Layout.mpOkay → ret = r1 ∧ Y' = Y) ∧
      (r1 = Layout.mpOkay → ExptmodNNPost Gi (X.withSign Layout.mpZpos) P Y Y' ret)

/-- **`mp_exptmod`, nonnegative exponent**: for `P > 1` (and `P` not one of the lossy
`mp_reduce_2k` moduli), `Y = G^X mod P`. -/
theorem ExptmodNNPost.spec {G X P Y Y' : MpInt} {ret : Int} (hX : X.Shape) (hP : P.Valid)
    (hPs : P.sign ≠ Layout.mpNeg) (hP1 : 1 < P.mag) (hbug : ¬ Lossy2k P) (h : ExptmodNNPost G X P Y Y' ret) :
    ret = Layout.mpOkay ∧ Y'.Valid ∧ Y'.val = G.val ^ X.mag % P.val := by
  cases h2 : is2kL P
  · by_cases hf : P.mag % 2 = 1 ∨ drMode P ≠ 0
    · obtain ⟨hr, hp⟩ := h.fast h2 hf
      refine ⟨hr, ?_⟩
      unfold drMode at hp
      cases hd : drIsMod P
      · cases hk : is2k P
        · simp only [hd, hk, Bool.false_eq_true, ite_false] at hp
          have hodd : P.mag % 2 = 1 := by
            rcases hf with hf | hf
            · exact hf
            · exfalso; apply hf; simp [drMode, hd, hk]
          exact hp.spec_mont hX hP.toShape hPs hodd hP1
        · simp only [hd, hk, Bool.false_eq_true, ite_false, ite_true] at hp
          have hs : 2 ^ nbits P.mag - P.mag < radix := by
            rcases Nat.lt_or_ge (2 ^ nbits P.mag - P.mag) radix with h' | h'
            · exact h'
            · exact absurd ⟨h2, hd, hk, h'⟩ hbug
          have := nbits_lt P.mag
          exact hp.spec_2k hX hPs hP1 (by rw [Nat.mod_eq_of_lt hs]; omega)
      · simp only [hd, ite_true] at hp
        obtain ⟨hu, hdig⟩ := drIsMod_digits hd
        exact hp.spec_dr hX hP.toShape hPs hP1 (dr_modulus P hP.toShape hu hdig)
    · have hf' : P.mag % 2 = 0 ∧ drMode P = 0 := by omega
      obtain ⟨hr, hp⟩ := h.barrett h2 hf'.1 hf'.2 (by omega)
      exact ⟨hr, (hp.spec hX hPs hP1).1, (hp.spec hX hPs hP1).2.2⟩
  · obtain ⟨hr, hp⟩ := h.l2k h2
    exact ⟨hr, (hp.spec hX hPs hP1).1, (hp.spec hX hPs hP1).2.2⟩

/-- **`mp_exptmod`, `X ≥ 0`.** -/
theorem ExptmodPost.spec_nonneg {G X P Y Y' : MpInt} {ret : Int} (hX : X.Shape) (hP : P.Valid)
    (hPs : P.sign ≠ Layout.mpNeg) (hP1 : 1 < P.mag) (hXs : X.sign ≠ Layout.mpNeg) (hbug : ¬ Lossy2k P)
    (h : ExptmodPost G X P Y Y' ret) : ret = Layout.mpOkay ∧ Y'.Valid ∧ Y'.val = G.val ^ X.mag % P.val :=
  (h.xpos hPs hXs).spec hX hP hPs hP1 hbug

theorem withSign_mag (X : MpInt) (s : Nat) : (X.withSign s).mag = X.mag := rfl

theorem withSign_shape {X : MpInt} (hX : X.Shape) (s : Nat) : (X.withSign s).Shape :=
  { len := hX.len, used_le := hX.used_le, alloc_lt := hX.alloc_lt, digit_lt := hX.digit_lt,
    high_zero := hX.high_zero }

/-- **`mp_exptmod`, `X < 0`**: with `G` invertible modulo `P` and `G ≥ 0` or `P` even,
`Y * G^|X| ≡ 1 (mod P)` and `0 ≤ Y < P`. -/
theorem ExptmodPost.spec_neg {G X P Y Y' : MpInt} {ret : Int} (hG : G.Valid) (hX : X.Shape) (hP : P.Valid)
    (hPs : P.sign ≠ Layout.mpNeg) (hP1 : 1 < P.mag) (hXs : X.sign = Layout.mpNeg) (hbug : ¬ Lossy2k P)
    (hg : Nat.gcd (invmodRem G P) P.mag = 1) (hsg : 0 ≤ G.val ∨ P.mag % 2 = 0)
    (h : ExptmodPost G X P Y Y' ret) :
    ret = Layout.mpOkay ∧ Y'.Valid ∧ (Y'.val * G.val ^ X.mag) % P.val = 1 := by
  obtain ⟨Gi0, Gi, r1, hi, _, hok⟩ := h.xneg hPs hXs
  have hPv := MpInt.val_pos_of_sign hPs
  obtain ⟨hr1, _, _, _, hinv⟩ := hi.spec_ok hG (by omega) hg hsg
  obtain ⟨hr, hv, hy⟩ := (hok hr1).spec (withSign_shape hX _) hP hPs hP1 hbug
  refine ⟨hr, hv, ?_⟩
  rw [hy, withSign_mag, Int.mul_emod, Int.emod_emod, ← Int.mul_emod, ← Int.mul_pow, int_pow_emod,
    Int.mul_comm Gi.val G.val, hinv, Int.one_pow, Int.emod_eq_of_lt (by decide) (by omega)]

/-- **`mp_exptmod`, `X < 0`, `G < 0`, `P` odd (the C's sign slip)**: `s_mp_invmod_fast` returns
`-G^-1`, so the result is the inverse of `(-G)^|X|`, not of `G^|X|`
(`mp_exptmod(-3, -1, 7) = 5`, while `(-3)^-1 ≡ 2`). -/
theorem ExptmodPost.spec_neg_odd {G X P Y Y' : MpInt} {ret : Int} (hG : G.Valid) (hX : X.Shape) (hP : P.Valid)
    (hPs : P.sign ≠ Layout.mpNeg) (hP1 : 1 < P.mag) (hXs : X.sign = Layout.mpNeg) (hbug : ¬ Lossy2k P)
    (hg : Nat.gcd (invmodRem G P) P.mag = 1) (hneg : G.val < 0) (hodd : P.mag % 2 = 1)
    (h : ExptmodPost G X P Y Y' ret) :
    ret = Layout.mpOkay ∧ Y'.Valid ∧ (Y'.val * (-G.val) ^ X.mag) % P.val = 1 := by
  obtain ⟨Gi0, Gi, r1, hi, _, hok⟩ := h.xneg hPs hXs
  have hPv := MpInt.val_pos_of_sign hPs
  obtain ⟨hr1, _, _, _, hinv, _⟩ := hi.spec_neg_odd hG (by omega) hg hneg hodd
  obtain ⟨hr, hv, hy⟩ := (hok hr1).spec (withSign_shape hX _) hP hPs hP1 hbug
  refine ⟨hr, hv, ?_⟩
  have hinv' : (Gi.val * -G.val) % P.val = 1 := by
    have e : Gi.val * -G.val = G.val * -Gi.val := by rw [Int.mul_neg, Int.mul_neg, Int.mul_comm]
    rw [e]; exact hinv
  rw [hy, withSign_mag, Int.mul_emod, Int.emod_emod, ← Int.mul_emod, ← Int.mul_pow, int_pow_emod,
    hinv', Int.one_pow, Int.emod_eq_of_lt (by decide) (by omega)]

end Exptmod

end Tom
