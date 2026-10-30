import Tom.Spec.SMpExptmodStep
import Tom.Spec.SMpExptmodFastStep
import Tom.Spec.ModShape
import Tom.Spec.CopyGStep

/-!
# `mp_exptmod`: the model steps

`bn_mp_exptmod.c` at `0x80000e94` (frame 96: `tmpG` at `sp`, `tmpX` at `sp + 24`):

* `P->sign == MP_NEG`: `MP_VAL` (`post_pneg`);
* `X->sign == MP_NEG`: `mp_init_multi(&tmpG, &tmpX, NULL)` (both `zeroN MP_PREC`),
  `mp_invmod(G, P, &tmpG)` (`InvmodPost`; on an error `goto LBL_ERR`), `mp_abs(X, &tmpX)`, the recursive `mp_exptmod(&tmpG, &tmpX, P, Y)` (`neg_rec`: its
  Post at `|X|` is the nonnegative case for `X.withSign MP_ZPOS`, `congrNN`),
  `mp_clear_multi` (`post_xneg`);
* else the dispatch (`post_xpos`): `mp_reduce_is_2k_l(P) == MP_YES` → `s_mp_exptmod(…, 1)`
  (`nn_l2k`); `dr = mp_dr_is_modulus(P) ? 1 : 0`, then `mp_reduce_is_2k(P) ? 2 : 0` (`drC`);
  `MP_IS_ODD(P) || dr != 0` → `s_mp_exptmod_fast(…, dr)` (`nn_fast`); else
  `s_mp_exptmod(…, 0)` (`nn_barrett`). All three are tail calls in the image.

The Spec (`Exptmod.ExptmodPost`) states the dispatch over `is2kL`, `drIsMod`, `is2k` "by
meaning"; the frozen contracts (`Api/Reduce2kL.lean`, `Api/DrIsModulus.lean`,
`Api/Reduce2k.lean`) return `isReduce2kL`, `IsDrModulus`, `isReduce2k` (`Spec/ModShape.lean`):
`is2kL_iff`, `drIsMod_iff`, `is2k_iff` prove them the same (`mag_testBit`: the bits of `|a|` are
its digits' bits). `MP_IS_ODD(P)` (`used > 0 && dp[0] & 1`) is `odd_iff`.

Callee Posts: the three predicates and `mp_abs` (`AbsPost`) as their frozen contracts give them,
`mp_init_multi` (`zeroN defPrec`); no contract yet, stated over the Spec Post: `mp_invmod`
(`InvmodPost`), `s_mp_exptmod` (`SMpExptmodStep.Out`), `s_mp_exptmod_fast` (`SExptmodFastPost`),
and `mp_exptmod` itself for the recursion (`ExptmodPost`).
-/

namespace Tom.MpExptmodStep

open MpInt Ledger Exptmod Mont

/-! ## The predicates: the leaf contracts' functions are the Spec's -/

theorem mask_eq : Layout.mpMask = radix - 1 := rfl

theorem countP_eq_countMax (f : Nat → Nat) :
    ∀ n, (List.range n).countP (fun i => f i == radix - 1) = countMax f n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.countP_append, countP_eq_countMax f n, countMax, mask_eq]
    simp only [List.countP_cons, List.countP_nil, Nat.zero_add, beq_iff_eq]

/-- `mp_reduce_is_2k_l`. -/
theorem is2kL_iff (a : MpInt) : is2kL a = true ↔ isReduce2kL a = 1 := by
  unfold is2kL isReduce2kL
  rw [countP_eq_countMax]
  by_cases h0 : a.used = 0
  · simp [h0]
  · by_cases h1 : a.used = 1
    · simp [h1]
    · simp only [h0, h1, if_false]
      split <;> simp_all

/-- `mp_dr_is_modulus`. -/
theorem drIsMod_iff (a : MpInt) : drIsMod a = true ↔ IsDrModulus a := by
  unfold drIsMod IsDrModulus
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, mask_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i hi1 hi2 => (h2 i hi2).resolve_left (by omega)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i hi => if h : i = 0 then Or.inl h else Or.inr (h2 i (by omega) hi)⟩

/-- The bits of `Σ f j radix^j` are the digits' bits. -/
theorem natUpTo_testBit (f : Nat → Nat) (hf : ∀ j, f j < radix) :
    ∀ n ix, ix < Layout.digitBits * n →
      (natUpTo f n).testBit ix = (f (ix / Layout.digitBits)).testBit (ix % Layout.digitBits)
  | 0, ix, h => absurd h (by simp)
  | n + 1, ix, h => by
    have hl : natUpTo f n < 2 ^ (Layout.digitBits * n) := by
      rw [Nat.pow_mul]; exact natUpTo_lt f hf n
    have e : natUpTo f (n + 1) = 2 ^ (Layout.digitBits * n) * f n + natUpTo f n := by
      show natUpTo f n + radix ^ n * f n = _
      rw [show radix ^ n = 2 ^ (Layout.digitBits * n) by rw [Nat.pow_mul], Nat.add_comm]
    rw [e, Nat.testBit_two_pow_mul_add _ hl]
    split
    · exact natUpTo_testBit f hf n ix (by omega)
    · have hq : ix / Layout.digitBits = n := by
        simp only [Layout.digitBits] at *; omega
      have hr : ix % Layout.digitBits = ix - Layout.digitBits * n := by
        simp only [Layout.digitBits] at *; omega
      rw [hq, hr]

theorem mag_testBit {a : MpInt} (ha : a.Shape) {ix : Nat} (h : ix < Layout.digitBits * a.used) :
    a.mag.testBit ix = (a.digit (ix / Layout.digitBits)).testBit (ix % Layout.digitBits) :=
  natUpTo_testBit a.digit ha.digit_lt a.used ix h

theorem nbits_le_used {a : MpInt} (ha : a.Shape) : nbits a.mag ≤ Layout.digitBits * a.used := by
  have := MpInt.mag_lt ha
  rw [show radix ^ a.used = 2 ^ (Layout.digitBits * a.used) by rw [Nat.pow_mul]] at this
  exact bitLen_le this

/-- `mp_reduce_is_2k`. -/
theorem is2k_iff {a : MpInt} (ha : a.Valid) : is2k a = true ↔ isReduce2k a = 1 := by
  have hc : countBits a = nbits a.mag := countBits_spec ha
  have hn := nbits_le_used ha.toShape
  have key : (∀ x, x < nbits a.mag → x < Layout.digitBits ∨ a.mag.testBit x = true) ↔
      (∀ ix, ix < nbits a.mag → Layout.digitBits ≤ ix →
        (a.digit (ix / Layout.digitBits)).testBit (ix % Layout.digitBits) = true) := by
    constructor
    · intro h ix hix hge
      rw [← mag_testBit ha.toShape (by omega)]
      exact (h ix hix).resolve_left (by omega)
    · intro h x hx
      by_cases hlt : x < Layout.digitBits
      · exact Or.inl hlt
      · exact Or.inr (by rw [mag_testBit ha.toShape (by omega)]; exact h x hx (by omega))
  by_cases h0 : a.used = 0
  · unfold is2k isReduce2k; simp [h0]
  · by_cases h1 : a.used = 1
    · unfold is2k isReduce2k; simp [h1]
    · have hL : is2k a = true ↔ (∀ x, x < nbits a.mag → x < Layout.digitBits ∨ a.mag.testBit x = true) := by
        unfold is2k; simp [h0, h1]
      have hR : isReduce2k a = (if (∀ ix, ix < nbits a.mag → Layout.digitBits ≤ ix →
          (a.digit (ix / Layout.digitBits)).testBit (ix % Layout.digitBits) = true) then 1 else 0) := by
        unfold isReduce2k; rw [hc, if_neg h0, if_neg h1]
      rw [hL, key, hR]
      split
      · exact ⟨fun _ => rfl, fun _ => by assumption⟩
      · exact ⟨fun h => absurd h (by assumption), fun h => absurd h (by decide)⟩

/-- `MP_IS_ODD(P)`: `P->used > 0 && (P->dp[0] & 1) == 1`. -/
theorem odd_iff {P : MpInt} (hP : P.Shape) : (0 < P.used ∧ P.digit 0 % 2 = 1) ↔ P.mag % 2 = 1 := by
  have hm : P.mag % 2 = P.digit 0 % 2 := by
    rw [← MpInt.mag_mod_radix hP, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ radix)]
  constructor
  · rintro ⟨_, h⟩; rw [hm]; exact h
  · intro h
    refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, by rw [← hm]; exact h⟩
    rw [MpInt.mag_used_zero h0] at h; exact absurd h (by decide)

/-- The C's `dr`. -/
def drC (P : MpInt) : Nat := if IsDrModulus P then 1 else if isReduce2k P = 1 then 2 else 0

theorem drC_eq {P : MpInt} (hP : P.Valid) : drC P = drMode P := by
  unfold drC drMode
  by_cases h1 : IsDrModulus P
  · rw [if_pos h1, if_pos ((drIsMod_iff P).2 h1)]
  · rw [if_neg h1, if_neg (fun e => h1 ((drIsMod_iff P).1 e))]
    by_cases h2 : isReduce2k P = 1
    · rw [if_pos h2, if_pos ((is2k_iff hP).2 h2)]
    · rw [if_neg h2, if_neg (fun e => h2 ((is2k_iff hP).1 e))]

/-! ## `X` enters only through its digits -/

theorem winRes_congr {red : Nat → Nat} {X X' : MpInt} (hd : X'.digit = X.digit) (hu : X'.used = X.used)
    (m1 res0 : Nat) : winRes red X' m1 res0 = winRes red X m1 res0 := by
  unfold winRes wsize MpInt.mag; rw [hd, hu]

section
variable {G X X' P Y Y' : MpInt} {ret : Int}

theorem congrS (hd : X'.digit = X.digit) (hu : X'.used = X.used) (h : SExptmodPost G X' P Y') :
    SExptmodPost G X P Y' :=
  ⟨h.valid, by rw [h.mag, winRes_congr hd hu], h.sign⟩

theorem congrF {dr : Nat} (hd : X'.digit = X.digit) (hu : X'.used = X.used)
    (h : SExptmodFastPost G X' P Y' dr) : SExptmodFastPost G X P Y' dr where
  valid := h.valid
  sign := h.sign
  mont e := by rw [h.mont e, winRes_congr hd hu]
  dr e := by rw [h.dr e, winRes_congr hd hu]
  r2k e := by rw [h.r2k e, winRes_congr hd hu]

theorem congrNN (hd : X'.digit = X.digit) (hu : X'.used = X.used) (h : ExptmodNNPost G X' P Y Y' ret) :
    ExptmodNNPost G X P Y Y' ret where
  l2k e := ⟨(h.l2k e).1, congrS hd hu (h.l2k e).2⟩
  fast e o := ⟨(h.fast e o).1, congrF hd hu (h.fast e o).2⟩
  zero := h.zero
  barrett e1 e2 e3 e4 := ⟨(h.barrett e1 e2 e3 e4).1, congrS hd hu (h.barrett e1 e2 e3 e4).2⟩

/-! ## The dispatch (`X ≥ 0`) -/

theorem pos_of_2kL (hP : P.Valid) (hl : isReduce2kL P = 1) : 0 < P.mag := by
  have hu : 0 < P.used := by
    unfold isReduce2kL at hl; by_cases h : P.used = 0
    · rw [if_pos h] at hl; exact absurd hl (by decide)
    · omega
  exact hP.mag_pos hu

/-- `mp_reduce_is_2k_l(P) == MP_YES`: `return s_mp_exptmod(G, X, P, Y, 1)`. -/
theorem nn_l2k (hP : P.Valid) (hl : isReduce2kL P = 1) (hs : SMpExptmodStep.Out G X P Y Y' 1 ret) :
    ExptmodNNPost G X P Y Y' ret where
  l2k _ := hs.pos (pos_of_2kL hP hl)
  fast e := absurd ((is2kL_iff P).2 hl) (by rw [e]; decide)
  zero e := absurd ((is2kL_iff P).2 hl) (by rw [e]; decide)
  barrett e := absurd ((is2kL_iff P).2 hl) (by rw [e]; decide)

/-- `MP_IS_ODD(P) || dr != 0`: `return s_mp_exptmod_fast(G, X, P, Y, dr)`. -/
theorem nn_fast (hP : P.Valid) (hl : isReduce2kL P ≠ 1) (hf : (0 < P.used ∧ P.digit 0 % 2 = 1) ∨ drC P ≠ 0)
    (hs : ret = Layout.mpOkay ∧ SExptmodFastPost G X P Y' (drC P)) : ExptmodNNPost G X P Y Y' ret where
  l2k e := absurd ((is2kL_iff P).1 e) hl
  fast _ _ := by rw [← drC_eq hP]; exact hs
  zero _ e2 e3 := by
    rcases hf with h | h
    · rw [(odd_iff hP.toShape).1 h] at e2; exact absurd e2 (by decide)
    · rw [drC_eq hP] at h; exact absurd e3 h
  barrett _ e2 e3 := by
    rcases hf with h | h
    · rw [(odd_iff hP.toShape).1 h] at e2; exact absurd e2 (by decide)
    · rw [drC_eq hP] at h; exact absurd e3 h

/-- Else: `return s_mp_exptmod(G, X, P, Y, 0)` (Barrett). -/
theorem nn_barrett (hP : P.Valid) (hl : isReduce2kL P ≠ 1) (hf : ¬ ((0 < P.used ∧ P.digit 0 % 2 = 1) ∨ drC P ≠ 0))
    (hs : SMpExptmodStep.Out G X P Y Y' 0 ret) : ExptmodNNPost G X P Y Y' ret where
  l2k e := absurd ((is2kL_iff P).1 e) hl
  fast _ o := by
    rcases o with h | h
    · exact absurd (Or.inl ((odd_iff hP.toShape).2 h)) hf
    · exact absurd (Or.inr (by rw [drC_eq hP]; exact h)) hf
  zero _ _ _ h := hs.zero rfl h
  barrett _ _ _ h := hs.pos h

/-! ## `mp_exptmod` -/

/-- `P->sign == MP_NEG`: `return MP_VAL`. -/
theorem post_pneg (hP : P.sign = Layout.mpNeg) : ExptmodPost G X P Y Y Layout.mpVal where
  pneg _ := ⟨rfl, rfl⟩
  xpos h := absurd hP h
  xneg h := absurd hP h

/-- `X->sign != MP_NEG`: the dispatch. -/
theorem post_xpos (hP : P.sign ≠ Layout.mpNeg) (hX : X.sign ≠ Layout.mpNeg) (h : ExptmodNNPost G X P Y Y' ret) :
    ExptmodPost G X P Y Y' ret where
  pneg e := absurd e hP
  xpos _ _ := h
  xneg _ e := absurd e hX

/-- `mp_abs(a, &t)` into a temporary whose digits are all zero: the digit twin, `MP_ZPOS`. -/
theorem absD_zero {a t B : MpInt} (ha : a.Shape) (hz : ∀ i, B.digit i = 0) (h : AbsPost a B t) :
    t.digit = a.digit ∧ t.used = a.used ∧ t.sign = Layout.mpZpos :=
  ⟨funext fun i => by
    rw [h.digit]; split
    · rfl
    · rw [hz i, ha.high_zero i (by omega)]; split <;> rfl, h.used, h.sign⟩

/-- The fresh `tmpX` as the growing `mp_copy` inside `mp_abs` leaves it before the copy: zero digits. -/
theorem copyIn_zero (a : MpInt) (i : Nat) : (copyIn a (MpInt.zeroN defPrec)).digit i = 0 := by
  unfold copyIn; split
  · rw [MpInt.growTo_digit (MpInt.zeroN_valid (by decide)).toShape (by omega)]; exact MpInt.zeroN_digit _ i
  · exact MpInt.zeroN_digit _ i

/-- `mp_abs(X, &tmpX)` into the fresh `tmpX` (growing it), then `mp_exptmod(&tmpG, &tmpX, P, Y)`: the
nonnegative case at `|X|`. -/
theorem neg_rec {Gi tX : MpInt} (hX : X.Shape) (hP : P.sign ≠ Layout.mpNeg)
    (ha : AbsPost X (copyIn X (MpInt.zeroN defPrec)) tX) (hr : ExptmodPost Gi tX P Y Y' ret) :
    ExptmodNNPost Gi (X.withSign Layout.mpZpos) P Y Y' ret :=
  have d := absD_zero hX (copyIn_zero X) ha
  congrNN d.1 d.2.1 (hr.xpos hP (by rw [d.2.2]; decide))

/-- `X->sign == MP_NEG`: `mp_invmod(G, P, &tmpG)` (an error: `goto LBL_ERR`, returned), then
`neg_rec`; `mp_clear_multi`. -/
theorem post_xneg {Gi0 Gi : MpInt} {r1 : Int} (hP : P.sign ≠ Layout.mpNeg) (hX : X.sign = Layout.mpNeg)
    (hi : InvmodPost G P Gi0 Gi r1) (herr : r1 ≠ Layout.mpOkay → ret = r1 ∧ Y' = Y)
    (hok : r1 = Layout.mpOkay → ExptmodNNPost Gi (X.withSign Layout.mpZpos) P Y Y' ret) :
    ExptmodPost G X P Y Y' ret where
  pneg e := absurd e hP
  xpos _ e := absurd hX e
  xneg _ _ := ⟨Gi0, Gi, r1, hi, herr, hok⟩

end

end Tom.MpExptmodStep
