import Tom.Spec.Canon
import Tom.Spec.Mont
import Tom.Spec.DigitShift
import Tom.Spec.SMpSqrG5Step
import Tom.Spec.Ledger

/-!
# `mp_montgomery_reduce`'s rows: the model steps

The slow path of `bn_mp_montgomery_reduce.c` over `x`'s digit function `f` (the first
`D = 2 n->used + 1` digits, `x->used := D`): row `ix` adds `mu * n * radix^ix` with
`mu = x->dp[ix] * rho mod radix` (`Mont.redcT`), first column by column with a carry
(the inner loop), then by propagating the carry upwards. The four cuts' value premises
(`OH` outer head, `IH` inner head, `PH` propagation, the outer step `OH` at `ix + 1`) and one
lemma per row that stores or decides, in the forms the rows (`mredcg.rows.json`) write; then
what `mp_clamp`, `mp_rshd(x, n->used)` and the conditional `s_mp_sub` leave (`fin_lt`,
`fin_sub`: `Mont.RedcPost`).

Over the Ledger (`Tom/Spec/Ledger.lean`): `IH`/`PH` are books (`toBal`/`ofBal`, `md` in
the `aux` slot); a column is `Bal.mac` with the row identity `row_succ`, a propagation step
`Bal.carry`, the propagation bound `Bal.k_lt`; the clamp is `settle`, then `xfer_rshd` and
`xfer_ssub`.
-/

namespace Tom.MontRedStep

open MpInt
open Mont (upd natUpTo_upd redcT redcMu)
open SqrStepG5 (store high_zero)
open Ledger (Bal)

theorem eR : radix = 268435456 := rfl

/-! ## The cuts' value premises -/

/-- At the outer head (`ix`): rows below `ix` added. -/
structure OH (x n : MpInt) (rho : Nat) (f : Nat → Nat) (ix : Nat) : Prop where
  dig : ∀ j, f j < radix
  high : ∀ j, 2 * n.used + 1 ≤ j → f j = 0
  val : natUpTo f (2 * n.used + 1) = redcT x.mag n.mag rho ix

/-- At the inner head (`ix`, `iy`, `mu`, the carry `c` into digit `ix + iy`). -/
structure IH (x n : MpInt) (rho : Nat) (f : Nat → Nat) (ix iy md c : Nat) : Prop where
  dig : ∀ j, f j < radix
  high : ∀ j, 2 * n.used + 1 ≤ j → f j = 0
  md_eq : md = redcMu rho (redcT x.mag n.mag rho ix) ix
  md_lt : md < radix
  val : natUpTo f (2 * n.used + 1) + radix ^ (ix + iy) * c =
    redcT x.mag n.mag rho ix + radix ^ ix * (md * natUpTo n.digit iy)
  c_lt : c < radix

/-- In the propagation (row `ix` done but for the carry `c` into digit `k`). -/
structure PH (x n : MpInt) (rho : Nat) (f : Nat → Nat) (ix k c : Nat) : Prop where
  dig : ∀ j, f j < radix
  high : ∀ j, 2 * n.used + 1 ≤ j → f j = 0
  val : natUpTo f (2 * n.used + 1) + radix ^ k * c = redcT x.mag n.mag rho (ix + 1)
  c_lt : c < radix

section
variable {x n : MpInt} {rho : Nat} {f : Nat → Nat}

theorem upd_dig {f : Nat → Nat} (hf : ∀ j, f j < radix) (k v : Nat) (hv : v < radix) :
    ∀ j, upd f k v j < radix := fun j => by
  unfold upd; split
  · exact hv
  · exact hf j

theorem upd_high {f : Nat → Nat} {D k : Nat} (hf : ∀ j, D ≤ j → f j = 0) (hk : k < D) (v : Nat) :
    ∀ j, D ≤ j → upd f k v j = 0 := fun j hj => by
  rw [Mont.upd_ne f v (by omega)]; exact hf j hj

/-- `|x| < |n| R` puts `x` in the `2 n->used` digits below `D`. -/
theorem used_le (hx : x.Valid) (hn : n.Valid) (hlt : x.mag < n.mag * radix ^ n.used) :
    x.used ≤ 2 * n.used := by
  have h3 : n.mag * radix ^ n.used ≤ radix ^ n.used * radix ^ n.used :=
    Nat.mul_le_mul_right _ (Nat.le_of_lt (MpInt.mag_lt hn.toShape))
  rw [← Nat.pow_add, ← Nat.two_mul] at h3
  exact Ledger.used_le_of_lt hx (by omega)

theorem OH.start (hx : x.Valid) (hn : n.Valid) (hlt : x.mag < n.mag * radix ^ n.used) :
    OH x n rho x.digit 0 :=
  have hu := used_le hx hn hlt
  { dig := hx.digit_lt
    high := fun j hj => hx.high_zero j (by omega)
    val := by
      show _ = x.mag
      exact natUpTo_zeros x.digit x.used _ (by omega) fun j h1 _ => hx.high_zero j h1 }

/-- `IH` and `PH` as books over `D = 2 n->used + 1` (`md` in the `aux` slot). -/
theorem IH.toBal {ix iy md c : Nat} (h : IH x n rho f ix iy md c) :
    Bal (2 * n.used + 1) (2 * n.used + 1) f (ix + iy) c
      (redcT x.mag n.mag rho ix + radix ^ ix * (md * natUpTo n.digit iy)) radix
      (md = redcMu rho (redcT x.mag n.mag rho ix) ix ∧ md < radix) :=
  .ofAll h.dig h.val h.c_lt ⟨h.md_eq, h.md_lt⟩

theorem IH.ofBal {ix iy md c : Nat} (b : Bal (2 * n.used + 1) (2 * n.used + 1) f (ix + iy) c
      (redcT x.mag n.mag rho ix + radix ^ ix * (md * natUpTo n.digit iy)) radix
      (md = redcMu rho (redcT x.mag n.mag rho ix) ix ∧ md < radix))
    (hi : ∀ j, 2 * n.used + 1 ≤ j → f j = 0) : IH x n rho f ix iy md c :=
  { dig := b.dig_all hi, high := hi, md_eq := b.aux.1, md_lt := b.aux.2, val := b.val, c_lt := b.c_lt }

theorem PH.toBal {ix k c : Nat} (h : PH x n rho f ix k c) :
    Bal (2 * n.used + 1) (2 * n.used + 1) f k c (redcT x.mag n.mag rho (ix + 1)) radix True :=
  .ofAll h.dig h.val h.c_lt trivial

theorem PH.ofBal {ix k c : Nat} (b : Bal (2 * n.used + 1) (2 * n.used + 1) f k c (redcT x.mag n.mag rho (ix + 1)) radix True)
    (hi : ∀ j, 2 * n.used + 1 ≤ j → f j = 0) : PH x n rho f ix k c :=
  { dig := b.dig_all hi, high := hi, val := b.val, c_lt := b.c_lt }

/-- `mu := x->dp[ix] rho & MP_MASK` (`mu`): the inner loop starts. -/
theorem OH.row {ix : Nat} (h : OH x n rho f ix) (hix : ix < 2 * n.used + 1) :
    IH x n rho f ix 0 (f ix * rho % 268435456) 0 :=
  IH.ofBal (.ofAll h.dig (by rw [h.val]; rfl) radix_pos
    ⟨by unfold redcMu; rw [← h.val, Mont.natUpTo_digit f h.dig _ ix hix]; rfl, Nat.mod_lt _ (by decide)⟩) h.high

/-- One column (`il`): `r := mu n[iy] + u + x[ix + iy]`, `x[ix + iy] := r mod R`, `u := r / R`. -/
theorem IH.step {ix iy md c : Nat} (h : IH x n rho f ix iy md c) (hdn : ∀ j, n.digit j < radix)
    (hk : ix + iy < 2 * n.used + 1) :
    IH x n rho (upd f (ix + iy) ((n.digit iy * md + f (ix + iy) + c) % 268435456)) ix (iy + 1) md
      ((n.digit iy * md + f (ix + iy) + c) / 268435456) :=
  IH.ofBal ((h.toBal.mac hk hk (hdn iy) h.md_lt).retarget (Ledger.row_succ _ _ _ _ _)) (upd_high h.high hk _)

theorem IH.row_end {ix md c : Nat} (h : IH x n rho f ix n.used md c) :
    natUpTo f (2 * n.used + 1) + radix ^ (ix + n.used) * c = redcT x.mag n.mag rho (ix + 1) := by
  rw [h.val, h.md_eq]
  show _ = redcT x.mag n.mag rho ix + redcMu rho (redcT x.mag n.mag rho ix) ix * n.mag * radix ^ ix
  have : natUpTo n.digit n.used = n.mag := rfl
  rw [this, Nat.mul_comm (radix ^ ix), Nat.mul_assoc]

/-- The row's last column (`ie`, `ip`): the carry left goes to the propagation. -/
theorem IH.last {ix iy md c : Nat} (h : IH x n rho f ix iy md c) (hdn : ∀ j, n.digit j < radix)
    (hk : ix + iy < 2 * n.used + 1) (hiy : iy + 1 = n.used) :
    PH x n rho (upd f (ix + iy) ((n.digit iy * md + f (ix + iy) + c) % 268435456)) ix (ix + n.used)
      ((n.digit iy * md + f (ix + iy) + c) / 268435456) :=
  have h' := IH.step h hdn hk
  { dig := h'.dig, high := h'.high, c_lt := h'.c_lt
    val := by rw [hiy] at h'; exact h'.row_end }

/-- A carry is left only below `D`: the propagation stays in the array. -/
theorem PH.k_lt {ix k c : Nat} (h : PH x n rho f ix k c) (hn : n.Valid)
    (hlt : x.mag < n.mag * radix ^ n.used) (hix : ix < n.used) (hc : c ≠ 0) : k < 2 * n.used + 1 :=
  h.toBal.k_lt (by have := Mont.redcT_lt x.mag n.mag rho n.used (MpInt.mag_lt hn.toShape) hlt (ix + 1) (by omega); omega) hc

/-- One propagation step (`pl`, `pe`): `x[k] += u`, `u := x[k] >> 28`, `x[k] &= MP_MASK`. -/
theorem PH.carry {ix k c : Nat} (h : PH x n rho f ix k c) (hk : k < 2 * n.used + 1) :
    PH x n rho (upd f k ((f k + c) % 268435456)) ix (k + 1) ((f k + c) / 268435456) :=
  PH.ofBal (h.toBal.carry hk hk) (upd_high h.high hk _)

/-- No carry left: the next row. -/
theorem PH.done {ix k c : Nat} (h : PH x n rho f ix k c) (hc : c = 0) : OH x n rho f (ix + 1) :=
  { dig := h.dig, high := h.high, val := h.toBal.close hc }

theorem OH.cast {i j : Nat} (h : OH x n rho f i) (e : i = j) : OH x n rho f j := e ▸ h

end

/-! ## The result -/

/-- `x` as `mp_clamp` is handed it: `used = D`, the digits `f`. -/
def xOf (x n : MpInt) (f : Nat → Nat) : MpInt := MpInt.ofDigits (2 * n.used + 1) x.alloc x.sign f

theorem xOf_shape {x n : MpInt} {rho : Nat} {f : Nat → Nat} (hx : x.Valid) (h : OH x n rho f n.used)
    (hD : 2 * n.used + 1 ≤ x.alloc) : (xOf x n f).Shape :=
  ofDigits_shape hD hx.alloc_lt (fun j _ => h.dig j) (fun j hj _ => h.high j hj)

theorem xOf_mag {x n : MpInt} {rho : Nat} {f : Nat → Nat} (h : OH x n rho f n.used)
    (hD : 2 * n.used + 1 ≤ x.alloc) : (xOf x n f).mag = redcT x.mag n.mag rho n.used := by
  show natUpTo (xOf x n f).digit (2 * n.used + 1) = _
  rw [natUpTo_congr (2 * n.used + 1) (e := f) (fun j hj => by
    show (MpInt.ofDigits _ x.alloc _ f).digit j = f j; rw [MpInt.ofDigits_digit, if_pos (by omega)]), h.val]

/-- What `mp_clamp` and `mp_rshd(x, n->used)` leave: `T / R`, valid, `x`'s `alloc`, `x`'s sign
unless zero. -/
structure Mid (x n : MpInt) (rho : Nat) (x3 : MpInt) : Prop where
  valid : x3.Valid
  alloc : x3.alloc = x.alloc
  mag : x3.mag = redcT x.mag n.mag rho n.used / radix ^ n.used
  sign : x3.sign = if x3.used = 0 then Layout.mpZpos else x.sign

/-- `|n| > 0` from REDC's input range. -/
theorem npos {x n : MpInt} (hlt : x.mag < n.mag * radix ^ n.used) : 0 < n.mag := by
  rcases Nat.eq_zero_or_pos n.mag with h0 | h0
  · rw [h0, Nat.zero_mul] at hlt; omega
  · exact h0

theorem nu_pos {x n : MpInt} (hlt : x.mag < n.mag * radix ^ n.used) : 0 < n.used := by
  rcases Nat.eq_zero_or_pos n.used with h0 | h0
  · have := npos hlt; rw [MpInt.mag_used_zero h0] at this; omega
  · exact h0

theorem mid {x n x2 x3 : MpInt} {rho : Nat} {f : Nat → Nat} (hx : x.Valid) (hn : n.Valid)
    (hlt : x.mag < n.mag * radix ^ n.used) (h : OH x n rho f n.used) (hD : 2 * n.used + 1 ≤ x.alloc)
    (hc : ClampPost (xOf x n f) x2) (hr : RshdPost x2 n.used x3) : Mid x n rho x3 :=
  have r := Ledger.xfer_rshd (Ledger.settle hD hx.alloc_lt hx.sign_ok (fun j _ => h.dig j)
    (fun j hj _ => h.high j hj) h.val hc) (nu_pos hlt) hr
  ⟨r.valid, r.alloc, r.mag, r.sign⟩

/-- `|x| < |n|`: `mp_montgomery_reduce` returns `x`. -/
theorem Mid.fin_lt {x n x3 : MpInt} {rho : Nat} (h : Mid x n rho x3) (hlt : x3.mag < n.mag) :
    Mont.RedcPost x n rho x3 :=
  { valid := h.valid, alloc := h.alloc, sign := h.sign
    mag := by unfold Mont.redc Mont.montOut; rw [if_neg (by rw [← h.mag]; omega), h.mag] }

/-- `|x| ≥ |n|`: `s_mp_sub(x, n, x)`'s contract holds (`Std.sSubA`'s residue). -/
theorem Mid.ge {x n x3 : MpInt} {rho : Nat} (h : Mid x n rho x3) (hn : n.Valid) (hge : ¬ x3.mag < n.mag) :
    n.used ≤ x3.used :=
  MpInt.used_le_of_mag_le h.valid.toShape hn (by omega)

/-- `|x| ≥ |n|`: `s_mp_sub(x, n, x)` leaves the REDC result. -/
theorem Mid.fin_sub {x n x3 x4 : MpInt} {rho : Nat} (h : Mid x n rho x3) (hn : n.Valid) (hnp : 0 < n.mag)
    (hge : ¬ x3.mag < n.mag) (hs : SSubPost x3 n x3 x4) : Mont.RedcPost x n rho x4 := by
  have s := Ledger.xfer_ssub ⟨h.valid, h.alloc, h.mag, h.sign⟩ hn (by rw [← h.mag]; omega) hs
  refine { valid := s.valid, alloc := s.alloc, mag := ?_, sign := s.sign }
  unfold Mont.redc Mont.montOut; rw [if_pos (by rw [← h.mag]; omega), s.mag]

end Tom.MontRedStep
