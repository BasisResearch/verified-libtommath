import Tom.Spec.MulFastGStep
import Tom.Spec.Reduce

/-!
# `s_mp_mul_high_digs_fast(a, b, a, digs)` with growth: the model steps

The high comba multiplier (`bn_s_mp_mul_high_digs_fast.c`) in place: `mp_grow(a, pa)`
(`pa = a->used + b->used`) when `a->alloc < pa`, then the columns `digs .. pa - 1` of
`Spec/Mul.lean`'s column model with the carry starting from zero at `digs` (`hc`: the columns
shifted by `digs`, `Reduce.highFastDigit`), stored in `W[ix]`; `memcpy(a->dp + digs, W + digs,
4 (pa - digs))`, `a->used := pa` (no `MP_ZERO_DIGITS`: in place `olduse = a->used ≤ pa`),
`mp_clamp(a)`.

* `OH` (a column head, `ix ≥ digs`), `IH` (the inner head `6cc8`), `SH` (the store point `6ce4`):
  `SH.store` (the store `W[ix]` and the carry, rows' literal forms), `OH.start`, `IH.step`,
  `IH.last`, `OH.empty` (an empty column);
* `hfRes a b A digs`: what `mp_clamp` is handed (`A` the destination after `mp_grow`), its digits
  after `memcpy` (`hf_fill`, `hf_fill0`), `hf_post`: `MulHighFastPost` from `mp_clamp`'s post,
  `hf_out`: the value (`MulHighFastPost.spec`).
-/

namespace Tom.MulHighFastGStep

open MpInt Tom.MulFastGStep Tom.Reduce
open Mont (upd)

/-- The columns from `digs` on (`highFastDigit`'s). -/
abbrev hc (a b : MpInt) (dg : Nat) : Nat → Nat := fun k => cl a b (dg + k)

/-- A column head `ix ≥ digs`: the high columns below `ix` stored in `g`, `w` the carry into `ix`. -/
structure OH (a b : MpInt) (dg ix w : Nat) (g : Nat → Nat) : Prop where
  le : dg ≤ ix
  w_eq : w = combaW (hc a b dg) (ix - dg)
  g_eq : ∀ j, dg ≤ j → j < ix → g j = combaD (hc a b dg) (j - dg)

/-- The store point of column `ix`: its sum in `w`. -/
structure SH (a b : MpInt) (dg ix w : Nat) (g : Nat → Nat) : Prop where
  le : dg ≤ ix
  w_eq : w = combaW (hc a b dg) (ix - dg) + cl a b ix
  g_eq : ∀ j, dg ≤ j → j < ix → g j = combaD (hc a b dg) (j - dg)

/-- Inside column `ix`, after `iz` of its `iy` products. -/
structure IH (a b : MpInt) (dg ix tx ty iy iz w : Nat) (g : Nat → Nat) : Prop where
  le : dg ≤ ix
  ub1 : 1 ≤ b.used
  tx_eq : tx = combaTx b.used ix
  ty_eq : ty = combaTy b.used ix
  iy_eq : iy = combaIy a.used b.used ix
  iz_lt : iz < iy
  w_eq : w = combaW (hc a b dg) (ix - dg) + combaPart a.digit b.digit b.used ix iz
  g_eq : ∀ j, dg ≤ j → j < ix → g j = combaD (hc a b dg) (j - dg)

section
variable {a b : MpInt} {dg ix tx ty iy iz w : Nat} {g : Nat → Nat}

/-- The first column (`_W = 0`). -/
theorem OH.init (g : Nat → Nat) : OH a b dg dg 0 g :=
  ⟨Nat.le_refl _, by rw [Nat.sub_self]; rfl, fun _ h1 h2 => absurd h2 (by omega)⟩

theorem OH.cast {i j : Nat} (h : OH a b dg i w g) (e : i = j) : OH a b dg j w g := e ▸ h

theorem SH.cast {i j : Nat} (h : SH a b dg i w g) (e : i = j) : SH a b dg j w g := e ▸ h

/-- The inner loop's set-up. -/
theorem OH.start (h : OH a b dg ix w g) (hub : 1 ≤ b.used) (htx : tx = combaTx b.used ix)
    (hty : ty = combaTy b.used ix) (hiy : iy = combaIy a.used b.used ix) (h0 : 0 < iy) :
    IH a b dg ix tx ty iy 0 w g :=
  { le := h.le, ub1 := hub, tx_eq := htx, ty_eq := hty, iy_eq := hiy, iz_lt := h0
    w_eq := by rw [h.w_eq]; rfl, g_eq := h.g_eq }

theorem IH.iy_le (h : IH a b dg ix tx ty iy iz w g) : iy ≤ ty + 1 := by
  rw [h.iy_eq, h.ty_eq]; unfold combaIy; omega

theorem IH.txiy (h : IH a b dg ix tx ty iy iz w g) : tx + iy ≤ a.used := by
  have := h.iz_lt
  rw [h.iy_eq, h.tx_eq] at *; unfold combaIy at *; omega

theorem IH.ty_lt (h : IH a b dg ix tx ty iy iz w g) : ty < b.used := by
  have := h.ub1; rw [h.ty_eq]; unfold combaTy; omega

/-- One product (`il`). -/
theorem IH.step (h : IH a b dg ix tx ty iy iz w g) (hlt : iz + 1 < iy) :
    IH a b dg ix tx ty iy (iz + 1) (w + a.digit (tx + iz) * b.digit (ty - iz)) g :=
  { le := h.le, ub1 := h.ub1, tx_eq := h.tx_eq, ty_eq := h.ty_eq, iy_eq := h.iy_eq, iz_lt := hlt, g_eq := h.g_eq
    w_eq := by rw [combaPart_succ, h.w_eq, h.tx_eq, h.ty_eq]; omega }

/-- A column's last product (`ie`): the column's sum. -/
theorem IH.last (h : IH a b dg ix tx ty iy iz w g) (he : iz + 1 = iy) :
    SH a b dg ix (w + a.digit (tx + iz) * b.digit (ty - iz)) g := by
  have hc := colC_eq a.digit b.digit a.used b.used ix h.ub1
  unfold colC at hc
  refine ⟨h.le, ?_, h.g_eq⟩
  rw [h.w_eq, Nat.add_assoc, h.tx_eq, h.ty_eq, ← combaPart_succ, he, h.iy_eq]; exact congrArg _ hc

/-- An empty column. -/
theorem OH.empty (h : OH a b dg ix w g) (hz : cl a b ix = 0) : SH a b dg ix w g :=
  ⟨h.le, by rw [hz, h.w_eq]; rfl, h.g_eq⟩

/-- The store `W[ix] := _W & MP_MASK`, `_W >>= 28`: the next column's head. -/
theorem SH.store (h : SH a b dg ix w g) :
    OH a b dg (ix + 1) (w / 268435456) (upd g ix (w % 268435456)) := by
  have hk : ix + 1 - dg = (ix - dg) + 1 := by have := h.le; omega
  have hc : hc a b dg (ix - dg) = cl a b ix := by
    show cl a b (dg + (ix - dg)) = _; rw [show dg + (ix - dg) = ix by have := h.le; omega]
  refine ⟨by have := h.le; omega, ?_, fun j h1 h2 => ?_⟩
  · rw [hk, h.w_eq, ← hc]; rfl
  · unfold upd; split
    · next e => subst e; rw [h.w_eq, ← hc]; rfl
    · next e => exact h.g_eq j h1 (by omega)

/-- The high columns leave `2 ^ 36` of room in 64 bits (`MP_MAXFAST`). -/
theorem hc_room (ha : a.ShapeU) (hb : b.ShapeU) (hm : min a.used b.used ≤ 256) (k : Nat) :
    hc a b dg k + 2 ^ 36 ≤ 2 ^ 64 := cl_room ha hb hm (dg + k)

theorem OH.w_lt (h : OH a b dg ix w g) (ha : a.ShapeU) (hb : b.ShapeU) (hm : min a.used b.used ≤ 256) :
    w < 2 ^ 36 := by
  rw [h.w_eq]; exact combaW_lt (hc_room ha hb hm) _

theorem SH.w_lt (h : SH a b dg ix w g) (ha : a.ShapeU) (hb : b.ShapeU) (hm : min a.used b.used ≤ 256) :
    w < 2 ^ 64 := by
  have h1 := combaW_lt (hc_room (dg := dg) ha hb hm) (ix - dg)
  have h2 := cl_room ha hb hm ix
  rw [h.w_eq]; omega

/-- `_W` stays in 64 bits through the column. -/
theorem IH.bound (h : IH a b dg ix tx ty iy iz w g) (ha : a.ShapeU) (hb : b.ShapeU)
    (hm : min a.used b.used ≤ 256) : w + a.digit (tx + iz) * b.digit (ty - iz) < 2 ^ 64 := by
  have hw := combaW_lt (hc_room (dg := dg) ha hb hm) (ix - dg)
  have hr := colC_room ha.digit_lt hb.digit_lt a.used b.used ix h.ub1 hm
  have hp := combaPart_le a.digit b.digit a.used b.used ix (iz + 1) (by have := h.iz_lt; rw [h.iy_eq] at this; omega)
  have e : w + a.digit (tx + iz) * b.digit (ty - iz) =
      combaW (hc a b dg) (ix - dg) + combaPart a.digit b.digit b.used ix (iz + 1) := by
    rw [combaPart_succ, h.w_eq, h.tx_eq, h.ty_eq]; omega
  rw [e]; omega

end

/-! ## The tail: `memcpy`, `mp_clamp` -/

/-- What `mp_clamp` is handed: `A`'s array with `highFastDigit`, `used := pa`. -/
def hfRes (a b A : MpInt) (dg : Nat) : MpInt :=
  { A with used := a.used + b.used, digits := (List.range A.alloc).map (highFastDigit a b A dg) }

/-- `Std.cpy` (`Api/StdLib.lean`, `memcpy`'s digit function), restated here (Spec does not import the
machine layer): `k` digits of `g` from `j` at `i` over `f`. -/
def cpyS (f g : Nat → Nat) (i j k : Nat) : Nat → Nat := fun t => if i ≤ t ∧ t < i + k then g (j + (t - i)) else f t

section tail
variable {a b A : MpInt} {dg w : Nat} {g : Nat → Nat}

theorem hfDigit_hi (hroom : a.used + b.used ≤ A.alloc) {j : Nat} (hj : A.alloc ≤ j) (hd : dg ≤ a.used + b.used) :
    highFastDigit a b A dg j = 0 := by
  simp [highFastDigit, show ¬ j < dg by omega, show ¬ j < a.used + b.used by omega]

theorem hfRes_digit (hroom : a.used + b.used ≤ A.alloc) (hd : dg ≤ a.used + b.used) :
    (hfRes a b A dg).digit = highFastDigit a b A dg := by
  funext i
  simp only [hfRes, MpInt.digit, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < A.alloc
  · simp [h]
  · have := hfDigit_hi (a := a) (b := b) hroom (show A.alloc ≤ i by omega) hd
    simp [h, this]

theorem hfRes_shape (hA : A.Shape) (hroom : a.used + b.used ≤ A.alloc) (hd : dg ≤ a.used + b.used) :
    (hfRes a b A dg).Shape :=
  { len := by simp [hfRes]
    used_le := hroom
    alloc_lt := hA.alloc_lt
    digit_lt := fun i => by rw [hfRes_digit hroom hd]; exact highFastDigit_lt hA dg i
    high_zero := fun i hi => by
      rw [hfRes_digit hroom hd]
      simp only [hfRes] at hi
      simp [highFastDigit, show ¬ i < dg by omega, show ¬ i < a.used + b.used by omega] }

/-- After `memcpy(a->dp + digs, W + digs, 4 (pa - digs))`: `mp_clamp`'s argument's digits. -/
theorem hf_fill (hA : A.Shape) (hu : A.used ≤ a.used + b.used) (h : OH a b dg (a.used + b.used) w g) (j : Nat) :
    highFastDigit a b A dg j = cpyS A.digit g dg dg (a.used + b.used - dg) j := by
  have hle := h.le
  unfold highFastDigit cpyS
  by_cases h1 : j < dg
  · rw [if_pos h1, if_neg (by omega)]
  · rw [if_neg h1]
    by_cases h2 : j < a.used + b.used
    · rw [if_pos h2, if_pos ⟨by omega, by omega⟩, show dg + (j - dg) = j by omega, h.g_eq j (by omega) h2]
    · rw [if_neg h2, if_neg (by omega), hA.high_zero j (by omega)]

/-- No column (`digs = pa`): the digits stay. -/
theorem hf_fill0 (hA : A.Shape) (hu : A.used ≤ a.used + b.used) (hd : dg = a.used + b.used) (j : Nat) :
    highFastDigit a b A dg j = A.digit j := by
  unfold highFastDigit
  by_cases h1 : j < dg
  · rw [if_pos h1]
  · rw [if_neg h1, if_neg (by omega), hA.high_zero j (by omega)]

/-- **`mp_clamp`'s result is `MulHighFastPost`** over the grown destination. -/
theorem hf_post {c4 : MpInt} (hA : A.Shape) (hroom : a.used + b.used ≤ A.alloc) (hd : dg ≤ a.used + b.used)
    (hcl : ClampPost (hfRes a b A dg) c4) : MulHighFastPost a b A c4 dg :=
  { alloc := hcl.alloc
    len := by rw [hcl.digits]; simp [hfRes]
    digit := by rw [hcl.digit, hfRes_digit hroom hd]
    used := by rw [hcl.used, hfRes_digit hroom hd]; rfl
    sign := by rw [hcl.sign]; rfl }

/-- **The contract's result**: valid, the old low digits plus the high product, `A`'s allocation,
the sign kept or reset. -/
theorem hf_out {c4 : MpInt} (ha : a.Shape) (hb : b.Shape) (hg : GrownOf a A) (hroom : a.used + b.used ≤ A.alloc)
    (hd : dg ≤ a.used + b.used) (hsign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg)
    (h : MulHighFastPost a b A c4 dg) :
    c4.Valid ∧ c4.mag = natUpTo a.digit dg + highProd a.digit b.digit a.used b.used dg ∧
      (c4.sign = Layout.mpZpos ∨ c4.sign = a.sign) := by
  have hsp := MulHighFastPost.spec (c := A) ha hb hg.shape hd hroom (by rw [hg.sign]; exact hsign) h
  refine ⟨hsp.1, by rw [hsp.2, hg.digit], ?_⟩
  rw [h.sign]; split
  · exact .inl rfl
  · exact .inr hg.sign

end tail

end Tom.MulHighFastGStep
