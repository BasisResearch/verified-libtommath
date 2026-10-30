import Tom.Spec.MulFastGStep

/-!
# `s_mp_sqr_fast` with growth: the model steps

The comba squarer (`bn_s_mp_sqr_fast.c`) over `Spec/Mul.lean`'s squaring column `colS`
(`cS a`): twice the half window `combaPart … (combaIyS u k)` plus the middle square in even
columns; the carry chain `combaW`/`combaD` (`colS_eq`, `sqrFast_digit`: the same digits as
`a · a`). `W[]` (digit function `g`) holds the columns done.

* `OS` (the column head `70a8`): the carry plus twice the window; `SF` (`70cc`): the column
  complete (`OS.even`: the square term added, `OS.odd`); `IS` (the inner head `7120`): `tx`,
  `ty`, `iy` the C's `MP_MIN`s, `iz` products in `c`;
* `SF.toI`/`SF.toO`: the next column's set-up (`win_lo`/`win_hi`: the window in the code's
  two regimes), `IS.step`/`IS.last`: one product, the last one (`_W + _W + W1`);
* the bounds the 64-bit `_W` needs (`colS_room`, `MP_WARRAY`: `a->used ≤ 256`);
* the tail: `mfRes a a A n` (`Spec/MulFastGStep.lean`) from the copied `W` (`sq_fill`), and the
  post `SqrFastPost` over the grown destination by `mf_post`.
-/

namespace Tom.SqrFastGStep

open MpInt Tom.MulFastGStep
open Mont (upd)

/-- The squaring columns. -/
abbrev cS (a : MpInt) : Nat → Nat := colS a.digit a.used

/-- Every squaring column leaves `2 ^ 36` of room in 64 bits. -/
theorem colS_room {a : MpInt} (ha : a.Shape) (hm : a.used ≤ 256) (k : Nat) : cS a k + 2 ^ 36 ≤ 2 ^ 64 := by
  by_cases h0 : a.used = 0
  · have : colS a.digit a.used k = 0 := by
      unfold colS combaIyS combaIy; rw [h0]
      simp only [Nat.zero_sub, Nat.min_eq_left (Nat.zero_le _), combaPart, sumTo]
      rw [ha.high_zero _ (by omega)]; simp
    show colS a.digit a.used k + 2 ^ 36 ≤ 2 ^ 64; omega
  by_cases hk : k < 2 * a.used
  · show colS a.digit a.used k + 2 ^ 36 ≤ 2 ^ 64
    rw [colS_eq _ _ _ (by omega) hk, ← colC_eq _ _ _ _ k (by omega)]
    exact colC_room ha.digit_lt ha.digit_lt _ _ k (by omega) (by omega)
  · have : colS a.digit a.used k = 0 := by
      have hiy : combaIyS a.used k = 0 := by unfold combaIyS combaIy combaTx combaTy; omega
      unfold colS; rw [hiy]
      simp only [combaPart, sumTo, Nat.mul_zero, Nat.zero_add]
      split
      · rw [ha.high_zero _ (by omega)]
      · rfl
    show colS a.digit a.used k + 2 ^ 36 ≤ 2 ^ 64; omega

/-- The window below `a->used` (`tx = 0`, `ty = k`, the half of `k + 1` terms). -/
theorem win_lo {u k : Nat} (hk : k < u) :
    combaTx u k = 0 ∧ combaTy u k = k ∧ combaIyS u k = (k + 1) / 2 := by
  unfold combaIyS combaIy combaTx combaTy; omega

/-- The window from `a->used` on (`ty = a->used - 1`). -/
theorem win_hi {u k : Nat} (hk : u ≤ k) (hk2 : k < 2 * u) :
    combaTx u k = k + 1 - u ∧ combaTy u k = u - 1 ∧ combaIyS u k = (2 * u - 1 - k) / 2 := by
  unfold combaIyS combaIy combaTx combaTy; omega

/-- At the column head: the carry plus twice the window; `W` below `ix`. -/
structure OS (a : MpInt) (ix w : Nat) (g : Nat → Nat) : Prop where
  w_eq : w = combaW (cS a) ix + 2 * combaPart a.digit a.digit a.used ix (combaIyS a.used ix)
  g_eq : ∀ j, j < ix → g j = combaD (cS a) j

/-- The column complete. -/
structure SF (a : MpInt) (ix w : Nat) (g : Nat → Nat) : Prop where
  w_eq : w = combaW (cS a) ix + cS a ix
  g_eq : ∀ j, j < ix → g j = combaD (cS a) j

/-- Inside column `ix`, after `iz` of its `iy` products (`c` their sum, `w` the carry in). -/
structure IS (a : MpInt) (ix tx ty iy iz w c : Nat) (g : Nat → Nat) : Prop where
  tx_eq : tx = combaTx a.used ix
  ty_eq : ty = combaTy a.used ix
  iy_eq : iy = combaIyS a.used ix
  iz_lt : iz < iy
  c_eq : c = combaPart a.digit a.digit a.used ix iz
  w_eq : w = combaW (cS a) ix
  g_eq : ∀ j, j < ix → g j = combaD (cS a) j

section
variable {a : MpInt} {ix tx ty iy iz w c : Nat} {g : Nat → Nat}

theorem OS.zero (g : Nat → Nat) : OS a 0 0 g :=
  ⟨by simp [combaIyS, combaIy, combaTx, combaTy, combaPart, sumTo, combaW], fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem OS.even (h : OS a ix w g) (he : ix % 2 = 0) : SF a ix (w + a.digit (ix / 2) * a.digit (ix / 2)) g :=
  ⟨by rw [h.w_eq]; show _ = _ + colS _ _ _; unfold colS; rw [if_pos he]; omega, h.g_eq⟩

theorem OS.odd (h : OS a ix w g) (he : ix % 2 = 1) : SF a ix w g :=
  ⟨by rw [h.w_eq]; show _ = _ + colS _ _ _; unfold colS; rw [if_neg (by omega)]; omega, h.g_eq⟩

theorem SF.next_g (h : SF a ix w g) : ∀ j, j < ix + 1 → upd g ix (w % 268435456) j = combaD (cS a) j := by
  intro j hj; unfold upd; split
  · next e => subst e; rw [h.w_eq]; rfl
  · next e => exact h.g_eq j (by omega)

theorem SF.carry (h : SF a ix w g) : w / 268435456 = combaW (cS a) (ix + 1) := by rw [h.w_eq]; rfl

/-- The next column's inner loop (`sn2`, `sc1`). -/
theorem SF.toI (h : SF a ix w g) (htx : tx = combaTx a.used (ix + 1)) (hty : ty = combaTy a.used (ix + 1))
    (hiy : iy = combaIyS a.used (ix + 1)) (h0 : 0 < iy) :
    IS a (ix + 1) tx ty iy 0 (w / 268435456) 0 (upd g ix (w % 268435456)) :=
  { tx_eq := htx, ty_eq := hty, iy_eq := hiy, iz_lt := h0, c_eq := rfl, w_eq := h.carry, g_eq := h.next_g }

/-- An empty window: the next column's head (`sz1`). -/
theorem SF.toO (h : SF a ix w g) (hiy : combaIyS a.used (ix + 1) = 0) :
    OS a (ix + 1) (w / 268435456) (upd g ix (w % 268435456)) :=
  ⟨by rw [hiy, h.carry]; rfl, h.next_g⟩

theorem IS.step (h : IS a ix tx ty iy iz w c g) (hlt : iz + 1 < iy) :
    IS a ix tx ty iy (iz + 1) w (c + a.digit (tx + iz) * a.digit (ty - iz)) g :=
  { h with iz_lt := hlt, c_eq := by rw [combaPart_succ, h.c_eq, h.tx_eq, h.ty_eq] }

theorem IS.last (h : IS a ix tx ty iy iz w c g) (he : iz + 1 = iy) :
    OS a ix (w + 2 * (c + a.digit (tx + iz) * a.digit (ty - iz))) g :=
  ⟨by rw [h.w_eq, h.c_eq, h.tx_eq, h.ty_eq, ← combaPart_succ, he, h.iy_eq], h.g_eq⟩

theorem IS.iy_le (h : IS a ix tx ty iy iz w c g) : iy ≤ ty + 1 := by
  rw [h.iy_eq, h.ty_eq]; unfold combaIyS combaIy; omega

theorem IS.txiy (h : IS a ix tx ty iy iz w c g) (hk : ix < 2 * a.used) : tx + iy ≤ a.used := by
  rw [h.iy_eq, h.tx_eq]; unfold combaIyS combaIy combaTx combaTy; omega

theorem IS.ty_lt (h : IS a ix tx ty iy iz w c g) (hu : 1 ≤ a.used) : ty < a.used := by
  rw [h.ty_eq]; unfold combaTy; omega

/-! ## Bounds -/

theorem SF.w_lt (h : SF a ix w g) (ha : a.Shape) (hm : a.used ≤ 256) : w < 2 ^ 64 := by
  have := combaW_lt (colS_room ha hm) ix; have := colS_room ha hm ix; rw [h.w_eq]; omega

theorem OS.sq_lt (h : OS a ix w g) (ha : a.Shape) (hm : a.used ≤ 256) (he : ix % 2 = 0) :
    w + a.digit (ix / 2) * a.digit (ix / 2) < 2 ^ 64 := (h.even he).w_lt ha hm

theorem OS.w_lt (h : OS a ix w g) (ha : a.Shape) (hm : a.used ≤ 256) : w < 2 ^ 64 := by
  have := combaW_lt (colS_room ha hm) ix; have := colS_room ha hm ix
  have : 2 * combaPart a.digit a.digit a.used ix (combaIyS a.used ix) ≤ colS a.digit a.used ix := by
    unfold colS; omega
  rw [h.w_eq]; simp only [cS] at *; omega

theorem IS.bound (h : IS a ix tx ty iy iz w c g) (ha : a.Shape) (hm : a.used ≤ 256) :
    w + 2 * (c + a.digit (tx + iz) * a.digit (ty - iz)) < 2 ^ 64 := by
  have hw := combaW_lt (colS_room ha hm) ix; have hr := colS_room ha hm ix
  have hp : combaPart a.digit a.digit a.used ix (iz + 1) ≤ combaPart a.digit a.digit a.used ix (combaIyS a.used ix) :=
    sumTo_mono _ (by have := h.iz_lt; rw [h.iy_eq] at this; omega)
  have : 2 * combaPart a.digit a.digit a.used ix (combaIyS a.used ix) ≤ colS a.digit a.used ix := by
    unfold colS; omega
  rw [h.w_eq, h.c_eq, h.tx_eq, h.ty_eq, ← combaPart_succ]; simp only [cS] at *; omega

end

/-! ## The tail -/

/-- The copied digits (`W[ix] & MP_MASK`, `cl`). -/
def wm (g : Nat → Nat) (j : Nat) : Nat := g j % 268435456

/-- `mp_clamp`'s argument from the copy (`wm g` below `n`), zeros up to the old `used`, `A`'s above. -/
theorem sq_fill {a A : MpInt} {n : Nat} {g f : Nat → Nat} (hA : A.Shape) (hroom : n ≤ A.alloc)
    (hn : n = a.used + a.used) (hg : ∀ j, j < n → g j = combaD (cS a) j)
    (hlo : ∀ j, j < n → f j = wm g j) (hmid : ∀ j, n ≤ j → j < A.used → f j = 0)
    (hhi : ∀ j, n ≤ j → A.used ≤ j → f j = A.digit j) (j : Nat) : (mfRes a a A n).digit j = f j := by
  rw [mfRes_digit hroom]
  unfold mulFastDigit
  by_cases h1 : j < n
  · rw [if_pos h1, hlo j h1, wm, hg j h1, Nat.mod_eq_of_lt (show combaD (cS a) j < 268435456 from combaD_lt _ _)]
    exact (sqrFast_digit a (by omega) j (by omega)).symm
  · rw [if_neg h1]
    by_cases h2 : j < A.used
    · rw [hmid j (by omega) h2]
    · rw [hhi j (by omega) (by omega), hA.high_zero j (by omega)]

/-- **The result**: valid, `|a|²`, grown only; `MP_OKAY` (`SqrFastPost` over the grown input). -/
theorem sq_out {a b A c4 : MpInt} {n : Nat} (ha : a.Shape) (hg : GrownOf b A)
    (hsign : b.sign = Layout.mpZpos ∨ b.sign = Layout.mpNeg) (hn : n = a.used + a.used) (hroom : n ≤ A.alloc)
    (hcl : ClampPost (mfRes a a A n) c4) :
    c4.Valid ∧ c4.mag = a.mag * a.mag ∧ b.alloc ≤ c4.alloc := by
  subst hn
  have hp : SqrFastPost a A c4 := mf_post hroom (by omega) hcl
  have := SqrFastPost.spec ha hroom hg.shape.alloc_lt (by rw [hg.sign]; exact hsign) hp
  exact ⟨this.1, this.2, by rw [hcl.alloc]; exact hg.alloc⟩

end Tom.SqrFastGStep
