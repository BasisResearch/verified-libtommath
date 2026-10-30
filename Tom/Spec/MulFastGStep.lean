import Tom.Spec.Mul
import Tom.Spec.Grow6Step
import Tom.Spec.Mont

/-!
# `s_mp_mul_digs_fast` with growth: the model steps

The comba multiplier (`bn_s_mp_mul_digs_fast.c`, HAC 14.12) over `Spec/Mul.lean`'s column
model: column `ix` is `col a.digit b.digit a.used b.used ix` (the C's `colC`, `colC_eq`), the
carry chain `combaW`/`combaD`. `W[]` (the frame's digit array, digit function `g`) holds the
digits of the columns done; `_W` is `w`.

* `OF` (the column head, `439c`): `w = combaW cl ix`, `g` the digits below `ix`;
* `IF` (the inner head, `43c8`): `tx`, `ty`, `iy` the C's `MP_MIN`s, `iz` products added;
* `IF.step`/`IF.last`/`OF.zcol`: one product, a column's last product, an empty column, in the
  rows' literal forms (`w + x * y`, `% 268435456`, `/ 268435456`);
* `mfIn c digs`: the destination after `mp_grow` (grown to `digs` iff short);
* `mfRes a b A n`: what `mp_clamp` is handed (`used := pa`, the digits `mulFastDigit`), its
  digits from the four tails (`fill_*`), and `mf_post`: `MulFastPost` from `mp_clamp`'s post.
-/

namespace Tom.MulFastGStep

open MpInt
open Mont (upd)

/-! ## The destination -/

/-- The destination `s_mp_mul_digs_fast(a, b, c, digs)` writes: `c`, grown to `digs` iff short. -/
def mfIn (c : MpInt) (dg : Nat) : MpInt := if c.alloc < dg then c.growTo dg else c

theorem mfIn_grown {c : MpInt} (hc : c.Shape) {dg : Nat} (h31 : dg < 2 ^ 31) : GrownOf c (mfIn c dg) :=
  GrownOf.ite hc id h31

theorem mfIn_room (c : MpInt) (dg : Nat) : dg ≤ (mfIn c dg).alloc := by
  unfold mfIn; split
  · simp [MpInt.growTo, MpInt.ofDigits]
  · omega

/-! ## The column loop -/

/-- The product's columns. -/
abbrev cl (a b : MpInt) : Nat → Nat := col a.digit b.digit a.used b.used

theorem eR : radix = 268435456 := rfl

/-- At the column head `ix`: the columns below `ix` stored in `g`, `w` the carry into `ix`. -/
structure OF (a b : MpInt) (ix w : Nat) (g : Nat → Nat) : Prop where
  w_eq : w = combaW (cl a b) ix
  g_eq : ∀ j, j < ix → g j = combaD (cl a b) j

/-- Inside column `ix`, after `iz` of its `iy` products. -/
structure IF (a b : MpInt) (ix tx ty iy iz w : Nat) (g : Nat → Nat) : Prop where
  ub1 : 1 ≤ b.used
  tx_eq : tx = combaTx b.used ix
  ty_eq : ty = combaTy b.used ix
  iy_eq : iy = combaIy a.used b.used ix
  iz_lt : iz < iy
  w_eq : w = combaW (cl a b) ix + combaPart a.digit b.digit b.used ix iz
  g_eq : ∀ j, j < ix → g j = combaD (cl a b) j

section
variable {a b : MpInt} {ix tx ty iy iz w : Nat} {g : Nat → Nat}

theorem OF.zero (g : Nat → Nat) : OF a b 0 0 g := ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem OF.cast {i j : Nat} (h : OF a b i w g) (e : i = j) : OF a b j w g := e ▸ h

theorem IF.iy_le (h : IF a b ix tx ty iy iz w g) : iy ≤ ty + 1 := by
  rw [h.iy_eq, h.ty_eq]; unfold combaIy; omega

theorem IF.txiy (h : IF a b ix tx ty iy iz w g) : tx + iy ≤ a.used := by
  have := h.iz_lt
  rw [h.iy_eq, h.tx_eq] at *; unfold combaIy at *; omega

theorem IF.ty_lt (h : IF a b ix tx ty iy iz w g) : ty < b.used := by
  have := h.ub1; rw [h.ty_eq]; unfold combaTy; omega

/-- The inner loop's set-up (`oa`, `ob`, `oc1`, `oc2`). -/
theorem OF.start (h : OF a b ix w g) (hub : 1 ≤ b.used) (htx : tx = combaTx b.used ix)
    (hty : ty = combaTy b.used ix) (hiy : iy = combaIy a.used b.used ix) (h0 : 0 < iy) :
    IF a b ix tx ty iy 0 w g :=
  { ub1 := hub, tx_eq := htx, ty_eq := hty, iy_eq := hiy, iz_lt := h0
    w_eq := by rw [h.w_eq]; rfl, g_eq := h.g_eq }

theorem combaPart_succ (da db : Nat → Nat) (ub k n : Nat) :
    combaPart da db ub k (n + 1) = combaPart da db ub k n + da (combaTx ub k + n) * db (combaTy ub k - n) := rfl

/-- One product (`il`). -/
theorem IF.step (h : IF a b ix tx ty iy iz w g) (hlt : iz + 1 < iy) :
    IF a b ix tx ty iy (iz + 1) (w + a.digit (tx + iz) * b.digit (ty - iz)) g :=
  { ub1 := h.ub1, tx_eq := h.tx_eq, ty_eq := h.ty_eq, iy_eq := h.iy_eq, iz_lt := hlt, g_eq := h.g_eq
    w_eq := by rw [combaPart_succ, h.w_eq, h.tx_eq, h.ty_eq]; omega }

/-- The column with every product added. -/
theorem IF.col (h : IF a b ix tx ty iy iz w g) (he : iz + 1 = iy) :
    w + a.digit (tx + iz) * b.digit (ty - iz) = combaW (cl a b) ix + cl a b ix := by
  have hc := colC_eq a.digit b.digit a.used b.used ix h.ub1
  unfold colC at hc
  rw [h.w_eq, Nat.add_assoc, h.tx_eq, h.ty_eq, ← combaPart_succ, he, h.iy_eq]; exact congrArg _ hc

/-- A column's last product (`ix1`, `ix2`): its digit stored, the carry on. -/
theorem IF.last (h : IF a b ix tx ty iy iz w g) (he : iz + 1 = iy) :
    OF a b (ix + 1) ((w + a.digit (tx + iz) * b.digit (ty - iz)) / 268435456)
      (upd g ix ((w + a.digit (tx + iz) * b.digit (ty - iz)) % 268435456)) := by
  rw [h.col he]
  refine ⟨rfl, fun j hj => ?_⟩
  unfold upd; split
  · next e => subst e; rfl
  · next e => exact h.g_eq j (by omega)

/-- An empty column (`obz`, `oc1z`, `oc2z`). -/
theorem OF.zcol (h : OF a b ix w g) (hz : cl a b ix = 0) :
    OF a b (ix + 1) (w / 268435456) (upd g ix (w % 268435456)) := by
  have e : w = combaW (cl a b) ix + cl a b ix := by rw [hz, h.w_eq]; rfl
  rw [e]
  refine ⟨rfl, fun j hj => ?_⟩
  unfold upd; split
  · next e => subst e; rfl
  · next e => exact h.g_eq j (by omega)

theorem col_ub0 (da db : Nat → Nat) (ua k : Nat) : col da db ua 0 k = 0 := by
  unfold col
  rw [sumTo_congr ua (g := fun _ => 0) (fun i _ => by simp), sumTo_zero_fun]

/-- The empty columns: `b->used = 0`, `a->used = 0`, or the top one. -/
theorem cl_zero (a b : MpInt) (ix : Nat) (h : b.used = 0 ∨ a.used = 0 ∨ a.used + b.used ≤ ix + 1) :
    cl a b ix = 0 := by
  rcases h with h | h | h
  · show col _ _ _ _ _ = 0; rw [h]; exact col_ub0 _ _ _ _
  · show col _ _ _ _ _ = 0; rw [h]; exact col_zero_ua _ _ _ _
  · exact col_high _ _ _ _ _ h

/-- Every column leaves `2 ^ 36` of room in 64 bits (`MP_MAXFAST`). -/
theorem cl_room {a b : MpInt} (ha : a.ShapeU) (hb : b.ShapeU) (hm : min a.used b.used ≤ 256) (k : Nat) :
    cl a b k + 2 ^ 36 ≤ 2 ^ 64 := by
  by_cases hub : 1 ≤ b.used
  · show col a.digit b.digit a.used b.used k + 2 ^ 36 ≤ 2 ^ 64
    rw [← colC_eq _ _ _ _ _ hub]; exact colC_room ha.digit_lt hb.digit_lt _ _ k hub hm
  · rw [cl_zero a b k (.inl (by omega))]; decide

theorem OF.w_lt (h : OF a b ix w g) (ha : a.ShapeU) (hb : b.ShapeU) (hm : min a.used b.used ≤ 256) :
    w < 2 ^ 36 := by
  rw [h.w_eq]; exact combaW_lt (cl_room ha hb hm) ix

/-- `_W` stays in 64 bits through the column (`il`, `ix1`, `ix2`). -/
theorem IF.bound (h : IF a b ix tx ty iy iz w g) (ha : a.ShapeU) (hb : b.ShapeU) (hm : min a.used b.used ≤ 256) :
    w + a.digit (tx + iz) * b.digit (ty - iz) < 2 ^ 64 := by
  have hw := combaW_lt (cl_room ha hb hm) ix
  have hr := colC_room ha.digit_lt hb.digit_lt a.used b.used ix h.ub1 hm
  have hp := combaPart_le a.digit b.digit a.used b.used ix (iz + 1) (by have := h.iz_lt; rw [h.iy_eq] at this; omega)
  have e : w + a.digit (tx + iz) * b.digit (ty - iz) =
      combaW (cl a b) ix + combaPart a.digit b.digit b.used ix (iz + 1) := by
    rw [combaPart_succ, h.w_eq, h.tx_eq, h.ty_eq]; omega
  rw [e]; omega

end

/-! ## The tail: `memcpy`, `MP_ZERO_DIGITS`, `mp_clamp` -/

/-- What `mp_clamp` is handed: `A`'s array with the comba digits below `pa`, `used := pa`. -/
def mfRes (a b A : MpInt) (n : Nat) : MpInt :=
  { A with used := n, digits := (List.range A.alloc).map (mulFastDigit a b n) }

theorem mfDigit_hi {a b : MpInt} {n j : Nat} (hj : n ≤ j) : mulFastDigit a b n j = 0 := by
  simp [mulFastDigit, show ¬ j < n by omega]

theorem mfRes_digit {a b A : MpInt} {n : Nat} (hroom : n ≤ A.alloc) : (mfRes a b A n).digit = mulFastDigit a b n := by
  funext i
  simp only [mfRes, MpInt.digit, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < A.alloc
  · simp [h]
  · simp [h, mfDigit_hi (a := a) (b := b) (show n ≤ i by omega)]

theorem mfRes_shape {a b A : MpInt} {n : Nat} (hA : A.Shape) (hroom : n ≤ A.alloc) : (mfRes a b A n).Shape :=
  { len := by simp [mfRes]
    used_le := hroom
    alloc_lt := hA.alloc_lt
    digit_lt := fun i => by rw [mfRes_digit hroom]; exact mulFastDigit_lt a b n i
    high_zero := fun i hi => by rw [mfRes_digit hroom]; exact mfDigit_hi (by simp only [mfRes] at hi; omega) }

/-- The four tails' digits (`memcpy` of `W` below `pa`, zeros up to the old `used`, `A`'s above). -/
theorem fill {a b A : MpInt} {n w : Nat} {g f : Nat → Nat} (hA : A.Shape) (hroom : n ≤ A.alloc)
    (h : OF a b n w g) (hlo : ∀ j, j < n → f j = g j) (hmid : ∀ j, n ≤ j → j < A.used → f j = 0)
    (hhi : ∀ j, n ≤ j → A.used ≤ j → f j = A.digit j) (j : Nat) : (mfRes a b A n).digit j = f j := by
  rw [mfRes_digit hroom]
  unfold mulFastDigit
  by_cases h1 : j < n
  · rw [if_pos h1, hlo j h1, h.g_eq j h1]
  · rw [if_neg h1]
    by_cases h2 : j < A.used
    · rw [hmid j (by omega) h2]
    · rw [hhi j (by omega) (by omega), hA.high_zero j (by omega)]

/-- **`mp_clamp`'s result is `MulFastPost`** over the grown destination. -/
theorem mf_post {a b A c4 : MpInt} {n dg : Nat} (hroom : n ≤ A.alloc) (hn : n = min dg (a.used + b.used))
    (hcl : ClampPost (mfRes a b A n) c4) : MulFastPost a b A c4 dg :=
  { alloc := hcl.alloc
    len := by rw [hcl.digits]; simp [mfRes]
    digit := by rw [hcl.digit, mfRes_digit hroom, hn]
    used := by rw [hcl.used, mfRes_digit hroom, ← hn]; rfl
    sign := by rw [hcl.sign]; rfl }

/-- **The contract's result**: valid, the product mod `radix ^ digs`, `A`'s allocation. -/
theorem mf_out {a b c A c4 : MpInt} {dg : Nat} (ha : a.ShapeU) (hb : b.ShapeU) (hg : GrownOf c A)
    (hroom : dg ≤ A.alloc) (hsign : c.sign = Layout.mpZpos ∨ c.sign = Layout.mpNeg)
    (h : MulFastPost a b A c4 dg) :
    c4.Valid ∧ c4.mag = (a.mag * b.mag) % radix ^ dg ∧ c4.alloc = A.alloc := by
  have hsp := MulFastPost.spec ha hb hroom hg.shape.alloc_lt (by rw [hg.sign]; exact hsign) h
  refine ⟨hsp.1, ?_, h.alloc⟩
  by_cases hd : a.used + b.used ≤ dg
  · rw [hsp.2.2 hd]
    refine (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ?_ (Nat.pow_le_pow_right radix_pos hd))).symm
    rw [Nat.pow_add]; exact Nat.mul_lt_mul'' ha.mag_lt hb.mag_lt
  · rw [hsp.2.1, Nat.min_eq_left (by omega)]

end Tom.MulFastGStep
