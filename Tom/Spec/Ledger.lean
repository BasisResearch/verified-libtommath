import Tom.Spec.LedgerAttr
import Tom.Spec.Mont
import Tom.Spec.Canon
import Tom.Spec.DigitShift
import Tom.Spec.DivD
import Tom.Spec.MulAlgo
import Tom.Spec.Cmp
import Tom.Spec.Init
import Tom.Spec.Div
import Tom.Spec.AddGStep
import Tom.Spec.Expt2
import Tom.Spec.Shift
import Tom.Spec.Reduce

/-!
# The Ledger: digit loops as balanced books, calls as transfers

* **Books** `Bal N Z f k c T B A`: the digits `f` below `N` (zero from `Z` on) plus the open
  carry `radix^k · c` balance the model `T`, `c < B`, and an `aux` slot `A` carried unchanged. `add0`: `f k + y` with no carry;
  `carry`: `f k + c`; `flush`: `c` into a zero slot). `retarget` (the model's one identity),
  `init`/`reopen` (open), `close`, `k_lt`, `zero_of_lt`; `row_succ` is the row identity of a
  scalar-times-row loop. `BalD` is the truncated book (`mod radix^D`, `dropD`).
* **Tapes** `Tape s out f0 i f`: a single-pass store loop at `s, s+1, …` after `i` steps.
* **Accounts**: `Settled t al M s` (what a clamped result is: valid, `alloc`, `|t| = M`, sign `s`
  unless zero) and the signed `Acct x al U V A` (valid, `al ≤ alloc`, `used ≤ U`, `val = V`).
  `settle` is `mp_clamp` of a digit temporary (`Canon.ofDigits_shape` + `ClampPost.spec`).
* **Transfers** `xfer_<callee>`: one per callee, each its Post's `.spec` read into an account.

`ledger_nf` (`Tom/Spec/LedgerAttr.lean`) folds the literal `268435456` into `radix`.
-/

namespace Tom.Ledger

open MpInt
open Mont (upd upd_ne)

/-! ## Units -/

@[ledger_nf] theorem lit : (268435456 : Nat) = radix := rfl
@[ledger_nf] theorem litMask : (268435455 : Nat) = radix - 1 := rfl
theorem eR : radix = 268435456 := rfl

/-! ## Books -/

/-- Books plus open carry balance the model `T`. -/
structure Bal (N Z : Nat) (f : Nat → Nat) (k c T B : Nat) (A : Prop) : Prop where
  dig : ∀ j, j < N → f j < radix
  zero : ∀ j, Z ≤ j → j < N → f j = 0
  val : natUpTo f N + radix ^ k * c = T
  c_lt : c < B
  aux : A

section
variable {N Z k c T B : Nat} {f : Nat → Nat} {A : Prop}

theorem Bal.retarget {T' : Nat} (h : Bal N Z f k c T B A) (e : T = T') : Bal N Z f k c T' B A := e ▸ h

/-- Open the books (no carry). -/
theorem Bal.init (hd : ∀ j, j < N → f j < radix) (hz : ∀ j, Z ≤ j → j < N → f j = 0)
    (hv : natUpTo f N = T) (hB : 0 < B) (a : A) : Bal N Z f k 0 T B A :=
  ⟨hd, hz, by rw [Nat.mul_zero, Nat.add_zero, hv], hB, a⟩

/-- Books over an array whose digits are all digits (zero floor at the top). -/
theorem Bal.ofAll (hd : ∀ j, f j < radix) (hv : natUpTo f N + radix ^ k * c = T) (hc : c < B) (a : A) :
    Bal N N f k c T B A := ⟨fun j _ => hd j, fun _ _ h2 => absurd h2 (by omega), hv, hc, a⟩

theorem Bal.dig_all (h : Bal N Z f k c T B A) (hi : ∀ j, N ≤ j → f j = 0) : ∀ j, f j < radix := fun j =>
  if hj : j < N then h.dig j hj else by rw [hi j (by omega)]; exact radix_pos

/-- Close the books (no carry left): the digits are the model. -/
theorem Bal.close (h : Bal N Z f k c T B A) (hc : c = 0) : natUpTo f N = T := by
  have := h.val; rwa [hc, Nat.mul_zero, Nat.add_zero] at this

/-- Reopen at another column with other `B`, `aux` (a new row). -/
theorem Bal.reopen {k' B' : Nat} {A' : Prop} (h : Bal N Z f k 0 T B A) (hB : 0 < B') (a : A') :
    Bal N Z f k' 0 T B' A' := .init h.dig h.zero (h.close rfl) hB a

/-- **The posting rule**: `r = y + x[k] + u; x[k] = r mod R; u = r / R` posts `R^k · y`. -/
theorem Bal.post {y Y : Nat} (h : Bal N Z f k c T B A) (hk : k < N) (hz : k < Z) (hy : y ≤ Y)
    (hYB : Y + radix + B ≤ radix * B + 1) :
    Bal N Z (upd f k ((y + f k + c) % 268435456)) (k + 1) ((y + f k + c) / 268435456)
      (T + radix ^ k * y) B A := by
  have hv : natUpTo (upd f k ((y + c + f k) % 268435456)) N + radix ^ (k + 1) * ((y + c + f k) / 268435456) =
      natUpTo f N + radix ^ k * (y + c) := Mont.cstep_val ⟨f, c⟩ k y N hk
  rw [Nat.add_right_comm y c (f k), Nat.mul_add] at hv
  have hd := h.dig k hk; have hc := h.c_lt; have hval := h.val
  refine ⟨fun j hj => ?_, fun j hj hjN => ?_, by omega, ?_, h.aux⟩
  · unfold upd; split
    · exact Nat.mod_lt _ (by decide)
    · exact h.dig j hj
  · rw [upd_ne _ _ (by omega)]; exact h.zero j hj hjN
  · rw [eR] at hd hYB; exact (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega)

theorem dprod_le {a b : Nat} (ha : a < radix) (hb : b < radix) : a * b ≤ (radix - 1) * (radix - 1) :=
  Nat.mul_le_mul (by omega) (by omega)

/-- Store form `a b + x[k] + u`, digits `a`, `b`, carry a digit (`mp_word` fits). -/
theorem Bal.mac {a b : Nat} (h : Bal N Z f k c T radix A) (hk : k < N) (hz : k < Z) (ha : a < radix)
    (hb : b < radix) :
    Bal N Z (upd f k ((a * b + f k + c) % 268435456)) (k + 1) ((a * b + f k + c) / 268435456)
      (T + radix ^ k * (a * b)) radix A :=
  h.post hk hz (dprod_le ha hb) (by decide)

/-- Store form `x[k] + u` (the propagation: nothing posted). -/
theorem Bal.carry (h : Bal N Z f k c T B A) (hk : k < N) (hz : k < Z) :
    Bal N Z (upd f k ((f k + c) % 268435456)) (k + 1) ((f k + c) / 268435456) T B A := by
  have hB : 0 + radix + B ≤ radix * B + 1 := by
    obtain ⟨b, rfl⟩ : ∃ b, B = b + 1 := ⟨B - 1, by have := h.c_lt; omega⟩
    rw [Nat.mul_succ]; have : b ≤ radix * b := Nat.le_mul_of_pos_left b radix_pos; omega
  have := h.post hk hz (Nat.le_refl 0) hB
  rwa [Nat.zero_add, Nat.mul_zero, Nat.add_zero] at this

/-- Store form `x[k] + y` with no carry in. -/
theorem Bal.add0 {y Y : Nat} (h : Bal N Z f k 0 T B A) (hk : k < N) (hz : k < Z) (hy : y ≤ Y)
    (hYB : Y + radix + B ≤ radix * B + 1) :
    Bal N Z (upd f k ((f k + y) % 268435456)) (k + 1) ((f k + y) / 268435456) (T + radix ^ k * y) B A := by
  have := h.post hk hz hy hYB; rwa [Nat.add_zero, Nat.add_comm y] at this

/-- Store form `u` into a zero slot (the carry flushed). -/
theorem Bal.flush (h : Bal N Z f k c T B A) (hk : k < N) (hz : k < Z) (h0 : f k = 0) (hc : c < radix) :
    Bal N Z (upd f k c) (k + 1) 0 T B A := by
  have e := Mont.natUpTo_upd f k c N hk
  have hv := h.val; have hB := h.c_lt
  rw [h0, Nat.mul_zero, Nat.add_zero] at e
  refine ⟨fun j hj => ?_, fun j hj hjN => ?_, by rw [Nat.mul_zero, Nat.add_zero]; omega, by omega, h.aux⟩
  · unfold upd; split
    · exact hc
    · exact h.dig j hj
  · rw [upd_ne _ _ (by omega)]; exact h.zero j hj hjN

/-- A carry is left only below `D` when the model is below `radix^D`. -/
theorem Bal.k_lt {D : Nat} (h : Bal N Z f k c T B A) (hT : T < radix ^ D) (hc : c ≠ 0) : k < D := by
  have e := h.val
  have : radix ^ k ≤ radix ^ k * c := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hc)
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < radix)).1 (show radix ^ k < radix ^ D by omega)

theorem natUpTo_le_of_le (f : Nat → Nat) {m n : Nat} (h : m ≤ n) : natUpTo f m ≤ natUpTo f n := by
  induction n with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact Nat.le_trans (ih (by omega)) (by simp only [natUpTo]; omega)
    · rw [h]; exact Nat.le_refl _

/-- Digits above a value bound are zero. -/
theorem zeros_of_lt {f : Nat → Nat} {N E : Nat} (h : natUpTo f N < radix ^ E) :
    ∀ j, E ≤ j → j < N → f j = 0 := fun j h1 h2 => by
  refine Classical.byContradiction fun hj => ?_
  have e1 := natUpTo_ge_top f j hj
  have e2 := natUpTo_le_of_le f (show j + 1 ≤ N by omega)
  have e3 := Nat.pow_le_pow_right radix_pos h1
  omega

theorem Bal.zero_of_lt {E : Nat} (h : Bal N Z f k c T B A) (hT : T < radix ^ E) :
    ∀ j, E ≤ j → j < N → f j = 0 :=
  zeros_of_lt (by have := h.val; omega)

/-- The row identity of `x[p + i] += m · d[i]`. -/
theorem row_succ (base p m i : Nat) (d : Nat → Nat) :
    base + radix ^ p * (m * natUpTo d i) + radix ^ (p + i) * (d i * m) =
      base + radix ^ p * (m * natUpTo d (i + 1)) := by
  rw [show natUpTo d (i + 1) = natUpTo d i + radix ^ i * d i from rfl, Nat.pow_add, Nat.mul_add, Nat.mul_add,
    Nat.add_assoc]
  congr 2; ac_rfl

/-! ### Truncated books (`mod radix^D`: the carry past `D` is dropped) -/

structure BalD (D N Z : Nat) (f : Nat → Nat) (k c T B : Nat) (A : Prop) : Prop where
  dig : ∀ j, j < N → f j < radix
  zero : ∀ j, Z ≤ j → j < N → f j = 0
  val : (natUpTo f D + radix ^ k * c) % radix ^ D = T % radix ^ D
  c_lt : c < B
  aux : A

theorem Bal.toD {D : Nat} (h : Bal D Z f k c T B A) : BalD D D Z f k c T B A :=
  ⟨h.dig, h.zero, by rw [h.val], h.c_lt, h.aux⟩

theorem BalD.post {D y Y : Nat} (h : BalD D N Z f k c T B A) (hk : k < D) (hDN : D ≤ N) (hz : k < Z)
    (hy : y ≤ Y) (hYB : Y + radix + B ≤ radix * B + 1) :
    BalD D N Z (upd f k ((y + f k + c) % 268435456)) (k + 1) ((y + f k + c) / 268435456)
      (T + radix ^ k * y) B A := by
  have b := Bal.post (N := D) (Z := Z) (T := natUpTo f D + radix ^ k * c) (A := A)
    ⟨fun j hj => h.dig j (by omega), fun j hj hjD => h.zero j hj (by omega), rfl, h.c_lt, h.aux⟩ hk hz hy hYB
  refine ⟨fun j hj => ?_, fun j hj hjN => ?_, ?_, b.c_lt, h.aux⟩
  · unfold upd; split
    · exact Nat.mod_lt _ (by decide)
    · exact h.dig j hj
  · rw [upd_ne _ _ (by omega)]; exact h.zero j hj hjN
  · rw [b.val, Nat.add_mod, h.val, ← Nat.add_mod]

/-- **Truncation**: at or past `D` a column (and its carry) leaves the value mod `radix^D`. -/
theorem BalD.dropD {D k' c' B' y : Nat} {A' : Prop} (h : BalD D N Z f k c T B A) (hk : D ≤ k) (hk' : D ≤ k')
    (hc' : c' < B') (a : A') : BalD D N Z f k' c' (T + radix ^ k * y) B' A' := by
  have e : ∀ j u, D ≤ j → radix ^ j * u % radix ^ D = 0 := fun j u hj => by
    rw [show j = D + (j - D) by omega, Nat.pow_add, Nat.mul_assoc, Nat.mul_mod_right]
  refine ⟨h.dig, h.zero, ?_, hc', a⟩
  have hv := h.val
  rw [Nat.add_mod, e k c hk, Nat.add_zero, Nat.mod_mod] at hv
  rw [Nat.add_mod, e k' c' hk', Nat.add_zero, Nat.mod_mod, hv, Nat.add_mod T, e k y hk, Nat.add_zero, Nat.mod_mod]

theorem BalD.fin {D : Nat} (h : BalD D N Z f k c T B A) (hk : D ≤ k) (hDN : D ≤ N) :
    natUpTo f D = T % radix ^ D := by
  have hv := h.val
  rw [show k = D + (k - D) by omega, Nat.pow_add, Nat.mul_assoc, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (natUpTo_lt' f fun j hj => h.dig j (by omega))] at hv
  exact hv
where
  natUpTo_lt' (f : Nat → Nat) {D : Nat} (hf : ∀ j, j < D → f j < radix) : natUpTo f D < radix ^ D := by
    rw [natUpTo_congr D (e := fun j => if j < D then f j else 0) (fun j hj => by rw [if_pos hj])]
    exact natUpTo_lt _ (fun j => by split; exact hf j ‹_›; exact radix_pos) D

end

/-! ## Tapes: single-pass store loops -/

/-- After `i` steps of a loop storing `out j` at `s + j`, everything else as in `f0`. -/
structure Tape (s : Nat) (out f0 : Nat → Nat) (i : Nat) (f : Nat → Nat) : Prop where
  done : ∀ j, j < i → f (s + j) = out j
  rest : ∀ j, (j < s ∨ s + i ≤ j) → f j = f0 j

section
variable {s i : Nat} {out f0 f : Nat → Nat}

theorem Tape.start (s : Nat) (out f0 : Nat → Nat) : Tape s out f0 0 f0 :=
  ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩

theorem Tape.step {v : Nat} (h : Tape s out f0 i f) (hv : v = out i) : Tape s out f0 (i + 1) (upd f (s + i) v) where
  done j hj := by
    by_cases e : j = i
    · subst e; rw [Mont.upd_same]; exact hv
    · rw [upd_ne _ _ (by omega)]; exact h.done j (by omega)
  rest j hj := by rw [upd_ne _ _ (by omega)]; exact h.rest j (by omega)

theorem Tape.fin (h : Tape s out f0 i f) (j : Nat) : f j = if s ≤ j ∧ j < s + i then out (j - s) else f0 j := by
  split
  · have := h.done (j - s) (by omega); rwa [show s + (j - s) = j by omega] at this
  · exact h.rest j (by omega)

end

/-! ## Accounts -/

/-- A clamped result: valid, `alloc`, magnitude `M`, sign `s` unless zero. -/
structure Settled (t : MpInt) (al M s : Nat) : Prop where
  valid : t.Valid
  alloc : t.alloc = al
  mag : t.mag = M
  sign : t.sign = if t.used = 0 then Layout.mpZpos else s

/-- A signed account: valid, room `al ≤ alloc`, `used ≤ U`, value `V`, and `aux`. -/
structure Acct (x : MpInt) (al U : Nat) (V : Int) (A : Prop) : Prop where
  valid : x.Valid
  room : al ≤ x.alloc
  used : x.used ≤ U
  val : x.val = V
  aux : A

section
variable {x t : MpInt} {al U M s : Nat} {V : Int} {A : Prop}

/-- Value bound → digit count. -/
theorem used_le_of_lt {j : Nat} (hx : x.Valid) (h : x.mag < radix ^ j) : x.used ≤ j := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have := MpInt.mag_ge hx (by omega)
  have := Nat.pow_le_pow_right radix_pos (show j ≤ x.used - 1 by omega)
  omega

theorem val_zpos (hs : x.sign = Layout.mpZpos) : x.val = x.mag := by
  simp [MpInt.val, hs, Layout.mpZpos, Layout.mpNeg]

theorem Settled.self (h : Settled t al M s) : Settled t t.alloc M s := ⟨h.valid, rfl, h.mag, h.sign⟩

theorem Settled.zpos (h : Settled t al M Layout.mpZpos) : t.sign = Layout.mpZpos := by
  rw [h.sign]; split <;> rfl

theorem Settled.val (h : Settled t al M Layout.mpZpos) : t.val = M := by rw [val_zpos h.zpos, h.mag]

theorem Settled.acct (h : Settled t al M Layout.mpZpos) (hU : M < radix ^ U) (a : A) : Acct t al U M A :=
  ⟨h.valid, h.alloc ▸ Nat.le_refl al, used_le_of_lt h.valid (by rw [h.mag]; exact hU), h.val, a⟩

theorem Acct.mag (h : Acct x al U V A) : x.mag = V.natAbs := by rw [← h.val, natAbs_val]

theorem Acct.magN {M : Nat} (h : Acct x al U (M : Int) A) : x.mag = M := by rw [h.mag]; rfl

theorem Acct.zpos (h : Acct x al U V A) (hV : 0 ≤ V) : x.sign = Layout.mpZpos := by
  rcases h.valid.sign_ok with e | e
  · exact e
  · have := h.valid.mag_pos_of_neg e
    have hv := h.val; unfold MpInt.val at hv; rw [if_pos e] at hv; omega

theorem Acct.settled {M : Nat} (h : Acct x al U (M : Int) A) : Settled x x.alloc M Layout.mpZpos :=
  ⟨h.valid, rfl, by rw [h.mag]; rfl, by rw [h.zpos (by omega)]; split <;> rfl⟩

/-- `mp_clamp` of a digit temporary (`used = D`, `alloc = al`, digits `f`). -/
theorem settle {D T : Nat} {f : Nat → Nat} {t' : MpInt} (hD : D ≤ al) (hal : al < 2 ^ 31)
    (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg) (hd : ∀ j, j < al → f j < radix)
    (hz : ∀ j, D ≤ j → j < al → f j = 0) (hv : natUpTo f D = T)
    (hc : ClampPost (MpInt.ofDigits D al s f) t') : Settled t' al T s := by
  obtain ⟨hv', hm⟩ := hc.spec (ofDigits_shape hD hal hd hz) hs
  refine ⟨hv', hc.alloc, ?_, hc.sign⟩
  rw [hm, ← hv]
  exact natUpTo_congr D fun j hj => by rw [MpInt.ofDigits_digit, if_pos (by omega)]

theorem Bal.settle {D k B T : Nat} {f : Nat → Nat} {t' : MpInt} (h : Bal al D f k 0 T B A) (hD : D ≤ al)
    (hal : al < 2 ^ 31) (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg)
    (hc : ClampPost (MpInt.ofDigits D al s f) t') : Settled t' al T s :=
  Ledger.settle hD hal hs h.dig h.zero (by rw [← natUpTo_zeros f D al hD h.zero]; exact h.close rfl) hc

end

/-! ## Transfers, one per callee -/

section
variable {x x' t t' n : MpInt} {al U M s k : Nat} {V : Int} {A : Prop}

/-- `mp_rshd(x, k)`, `k > 0`. -/
theorem xfer_rshd (h : Settled x al M s) (hk : 0 < k) (hr : RshdPost x k x') :
    Settled x' al (M / radix ^ k) s := by
  by_cases hu : k < x.used
  · have hsh := hr.shift hk hu
    obtain ⟨hv, hm⟩ := hsh.spec h.valid hu
    refine ⟨hv, by rw [hsh.alloc, h.alloc], by rw [hm, h.mag], ?_⟩
    rw [hsh.sign, h.sign, if_neg (by omega), if_neg (by rw [hsh.used]; omega)]
  · have hz := hr.zero hk (by omega)
    obtain ⟨hv, hm, _⟩ := hz.spec h.valid.toShape
    refine ⟨hv, by rw [hz.alloc, h.alloc], ?_, by rw [hz.sign, if_pos hz.used]⟩
    rw [hm, ← h.mag]
    exact (Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (MpInt.mag_lt h.valid.toShape)
      (Nat.pow_le_pow_right radix_pos (by omega)))).symm

/-- `mp_rshd(x, k)` on a nonnegative account, any `k`. -/
theorem xfer_rshd0 (h : Settled x al M Layout.mpZpos) (hr : RshdPost x k x') :
    Settled x' al (M / radix ^ k) Layout.mpZpos := by
  rcases Nat.eq_zero_or_pos k with h0 | hk
  · rw [hr.noop h0, h0, Nat.pow_zero, Nat.div_one]; exact h
  · exact xfer_rshd h hk hr

/-- `s_mp_sub(x, n, x)`, `|n| ≤ |x|`. -/
theorem xfer_ssub (h : Settled x al M s) (hn : n.Valid) (hle : n.mag ≤ M) (hs : SSubPost x n x x') :
    Settled x' al (M - n.mag) s := by
  have hv := h.valid
  obtain ⟨hv', hm⟩ := hs.spec hv.toShape hn.toShape (by rw [h.mag]; exact hle) hv.used_le hv.alloc_lt hv.sign_ok
  refine ⟨hv', by rw [hs.alloc, h.alloc], by rw [hm, h.mag], ?_⟩
  rw [hs.sign]; split
  · rfl
  · rename_i hu'
    have hu : x.used ≠ 0 := fun h0 => hu' (hv'.used_zero (by rw [hm, MpInt.mag_used_zero h0]; exact Nat.zero_sub _))
    rw [h.sign, if_neg hu]

/-- `mp_rshd(x, k)`: the digit twin (`x'[i] = x[k + i]`). -/
theorem xfer_rshdD (hx : x.Shape) (hr : RshdPost x k x') : x'.digit = (fun i => x.digit (k + i)) ∧ x'.used = x.used - k := by
  rcases Nat.eq_zero_or_pos k with h0 | hk
  · subst h0; rw [hr.noop rfl]; exact ⟨funext fun i => by rw [Nat.zero_add], rfl⟩
  by_cases hu : k < x.used
  · have hs := hr.shift hk hu
    refine ⟨funext fun i => ?_, by rw [hs.used]⟩
    rw [hs.digit]; split
    · rw [Nat.add_comm]
    · rw [hx.high_zero (k + i) (by omega)]; split
      · rfl
      · exact hx.high_zero i (by omega)
  · have hz := hr.zero hk (by omega)
    exact ⟨funext fun i => by rw [hz.digit, hx.high_zero (k + i) (by omega)], by rw [hz.used]; omega⟩

/-- `mp_init_copy(&t, a)`: the digit twin. -/
theorem xfer_copyD {a : MpInt} {n : Nat} (ha : a.Shape) (h : CopyPost a (MpInt.zeroN n) t) :
    t.digit = a.digit ∧ t.used = a.used :=
  ⟨funext fun i => by
    rw [h.digit]; split
    · rfl
    · rw [if_neg (by simp [MpInt.zeroN]), MpInt.zeroN_digit, ha.high_zero i (by omega)], h.used⟩

/-- `mp_init_copy(&t, a)` (`n = initPrec a.used`). -/
theorem xfer_copy {a : MpInt} {n : Nat} (ha : a.Valid) (hn : a.used ≤ n) (hn' : n < 2 ^ 31)
    (h : CopyPost a (MpInt.zeroN n) t) : Acct t n a.used a.val True := by
  obtain ⟨hv, -, hval⟩ := h.spec ha (MpInt.zeroN_valid hn').toShape hn
  exact ⟨hv, by rw [h.alloc]; exact Nat.le_refl _, by rw [h.used]; exact Nat.le_refl _, hval, trivial⟩

/-- The C's `t.sign = MP_ZPOS`. -/
theorem xfer_setZpos (h : Acct t al U V A) : Acct (t.withSign Layout.mpZpos) al U (V.natAbs : Int) A where
  valid := { len := h.valid.len, used_le := h.valid.used_le, alloc_lt := h.valid.alloc_lt
             digit_lt := h.valid.digit_lt, high_zero := h.valid.high_zero, top := h.valid.top
             sign_ok := Or.inl rfl, zero_pos := fun _ => rfl }
  room := h.room
  used := h.used
  val := by rw [← h.mag]; rfl
  aux := h.aux

/-- `mp_div_d(t, v, t, &d)` (in place). -/
theorem xfer_divD {v : Nat} (h : Acct t al U (M : Int) A) (hal : 1 ≤ al) (hv : 0 < v) (hq : DivDQuot t v t t') :
    Acct t' 1 U ((M / v : Nat) : Int) A := by
  have hz := h.zpos (by omega)
  have hm : t.mag = M := by have := h.mag; simpa using this
  obtain ⟨hv', hm', hval⟩ := hq.spec h.valid hv h.valid.used_le h.valid.alloc_lt
  refine ⟨hv', ?_, Nat.le_trans (MpInt.used_le_of_mag_le h.valid.toShape hv'
    (by rw [hm']; exact Nat.div_le_self _ _)) h.used, ?_, h.aux⟩
  · have := h.room
    by_cases h1 : v = 1 ∨ t.used = 0
    · rw [(hq.copy h1).alloc]; omega
    · have hv1 : v ≠ 1 := fun e => h1 (Or.inl e)
      have hu : t.used ≠ 0 := fun e => h1 (Or.inr e)
      by_cases h2 : v &&& (v - 1) = 0
      · rw [ClampedTo.alloc (hq.pow2 hv1 hu h2)]; omega
      · rw [ClampedTo.alloc (hq.long hv1 hu h2)]; omega
  · rw [hval, MpInt.val_sval, sval_tdiv, hz, hm]; rfl

/-- `mp_mod_2d(x, sh, x)` (in place). -/
theorem xfer_mod2d {sh : Nat} (hx : x.Valid) (h : Mod2dPost x sh x x') : Settled x' x.alloc (x.mag % 2 ^ sh) x.sign :=
  have hm := Mod2dPost.spec hx hx.used_le hx.alloc_lt h
  ⟨hm.1, ClampedTo.alloc h, hm.2.1, ClampedTo.sign h⟩

/-- `mp_sub(x, b, x)` (in place), room for the larger operand plus one. -/
theorem xfer_sub {b : MpInt} {Vb : Int} {Ub alb : Nat} {Ab : Prop} (h : Acct x al U V A) (hb : Acct b alb Ub Vb Ab)
    (hroom : max x.used b.used + 1 ≤ x.alloc) {U' : Nat} (hU : (V - Vb).natAbs < radix ^ U')
    (hs : SubPost x b x x') : Acct x' al U' (V - Vb) A := by
  obtain ⟨hv, hval⟩ := hs.spec h.valid hb.valid hroom h.valid.alloc_lt
  have hal : x'.alloc = x.alloc := by
    by_cases e : x.sign = b.sign
    · by_cases c : cmpMag x b = .lt
      · exact (hs.lt e c).alloc
      · exact (hs.ge e c).alloc
    · exact (hs.diff e).alloc
  refine ⟨hv, by rw [hal]; exact h.room, used_le_of_lt hv ?_, by rw [hval, h.val, hb.val], h.aux⟩
  rw [← natAbs_val, hval, h.val, hb.val]; exact hU

/-- `mp_add(x, b, x)` (in place). -/
theorem xfer_add {b : MpInt} {Vb : Int} {Ub alb : Nat} {Ab : Prop} (h : Acct x al U V A) (hb : Acct b alb Ub Vb Ab)
    (hroom : max x.used b.used + 1 ≤ x.alloc) {U' : Nat} (hU : (V + Vb).natAbs < radix ^ U')
    (hs : AddPost x b x x') : Acct x' al U' (V + Vb) A := by
  obtain ⟨hv, hval⟩ := hs.spec h.valid hb.valid hroom h.valid.alloc_lt
  have hal : x'.alloc = x.alloc := by
    by_cases e : x.sign = b.sign
    · exact (hs.same e).alloc
    · by_cases c : cmpMag x b = .lt
      · exact (hs.lt e c).alloc
      · exact (hs.ge e c).alloc
  refine ⟨hv, by rw [hal]; exact h.room, used_le_of_lt hv ?_, by rw [hval, h.val, hb.val], h.aux⟩
  rw [← natAbs_val, hval, h.val, hb.val]; exact hU

/-- `mp_set(x, d)`. -/
theorem xfer_set {d : Nat} (hx : x.Shape) (hal : 0 < x.alloc) (hd : d < radix) (h : SetPost x d x') :
    Settled x' x.alloc d Layout.mpZpos :=
  have hm := h.spec hx hal hd
  ⟨hm.1, h.alloc, hm.2.1, by rw [h.sign]; split <;> rfl⟩

/-- `mp_lshd(x, k)`, room for `k` more digits. -/
theorem xfer_lshd (h : Settled x al M Layout.mpZpos) (hroom : x.used + k ≤ x.alloc) (hl : LshdPost x k x') :
    Settled x' al (M * radix ^ k) Layout.mpZpos := by
  obtain ⟨hv, hm⟩ := hl.spec h.valid hroom
  have hal : x'.alloc = x.alloc := by
    by_cases h0 : k = 0 ∨ x.used = 0
    · rw [hl.noop h0]
    · exact (hl.shift (by omega) (by omega)).alloc
  have hs : x'.sign = x.sign := by
    by_cases h0 : k = 0 ∨ x.used = 0
    · rw [hl.noop h0]
    · exact (hl.shift (by omega) (by omega)).sign
  exact ⟨hv, by rw [hal, h.alloc], by rw [hm, h.mag], by rw [hs, h.zpos]; split <;> rfl⟩

/-- `mp_mul(a, b, c)`. -/
theorem xfer_mul {a b c' : MpInt} {Ma Mb : Nat} (ha : a.val = Ma) (hb : b.val = Mb) (h : MulPost a b c') :
    Settled c' c'.alloc (Ma * Mb) Layout.mpZpos := by
  have hv := h.valid
  have e : c'.val = ((Ma * Mb : Nat) : Int) := by rw [h.val, ha, hb]; rfl
  have hm : c'.mag = Ma * Mb := by rw [← natAbs_val, e]; rfl
  refine ⟨hv, rfl, hm, ?_⟩
  rcases hv.sign_ok with e1 | e1
  · rw [e1]; split <;> rfl
  · have := hv.mag_pos_of_neg e1
    unfold MpInt.val at e; rw [if_pos e1] at e; omega

/-- `mp_cmp_d(x, 0)`: `MP_LT` exactly for a negative value. -/
theorem xfer_cmpD0 (h : Acct x al U V A) : cmpD x 0 = .lt ↔ V < 0 := by
  rw [cmpD_spec h.valid radix_pos, h.val]
  simp only [compare, compareOfLessAndEq]
  by_cases hv : V < 0
  · simp [hv]
  · simp only [Int.natCast_zero, hv, if_false, iff_false]; split <;> simp

/-- `mp_cmp(x, n)`: `MP_LT` exactly for `V < n`. -/
theorem xfer_cmp {Vn : Int} (h : Acct x al U V A) (hn : n.Valid) (hvn : n.val = Vn) : cmpS x n = .lt ↔ V < Vn := by
  rw [cmpS_spec h.valid hn, h.val, hvn]
  simp only [compare, compareOfLessAndEq]
  by_cases hv : V < Vn
  · simp [hv]
  · simp only [hv, if_false, iff_false]; split <;> simp

end

/-! ## Magnitude accounts -/

/-- A magnitude account: valid, `alloc`, `|x| = M`, the sign `s` or `MP_ZPOS` (a clamp on the way
reset it: what a chain of magnitude-only callees, `mp_mod_2d`/`s_mp_add`/`s_mp_sub`, leaves). -/
structure MagAcct (x : MpInt) (al M s : Nat) : Prop where
  valid : x.Valid
  alloc : x.alloc = al
  mag : x.mag = M
  sign : x.sign = Layout.mpZpos ∨ x.sign = s

section
variable {x x' n : MpInt} {al M s : Nat}

theorem sign_clamp {c' : MpInt} {t : Nat} (h : c'.sign = if c'.used = 0 then Layout.mpZpos else t)
    (ht : t = Layout.mpZpos ∨ t = s) : c'.sign = Layout.mpZpos ∨ c'.sign = s := by
  rw [h]; split
  · exact Or.inl rfl
  · exact ht

theorem MagAcct.start (hx : x.Valid) : MagAcct x x.alloc x.mag x.sign := ⟨hx, rfl, rfl, Or.inr rfl⟩

/-- `mp_div_2d(a, p, &q, a)` (`Api/MpDiv2dR.lean`): `a mod 2^p` in place, `a / 2^p` in `q`. -/
theorem xfer_div2dR {p : Nat} {q q' : MpInt} (h : MagAcct x al M s) (hq : q.Shape) (hroom : x.used ≤ q.alloc)
    (hd : Div2dPost x p q q') (hm : Mod2dPost x p x x') :
    MagAcct x' al (M % 2 ^ p) s ∧ MagAcct q' q.alloc (M / 2 ^ p) s := by
  obtain ⟨hv, hmm, -⟩ := Mod2dPost.spec h.valid h.valid.used_le h.valid.alloc_lt hm
  obtain ⟨hvq, hmq, -⟩ := Div2dPost.spec h.valid hroom hq.alloc_lt hd
  exact ⟨⟨hv, (ClampedTo.alloc hm).trans h.alloc, by rw [hmm, h.mag], sign_clamp (ClampedTo.sign hm) h.sign⟩,
    ⟨hvq, ClampedTo.alloc hd, by rw [hmq, h.mag], sign_clamp (ClampedTo.sign hd) h.sign⟩⟩

/-- `mp_mul(a, b, c)`, magnitudes (any signs). -/
theorem xfer_mulM {a b c' : MpInt} (h : MulPost a b c') : c'.Valid ∧ c'.mag = a.mag * b.mag :=
  ⟨h.valid, by rw [← natAbs_val, h.val, Int.natAbs_mul, natAbs_val, natAbs_val]⟩

/-- `s_mp_add(x, b, x)` (in place, room: `Api/SAddAlias.lean`). -/
theorem xfer_saddI {b : MpInt} (h : MagAcct x al M s) (hb : b.Shape) (hroom : max x.used b.used + 1 ≤ x.alloc)
    (hs : SAddPost x b x x') : MagAcct x' al (M + b.mag) s := by
  obtain ⟨hv, hm⟩ := hs.spec h.valid.toShape hb hroom h.valid.alloc_lt h.valid.sign_ok
  exact ⟨hv, hs.alloc.trans h.alloc, by rw [hm, h.mag], sign_clamp hs.sign h.sign⟩

/-- `s_mp_sub(x, n, x)` (in place, `|n| ≤ |x|`: `Api/SSubAlias.lean`). -/
theorem xfer_ssubM (h : MagAcct x al M s) (hn : n.Shape) (hle : n.mag ≤ M) (hs : SSubPost x n x x') :
    MagAcct x' al (M - n.mag) s := by
  obtain ⟨hv, hm⟩ := hs.spec h.valid.toShape hn (by rw [h.mag]; exact hle) h.valid.used_le h.valid.alloc_lt
    h.valid.sign_ok
  exact ⟨hv, hs.alloc.trans h.alloc, by rw [hm, h.mag], sign_clamp hs.sign h.sign⟩

/-- `mp_div(a, b, c, d)`'s remainder `d'` (`DivRem`, any `c`, also `NULL`): `|a| mod |b|`, `a`'s sign.
The room is needed only in the copy case (`|a| < |b|`, `mp_copy(a, d)`). -/
theorem xfer_divRem {a b d d' : MpInt} (ha : a.Valid)
    (hroom : a.mag < b.mag → a.used ≤ d.alloc) (hd : d.alloc < 2 ^ 31) (h : DivRem a b d d') :
    Settled d' d'.alloc (a.mag % b.mag) a.sign := by
  by_cases hs : a.mag < b.mag
  · have hc := h.small hs
    obtain ⟨hv, hm, -⟩ := ClampedTo.spec hc ha.digit_lt ha.high_zero (hroom hs) hd ha.sign_ok
    exact ⟨hv, rfl, by rw [hm, Nat.mod_eq_of_lt hs]; rfl, hc.sign⟩
  · have hp := h.big (Nat.le_of_not_lt hs)
    exact ⟨hp.valid, rfl, hp.mag, hp.sign⟩

/-- `mp_div(a, b, c, d)`'s quotient `c'` (`DivQuot`, any `d`, also `NULL`; `c = a` too). -/
theorem xfer_divQuot {a b c c' : MpInt} (ha : a.Valid) (hb : b.Valid) (hb0 : 0 < b.used) (hau : a.used + 2 < 2 ^ 31)
    (hc : c.alloc < 2 ^ 31) (h : DivQuot a b c c') : MagAcct c' c'.alloc (a.mag / b.mag) (divSign a.sign b.sign) := by
  obtain ⟨hv, hm, -⟩ := DivQuot.spec ha hb hb0 hau hc h
  refine ⟨hv, rfl, hm, ?_⟩
  by_cases hs : a.mag < b.mag
  · left; rw [(h.small hs).sign]; split <;> rfl
  · exact Or.inr (h.big (Nat.le_of_not_lt hs)).sign

/-- `mp_2expt(a, k)` (room: `Api/Expt2.lean`). -/
theorem xfer_expt2 {a a' : MpInt} {k : Nat} (hroom : k / Layout.digitBits + 1 ≤ a.alloc) (hal : a.alloc < 2 ^ 31)
    (h : Expt2Post a k a') : Settled a' a.alloc (2 ^ k) Layout.mpZpos :=
  have hs := h.spec hroom hal
  ⟨hs.1, h.alloc, hs.2.1, by rw [h.sign]; split <;> rfl⟩

/-- `mp_add(a, b, c)` growing `c` (`Api/MpAddG.lean`'s `Q`). -/
theorem xfer_addG {a b c c' : MpInt} (ha : a.Valid) (hb : b.Valid) (hc : c.Shape) (h31 : max a.used b.used + 1 < 2 ^ 31)
    (h : AddG a b (SAddPost a b (sAddIn a b (c.withSign a.sign)) c') (SSubPost b a (sSubIn b (c.withSign b.sign)) c')
      (SSubPost a b (sSubIn a (c.withSign a.sign)) c')) : HasVal c' (a.val + b.val) := by
  have hsa := sign_cases ha.sign_ok
  have hsb := sign_cases hb.sign_ok
  rw [MpInt.val_eq (a := a), MpInt.val_eq (a := b)]
  by_cases hs : a.sign = b.sign
  · have hp := h.same hs
    have g := sAddIn_grown (a := a) (b := b) (hc.withSign a.sign) h31
    obtain ⟨hv, hm⟩ := SAddPost.spec ha.toShape hb.toShape (sAddIn_room _ _ _) g.shape.alloc_lt
      (by rw [g.sign]; exact ha.sign_ok) hp
    have hsg : c'.sign = if c'.used = 0 then Layout.mpZpos else a.sign := by rw [hp.sign, g.sign]; rfl
    refine ⟨hv, ?_⟩
    rw [val_of_post hsg hm, ← hs]
    simp only [Layout.mpNeg] at *
    rcases hsa with h0 | h0 <;> simp [h0] <;> omega
  · by_cases hlt : a.mag < b.mag
    · have hp := h.lt hs hlt
      have g := sSubIn_grown (a := b) (hc.withSign b.sign) (by have := hb.used_le; have := hb.alloc_lt; omega)
      obtain ⟨hv, hm⟩ := SSubPost.spec hb.toShape ha.toShape (Nat.le_of_lt hlt) (sSubIn_room _ _) g.shape.alloc_lt
        (by rw [g.sign]; exact hb.sign_ok) hp
      have hsg : c'.sign = if c'.used = 0 then Layout.mpZpos else b.sign := by rw [hp.sign, g.sign]; rfl
      refine ⟨hv, ?_⟩
      rw [val_of_post hsg hm]
      simp only [Layout.mpNeg] at *
      rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega
    · have hp := h.ge hs hlt
      have g := sSubIn_grown (a := a) (hc.withSign a.sign) (by have := ha.used_le; have := ha.alloc_lt; omega)
      obtain ⟨hv, hm⟩ := SSubPost.spec ha.toShape hb.toShape (Nat.le_of_not_lt hlt) (sSubIn_room _ _) g.shape.alloc_lt
        (by rw [g.sign]; exact ha.sign_ok) hp
      have hsg : c'.sign = if c'.used = 0 then Layout.mpZpos else a.sign := by rw [hp.sign, g.sign]; rfl
      refine ⟨hv, ?_⟩
      rw [val_of_post hsg hm]
      simp only [Layout.mpNeg] at *
      rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega

/-- `mp_mod(a, b, c)` (`ModPost`, no machine contract yet), `b > 0`: `c = a mod b` in `[0, b)`. -/
theorem xfer_mod {a b c' : MpInt} (ha : a.Valid) (hb : b.Valid) (hb0 : 0 < b.used) (hpos : 0 < b.val)
    (h : ModPost a b c') : HasVal c' (a.val % b.val) :=
  have hs := ModPost.spec ha hb hb0 h
  ⟨hs.valid, by rw [hs.val, Int.fmod_eq_emod_of_nonneg _ (Int.le_of_lt hpos)]⟩

end

/-! ## Transfers for `mp_invmod`

`mp_div_2` in place, `mp_mod` (no frozen contract: its Spec Post `ModPost`), the macros
`MP_IS_ODD`/`MP_IS_ZERO` and the sign test `x->sign == MP_NEG`, `mp_cmp_d(x, d) == MP_EQ`,
`mp_cmp_mag(x, n) == MP_LT`; and the bound an in-place `mp_add`/`mp_sub` result meets when
both operands are below the room (`Acct.fit`). -/

/-- `MP_IS_ODD(x)` as the C (and the code) reads it: `used > 0` and the low bit of `dp[0]`. -/
def isOdd (x : MpInt) : Prop := 0 < x.used ∧ x.digit 0 % 2 = 1

section
variable {x x' n : MpInt} {al U : Nat} {V : Int} {A : Prop}

theorem Acct.mono {U' : Nat} (h : Acct x al U V A) (hU : U ≤ U') : Acct x al U' V A :=
  ⟨h.valid, h.room, Nat.le_trans h.used hU, h.val, h.aux⟩

/-- Both operands below `D - 1` digits: the sum and the difference are below `radix ^ D`. -/
theorem Acct.fit {W : Int} {D alb Ub : Nat} {Ab : Prop} (h : Acct x al U V A) (hn : Acct n alb Ub W Ab)
    (hroom : max x.used n.used + 1 ≤ D) : (V - W).natAbs < radix ^ D ∧ (V + W).natAbs < radix ^ D := by
  have h1 := MpInt.mag_lt h.valid.toShape
  have h2 := MpInt.mag_lt hn.valid.toShape
  rw [h.mag] at h1; rw [hn.mag] at h2
  have e1 := Nat.pow_le_pow_right radix_pos (show x.used ≤ D - 1 by omega)
  have e2 := Nat.pow_le_pow_right radix_pos (show n.used ≤ D - 1 by omega)
  have e3 : radix ^ D = radix * radix ^ (D - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have e4 : 2 * radix ^ (D - 1) ≤ radix * radix ^ (D - 1) := Nat.mul_le_mul_right _ (by decide)
  have s1 := Int.natAbs_sub_le V W
  have s2 := Int.natAbs_add_le V W
  omega

/-- `mp_div_2(x, x)` (in place): the value halved toward zero. -/
theorem xfer_div2 (h : Acct x al U V A) (hd : Div2Post x x x') : Acct x' al U (V.tdiv 2) A := by
  obtain ⟨hv, hm, hval⟩ := Div2Post.spec h.valid h.valid.used_le h.valid.alloc_lt hd
  exact ⟨hv, by rw [hd.alloc]; exact h.room,
    Nat.le_trans (MpInt.used_le_of_mag_le h.valid.toShape hv (by rw [hm]; exact Nat.div_le_self _ _)) h.used,
    by rw [hval, h.val], h.aux⟩

/-- `mp_mod(a, n, x)`, `n > 0` (`ModPost`, `Tom/Spec/Div.lean`): the Euclidean remainder, so
`used ≤ n.used`; its `alloc` is not known. -/
theorem xfer_modA {a : MpInt} (ha : a.Valid) (hn : n.Valid) (hz : n.sign = Layout.mpZpos) (hn0 : 0 < n.used)
    (h : ModPost a n x') : Acct x' 0 n.used (a.val % n.val) True := by
  have hv := ModPost.spec ha hn hn0 h
  have hnv : n.val = n.mag := val_zpos hz
  have hpos := hn.mag_pos hn0
  rw [Int.fmod_eq_emod_of_nonneg _ (by omega)] at hv
  have h0 := Int.emod_nonneg a.val (show n.val ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos a.val (show 0 < n.val by omega)
  refine ⟨hv.valid, Nat.zero_le _, used_le_of_lt hv.valid ?_, hv.val, trivial⟩
  have := MpInt.mag_lt hn.toShape
  have e := Int.natAbs_of_nonneg h0
  rw [← natAbs_val, hv.val]; omega

/-- `MP_IS_ODD(x)`: the value is odd. -/
theorem xfer_isOdd (h : Acct x al U V A) : isOdd x ↔ V % 2 = 1 := by
  have e1 : x.mag % 2 = x.digit 0 % 2 := by
    rw [← Mont.MpInt.mag_mod_radix h.valid.toShape, Nat.mod_mod_of_dvd _ (show 2 ∣ radix from ⟨134217728, rfl⟩)]
  have e2 : V % 2 = 1 ↔ x.mag % 2 = 1 := by rw [← h.val]; unfold MpInt.val; split <;> omega
  unfold isOdd; rw [e2, e1]
  refine ⟨fun hh => hh.2, fun hh => ⟨Nat.pos_of_ne_zero fun hu => ?_, hh⟩⟩
  rw [h.valid.high_zero 0 (by omega)] at hh; exact absurd hh (by decide)

/-- `MP_IS_ZERO(x)`: the value is zero. -/
theorem xfer_isZero (h : Acct x al U V A) : x.used = 0 ↔ V = 0 := by
  rw [← h.val]
  refine ⟨fun hu => by unfold MpInt.val; rw [MpInt.mag_used_zero hu]; split <;> rfl, fun hv => ?_⟩
  have hm : x.mag = 0 := by rw [← natAbs_val, hv]; rfl
  refine Nat.eq_zero_of_not_pos fun hu => ?_
  have := MpInt.mag_ge h.valid hu; have := Nat.pow_pos (n := x.used - 1) radix_pos
  omega

/-- `x->sign == MP_NEG`: the value is negative. -/
theorem xfer_isNeg (h : Acct x al U V A) : x.sign = Layout.mpNeg ↔ V < 0 := by
  rw [← h.val]; unfold MpInt.val
  refine ⟨fun hn => ?_, fun hl => Classical.byContradiction fun hn => ?_⟩
  · rw [if_pos hn]; have := h.valid.mag_pos_of_neg hn; omega
  · rw [if_neg hn] at hl; omega

/-- `mp_cmp_d(x, d) == MP_EQ`: the value is `d`. -/
theorem xfer_cmpDeq {d : Nat} (h : Acct x al U V A) (hd : d < radix) : cmpD x d = .eq ↔ V = d := by
  rw [cmpD_spec h.valid hd, h.val]; exact Int.compare_eq_eq

/-- `mp_cmp_mag(x, n) == MP_LT`: `|V| < |n|`. -/
theorem xfer_cmpMag (h : Acct x al U V A) (hn : n.Valid) : cmpMag x n = .lt ↔ V.natAbs < n.mag := by
  rw [cmpMag_eq h.valid hn, h.mag]; exact Nat.compare_eq_lt

end

/-! ## Transfers of the exponentiations (`mp_exptmod`, `s_mp_exptmod(_fast)`) -/

section
variable {x x' a b c d' t : MpInt} {al M : Nat}

/-- A valid nonnegative result as an account. -/
theorem settled_zpos (hv : t.Valid) (hs : t.sign = Layout.mpZpos) (hm : t.mag = M) :
    Settled t t.alloc M Layout.mpZpos :=
  ⟨hv, rfl, hm, by rw [hs]; split <;> rfl⟩

/-- A valid result with a nonnegative value is a nonnegative account. -/
theorem settled_of_val (hv : t.Valid) (e : t.val = (M : Int)) : Settled t t.alloc M Layout.mpZpos := by
  have hm : t.mag = M := by rw [← natAbs_val, e]; rfl
  refine ⟨hv, rfl, hm, ?_⟩
  rcases hv.sign_ok with e1 | e1
  · rw [e1]; split <;> rfl
  · have := hv.mag_pos_of_neg e1
    unfold MpInt.val at e; rw [if_pos e1] at e; omega

/-- `mp_sqr(a, b)`. -/
theorem xfer_sqr {Ma : Nat} (ha : a.val = Ma) (h : SqrPost a b) : Settled b b.alloc (Ma * Ma) Layout.mpZpos :=
  xfer_mul ha ha ⟨h.valid, h.val⟩

/-- `mp_montgomery_reduce(x, n, rho)`, `s_mp_montgomery_reduce_fast(x, n, rho)`. -/
theorem xfer_redc {n : MpInt} {rho : Nat} (h : Settled x al M Layout.mpZpos) (hr : Mont.RedcPost x n rho x') :
    Settled x' al (Mont.redc M n.mag rho n.used) Layout.mpZpos :=
  ⟨hr.valid, by rw [hr.alloc, h.alloc], by rw [hr.mag, h.mag], by rw [hr.sign, h.zpos]⟩

/-- `mp_dr_reduce(x, n, k)`. -/
theorem xfer_drReduce {n : MpInt} {k : Nat} (h : Settled x al M Layout.mpZpos) (hr : Reduce.DrReducePost x n k x') :
    Settled x' x'.alloc (Reduce.redLoop (Reduce.drFold n.used k) n.mag (M + 1) M) Layout.mpZpos :=
  ⟨hr.valid, rfl, by rw [hr.mag, h.mag], by rw [hr.sign, h.zpos]⟩

/-- `mp_reduce_2k(x, n, d)`, `mp_reduce_2k_l(x, n, d)` (`d = |d|`). -/
theorem xfer_reduce2k {n : MpInt} {d : Nat} (h : Settled x al M Layout.mpZpos) (hr : Reduce.Reduce2kPost x n d x') :
    Settled x' x'.alloc (Reduce.redLoop (Reduce.fold2k (Mont.nbits n.mag) d) n.mag (M + 1) M) Layout.mpZpos :=
  settled_zpos hr.valid (hr.sign.elim id fun e => e.trans h.zpos) (by rw [hr.mag, h.mag])

/-- `mp_reduce(x, m, mu)` (Barrett), `mu` from `mp_reduce_setup`, `x < radix^(2 m->used)`. -/
theorem xfer_reduce {m mu : MpInt} (h : Settled x al M Layout.mpZpos) (hm : m.Valid) (hk : 0 < m.used)
    (hmu : Reduce.ReduceSetupPost m mu) (hxb : M < radix ^ (2 * m.used)) (hr : Reduce.ReducePost x m mu x') :
    Settled x' x'.alloc (M % m.mag) Layout.mpZpos := by
  obtain ⟨hv, hmag, -⟩ := hr.spec h.valid.toShape hm hmu.valid.toShape hk hmu.mag (by rw [h.mag]; exact hxb)
  exact settled_zpos hv hr.sign (by rw [hmag, h.mag])

/-- `mp_montgomery_calc_normalization(a, b)`, `b` odd, `> 1`: `R mod b`. -/
theorem xfer_norm (hb : b.Valid) (hodd : b.mag % 2 = 1) (h1 : 1 < b.mag) (h : Mont.NormPost b a) :
    Settled a a.alloc (radix ^ b.used % b.mag) Layout.mpZpos :=
  settled_zpos h.valid h.sign (h.spec hb hodd h1).2.1

/-- `mp_mulmod(a, b, c, d)`, `c > 0`. -/
theorem xfer_mulmod (hc : 0 < c.val) (h : Reduce.MulmodPost a b c d') :
    Settled d' d'.alloc ((a.val * b.val) % c.val).toNat Layout.mpZpos := by
  obtain ⟨hv, h0, -, he⟩ := h.spec hc
  exact settled_of_val hv (by rw [Int.toNat_of_nonneg (by rw [← he]; exact h0)]; exact he)

/-- `mp_mod(a, b, c)`, `b > 0`: `a mod b` in `[0, b)`. -/
theorem xfer_modE (ha : a.Valid) (hb : b.Valid) (hb0 : 0 < b.used) (hs : b.sign = Layout.mpZpos)
    (h : ModPost a b c) : Settled c c.alloc (a.val % b.val).toNat Layout.mpZpos := by
  have hv := h.spec ha hb hb0
  have hbv : 0 < b.val := by rw [val_zpos hs]; have := hb.mag_pos hb0; omega
  have e : c.val = a.val % b.val := by rw [hv.val, Int.fmod_eq_emod_of_nonneg _ (by omega)]
  exact settled_of_val hv.valid (by rw [e, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))])

/-- `mp_abs(a, &t)` into a fresh `t`: the digit twin, `MP_ZPOS`. -/
theorem xfer_absD {n : Nat} (ha : a.Shape) (h : AbsPost a (MpInt.zeroN n) t) :
    t.digit = a.digit ∧ t.used = a.used ∧ t.sign = Layout.mpZpos :=
  ⟨funext fun i => by
    rw [h.digit]; split
    · rfl
    · rw [if_neg (by simp [MpInt.zeroN]), MpInt.zeroN_digit, ha.high_zero i (by omega)], h.used, h.sign⟩

end

end Tom.Ledger
