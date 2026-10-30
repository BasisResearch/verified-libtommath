import Tom.Spec.MpInt

/-!
# The sliding-window loop of `s_mp_exptmod` and `s_mp_exptmod_fast`

Both functions (`vendor/libtommath/bn_s_mp_exptmod.c`, `bn_s_mp_exptmod_fast.c`)
run the same left-to-right sliding-window loop over the bits of the exponent
`X`; they differ only in the reduction `redux` and in the representation of the
values (Montgomery form `v·R mod P` with `R = radix ^ P.used`, or plain `v mod P`
with `R = 1`). This file states the loop over `Nat` values with an abstract
reduction `red : Nat → Nat` (the value `redux` leaves, as a function of the value
it is given) and proves it computes `g ^ X · R mod P`.

* `winSize`: the window size from `mp_count_bits(X)`.
* `table`: the precomputed table (`M[1]`, `M[2^(w-1)]` by `w - 1` squarings,
  `M[x] = redux(M[x-1]·M[1])` above); `table_ok`: every entry used holds `g^x`.
* `bitStep`: one pass of the `for (;;)` body on the exponent bit `y`
  (state `St`: `mode`, `bitcpy`, `bitbuf`, `res`); `runBits`: the 28 bits of one
  digit, most significant first; `runDigits`: the digits from `used - 1` down to
  `0`; `finish`: the tail `if ((mode == 2) && (bitcpy > 0))`.
* `Inv`: the loop invariant (three modes); `bitStep_inv`, `runBits_inv`,
  `runDigits_inv`.
* `window_correct`: the final `res` is `enc P R g X = (g ^ X · R) % P`;
  `fixup_correct`: Montgomery's final `redux` gives `g ^ X % P`.
* `bit_extract`, `buf_shift`: the C's `y = (buf >> 27) & 1; buf <<= 1` on
  `uint32` reads the digit's bits most significant first; `or_bit`: the C's
  `bitbuf |= y << (winsize - ++bitcpy)` adds a fresh bit; `and_bit`: the tail's
  `bitbuf & (1 << winsize)`.

The C's outer bookkeeping (`bitcnt`, `digidx`, `buf`): at the top of the loop,
with digit `i` read and `t` of its bits done (`1 ≤ t ≤ 28`), `bitcnt = 29 - t`,
`digidx = i - 1`, `buf = (X->dp[i] * 2^t) % 2^32` (`buf_shift`); the refill
`--bitcnt == 0` happens exactly when `t = 28` (initially `bitcnt = 1` stands for
`t = 28` of a digit `X->used`), and the loop breaks when it would read digit
`-1`. So the bits it consumes are those of `runDigits`.
-/

namespace Tom.Window

/-! ## Window size and representation -/

/-- `winsize` from `x = mp_count_bits(X)` (`MAX_WINSIZE = 0`: no cap). -/
def winSize (x : Nat) : Nat :=
  if x ≤ 7 then 2 else if x ≤ 36 then 3 else if x ≤ 140 then 4 else if x ≤ 450 then 5
  else if x ≤ 1303 then 6 else if x ≤ 3529 then 7 else 8

theorem two_le_winSize (x : Nat) : 2 ≤ winSize x := by
  unfold winSize; repeat' split
  all_goals omega

theorem winSize_le (x : Nat) : winSize x ≤ 8 := by
  unfold winSize; repeat' split
  all_goals omega

/-- The table fits `M[TAB_SIZE]`, `TAB_SIZE = 256`. -/
theorem two_pow_winSize_le (x : Nat) : 2 ^ winSize x ≤ 256 :=
  Nat.le_trans (Nat.pow_le_pow_right (by decide) (winSize_le x)) (by decide)

/-- The value representing exponent `e`: `g^e · R mod P`. -/
def enc (P R g e : Nat) : Nat := (g ^ e * R) % P

theorem enc_lt {P : Nat} (hP : 0 < P) (R g e : Nat) : enc P R g e < P := Nat.mod_lt _ hP

/-- A product of two values below `P` is a legal `redux` argument. -/
theorem mul_le_sq {P a b : Nat} (ha : a < P) (hb : b < P) : a * b ≤ (P - 1) * (P - 1) :=
  Nat.mul_le_mul (by omega) (by omega)

/-- What the window loop needs of `redux`: on every argument up to `(P-1)^2` it
returns a value below `P` that is the argument divided by `R` mod `P`, with `R`
invertible mod `P`. (`R = 1`: Barrett, diminished radix, `2^k`; `R = radix^P.used`:
Montgomery.) -/
structure Red (red : Nat → Nat) (P R : Nat) : Prop where
  lt : ∀ x, x ≤ (P - 1) * (P - 1) → red x < P
  mod : ∀ x, x ≤ (P - 1) * (P - 1) → (red x * R) % P = x % P
  coprime : Nat.Coprime P R

/-! ## Cancelling `R` mod `P` -/

theorem mod_eq_of_dvd_sub {P a b : Nat} (hba : b ≤ a) (h : P ∣ a - b) : a % P = b % P := by
  obtain ⟨c, hc⟩ := h
  rw [show a = b + P * c by omega, Nat.add_mul_mod_self_left]

theorem cancel_le {P R a b : Nat} (hc : Nat.Coprime P R) (hba : b ≤ a)
    (h : (a * R) % P = (b * R) % P) : a % P = b % P := by
  have h1 : P ∣ (a - b) * R := by
    rw [Nat.sub_mul]; exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h)
  exact mod_eq_of_dvd_sub hba (hc.dvd_of_dvd_mul_right h1)

/-- `a·R ≡ b·R (mod P)` with `R` invertible mod `P` gives `a ≡ b`. -/
theorem cancel {P R a b : Nat} (hc : Nat.Coprime P R) (h : (a * R) % P = (b * R) % P) :
    a % P = b % P := by
  rcases Nat.le_total b a with hba | hab
  · exact cancel_le hc hba h
  · exact (cancel_le hc hab h.symm).symm

/-- **The step lemma**: reducing the product of two represented values represents
the sum of the exponents. -/
theorem red_mul {red : Nat → Nat} {P R g : Nat} (hr : Red red P R) (hP : 0 < P) (e1 e2 : Nat) :
    red (enc P R g e1 * enc P R g e2) = enc P R g (e1 + e2) := by
  have hle := mul_le_sq (enc_lt hP R g e1) (enc_lt hP R g e2)
  have h1 := hr.mod _ hle
  have h2 : (enc P R g e1 * enc P R g e2) % P = (g ^ (e1 + e2) * R * R) % P := by
    unfold enc
    rw [← Nat.mul_mod, Nat.pow_add]
    congr 1
    rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_left_comm R (g ^ e2) R]
  have h3 := cancel hr.coprime (h1.trans h2)
  rw [Nat.mod_eq_of_lt (hr.lt _ hle)] at h3
  exact h3

/-- `redux` of a represented value divides by `R` once more: Montgomery's final
fixup turns `g^e · R mod P` into `g^e mod P`. -/
theorem red_enc {red : Nat → Nat} {P R g : Nat} (hr : Red red P R) (hP : 0 < P) (e : Nat) :
    red (enc P R g e) = g ^ e % P := by
  have hle : enc P R g e ≤ (P - 1) * (P - 1) := by
    have := enc_lt hP R g e
    rcases Nat.lt_or_ge P 2 with h | h
    · rw [show P = 1 by omega] at this ⊢; omega
    · exact Nat.le_trans (by omega : enc P R g e ≤ (P - 1) * 1) (Nat.mul_le_mul_left _ (by omega))
  have h1 := hr.mod _ hle
  have h2 : (enc P R g e) % P = (g ^ e * R) % P := by unfold enc; exact Nat.mod_mod _ _
  have h3 := cancel hr.coprime (h1.trans h2)
  rwa [Nat.mod_eq_of_lt (hr.lt _ hle)] at h3

/-! ## Squarings -/

/-- `n` rounds of `v = redux(v·v)` (the C's `for (x = 0; x < n; x++)` of
`mp_sqr` + `redux`). -/
def sqIter (red : Nat → Nat) : Nat → Nat → Nat
  | 0, v => v
  | n + 1, v => red (sqIter red n v * sqIter red n v)

theorem sqIter_enc {red : Nat → Nat} {P R g : Nat} (hr : Red red P R) (hP : 0 < P) (e : Nat) :
    ∀ n, sqIter red n (enc P R g e) = enc P R g (e * 2 ^ n)
  | 0 => by simp [sqIter]
  | n + 1 => by
    rw [sqIter, sqIter_enc hr hP e n, red_mul hr hP, Nat.pow_succ]
    congr 1; rw [Nat.mul_two, Nat.mul_add]

/-! ## The table -/

/-- `M[2^(w-1) + j]`: `M[2^(w-1)]` is `M[1]` squared `w - 1` times, and each
next entry is `redux(M[x-1] · M[1])`. -/
def tblUp (red : Nat → Nat) (m1 w : Nat) : Nat → Nat
  | 0 => sqIter red (w - 1) m1
  | j + 1 => red (tblUp red m1 w j * m1)

/-- The table `M[x]` as the C builds it (entries `1` and `2^(w-1) .. 2^w - 1`;
the others are never read). -/
def table (red : Nat → Nat) (m1 w x : Nat) : Nat :=
  if x = 1 then m1 else tblUp red m1 w (x - 2 ^ (w - 1))

/-- The table entries the loop reads represent their index. -/
structure TableOk (P R g w : Nat) (M : Nat → Nat) : Prop where
  one : M 1 = enc P R g 1
  upper : ∀ x, 2 ^ (w - 1) ≤ x → x < 2 ^ w → M x = enc P R g x

theorem tblUp_enc {red : Nat → Nat} {P R g : Nat} (hr : Red red P R) (hP : 0 < P) (w : Nat) :
    ∀ j, tblUp red (enc P R g 1) w j = enc P R g (2 ^ (w - 1) + j)
  | 0 => by rw [tblUp, sqIter_enc hr hP, Nat.one_mul, Nat.add_zero]
  | j + 1 => by rw [tblUp, tblUp_enc hr hP w j, red_mul hr hP, Nat.add_assoc]

/-- **The table**: from `M[1] = g·R mod P`, every entry read holds `g^x·R mod P`. -/
theorem table_ok {red : Nat → Nat} {P R g w : Nat} (hr : Red red P R) (hP : 0 < P) (hw : 2 ≤ w) :
    TableOk P R g w (table red (enc P R g 1) w) where
  one := by simp [table]
  upper x h1 _ := by
    have : 2 ≤ 2 ^ (w - 1) := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ w - 1 by omega); simpa using this
    rw [table, ite_eq_right_of_eq_false _ _ (by simp; omega), tblUp_enc hr hP, Nat.add_sub_cancel' h1]

/-! ## The loop -/

/-- The loop state: `mode`, `bitcpy`, `bitbuf` and the value of `res`. -/
structure St where
  mode : Nat
  bitcpy : Nat
  bitbuf : Nat
  res : Nat

/-- The state before the loop (`mode = 0`, `bitcpy = 0`, `bitbuf = 0`, `res`). -/
def start (res0 : Nat) : St := ⟨0, 0, 0, res0⟩

/-- One pass of the loop body on bit `y`: skip leading zeros (`mode == 0`),
square on a zero between windows (`mode == 1`), else add `y` to the window
(`bitbuf |= y << (w - ++bitcpy)`, `or_bit`) and, when it is full, square `w`
times and multiply by `M[bitbuf]`. -/
def bitStep (red : Nat → Nat) (M : Nat → Nat) (w : Nat) (s : St) (y : Nat) : St :=
  if s.mode = 0 ∧ y = 0 then s
  else if s.mode = 1 ∧ y = 0 then { s with res := red (s.res * s.res) }
  else
    let bc := s.bitcpy + 1
    let bb := s.bitbuf + y * 2 ^ (w - bc)
    if bc = w then ⟨1, 0, 0, red (sqIter red w s.res * M bb)⟩
    else ⟨2, bc, bb, s.res⟩

/-- The first `t` bits of digit `d`, most significant first (bit `27 - i` at
step `i`). -/
def runBits (red : Nat → Nat) (M : Nat → Nat) (w : Nat) (s : St) (d : Nat) : Nat → St
  | 0 => s
  | t + 1 => bitStep red M w (runBits red M w s d t) (d / 2 ^ (27 - t) % 2)

/-- Digits `n - 1` down to `0` of `dig`, each by `runBits … 28`. -/
def runDigits (red : Nat → Nat) (M : Nat → Nat) (w : Nat) (dig : Nat → Nat) : Nat → St → St
  | 0, s => s
  | n + 1, s => runDigits red M w dig n (runBits red M w s (dig n) 28)

/-- The tail loop `for (x = 0; x < bitcpy; x++)`: square, shift `bitbuf`, and
multiply by `M[1]` when bit `w` of `bitbuf` is set; on `(res, bitbuf)`. -/
def tailLoop (red : Nat → Nat) (M : Nat → Nat) (w : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | n + 1, p =>
    let q := tailLoop red M w n p
    let r := red (q.1 * q.1)
    let bb := q.2 * 2
    (if bb / 2 ^ w % 2 = 1 then red (r * M 1) else r, bb)

/-- The value of `res` after the loop and the tail
(`if ((mode == 2) && (bitcpy > 0))`). -/
def finish (red : Nat → Nat) (M : Nat → Nat) (w : Nat) (s : St) : Nat :=
  if s.mode = 2 ∧ 0 < s.bitcpy then (tailLoop red M w s.bitcpy (s.res, s.bitbuf)).1 else s.res

/-! ## The invariant -/

/-- The loop invariant after the bits forming the number `E`:
* `idle`: only zero bits so far, `res` untouched;
* `sqr`: between windows, `res` represents `E`;
* `win`: a window of `c` bits `b` (top bit set) is pending in `bitbuf`
  (`b·2^(w-c)`), `res` represents the bits above it. -/
inductive Inv (P R g w res0 : Nat) : Nat → St → Prop
  | idle : Inv P R g w res0 0 ⟨0, 0, 0, res0⟩
  | sqr (e : Nat) : Inv P R g w res0 e ⟨1, 0, 0, enc P R g e⟩
  | win (eh b c : Nat) (hc0 : 0 < c) (hcw : c < w) (hb1 : 2 ^ (c - 1) ≤ b) (hb2 : b < 2 ^ c) :
      Inv P R g w res0 (eh * 2 ^ c + b) ⟨2, c, b * 2 ^ (w - c), enc P R g eh⟩

theorem inv_start (P R g w res0 : Nat) : Inv P R g w res0 0 (start res0) := Inv.idle

/-- The hypotheses of the step lemmas. -/
structure Ctx (red : Nat → Nat) (M : Nat → Nat) (P R g w res0 : Nat) : Prop where
  red : Red red P R
  pos : 0 < P
  w2 : 2 ≤ w
  tab : TableOk P R g w M
  res0 : res0 = enc P R g 0

theorem two_pow_pos' (n : Nat) : 0 < 2 ^ n := Nat.two_pow_pos n

theorem step_idle {red : Nat → Nat} {M : Nat → Nat} {P R g w res0 : Nat}
    (cx : Ctx red M P R g w res0) {y : Nat} (hy : y ≤ 1) :
    Inv P R g w res0 (2 * 0 + y) (bitStep red M w ⟨0, 0, 0, res0⟩ y) := by
  have hw := cx.w2
  rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl
  · simp only [bitStep, and_self, ite_true]; exact Inv.idle
  · simp only [bitStep, show ¬ (0 + 1 = w) by omega, ite_false, Nat.zero_add, Nat.one_mul,
      show ¬ (0 = 1 ∧ 1 = 0) by omega]
    have := Inv.win (P := P) (R := R) (g := g) (w := w) (res0 := res0) 0 1 1 (by omega) (by omega)
      (by simp) (by simp)
    rw [← cx.res0] at this
    simpa using this

theorem step_sqr {red : Nat → Nat} {M : Nat → Nat} {P R g w res0 : Nat}
    (cx : Ctx red M P R g w res0) (e : Nat) {y : Nat} (hy : y ≤ 1) :
    Inv P R g w res0 (2 * e + y) (bitStep red M w ⟨1, 0, 0, enc P R g e⟩ y) := by
  have hw := cx.w2
  rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl
  · simp only [bitStep, and_self, ite_true]
    rw [red_mul cx.red cx.pos, Nat.add_zero, Nat.two_mul]; exact Inv.sqr _
  · simp only [bitStep, show ¬ (1 = 0 ∧ 1 = 0) by omega,
      show ¬ (0 + 1 = w) by omega, ite_false, Nat.zero_add, Nat.one_mul]
    have := Inv.win (P := P) (R := R) (g := g) (w := w) (res0 := res0) e 1 1 (by omega) (by omega)
      (by simp) (by simp)
    rw [show 2 * e + 1 = e * 2 ^ 1 + 1 by omega]; simpa using this

theorem step_win {red : Nat → Nat} {M : Nat → Nat} {P R g w res0 : Nat}
    (cx : Ctx red M P R g w res0) (eh b c : Nat) (hc0 : 0 < c) (hcw : c < w)
    (hb1 : 2 ^ (c - 1) ≤ b) (hb2 : b < 2 ^ c) {y : Nat} (hy : y ≤ 1) :
    Inv P R g w res0 (2 * (eh * 2 ^ c + b) + y)
      (bitStep red M w ⟨2, c, b * 2 ^ (w - c), enc P R g eh⟩ y) := by
  have hbb : b * 2 ^ (w - c) + y * 2 ^ (w - (c + 1)) = (2 * b + y) * 2 ^ (w - (c + 1)) := by
    rw [show w - c = (w - (c + 1)) + 1 by omega, Nat.pow_succ]
    rw [Nat.add_mul, Nat.mul_comm 2 b, Nat.mul_assoc, Nat.mul_comm 2]
  have hE : 2 * (eh * 2 ^ c + b) + y = eh * 2 ^ (c + 1) + (2 * b + y) := by
    have : eh * 2 ^ (c + 1) = 2 * (eh * 2 ^ c) := by rw [Nat.pow_succ, Nat.mul_comm 2, Nat.mul_assoc]
    omega
  have hlo : 2 ^ c ≤ 2 * b + y := by
    have : 2 ^ c = 2 * 2 ^ (c - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    omega
  have hhi : 2 * b + y < 2 ^ (c + 1) := by rw [Nat.pow_succ]; omega
  simp only [bitStep, show ¬ (2 = 0 ∧ y = 0) by omega, show ¬ (2 = 1 ∧ y = 0) by omega, ite_false]
  rw [hbb, hE]
  by_cases hf : c + 1 = w
  · simp only [hf, ite_true, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    rw [sqIter_enc cx.red cx.pos, cx.tab.upper _ (by rw [← hf]; simpa using hlo)
      (by rw [← hf]; exact hhi), red_mul cx.red cx.pos, ← hf]
    exact Inv.sqr _
  · simp only [hf, ite_false]
    exact Inv.win eh (2 * b + y) (c + 1) (by omega) (by omega) (by simpa using hlo) hhi

/-- **One bit**: the invariant goes from `E` to `2E + y`. -/
theorem bitStep_inv {red : Nat → Nat} {M : Nat → Nat} {P R g w res0 : Nat}
    (cx : Ctx red M P R g w res0) {E : Nat} {s : St} (h : Inv P R g w res0 E s) {y : Nat}
    (hy : y ≤ 1) : Inv P R g w res0 (2 * E + y) (bitStep red M w s y) := by
  cases h with
  | idle => exact step_idle cx hy
  | sqr => exact step_sqr cx _ hy
  | win eh b c hc0 hcw hb1 hb2 => exact step_win cx eh b c hc0 hcw hb1 hb2 hy

theorem div_pow_succ (d k : Nat) : d / 2 ^ k = 2 * (d / 2 ^ (k + 1)) + d / 2 ^ k % 2 := by
  have h1 : d / 2 ^ (k + 1) = d / 2 ^ k / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [h1]; exact (Nat.div_add_mod _ 2).symm

/-- **One digit**: after `t` bits of `d` the invariant is at `E·2^t + d / 2^(28-t)`. -/
theorem runBits_inv {red : Nat → Nat} {M : Nat → Nat} {P R g w res0 : Nat}
    (cx : Ctx red M P R g w res0) {E : Nat} {s : St} (h : Inv P R g w res0 E s) {d : Nat}
    (hd : d < 2 ^ 28) :
    ∀ t, t ≤ 28 → Inv P R g w res0 (E * 2 ^ t + d / 2 ^ (28 - t)) (runBits red M w s d t)
  | 0, _ => by
    simp only [runBits, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, Nat.div_eq_of_lt hd, Nat.add_zero]
    exact h
  | t + 1, ht => by
    have ih := runBits_inv cx h hd t (by omega)
    have hb : d / 2 ^ (27 - t) % 2 ≤ 1 := by omega
    have := bitStep_inv cx ih hb
    have e := div_pow_succ d (27 - t)
    rw [show 27 - t + 1 = 28 - t by omega] at e
    rw [show 28 - (t + 1) = 27 - t by omega, Nat.pow_succ]
    simp only [runBits]
    rw [show E * (2 ^ t * 2) + d / 2 ^ (27 - t) =
      2 * (E * 2 ^ t + d / 2 ^ (28 - t)) + d / 2 ^ (27 - t) % 2 by
        rw [e, Nat.mul_add, Nat.mul_comm 2 (E * 2 ^ t), Nat.mul_assoc]; omega]
    exact this

theorem radix_eq' : radix = 2 ^ 28 := rfl

/-- **The digits**: after digits `n - 1 .. 0` the invariant is at
`E·radix^n + natUpTo dig n`. -/
theorem runDigits_inv {red : Nat → Nat} {M : Nat → Nat} {P R g w res0 : Nat}
    (cx : Ctx red M P R g w res0) {dig : Nat → Nat} (hdig : ∀ i, dig i < radix) :
    ∀ n {E : Nat} {s : St}, Inv P R g w res0 E s →
      Inv P R g w res0 (E * radix ^ n + natUpTo dig n) (runDigits red M w dig n s)
  | 0, E, s, h => by simpa [runDigits, natUpTo] using h
  | n + 1, E, s, h => by
    have h1 := runBits_inv cx h (hdig n) 28 (Nat.le_refl _)
    simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one] at h1
    have := runDigits_inv cx hdig n h1
    simp only [runDigits]
    rw [show E * radix ^ (n + 1) + natUpTo dig (n + 1) =
      (E * 2 ^ 28 + dig n) * radix ^ n + natUpTo dig n by
        rw [natUpTo, Nat.pow_succ, radix_eq', Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ 28)]
        rw [Nat.mul_comm (dig n)]; omega]
    exact this

/-! ## The tail and the result -/

theorem tailLoop_inv {red : Nat → Nat} {M : Nat → Nat} {P R g w res0 : Nat}
    (cx : Ctx red M P R g w res0) (eh b c : Nat) (hcw : c < w) (hb2 : b < 2 ^ c) :
    ∀ j, j ≤ c → tailLoop red M w j (enc P R g eh, b * 2 ^ (w - c)) =
      (enc P R g (eh * 2 ^ j + b / 2 ^ (c - j)), b * 2 ^ (w - c) * 2 ^ j)
  | 0, _ => by simp [tailLoop, Nat.div_eq_of_lt hb2]
  | j + 1, hj => by
    have ih := tailLoop_inv cx eh b c hcw hb2 j (by omega)
    simp only [tailLoop, ih]
    have hbit : b * 2 ^ (w - c) * 2 ^ j * 2 / 2 ^ w % 2 = b / 2 ^ (c - (j + 1)) % 2 := by
      rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_succ, ← Nat.pow_add,
        show w - c + (j + 1) = w - (c - (j + 1)) by omega,
        show w = (w - (c - (j + 1))) + (c - (j + 1)) by omega, Nat.pow_add,
        show w - (c - (j + 1)) + (c - (j + 1)) - (c - (j + 1)) = w - (c - (j + 1)) by omega,
        Nat.mul_comm (2 ^ (w - (c - (j + 1)))), Nat.mul_div_mul_right _ _ (two_pow_pos' _)]
    rw [hbit, red_mul cx.red cx.pos]
    have e := div_pow_succ b (c - (j + 1))
    rw [show c - (j + 1) + 1 = c - j by omega] at e
    have hsnd : b * 2 ^ (w - c) * 2 ^ j * 2 = b * 2 ^ (w - c) * 2 ^ (j + 1) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    have hx : eh * 2 ^ (j + 1) = eh * 2 ^ j * 2 := by rw [Nat.pow_succ, Nat.mul_assoc]
    rw [hsnd]
    by_cases hb : b / 2 ^ (c - (j + 1)) % 2 = 1
    · rw [ite_eq_left hb, cx.tab.one, red_mul cx.red cx.pos]
      have : eh * 2 ^ j + b / 2 ^ (c - j) + (eh * 2 ^ j + b / 2 ^ (c - j)) + 1 =
          eh * 2 ^ (j + 1) + b / 2 ^ (c - (j + 1)) := by rw [hx, e]; omega
      rw [this]
    · rw [ite_eq_right hb]
      have : eh * 2 ^ j + b / 2 ^ (c - j) + (eh * 2 ^ j + b / 2 ^ (c - j)) =
          eh * 2 ^ (j + 1) + b / 2 ^ (c - (j + 1)) := by rw [hx, e]; omega
      rw [this]

theorem finish_inv {red : Nat → Nat} {M : Nat → Nat} {P R g w res0 : Nat}
    (cx : Ctx red M P R g w res0) {E : Nat} {s : St} (h : Inv P R g w res0 E s) :
    finish red M w s = enc P R g E := by
  cases h with
  | idle => simp [finish, cx.res0]
  | sqr e => simp [finish]
  | win eh b c hc0 hcw hb1 hb2 =>
    simp only [finish, show 0 < c from hc0, and_self, ite_true]
    rw [tailLoop_inv cx eh b c hcw hb2 c (Nat.le_refl _), Nat.sub_self, Nat.pow_zero, Nat.div_one]

/-- **The window loop**: with `redux` dividing by `R` mod `P`, a table whose
entries represent their indices, and `res` starting at `R mod P` (Montgomery:
`mp_montgomery_calc_normalization`; the others: `1`, which is `1 mod P` for
`P > 1`), the loop over digits `n - 1 .. 0` of the exponent and the tail leave
`res = g^X · R mod P` with `X = natUpTo dig n`. -/
theorem window_correct {red : Nat → Nat} {M : Nat → Nat} {P R g w res0 : Nat}
    (cx : Ctx red M P R g w res0) {dig : Nat → Nat} (hdig : ∀ i, dig i < radix) (n : Nat) :
    finish red M w (runDigits red M w dig n (start res0)) = enc P R g (natUpTo dig n) := by
  have := runDigits_inv cx hdig n (inv_start P R g w res0)
  rw [Nat.zero_mul, Nat.zero_add] at this
  exact finish_inv cx this

/-- The same with the table built as the C builds it from `M[1] = g·R mod P`. -/
theorem window_correct_table {red : Nat → Nat} {P R g w : Nat} (hr : Red red P R) (hP : 0 < P)
    (hw : 2 ≤ w) {dig : Nat → Nat} (hdig : ∀ i, dig i < radix) (n : Nat) :
    finish red (table red (enc P R g 1) w) w (runDigits red (table red (enc P R g 1) w) w dig n
      (start (R % P))) = enc P R g (natUpTo dig n) :=
  window_correct ⟨hr, hP, hw, table_ok hr hP hw, by simp [enc]⟩ hdig n

/-- **Montgomery's fixup** (`s_mp_exptmod_fast`, `redmode == 0`): one more
`redux` of the result gives `g^X mod P`. -/
theorem fixup_correct {red : Nat → Nat} {M : Nat → Nat} {P R g w res0 : Nat}
    (cx : Ctx red M P R g w res0) {dig : Nat → Nat} (hdig : ∀ i, dig i < radix) (n : Nat) :
    red (finish red M w (runDigits red M w dig n (start res0))) = g ^ natUpTo dig n % P := by
  rw [window_correct cx hdig n, red_enc cx.red cx.pos]

/-- With `R = 1` (`redux` = reduction mod `P`) the result is `g^X mod P`. -/
theorem window_correct_one {red : Nat → Nat} {M : Nat → Nat} {P g w res0 : Nat}
    (cx : Ctx red M P 1 g w res0) {dig : Nat → Nat} (hdig : ∀ i, dig i < radix) (n : Nat) :
    finish red M w (runDigits red M w dig n (start res0)) = g ^ natUpTo dig n % P := by
  rw [window_correct cx hdig n, enc, Nat.mul_one]

/-- An all-zero exponent leaves `res` untouched, whatever it is (so
`s_mp_exptmod` with `X = 0` returns `1` even for `P = 1`). -/
theorem runDigits_zero (red : Nat → Nat) (M : Nat → Nat) (w res0 : Nat) {dig : Nat → Nat}
    (hz : ∀ i, dig i = 0) : ∀ n, finish red M w (runDigits red M w dig n (start res0)) = res0 := by
  have hb : ∀ t, runBits red M w (start res0) 0 t = start res0 := by
    intro t; induction t with
    | zero => rfl
    | succ t ih => rw [runBits, ih]; simp [bitStep, start]
  have hd : ∀ n, runDigits red M w dig n (start res0) = start res0 := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => simp only [runDigits, hz n, hb, ih]
  intro n; rw [hd]; simp [finish, start]

/-! ## Bounds and the C's bit operations -/

/-- Every `redux` argument is a product of two values below `P`: the represented
values (`res`, the table) are below `P`. -/
theorem Inv.res_lt {P R g w res0 E : Nat} {s : St} (h : Inv P R g w res0 E s) (hP : 0 < P)
    (h0 : res0 < P) : s.res < P := by
  cases h with
  | idle => exact h0
  | sqr e => exact enc_lt hP _ _ _
  | win => exact enc_lt hP _ _ _

/-- The pending window stays below `2^w` and `bitcpy < w` (C `int`s). -/
theorem Inv.bitbuf_lt {P R g w res0 E : Nat} {s : St} (h : Inv P R g w res0 E s) (hw : 2 ≤ w) :
    s.bitbuf < 2 ^ w ∧ s.bitcpy < w := by
  cases h with
  | idle => exact ⟨two_pow_pos' _, show 0 < w by omega⟩
  | sqr e => exact ⟨two_pow_pos' _, show 0 < w by omega⟩
  | win eh b c hc0 hcw hb1 hb2 =>
    refine ⟨?_, hcw⟩
    show b * 2 ^ (w - c) < 2 ^ w
    calc b * 2 ^ (w - c) < 2 ^ c * 2 ^ (w - c) := Nat.mul_lt_mul_of_pos_right hb2 (two_pow_pos' _)
      _ = 2 ^ w := by rw [← Nat.pow_add]; congr 1; omega

/-- The window index read when the window fills is a computed entry. -/
theorem fill_index {b c y w : Nat} (hcw : c + 1 = w) (hb1 : 2 ^ (c - 1) ≤ b) (hb2 : b < 2 ^ c)
    (hc0 : 0 < c) (hy : y ≤ 1) : 2 ^ (w - 1) ≤ 2 * b + y ∧ 2 * b + y < 2 ^ w := by
  subst hcw
  have : 2 ^ c = 2 * 2 ^ (c - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  simp only [Nat.add_sub_cancel, Nat.pow_succ]; omega

/-- `bitbuf |= y << k` adds a fresh bit when `bitbuf` is a multiple of `2^(k+1)`. -/
theorem or_bit (a k y : Nat) (hy : y ≤ 1) : (2 ^ (k + 1) * a) ||| (y <<< k) = 2 ^ (k + 1) * a + y * 2 ^ k := by
  rw [Nat.shiftLeft_eq]
  have hlt : y * 2 ^ k < 2 ^ (k + 1) := by
    rw [Nat.pow_succ]; have := two_pow_pos' k
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> omega
  exact (Nat.two_pow_add_eq_or_of_lt hlt a).symm

/-- In the C's terms: in every state of the invariant, `bitbuf` is a multiple of
`2^(w - bitcpy)`, so the `|=` of the next bit is the `+` of `bitStep`. -/
theorem Inv.or_eq {P R g w res0 E : Nat} {s : St} (h : Inv P R g w res0 E s) {y : Nat} (hy : y ≤ 1) :
    s.mode ≠ 0 ∨ y ≠ 0 → s.bitcpy + 1 ≤ w →
      s.bitbuf ||| (y <<< (w - (s.bitcpy + 1))) = s.bitbuf + y * 2 ^ (w - (s.bitcpy + 1)) := by
  intro _ hc
  cases h with
  | idle => simp [Nat.shiftLeft_eq]
  | sqr e => simp [Nat.shiftLeft_eq]
  | win eh b c hc0 hcw hb1 hb2 =>
    show b * 2 ^ (w - c) ||| (y <<< (w - (c + 1))) = b * 2 ^ (w - c) + y * 2 ^ (w - (c + 1))
    have := or_bit b (w - (c + 1)) y hy
    rwa [show w - (c + 1) + 1 = w - c by omega, Nat.mul_comm (2 ^ (w - c))] at this

/-- The tail's test `(bitbuf & (1 << winsize)) != 0` is bit `w` of `bitbuf`. -/
theorem and_bit (n w : Nat) : (n &&& (1 <<< w) ≠ 0) ↔ n / 2 ^ w % 2 = 1 := by
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  constructor
  · intro h
    apply Classical.byContradiction; intro hb
    apply h
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : w = i
    · subst hi
      rw [Nat.testBit_eq_decide_div_mod_eq] ; simp; omega
    · simp [hi]
  · intro h h0
    have := congrArg (fun m => Nat.testBit m w) h0
    simp only [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true, Nat.zero_testBit] at this
    rw [Nat.testBit_eq_decide_div_mod_eq] at this; simp at this; omega

/-- `buf <<= 1` on `uint32`: after `t` shifts `buf = d·2^t mod 2^32`. -/
theorem buf_shift (d t : Nat) : (d * 2 ^ t % 2 ^ 32) * 2 % 2 ^ 32 = d * 2 ^ (t + 1) % 2 ^ 32 := by
  rw [Nat.mod_mul_mod, show (2 : Nat) ^ (t + 1) = 2 ^ t * 2 from Nat.pow_succ 2 t, Nat.mul_assoc]

/-- **Bit extraction**: `y = (buf >> 27) & 1` with `buf = d·2^t mod 2^32` is bit
`27 - t` of the digit `d`. -/
theorem bit_extract (d t : Nat) (ht : t ≤ 27) :
    d * 2 ^ t % 2 ^ 32 / 2 ^ 27 % 2 = d / 2 ^ (27 - t) % 2 := by
  rw [show (2 : Nat) ^ 32 = 2 ^ 27 * 2 ^ 5 by rw [← Nat.pow_add], Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (by exact ⟨16, rfl⟩)]
  congr 1
  rw [show (2 : Nat) ^ 27 = 2 ^ (27 - t) * 2 ^ t by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mul_div_mul_right _ _ (two_pow_pos' _)]

/-- The C's `(x >> 27) & 1`, `& MP_MASK`-free form. -/
theorem shr_and_one (x : Nat) : (x >>> 27) &&& 1 = x / 2 ^ 27 % 2 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

end Tom.Window
