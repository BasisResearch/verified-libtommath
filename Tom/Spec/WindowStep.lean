import Tom.Spec.Exptmod
import Tom.Spec.Ledger
import Tom.Spec.Bits

/-!
# The window loop of `s_mp_exptmod(_fast)`: the model steps over the Ledger

`bn_s_mp_exptmod.c` and `bn_s_mp_exptmod_fast.c` share everything after their setups: the
table (`mp_copy(&M[1], &M[2^(w-1)])`, `w - 1` squarings, `M[x] = redux(M[x-1] M[1])` for
`x < 2^w`), the `for (;;)` loop over the exponent's bits and the tail; they differ in
`redux` (Barrett / `2^k-L`, or Montgomery / DR / `2^k`) and in what `res` and `M[1]` start
from. This file is that shared part, once (law 3), over an abstract `redux`:

* `Rx RP red B U`: `redux(&x, P, mp)` as a **transfer** — its Post `RP x x'` on a nonnegative
  product of two residues leaves `red v`, again a residue (`Rs`: an `Acct` with value `< B`);
  `Rx.sqr` (`mp_sqr(&x, &x)` + `redux`) and `Rx.mul` (`mp_mul` + `redux`) are the two blocks
  every loop is built of, over the frozen Posts `SqrPost` (`Api/MpSqrA.lean`) and `MulPost`
  (`Api/MpMulA.lean`, `Api/MpMul.lean`) through `xfer_sqr`, `xfer_mul`.
* The table: `tab_copy`, `tab_sqr` (the squarings of `M[2^(w-1)]`), `TUp` (the upper half),
  `TUp.fin` → `Tab`.
* The loop: the model's state after the bits read so far is `pos r i t` (digit `i`, `t` of its
  bits, `Window.runBits`/`runDigits`); one structure **per bit-processing mode** of that state
  (`Idle` for `mode == 0`, `Sqr` for `mode == 1`, `Win` for `mode == 2`, joined in `Md`), the
  head `Hd` (before `--bitcnt`) and the body entry `Bt` (after `y = (buf >> 27) & 1;
  buf <<= 1`), `Fw` (the window's `winsize` squarings). Steps: `Hd.next`, `Hd.refill`,
  `Hd.exit`; `Bt.skip` (`mode == 0`, `y == 0`), `Bt.sqr` (`mode == 1`, `y == 0`), `Bt.add`
  (a bit into the window), `Bt.fill`/`Fw.sqr`/`Fw.mul` (the window full).
* The tail `if ((mode == 2) && (bitcpy > 0))`: `TL`/`TM` and their steps; `Ex.skip`,
  `TL.fin` → `Done`: `res` holds `finish … (runDigits …)`, the Spec's `winRes`.

The state tracked is the model's `St` itself, not its meaning (`Window.Inv` needs `Red`): the
lossy `mp_reduce_2k` setup runs the same loop on a `redux` that is not a
reduction modulo `P`, and the Spec states that run. Only the shape facts of the modes (red-free,
`Md.step`) and the residue bound `< B` are carried.
-/

namespace Tom.WindowStep

open MpInt Ledger Window

/-! ## Residue accounts; `redux` as a transfer -/

/-- A residue account: `x` valid, nonnegative, `used ≤ U`, value `v < B`. `alloc` is not tracked
(`mp_mul`'s Post has no `alloc`, `Api/MpMulA.lean`; the callees' D5 premises stay theirs). -/
abbrev Rs (B U : Nat) (x : MpInt) (v : Nat) : Prop := Acct x 0 U (v : Int) (v < B)

theorem Rs.of {B U v al : Nat} {x : MpInt} (h : Settled x al v Layout.mpZpos) (hB : v < B)
    (hBU : B ≤ radix ^ U) : Rs B U x v :=
  ⟨h.valid, Nat.zero_le _, used_le_of_lt h.valid (by rw [h.mag]; omega), h.val, hB⟩

/-- `redux(&x, P, mp)` as the loop sees it: its Post `RP x x'` on a nonnegative product of two
residues (`≤ (B - 1)^2`) leaves `red v`, again below `B ≤ radix^U`. -/
structure Rx (RP : MpInt → MpInt → Prop) (red : Nat → Nat) (B U : Nat) : Prop where
  fit : B ≤ radix ^ U
  lt : ∀ v, v ≤ (B - 1) * (B - 1) → red v < B
  xfer : ∀ {x x' : MpInt} {v : Nat}, Settled x x.alloc v Layout.mpZpos → v ≤ (B - 1) * (B - 1) → RP x x' →
    Settled x' x'.alloc (red v) Layout.mpZpos

section
variable {RP : MpInt → MpInt → Prop} {red : Nat → Nat} {B U v m : Nat} {x x' x1 x2 e : MpInt}

theorem Rx.post (hr : Rx RP red B U) (h : Settled x x.alloc v Layout.mpZpos) (hv : v ≤ (B - 1) * (B - 1))
    (hp : RP x x') : Rs B U x' (red v) :=
  Rs.of (hr.xfer h hv hp) (hr.lt v hv) hr.fit

/-- `mp_sqr(&x, &x)`, `redux(&x, P, mp)`. -/
theorem Rx.sqr (hr : Rx RP red B U) (h : Rs B U x v) (hs : SqrPost x x1) (hp : RP x1 x2) :
    Rs B U x2 (red (v * v)) :=
  hr.post (xfer_sqr h.val hs) (mul_le_sq h.aux h.aux) hp

/-- `mp_mul(&x, &e, &x)` (or into a fresh `x1`), `redux(&x1, P, mp)`. -/
theorem Rx.mul (hr : Rx RP red B U) (h : Rs B U x v) (he : Rs B U e m) (hm : MulPost x e x1) (hp : RP x1 x2) :
    Rs B U x2 (red (v * m)) :=
  hr.post (xfer_mul h.val he.val hm) (mul_le_sq h.aux he.aux) hp

/-- One more `redux` of a residue (Montgomery's fixup). -/
theorem Rx.once (hr : Rx RP red B U) (h : Rs B U x v) (hp : RP x x') : Rs B U x' (red v) := by
  have hb := h.aux
  have hv : v ≤ (B - 1) * (B - 1) := by
    rcases Nat.eq_zero_or_pos (B - 1) with h0 | h0
    · rw [h0]; omega
    · exact Nat.le_trans (by omega) (Nat.le_mul_of_pos_right _ h0)
  exact hr.post h.settled hv hp

end

/-! ## The table (`M[1]`, `M[2^(w-1)] … M[2^w - 1]`) -/

/-- `M[k] := e`. -/
def setT (Mt : Nat → MpInt) (k : Nat) (e : MpInt) : Nat → MpInt := fun j => if j = k then e else Mt j

/-- The table the loop reads: `M[1]` and the upper half hold the values `T`. -/
structure Tab (B U w : Nat) (T : Nat → Nat) (Mt : Nat → MpInt) : Prop where
  one : Rs B U (Mt 1) (T 1)
  upper : ∀ x, 2 ^ (w - 1) ≤ x → x < 2 ^ w → Rs B U (Mt x) (T x)

theorem two_le_half {w : Nat} (hw : 2 ≤ w) : 2 ≤ 2 ^ (w - 1) := by
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ w - 1 by omega); simpa using this

theorem half_lt {w : Nat} (hw : 2 ≤ w) : 2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ w := by
  rw [← Nat.two_mul, ← Nat.pow_succ']; congr 1; omega

theorem table_hi {red : Nat → Nat} {m1 w j : Nat} (hw : 2 ≤ w) (hj : 2 ^ (w - 1) ≤ j) :
    table red m1 w j = tblUp red m1 w (j - 2 ^ (w - 1)) := by
  have := two_le_half hw
  rw [table, if_neg (by omega)]

section
variable {RP : MpInt → MpInt → Prop} {red : Nat → Nat} {B U w v n x : Nat} {Mt : Nat → MpInt}
  {m1 e e1 e2 : MpInt}

/-- `mp_copy(&M[1], &M[2^(w-1)])` into the fresh `M[2^(w-1)]` (`mp_init(_size)`, `n` digits):
the squarings start. -/
theorem tab_copy (h1 : Rs B U m1 v) (hn : m1.used ≤ n) (hn' : n < 2 ^ 31) (hc : CopyPost m1 (MpInt.zeroN n) e) :
    Rs B U e (sqIter red 0 v) :=
  have a := xfer_copy h1.valid hn hn' hc
  ⟨a.valid, Nat.zero_le _, Nat.le_trans a.used h1.used, a.val.trans h1.val, h1.aux⟩

/-- One of the `w - 1` squarings of `M[2^(w-1)]` (`mp_sqr`, `redux`). -/
theorem tab_sqr (hr : Rx RP red B U) {k : Nat} (h : Rs B U e (sqIter red k v)) (hs : SqrPost e e1)
    (hp : RP e1 e2) : Rs B U e2 (sqIter red (k + 1) v) :=
  hr.sqr h hs hp

/-- The upper half below `x` (`for (x = 2^(w-1) + 1; x < 2^w; x++)`), `M[1]` kept. -/
structure TUp (B U w v : Nat) (red : Nat → Nat) (Mt : Nat → MpInt) (x : Nat) : Prop where
  one : Rs B U (Mt 1) v
  done : ∀ j, 2 ^ (w - 1) ≤ j → j < x → Rs B U (Mt j) (table red v w j)
  lo : 2 ^ (w - 1) < x
  hi : x ≤ 2 ^ w

/-- After the squarings: `M[2^(w-1)]` is the first entry of the upper half. -/
theorem TUp.start (hw : 2 ≤ w) (h1 : Rs B U (Mt 1) v) (hh : Rs B U (Mt (2 ^ (w - 1))) (sqIter red (w - 1) v)) :
    TUp B U w v red Mt (2 ^ (w - 1) + 1) where
  one := h1
  done j hj1 hj2 := by
    obtain rfl : j = 2 ^ (w - 1) := by omega
    rw [table_hi hw (Nat.le_refl _), Nat.sub_self]; exact hh
  lo := by omega
  hi := by have := half_lt hw; have := two_le_half hw; omega

/-- `mp_mul(&M[x-1], &M[1], &M[x])`, `redux(&M[x], P, mp)`. -/
theorem TUp.step (hr : Rx RP red B U) (hw : 2 ≤ w) (h : TUp B U w v red Mt x) (hx : x < 2 ^ w)
    (hm : MulPost (Mt (x - 1)) (Mt 1) e1) (hp : RP e1 e2) : TUp B U w v red (setT Mt x e2) (x + 1) where
  one := by
    have := h.lo; have := two_le_half hw
    show Rs B U (if 1 = x then e2 else Mt 1) v
    rw [if_neg (by omega)]; exact h.one
  done j hj1 hj2 := by
    show Rs B U (if j = x then e2 else Mt j) _
    by_cases ej : j = x
    · subst ej
      rw [if_pos rfl]
      have hl := h.lo
      have h2 := two_le_half hw
      have hj1' : 2 ^ (w - 1) ≤ j - 1 := by omega
      have := hr.mul (h.done (j - 1) hj1' (by omega)) h.one hm hp
      rw [table_hi hw hj1'] at this
      rw [table_hi hw hj1, show j - 2 ^ (w - 1) = (j - 1 - 2 ^ (w - 1)) + 1 by omega]
      exact this
    · rw [if_neg ej]; exact h.done j hj1 (by omega)
  lo := by have := h.lo; omega
  hi := hx

/-- `x == 2^w`: the table. -/
theorem TUp.fin (h : TUp B U w v red Mt x) (hx : ¬ x < 2 ^ w) : Tab B U w (table red v w) Mt where
  one := by rw [show table red v w 1 = v by simp [table]]; exact h.one
  upper j h1 h2 := h.done j h1 (by have := h.hi; omega)

end

/-! ## The run and the model's position -/

/-- The run's fixed data: `redux`'s value function, the table's values, `winsize`, the start of
`res`, the exponent's digits and `X->used`. -/
structure Run where
  red : Nat → Nat
  tab : Nat → Nat
  w : Nat
  res0 : Nat
  dig : Nat → Nat
  u : Nat

/-- The model's state after the top `k` digits. -/
def hiRun (r : Run) : Nat → St
  | 0 => start r.res0
  | k + 1 => runBits r.red r.tab r.w (hiRun r k) (r.dig (r.u - 1 - k)) 28

/-- The model's state at digit `i` with `t` of its bits read (digit `X->used`, a zero, stands
for the start). -/
def pos (r : Run) (i t : Nat) : St := runBits r.red r.tab r.w (hiRun r (r.u - (i + 1))) (r.dig i) t

section
variable (r : Run)

theorem runBits_start0 : ∀ t, runBits r.red r.tab r.w (start r.res0) 0 t = start r.res0
  | 0 => rfl
  | t + 1 => by rw [runBits, runBits_start0 t]; simp [bitStep, start]

theorem runDigits_split : ∀ k, k ≤ r.u →
    runDigits r.red r.tab r.w r.dig r.u (start r.res0) = runDigits r.red r.tab r.w r.dig (r.u - k) (hiRun r k)
  | 0, _ => rfl
  | k + 1, h => by
    rw [runDigits_split k (by omega)]
    obtain ⟨j, hj⟩ : ∃ j, r.u - k = j + 1 := ⟨r.u - k - 1, by omega⟩
    rw [hj, show r.u - (k + 1) = j by omega]
    show runDigits r.red r.tab r.w r.dig j (runBits r.red r.tab r.w (hiRun r k) (r.dig j) 28) =
      runDigits r.red r.tab r.w r.dig j (runBits r.red r.tab r.w (hiRun r k) (r.dig (r.u - 1 - k)) 28)
    rw [show r.u - 1 - k = j by omega]

theorem pos_zero (i : Nat) : pos r i 0 = hiRun r (r.u - (i + 1)) := rfl

theorem pos_28 (hz : r.dig r.u = 0) {i : Nat} (hi : i ≤ r.u) : pos r i 28 = hiRun r (r.u - i) := by
  rcases Nat.lt_or_ge i r.u with h | h
  · obtain ⟨k, hk⟩ : ∃ k, r.u - i = k + 1 := ⟨r.u - i - 1, by omega⟩
    rw [hk]; unfold pos; rw [show r.u - (i + 1) = k by omega]
    show _ = runBits r.red r.tab r.w (hiRun r k) (r.dig (r.u - 1 - k)) 28
    rw [show r.u - 1 - k = i by omega]
  · obtain rfl : i = r.u := by omega
    unfold pos; rw [show r.u - (r.u + 1) = 0 by omega, Nat.sub_self, hz]; exact runBits_start0 r 28

theorem pos_refill (hz : r.dig r.u = 0) {i : Nat} (h0 : 0 < i) (hi : i ≤ r.u) : pos r (i - 1) 0 = pos r i 28 := by
  rw [pos_zero, pos_28 r hz hi, show i - 1 + 1 = i by omega]

theorem pos_exit (hz : r.dig r.u = 0) : pos r 0 28 = runDigits r.red r.tab r.w r.dig r.u (start r.res0) := by
  rw [pos_28 r hz (Nat.zero_le _), Nat.sub_zero, runDigits_split r r.u (Nat.le_refl _), Nat.sub_self]; rfl

theorem pos_succ (i t : Nat) :
    pos r i (t + 1) = bitStep r.red r.tab r.w (pos r i t) (r.dig i / 2 ^ (27 - t) % 2) := rfl

theorem pos_start (hz : r.dig r.u = 0) : pos r r.u 28 = start r.res0 := by
  rw [pos_28 r hz (Nat.le_refl _), Nat.sub_self]; rfl

end

/-! ## The modes (one structure per bit-processing mode) -/

/-- `mode == 0`: only zero bits so far; `res` untouched. -/
structure Idle (res0 : Nat) (s : St) : Prop where
  mode : s.mode = 0
  cpy : s.bitcpy = 0
  buf : s.bitbuf = 0
  res : s.res = res0

/-- `mode == 1`: between windows. -/
structure Sqr (s : St) : Prop where
  mode : s.mode = 1
  cpy : s.bitcpy = 0
  buf : s.bitbuf = 0

/-- `mode == 2`: `bitcpy` bits pending in `bitbuf` (a multiple of `2^(w - bitcpy)`), the window's
top bit set (`2^(w-1) ≤ bitbuf`). -/
structure Win (w : Nat) (s : St) : Prop where
  mode : s.mode = 2
  c0 : 0 < s.bitcpy
  cw : s.bitcpy < w
  dvd : 2 ^ (w - s.bitcpy) ∣ s.bitbuf
  lo : 2 ^ (w - 1) ≤ s.bitbuf
  hi : s.bitbuf < 2 ^ w

/-- The state is in one of the three modes. -/
inductive Md (w res0 : Nat) (s : St) : Prop
  | idle (h : Idle res0 s)
  | sqr (h : Sqr s)
  | win (h : Win w s)

section
variable {red : Nat → Nat} {M : Nat → Nat} {w res0 y : Nat} {s : St}

theorem bitStep_skip (h : s.mode = 0) : bitStep red M w s 0 = s := by
  simp [bitStep, h]

theorem bitStep_sq (h : s.mode = 1) : bitStep red M w s 0 = { s with res := red (s.res * s.res) } := by
  simp [bitStep, h]

theorem bitStep_add (h0 : ¬ (s.mode = 0 ∧ y = 0)) (h1 : ¬ (s.mode = 1 ∧ y = 0)) (hf : s.bitcpy + 1 ≠ w) :
    bitStep red M w s y = ⟨2, s.bitcpy + 1, s.bitbuf + y * 2 ^ (w - (s.bitcpy + 1)), s.res⟩ := by
  simp only [bitStep, if_neg h0, if_neg h1, if_neg hf]

theorem bitStep_full (h0 : ¬ (s.mode = 0 ∧ y = 0)) (h1 : ¬ (s.mode = 1 ∧ y = 0)) (hf : s.bitcpy + 1 = w) :
    bitStep red M w s y = ⟨1, 0, 0, red (sqIter red w s.res * M (s.bitbuf + y * 2 ^ (w - (s.bitcpy + 1))))⟩ := by
  simp only [bitStep, if_neg h0, if_neg h1, if_pos hf]

/-- A bit into a window of `c` bits (`bitbuf` a multiple of `2^(w-c)`). -/
theorem win_add {c b0 : Nat} (hcw : c < w) (hd : 2 ^ (w - c) ∣ b0) (hhi : b0 < 2 ^ w) (hy : y ≤ 1) :
    2 ^ (w - (c + 1)) ∣ b0 + y * 2 ^ (w - (c + 1)) ∧ b0 + y * 2 ^ (w - (c + 1)) < 2 ^ w := by
  have e1 : 2 ^ (w - c) = 2 ^ (w - (c + 1)) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
  have e2 : 2 ^ w = 2 ^ (w - c) * 2 ^ c := by rw [← Nat.pow_add]; congr 1; omega
  obtain ⟨q, rfl⟩ := hd
  have hq : q < 2 ^ c := by rw [e2] at hhi; exact Nat.lt_of_mul_lt_mul_left hhi
  have hq' : 2 ^ (w - c) * q + 2 ^ (w - c) ≤ 2 ^ w := by
    rw [e2, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hq
  have hyK : y * 2 ^ (w - (c + 1)) ≤ 2 ^ (w - (c + 1)) := by
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> omega
  refine ⟨⟨2 * q + y, ?_⟩, ?_⟩
  · rw [e1, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm y]
  · have := Nat.two_pow_pos (w - (c + 1))
    rw [e1] at hq' ⊢; omega

/-- The C's `bitbuf |= y << (winsize - ++bitcpy)` is the model's `+` (the bit is fresh). -/
theorem Md.or_eq (h : Md w res0 s) (hy : y ≤ 1) (hc : s.bitcpy + 1 ≤ w) :
    s.bitbuf ||| (y <<< (w - (s.bitcpy + 1))) = s.bitbuf + y * 2 ^ (w - (s.bitcpy + 1)) := by
  rcases h with h | h | h
  · rw [h.buf]; simp [Nat.shiftLeft_eq]
  · rw [h.buf]; simp [Nat.shiftLeft_eq]
  · obtain ⟨q, hq⟩ := h.dvd
    have := or_bit q (w - (s.bitcpy + 1)) y hy
    rwa [show w - (s.bitcpy + 1) + 1 = w - s.bitcpy by have := h.cw; omega, ← hq] at this

/-- **The modes are kept** by every bit (red-free). -/
theorem Md.step (hw : 2 ≤ w) (h : Md w res0 s) (hy : y ≤ 1) : Md w res0 (bitStep red M w s y) := by
  have hh := half_lt hw
  have h2 := two_le_half hw
  -- a first bit opens a window of one bit
  have first : ∀ (s : St), s.bitcpy = 0 → s.bitbuf = 0 → ¬ (s.mode = 0 ∧ 1 = 0) → ¬ (s.mode = 1 ∧ 1 = 0) →
      Md w res0 (bitStep red M w s 1) := fun s hc hb h0 h1 => by
    rw [bitStep_add h0 h1 (by omega)]
    refine .win ⟨rfl, by simp, by simp; omega, ?_, ?_, ?_⟩ <;> simp only [hc, hb, Nat.zero_add, Nat.one_mul]
    · exact Nat.dvd_refl _
    · exact Nat.le_refl _
    · omega
  rcases h with h | h | h
  · rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl
    · rw [bitStep_skip h.mode]; exact .idle h
    · exact first s h.cpy h.buf (by omega) (by rw [h.mode]; omega)
  · rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl
    · rw [bitStep_sq h.mode]; exact .sqr ⟨h.mode, h.cpy, h.buf⟩
    · exact first s h.cpy h.buf (by rw [h.mode]; omega) (by omega)
  · have h0 : ¬ (s.mode = 0 ∧ y = 0) := by rw [h.mode]; omega
    have h1 : ¬ (s.mode = 1 ∧ y = 0) := by rw [h.mode]; omega
    by_cases hf : s.bitcpy + 1 = w
    · rw [bitStep_full h0 h1 hf]; exact .sqr ⟨rfl, rfl, rfl⟩
    · rw [bitStep_add h0 h1 hf]
      have := win_add (y := y) h.cw h.dvd h.hi hy
      exact .win ⟨rfl, by simp, by simp; have := h.cw; omega, this.1, by have := h.lo; simp; omega, this.2⟩

/-- The full window's index is a computed entry of the table. -/
theorem Md.fill (hw : 2 ≤ w) (h : Md w res0 s) (hy : y ≤ 1) (hf : s.bitcpy + 1 = w) :
    2 ^ (w - 1) ≤ s.bitbuf + y * 2 ^ (w - (s.bitcpy + 1)) ∧ s.bitbuf + y * 2 ^ (w - (s.bitcpy + 1)) < 2 ^ w := by
  rcases h with h | h | h
  · rw [h.cpy] at hf; omega
  · rw [h.cpy] at hf; omega
  · have := win_add (y := y) h.cw h.dvd h.hi hy
    exact ⟨by have := h.lo; omega, this.2⟩

end

/-! ## The loop -/

/-- The run's fixed facts: `redux` a transfer, `winsize ≥ 2`, `X->dp[X->used] = 0`, the table. -/
structure Env (RP : MpInt → MpInt → Prop) (r : Run) (B U : Nat) (Mt : Nat → MpInt) : Prop where
  rx : Rx RP r.red B U
  w2 : 2 ≤ r.w
  top : r.dig r.u = 0
  tab : Tab B U r.w r.tab Mt

/-- **The head** of `for (;;)` (before `--bitcnt`): digit `i` with `t` of its bits read (`i =
X->used`, `t = 28` before the first), `bitcnt = 29 - t`, `digidx = i - 1`, `buf = X->dp[i] 2^t
mod 2^32`; the state `s` (`mode`, `bitcpy`, `bitbuf`, `|res|`) is the model's after those bits,
in one of the modes, and `res` its residue account. -/
structure Hd (r : Run) (B U : Nat) (i t bitcnt : Nat) (digidx : Int) (buf : Nat) (s : St) (res : MpInt) :
    Prop where
  t1 : 1 ≤ t
  t28 : t ≤ 28
  iu : i ≤ r.u
  top : i = r.u → t = 28
  cnt : bitcnt = 29 - t
  idx : digidx = (i : Int) - 1
  buf : buf = r.dig i * 2 ^ t % 2 ^ 32
  st : s = pos r i t
  md : Md r.w r.res0 s
  acct : Rs B U res s.res

/-- Where a bit is processed: digit `i`, `t` bits read before it; `y` the bit, `buf` shifted. -/
structure At (r : Run) (i t bitcnt : Nat) (digidx : Int) (buf y : Nat) (s : St) : Prop where
  iu : i < r.u
  t27 : t ≤ 27
  cnt : bitcnt = 28 - t
  idx : digidx = (i : Int) - 1
  buf : buf = r.dig i * 2 ^ (t + 1) % 2 ^ 32
  bit : y = r.dig i / 2 ^ (27 - t) % 2
  st : s = pos r i t
  md : Md r.w r.res0 s

/-- **The body entry** (after `y = (buf >> 27) & 1; buf <<= 1`). -/
structure Bt (r : Run) (B U : Nat) (i t bitcnt : Nat) (digidx : Int) (buf y : Nat) (s : St) (res : MpInt) :
    Prop where
  pt : At r i t bitcnt digidx buf y s
  acct : Rs B U res s.res

/-- After `break` (`digidx == -1`): the state after all digits. -/
structure Ex (r : Run) (B U : Nat) (s : St) (res : MpInt) : Prop where
  st : s = runDigits r.red r.tab r.w r.dig r.u (start r.res0)
  md : Md r.w r.res0 s
  acct : Rs B U res s.res

section
variable {RP : MpInt → MpInt → Prop} {r : Run} {B U : Nat} {Mt : Nat → MpInt}
  {i t bitcnt buf y : Nat} {digidx : Int} {s : St} {res r1 r2 : MpInt}

/-- Before the loop: `mode = 0`, `bitcnt = 1`, `buf = 0`, `digidx = X->used - 1`, `bitcpy = bitbuf = 0`,
`res` its start. -/
theorem Hd.start (env : Env RP r B U Mt) (h : Rs B U res r.res0) :
    Hd r B U r.u 28 1 ((r.u : Int) - 1) 0 (start r.res0) res where
  t1 := by decide
  t28 := Nat.le_refl _
  iu := Nat.le_refl _
  top := fun _ => rfl
  cnt := rfl
  idx := rfl
  buf := by rw [env.top]
  st := (pos_start r env.top).symm
  md := .idle ⟨rfl, rfl, rfl, rfl⟩
  acct := h

/-- `--bitcnt != 0`: the next bit of the same digit. -/
theorem Hd.next (h : Hd r B U i t bitcnt digidx buf s res) (ht : t < 28) :
    Bt r B U i t (bitcnt - 1) digidx (buf * 2 % 2 ^ 32) ((buf >>> 27) &&& 1) s res where
  pt := { iu := by have := h.iu; have := h.top; omega
          t27 := by omega
          cnt := by rw [h.cnt]; omega
          idx := h.idx
          buf := by rw [h.buf]; exact buf_shift _ _
          bit := by rw [shr_and_one, h.buf]; exact bit_extract _ _ (by omega)
          st := h.st
          md := h.md }
  acct := h.acct

/-- `--bitcnt == 0`, `digidx != -1`: `buf = X->dp[digidx--]`, `bitcnt = MP_DIGIT_BIT`, then the bit. -/
theorem Hd.refill (env : Env RP r B U Mt) (h : Hd r B U i 28 bitcnt digidx buf s res) (hi : digidx ≠ -1) :
    Bt r B U (i - 1) 0 28 (digidx - 1) (r.dig (i - 1) * 2 % 2 ^ 32) ((r.dig (i - 1) >>> 27) &&& 1) s res where
  pt := { iu := by have := h.iu; have := h.idx; omega
          t27 := by omega
          cnt := rfl
          idx := by have := h.idx; omega
          buf := by rw [Nat.zero_add, Nat.pow_one]
          bit := by rw [shr_and_one]
          st := by rw [h.st, pos_refill r env.top (by have := h.idx; omega) h.iu]
          md := h.md }
  acct := h.acct

/-- `--bitcnt == 0`, `digidx == -1`: `break`. -/
theorem Hd.exit (env : Env RP r B U Mt) (h : Hd r B U i 28 bitcnt digidx buf s res) (hi : digidx = -1) :
    Ex r B U s res where
  st := by
    obtain rfl : i = 0 := by have := h.idx; omega
    rw [h.st, pos_exit r env.top]
  md := h.md
  acct := h.acct

/-- Back to the head with the model's next state (`bitStep`). -/
theorem At.close (env : Env RP r B U Mt) {res' : MpInt} (h : At r i t bitcnt digidx buf y s)
    (ha : Rs B U res' (bitStep r.red r.tab r.w s y).res) :
    Hd r B U i (t + 1) bitcnt digidx buf (bitStep r.red r.tab r.w s y) res' where
  t1 := by omega
  t28 := by have := h.t27; omega
  iu := Nat.le_of_lt h.iu
  top := fun e => absurd e (Nat.ne_of_lt h.iu)
  cnt := by rw [h.cnt]; have := h.t27; omega
  idx := h.idx
  buf := h.buf
  st := by rw [h.st, h.bit]; rfl
  md := Md.step env.w2 h.md (by rw [h.bit]; omega)
  acct := ha

theorem At.y_le (h : At r i t bitcnt digidx buf y s) : y ≤ 1 := by rw [h.bit]; omega

/-- `(mode == 0) && (y == 0)`: `continue`. -/
theorem Bt.skip (env : Env RP r B U Mt) (h : Bt r B U i t bitcnt digidx buf y s res) (hm : s.mode = 0) (hy : y = 0) :
    Hd r B U i (t + 1) bitcnt digidx buf s res := by
  have := h.pt.close env (res' := res) (by subst hy; rw [bitStep_skip hm]; exact h.acct)
  rwa [hy, bitStep_skip hm] at this

/-- `(mode == 1) && (y == 0)`: `mp_sqr(&res, &res)`, `redux(&res, P, mp)`, `continue`. -/
theorem Bt.sqr (env : Env RP r B U Mt) (h : Bt r B U i t bitcnt digidx buf y s res) (hm : s.mode = 1) (hy : y = 0)
    (hs : SqrPost res r1) (hp : RP r1 r2) :
    Hd r B U i (t + 1) bitcnt digidx buf { s with res := r.red (s.res * s.res) } r2 := by
  have := h.pt.close env (res' := r2) (by subst hy; rw [bitStep_sq hm]; exact env.rx.sqr h.acct hs hp)
  rwa [hy, bitStep_sq hm] at this

/-- Else, the bit into the window (`bitbuf |= y << (winsize - ++bitcpy)`, `Md.or_eq`; `mode = 2`),
the window not full: `continue`. -/
theorem Bt.add (env : Env RP r B U Mt) (h : Bt r B U i t bitcnt digidx buf y s res) (h0 : ¬ (s.mode = 0 ∧ y = 0))
    (h1 : ¬ (s.mode = 1 ∧ y = 0)) (hf : s.bitcpy + 1 ≠ r.w) :
    Hd r B U i (t + 1) bitcnt digidx buf ⟨2, s.bitcpy + 1, s.bitbuf + y * 2 ^ (r.w - (s.bitcpy + 1)), s.res⟩ res := by
  have := h.pt.close env (res' := res) (by rw [bitStep_add h0 h1 hf]; exact h.acct)
  rwa [bitStep_add h0 h1 hf] at this

/-- The window full (`bitcpy == winsize`): `x` of its `winsize` squarings of `res` done. -/
structure Fw (r : Run) (B U : Nat) (i t bitcnt : Nat) (digidx : Int) (buf y : Nat) (s : St) (x : Nat) (res : MpInt) :
    Prop where
  pt : At r i t bitcnt digidx buf y s
  n0 : ¬ (s.mode = 0 ∧ y = 0)
  n1 : ¬ (s.mode = 1 ∧ y = 0)
  full : s.bitcpy + 1 = r.w
  x_le : x ≤ r.w
  acct : Rs B U res (sqIter r.red x s.res)

/-- Else, the bit fills the window: the squarings start (`x = 0`). -/
theorem Bt.fill (h : Bt r B U i t bitcnt digidx buf y s res) (h0 : ¬ (s.mode = 0 ∧ y = 0))
    (h1 : ¬ (s.mode = 1 ∧ y = 0)) (hf : s.bitcpy + 1 = r.w) : Fw r B U i t bitcnt digidx buf y s 0 res :=
  ⟨h.pt, h0, h1, hf, Nat.zero_le _, h.acct⟩

/-- `x < winsize`: `mp_sqr(&res, &res)`, `redux(&res, P, mp)`. -/
theorem Fw.sqr (env : Env RP r B U Mt) {x : Nat} (h : Fw r B U i t bitcnt digidx buf y s x res) (hx : x < r.w)
    (hs : SqrPost res r1) (hp : RP r1 r2) : Fw r B U i t bitcnt digidx buf y s (x + 1) r2 :=
  ⟨h.pt, h.n0, h.n1, h.full, hx, tab_sqr env.rx h.acct hs hp⟩

/-- `x == winsize`: `mp_mul(&res, &M[bitbuf], &res)`, `redux(&res, P, mp)`, then `bitcpy = 0`,
`bitbuf = 0`, `mode = 1` (`Md.fill`: `M[bitbuf]` is a computed entry). -/
theorem Fw.mul (env : Env RP r B U Mt) {x : Nat} (h : Fw r B U i t bitcnt digidx buf y s x res) (hx : ¬ x < r.w)
    (hm : MulPost res (Mt (s.bitbuf + y * 2 ^ (r.w - (s.bitcpy + 1)))) r1) (hp : RP r1 r2) :
    Hd r B U i (t + 1) bitcnt digidx buf
      ⟨1, 0, 0, r.red (sqIter r.red r.w s.res * r.tab (s.bitbuf + y * 2 ^ (r.w - (s.bitcpy + 1))))⟩ r2 := by
  obtain rfl : x = r.w := by have := h.x_le; omega
  have hi := Md.fill env.w2 h.pt.md h.pt.y_le h.full
  have ha := env.rx.mul h.acct (env.tab.upper _ hi.1 hi.2) hm hp
  have := h.pt.close env (res' := r2) (by rw [bitStep_full h.n0 h.n1 h.full]; exact ha)
  rwa [bitStep_full h.n0 h.n1 h.full] at this

end

/-! ## The tail `if ((mode == 2) && (bitcpy > 0))` and the result -/

/-- What `res` holds at the end: the model's `finish` of the run (`Exptmod.winRes`). -/
abbrev Done (r : Run) (B U : Nat) (res : MpInt) : Prop :=
  Rs B U res (finish r.red r.tab r.w (runDigits r.red r.tab r.w r.dig r.u (start r.res0)))

/-- `x` of the tail's `bitcpy` rounds done; `bitbuf` the C's shifted window. -/
structure TL (r : Run) (B U : Nat) (s : St) (x bitbuf : Nat) (res : MpInt) : Prop where
  ex : s = runDigits r.red r.tab r.w r.dig r.u (start r.res0)
  win : Win r.w s
  x_le : x ≤ s.bitcpy
  buf : bitbuf = (tailLoop r.red r.tab r.w x (s.res, s.bitbuf)).2
  acct : Rs B U res (tailLoop r.red r.tab r.w x (s.res, s.bitbuf)).1

/-- In round `x`, after `mp_sqr(&res, &res)`, `redux(&res, P, mp)`, `bitbuf <<= 1`. -/
structure TM (r : Run) (B U : Nat) (s : St) (x bitbuf : Nat) (res : MpInt) : Prop where
  ex : s = runDigits r.red r.tab r.w r.dig r.u (start r.res0)
  win : Win r.w s
  x_lt : x < s.bitcpy
  buf : bitbuf = (tailLoop r.red r.tab r.w x (s.res, s.bitbuf)).2 * 2
  acct : Rs B U res (r.red ((tailLoop r.red r.tab r.w x (s.res, s.bitbuf)).1 *
    (tailLoop r.red r.tab r.w x (s.res, s.bitbuf)).1))

theorem tailLoop_snd (red : Nat → Nat) (M : Nat → Nat) (w : Nat) (p : Nat × Nat) :
    ∀ x, (tailLoop red M w x p).2 = p.2 * 2 ^ x
  | 0 => by simp [tailLoop]
  | x + 1 => by simp only [tailLoop]; rw [tailLoop_snd red M w p x, Nat.pow_succ, Nat.mul_assoc]

section
variable {RP : MpInt → MpInt → Prop} {r : Run} {B U : Nat} {Mt : Nat → MpInt} {x bitbuf : Nat} {s : St}
  {res r1 r2 : MpInt}

/-- Not `(mode == 2) && (bitcpy > 0)`: nothing to do. -/
theorem Ex.skip (h : Ex r B U s res) (hn : ¬ (s.mode = 2 ∧ 0 < s.bitcpy)) : Done r B U res := by
  have e : finish r.red r.tab r.w s = s.res := by simp only [finish, if_neg hn]
  show Rs B U res (finish r.red r.tab r.w (runDigits r.red r.tab r.w r.dig r.u (start r.res0)))
  rw [← h.st, e]; exact h.acct

/-- `(mode == 2) && (bitcpy > 0)`: the tail loop starts (`x = 0`). -/
theorem Ex.tail (h : Ex r B U s res) (hy : s.mode = 2 ∧ 0 < s.bitcpy) : TL r B U s 0 s.bitbuf res where
  ex := h.st
  win := by
    rcases h.md with h' | h' | h'
    · rw [h'.mode] at hy; omega
    · rw [h'.mode] at hy; omega
    · exact h'
  x_le := Nat.zero_le _
  buf := rfl
  acct := h.acct

/-- The C's `bitbuf` in the tail stays below `2^(2w)` (an `int`). -/
theorem TL.buf_lt (h : TL r B U s x bitbuf res) : bitbuf < 2 ^ (2 * r.w) := by
  rw [h.buf, tailLoop_snd]
  have := h.win.hi; have := h.win.cw; have := h.x_le
  calc s.bitbuf * 2 ^ x < 2 ^ r.w * 2 ^ r.w :=
        Nat.mul_lt_mul_of_lt_of_le h.win.hi (Nat.pow_le_pow_right (by decide) (by omega)) (Nat.two_pow_pos _)
    _ = 2 ^ (2 * r.w) := by rw [← Nat.pow_add, Nat.two_mul]

/-- `x < bitcpy`: `mp_sqr(&res, &res)`, `redux(&res, P, mp)`, `bitbuf <<= 1`. -/
theorem TL.sqr (env : Env RP r B U Mt) (h : TL r B U s x bitbuf res) (hx : x < s.bitcpy) (hs : SqrPost res r1)
    (hp : RP r1 r2) : TM r B U s x (bitbuf * 2) r2 :=
  ⟨h.ex, h.win, hx, by rw [h.buf], env.rx.sqr h.acct hs hp⟩

/-- `(bitbuf & (1 << winsize)) != 0`: `mp_mul(&res, &M[1], &res)`, `redux(&res, P, mp)`. -/
theorem TM.mul (env : Env RP r B U Mt) (h : TM r B U s x bitbuf res) (hb : bitbuf &&& (1 <<< r.w) ≠ 0)
    (hm : MulPost res (Mt 1) r1) (hp : RP r1 r2) : TL r B U s (x + 1) bitbuf r2 where
  ex := h.ex
  win := h.win
  x_le := h.x_lt
  buf := by rw [h.buf]; rfl
  acct := by
    have hb' := (and_bit _ _).1 hb
    rw [h.buf] at hb'
    have := env.rx.mul h.acct env.tab.one hm hp
    show Rs B U r2 (if (tailLoop r.red r.tab r.w x (s.res, s.bitbuf)).2 * 2 / 2 ^ r.w % 2 = 1 then _ else _)
    rw [if_pos hb']; exact this

/-- `(bitbuf & (1 << winsize)) == 0`: the round ends. -/
theorem TM.skip (h : TM r B U s x bitbuf res) (hb : ¬ bitbuf &&& (1 <<< r.w) ≠ 0) : TL r B U s (x + 1) bitbuf res where
  ex := h.ex
  win := h.win
  x_le := h.x_lt
  buf := by rw [h.buf]; rfl
  acct := by
    have hb' : ¬ ((tailLoop r.red r.tab r.w x (s.res, s.bitbuf)).2 * 2 / 2 ^ r.w % 2 = 1) := by
      rw [← h.buf]; exact fun e => hb ((and_bit _ _).2 e)
    show Rs B U res (if (tailLoop r.red r.tab r.w x (s.res, s.bitbuf)).2 * 2 / 2 ^ r.w % 2 = 1 then _ else _)
    rw [if_neg hb']; exact h.acct

/-- `x == bitcpy`: the result. -/
theorem TL.fin (h : TL r B U s x bitbuf res) (hx : ¬ x < s.bitcpy) : Done r B U res := by
  obtain rfl : x = s.bitcpy := by have := h.x_le; omega
  have e : finish r.red r.tab r.w s = (tailLoop r.red r.tab r.w s.bitcpy (s.res, s.bitbuf)).1 := by
    simp only [finish, if_pos (show s.mode = 2 ∧ 0 < s.bitcpy from ⟨h.win.mode, h.win.c0⟩)]
  show Rs B U res (finish r.red r.tab r.w (runDigits r.red r.tab r.w r.dig r.u (start r.res0)))
  rw [← h.ex, e]; exact h.acct

end


/-! ## The run of `s_mp_exptmod(_fast)` (`Exptmod.winRes`) and the shared setup blocks -/

open Exptmod in
/-- The run for `redux`'s value function `red`, `M[1] = m1`, `res = res0`, over `X`'s digits with
`winsize = wsize X`. -/
def run (red : Nat → Nat) (X : MpInt) (m1 res0 : Nat) : Run :=
  ⟨red, table red m1 (Exptmod.wsize X), Exptmod.wsize X, res0, X.digit, X.used⟩

section
open Exptmod
variable {RP : MpInt → MpInt → Prop} {red : Nat → Nat} {B U m1 res0 : Nat} {X G P res M1 res' : MpInt}
  {Mt : Nat → MpInt}

/-- `x = mp_count_bits(X)` and the `if` chain on it: `winsize = wsize X`. -/
theorem winsize_eq (hX : X.Valid) : winSize (countBits X) = wsize X := by
  rw [countBits_spec hX]; rfl

/-- The table built and `X` shaped: the loop's fixed facts. -/
theorem env_of (hr : Rx RP red B U) (hX : X.Shape) (ht : Tab B U (wsize X) (table red m1 (wsize X)) Mt) :
    Env RP (run red X m1 res0) B U Mt :=
  ⟨hr, two_le_winSize _, hX.high_zero _ (Nat.le_refl _), ht⟩

/-- The loop's result is the Spec's `winRes`. -/
theorem Done.winRes (h : Done (run red X m1 res0) B U res) : Rs B U res (winRes red X m1 res0) := h

/-- `mp_set(&res, 1uL)` (`Api/MpSet.lean`: `SetPost res (1 % radix) res'`). -/
theorem res_one (hs : res.Shape) (hal : 0 < res.alloc) (hB : 1 < B) (hBU : B ≤ radix ^ U)
    (h : SetPost res (1 % radix) res') : Rs B U res' 1 :=
  Rs.of (xfer_set hs hal (by decide) h) hB hBU

theorem used_pos {P : MpInt} (hP0 : 0 < P.mag) : 0 < P.used := by
  rcases Nat.eq_zero_or_pos P.used with h0 | h0
  · rw [MpInt.mag_used_zero h0] at hP0; omega
  · exact h0

/-- `mp_mod(G, P, &M[1])`, `P > 0`: `M[1] = G mod P`. -/
theorem m1_mod (hG : G.Valid) (hP : P.Valid) (hPs : P.sign = Layout.mpZpos) (hP0 : 0 < P.mag) (hB : P.mag ≤ B)
    (hBU : B ≤ radix ^ U) (h : ModPost G P M1) : Rs B U M1 (base G P) :=
  Rs.of (xfer_modE hG hP (used_pos hP0) hPs h) (Nat.lt_of_lt_of_le (base_lt (by rw [hPs]; decide) hP0) hB) hBU

end

end Tom.WindowStep
