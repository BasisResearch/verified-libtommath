import Tom.Spec.Mont

/-!
# Barrett, diminished-radix and `2^p - d` reduction

`MP_32BIT` (`radix = 2^28`). All three reductions end in the same kind of loop: fold the
value (keeping it congruent and not larger), then subtract the modulus while the value is
not below it. `redLoop fold n fuel a` is that loop with fuel; `redLoop_spec`: when every
fold keeps the residue and does not grow the value, the loop computes `a % n`.

* `mp_reduce_2k(a, n, d)` / `mp_reduce_2k_l(a, n, d)` (`n = 2^p - d`, `p = mp_count_bits(n)`):
  the fold is `a mod 2^p + d * (a / 2^p)` (`fold2k`; `mp_div_2d`, `mp_mul_d` / `mp_mul`,
  `s_mp_add`). `Reduce2kPost.spec`. The setups: `mp_reduce_2k_setup` keeps only the low
  digit of `2^p - n` (`Setup2kPost`), which is the true `d` only when `2^p - n < radix`;
  `setup2k_lossy` is a modulus where it is not (`n = 3 * 2^28`, `d = 0`; the real library
  then computes `mp_exptmod(2, 30, 3 * 2^28) = 0` instead of `2^28`).
* `mp_dr_reduce(x, n, k)` (`n = radix^m - k`): the fold is the digit loop
  `x[i] = (x[m + i] * k + x[i] + mu) mod radix` (`drRow`), i.e.
  `x mod radix^m + k * (x / radix^m mod radix^m)` (`drFold`). `DrReducePost.spec`;
  `dr_modulus`: `mp_dr_is_modulus` moduli with `k = mp_dr_setup` satisfy `n + k = radix^m`.
* `mp_reduce(x, m, mu)` (Barrett, `mu = ⌊radix^(2k) / m⌋`, `k = m->used`): the quotient
  estimate from the high columns of `q1 * mu` (`s_mp_mul_high_digs(_fast)`: `highCols`,
  `highFastDigit`), the remainder modulo `radix^(k+1)`, and at most `k + 2` subtractions
  (`barrett_bound`). `ReducePost.spec`.
-/

namespace Tom

open MpInt

namespace Reduce

open Mont

/-! ## The fold-and-subtract loop -/

/-- `top: a = fold(a); if (a ≥ n) { a -= n; goto top; }` with fuel. -/
def redLoop (fold : Nat → Nat) (n : Nat) : Nat → Nat → Nat
  | 0, a => a
  | fuel + 1, a => if n ≤ fold a then redLoop fold n fuel (fold a - n) else fold a

/-- A fold that keeps the residue and does not grow the value. -/
structure FoldOk (fold : Nat → Nat) (n a0 : Nat) : Prop where
  le : ∀ a, a ≤ a0 → fold a ≤ a
  mod : ∀ a, a ≤ a0 → fold a % n = a % n

/-- The loop computes the residue, given more fuel than the starting value. -/
theorem redLoop_spec (fold : Nat → Nat) (n : Nat) (hn : 0 < n) :
    ∀ fuel a0 a, FoldOk fold n a0 → a ≤ a0 → a < fuel → redLoop fold n fuel a = a % n
  | 0, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, a0, a, hf, ha, hfu => by
    simp only [redLoop]
    have hle := hf.le a ha
    have hm := hf.mod a ha
    split <;> rename_i hge
    · rw [redLoop_spec fold n hn fuel a0 (fold a - n) hf (by omega) (by omega), ← hm]
      exact (Nat.mod_eq_sub_mod hge).symm
    · rw [← hm, Nat.mod_eq_of_lt (by omega)]

/-- Every value the loop meets is below `a0 + 1`: the measure for termination
(each pass that subtracts strictly decreases the value). -/
theorem redLoop_step_lt (fold : Nat → Nat) (n a0 a : Nat) (hf : FoldOk fold n a0) (ha : a ≤ a0) (hn : 0 < n)
    (hge : n ≤ fold a) : fold a - n < a := by
  have := hf.le a ha; omega

/-! ## `mp_reduce_2k`, `mp_reduce_2k_l` -/

/-- One pass of `mp_reduce_2k(_l)`: `mp_div_2d(a, p, &q, a)` (`q = a / 2^p`, `a = a mod 2^p`),
`q *= d` (`mp_mul_d`, skipped for `d == 1`; `mp_mul` for `_l`), `s_mp_add(a, &q, a)`. -/
def fold2k (p d a : Nat) : Nat := a % 2 ^ p + d * (a / 2 ^ p)

theorem fold2k_ok (p d n a0 : Nat) (h : n + d = 2 ^ p) : FoldOk (fold2k p d) n a0 where
  le := fun a _ => by
    unfold fold2k
    have := Nat.mod_add_div a (2 ^ p)
    have : d * (a / 2 ^ p) ≤ 2 ^ p * (a / 2 ^ p) := Nat.mul_le_mul_right _ (by omega)
    omega
  mod := fun a _ => by
    unfold fold2k
    have hdm := Nat.mod_add_div a (2 ^ p)
    have e : a = (a % 2 ^ p + d * (a / 2 ^ p)) + n * (a / 2 ^ p) := by
      have : 2 ^ p * (a / 2 ^ p) = n * (a / 2 ^ p) + d * (a / 2 ^ p) := by rw [← h, Nat.add_mul]
      omega
    conv => rhs; rw [e]
    rw [Nat.add_mul_mod_self_left]

/-- What `mp_reduce_2k(a, n, d)` (`d` an `mp_digit`) and `mp_reduce_2k_l(a, n, d)`
(`d = |d|`) leave in `a`: the fold-and-subtract loop with `p = mp_count_bits(n)`, valid,
the sign of `a` or `MP_ZPOS`. No pass sets `a`'s sign (`mp_mod_2d(a, p, a)`, `s_mp_add(a, &q, a)`,
`s_mp_sub(a, n, a)` work on magnitudes), but each ends in `mp_clamp`, which resets it when the
value is zero *in the middle of the loop*: for `a < 0` with `|a| mod 2^p = 0` the sign is
`MP_ZPOS` from `mp_mod_2d` on, also when the fold `d·(|a| / 2^p)` is nonzero (e.g. `|a| = 2^p`
leaves `|a'| = d`, sign `MP_ZPOS`). So the sign is `a`'s or `MP_ZPOS`, and `MP_ZPOS` for `a ≥ 0`
(`spec_val`). -/
structure Reduce2kPost (a n : MpInt) (d : Nat) (a' : MpInt) : Prop where
  valid : a'.Valid
  mag : a'.mag = redLoop (fold2k (nbits n.mag) d) n.mag (a.mag + 1) a.mag
  sign : a'.sign = Layout.mpZpos ∨ a'.sign = a.sign

/-- **`2^p - d` reduction**: for `n = 2^p - d` (`p = mp_count_bits(n)`), `|a'| = |a| mod |n|`. -/
theorem Reduce2kPost.spec {a n a' : MpInt} {d : Nat} (hn : 0 < n.mag) (hd : n.mag + d = 2 ^ nbits n.mag)
    (h : Reduce2kPost a n d a') : a'.Valid ∧ a'.mag = a.mag % n.mag := by
  refine ⟨h.valid, ?_⟩
  rw [h.mag]
  exact redLoop_spec _ _ hn _ a.mag a.mag (fold2k_ok _ _ _ _ hd) (Nat.le_refl _) (Nat.lt_succ_self _)

/-- For a nonnegative `a`, the value: `a' = a mod n`. -/
theorem Reduce2kPost.spec_val {a n a' : MpInt} {d : Nat} (hn : 0 < n.mag)
    (hd : n.mag + d = 2 ^ nbits n.mag) (hpos : a.sign = Layout.mpZpos) (h : Reduce2kPost a n d a') :
    a'.val = ((a.mag % n.mag : Nat) : Int) := by
  have hs : a'.sign = Layout.mpZpos := h.sign.elim id (fun e => e.trans hpos)
  rw [← (h.spec hn hd).2]
  unfold MpInt.val; rw [hs]; simp [Layout.mpZpos, Layout.mpNeg]

/-- What `mp_reduce_2k_setup(a, &d)` leaves: the low digit of `2^p - |a|`
(`mp_2expt`, `s_mp_sub`, `tmp.dp[0]`). -/
structure Setup2kPost (a : MpInt) (d : Nat) : Prop where
  val : d = (2 ^ nbits a.mag - a.mag) % radix

/-- When `2^p - n` is a single digit, the setup gives the true `d`. -/
theorem Setup2kPost.spec {a : MpInt} {d : Nat} (h : Setup2kPost a d) (hs : 2 ^ nbits a.mag - a.mag < radix) :
    a.mag + d = 2 ^ nbits a.mag := by
  have := nbits_lt a.mag
  rw [h.val, Nat.mod_eq_of_lt hs]; omega

theorem nbits_eq (m k : Nat) (h1 : 2 ^ k ≤ m) (h2 : m < 2 ^ (k + 1)) : nbits m = k + 1 := by
  unfold nbits
  have hm : m ≠ 0 := by have := Nat.two_pow_pos k; omega
  simp only [hm, ite_false]
  rw [(Nat.log2_eq_iff hm).2 ⟨h1, h2⟩]

/-- **`mp_reduce_2k_setup` is lossy**: for `n = 3 * 2^28` (`p = 30`, `2^p - n = 2^28`, one more
than a digit) it gives `d = 0`, and the fold `a mod 2^30` is not a reduction modulo `n`
(`2^30 ≡ 2^28`). `mp_exptmod` reaches this through `s_mp_exptmod_fast(..., 2)` for two-digit
moduli `n = (2^j - 1) * 2^28` with `0 < j < 28` (`mp_reduce_is_2k` yes, `mp_reduce_is_2k_l` no). -/
theorem setup2k_lossy :
    nbits (3 * 2 ^ 28) = 30 ∧ (2 ^ 30 - 3 * 2 ^ 28) % radix = 0 ∧
      fold2k 30 0 (2 ^ 30) = 0 ∧ 2 ^ 30 % (3 * 2 ^ 28) = 2 ^ 28 := by
  refine ⟨nbits_eq _ 29 (by decide) (by decide), by decide, by decide, by decide⟩

/-- What `mp_reduce_2k_setup_l(a, d)` leaves in `d`: `2^p - |a|` in full. -/
structure Setup2kLPost (a d' : MpInt) : Prop where
  valid : d'.Valid
  mag : d'.mag = 2 ^ nbits a.mag - a.mag

theorem Setup2kLPost.spec {a d' : MpInt} (h : Setup2kLPost a d') : a.mag + d'.mag = 2 ^ nbits a.mag := by
  have := nbits_lt a.mag; rw [h.mag]; omega

/-! ## `mp_dr_reduce` -/

/-- The digit loop of `mp_dr_reduce` after `i` steps:
`r = x[m + i] * k + x[i] + mu; x[i] = r & MP_MASK; mu = r >> MP_DIGIT_BIT`.
The upper half `x[m ..]` is read, never written, by the loop. -/
def drRow (f : Nat → Nat) (m k : Nat) : Nat → CSt
  | 0 => ⟨f, 0⟩
  | i + 1 => cstep (drRow f m k i) i (k * f (m + i))

/-- The array after a pass: the loop's digits below `m`, the carry `x[m] = mu`, and
`MP_ZERO_DIGITS` above (digits from `x->used` on are zero already). -/
def drPass (f : Nat → Nat) (m k : Nat) : Nat → Nat := fun i =>
  if i < m then (drRow f m k m).dig i else if i = m then (drRow f m k m).u else 0

theorem drRow_out (f : Nat → Nat) (m k : Nat) : ∀ i j, i ≤ j → (drRow f m k i).dig j = f j
  | 0, _, _ => rfl
  | i + 1, j, h => by
    simp only [drRow]; rw [cstep_dig_ne _ _ (by omega), drRow_out f m k i j (by omega)]

theorem drRow_val (f : Nat → Nat) (m k : Nat) :
    ∀ i, i ≤ m → natUpTo (drRow f m k i).dig m + radix ^ i * (drRow f m k i).u =
      natUpTo f m + k * natUpTo (fun j => f (m + j)) i
  | 0, _ => by simp [drRow, natUpTo]
  | i + 1, h => by
    have ih := drRow_val f m k i (by omega)
    simp only [drRow]
    have hc := cstep_val (drRow f m k i) i (k * f (m + i)) m (by omega)
    rw [Nat.mul_add] at hc
    simp only [natUpTo, Nat.mul_add]
    have e : radix ^ i * (k * f (m + i)) = k * (radix ^ i * f (m + i)) := by ac_rfl
    omega

/-- A pass computes `x mod radix^m + k * (x / radix^m mod radix^m)`. -/
def drFold (m k x : Nat) : Nat := x % radix ^ m + k * (x / radix ^ m % radix ^ m)

theorem drPass_val (f : Nat → Nat) (m k : Nat) (hf : ∀ i, f i < radix) :
    natUpTo (drPass f m k) (m + 1) = drFold m k (natUpTo f (2 * m)) := by
  have hv := drRow_val f m k m (Nat.le_refl _)
  have hlo : natUpTo (drPass f m k) m = natUpTo (drRow f m k m).dig m :=
    natUpTo_congr m (fun i hi => by simp [drPass, hi])
  simp only [natUpTo]
  rw [hlo]
  simp only [drPass, Nat.lt_irrefl, ite_false, ite_true]
  unfold drFold
  rw [show 2 * m = m + m by omega, natUpTo_split f m m, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (natUpTo_lt f hf m), Nat.add_mul_div_left _ _ (Nat.pow_pos radix_pos),
    Nat.div_eq_of_lt (natUpTo_lt f hf m), Nat.zero_add,
    Nat.mod_eq_of_lt (natUpTo_lt (fun j => f (m + j)) (fun j => hf _) m)]
  omega

/-- The carry stays a digit and `r` fits in `mp_word` when `k < radix` (`n->dp[0] ≠ 0`). -/
theorem drRow_bound (f : Nat → Nat) (m k : Nat) (hf : ∀ i, f i < radix) (hk : k < radix) :
    ∀ i, (∀ j, (drRow f m k i).dig j < radix) ∧ (drRow f m k i).u < radix
  | 0 => ⟨hf, radix_pos⟩
  | i + 1 => by
    obtain ⟨h1, h2⟩ := drRow_bound f m k hf hk i
    have ht : k * f (m + i) ≤ (radix - 1) * (radix - 1) :=
      Nat.mul_le_mul (by omega) (by have := hf (m + i); omega)
    exact ⟨cstep_dig_lt _ _ _ h1, (cstep_bound _ _ _ h2 (h1 i) ht).2⟩

theorem drFold_ok (m k n a0 : Nat) (h : n + k = radix ^ m) (ha0 : a0 < radix ^ (2 * m)) :
    FoldOk (drFold m k) n a0 where
  le := fun a ha => by
    have hlt : a / radix ^ m < radix ^ m := by
      apply Nat.div_lt_of_lt_mul; rw [← Nat.pow_add, show m + m = 2 * m by omega]; omega
    have e : drFold m k a = fold2k (Layout.digitBits * m) k a := by
      unfold drFold fold2k; rw [Nat.mod_eq_of_lt hlt, radix, ← Nat.pow_mul]
    rw [e]; exact (fold2k_ok _ k n a0 (by rw [h, radix, Nat.pow_mul])).le a ha
  mod := fun a ha => by
    have hlt : a / radix ^ m < radix ^ m := by
      apply Nat.div_lt_of_lt_mul; rw [← Nat.pow_add, show m + m = 2 * m by omega]; omega
    have e : drFold m k a = fold2k (Layout.digitBits * m) k a := by
      unfold drFold fold2k; rw [Nat.mod_eq_of_lt hlt, radix, ← Nat.pow_mul]
    rw [e]; exact (fold2k_ok _ k n a0 (by rw [h, radix, Nat.pow_mul])).mod a ha

/-- What `mp_dr_reduce(x, n, k)` leaves in `x` (`x->alloc ≥ 2 n->used`, no `mp_grow`):
the fold-and-subtract loop of `drFold`, valid, the sign of `x` (reset if zero). The digit
loop (`drRow`, `drPass_val`) is the fold when `x->used ≤ 2 n->used`. -/
structure DrReducePost (x n : MpInt) (k : Nat) (x' : MpInt) : Prop where
  valid : x'.Valid
  mag : x'.mag = redLoop (drFold n.used k) n.mag (x.mag + 1) x.mag
  sign : x'.sign = if x'.used = 0 then Layout.mpZpos else x.sign

/-- **Diminished radix reduction**: for `n = radix^m - k` and `x < radix^(2m)`
(the C asks for `x ≤ (n - 1)^2`), `|x'| = |x| mod |n|`. -/
theorem DrReducePost.spec {x n x' : MpInt} {k : Nat} (hn : 0 < n.mag) (hk : n.mag + k = radix ^ n.used)
    (hx : x.mag < radix ^ (2 * n.used)) (h : DrReducePost x n k x') : x'.Valid ∧ x'.mag = x.mag % n.mag := by
  refine ⟨h.valid, ?_⟩
  rw [h.mag]
  exact redLoop_spec _ _ hn _ x.mag x.mag (drFold_ok _ _ _ _ hk hx) (Nat.le_refl _) (Nat.lt_succ_self _)

/-- `Σ_{i<n} f i radix^i` with `f 0 = d` and every other digit `radix - 1` is `radix^n - radix + d`. -/
theorem natUpTo_top_ones (f : Nat → Nat) (hf : ∀ i, 1 ≤ i → f i = radix - 1) :
    ∀ n, 1 ≤ n → natUpTo f n + radix = radix ^ n + f 0
  | 1, _ => by simp [natUpTo]; omega
  | n + 2, _ => by
    have ih := natUpTo_top_ones f hf (n + 1) (by omega)
    rw [natUpTo, hf (n + 1) (by omega), show radix ^ (n + 2) = radix ^ (n + 1) * radix from Nat.pow_succ _ _]
    have : radix ^ (n + 1) * (radix - 1) + radix ^ (n + 1) = radix ^ (n + 1) * radix := by
      rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ radix_pos)]
    omega

/-- **The DR moduli**: `mp_dr_is_modulus(n)` (at least two digits, all but the lowest
`MP_MASK`) and `k = mp_dr_setup(n) = radix - n->dp[0]` give `n + k = radix^n->used`. -/
theorem dr_modulus (n : MpInt) (hn : n.Shape) (h2 : 2 ≤ n.used)
    (hd : ∀ i, 1 ≤ i → i < n.used → n.digit i = radix - 1) :
    n.mag + (radix - n.digit 0) = radix ^ n.used := by
  have := natUpTo_top_ones (fun i => if i < n.used then n.digit i else radix - 1)
    (fun i hi => by split <;> simp_all) n.used (by omega)
  have e : natUpTo (fun i => if i < n.used then n.digit i else radix - 1) n.used = n.mag :=
    natUpTo_congr _ (fun i hi => by simp [hi])
  rw [e] at this
  simp only [show 0 < n.used by omega, ite_true] at this
  have := hn.digit_lt 0
  unfold MpInt.mag at *; omega

/-! ## `s_mp_mul_high_digs_fast`: the columns from `digs` on -/

/-- Column `k` of `a * b` if `k ≥ digs`, else `0`. -/
def highCol (da db : Nat → Nat) (ua ub digs k : Nat) : Nat := if digs ≤ k then col da db ua ub k else 0

/-- Column `k` of `a * b` if `k < digs`, else `0`: what the high product leaves out. -/
def lowCol (da db : Nat → Nat) (ua ub digs k : Nat) : Nat := if digs ≤ k then 0 else col da db ua ub k

/-- `Σ_{i + j ≥ digs} a_i b_j radix^(i+j)`. -/
def highProd (da db : Nat → Nat) (ua ub digs : Nat) : Nat := natUpTo (highCol da db ua ub digs) (ua + ub)

theorem high_add_low (da db : Nat → Nat) (ua ub digs : Nat) :
    highProd da db ua ub digs + natUpTo (lowCol da db ua ub digs) (ua + ub) = natUpTo da ua * natUpTo db ub := by
  unfold highProd
  rw [← natUpTo_add, prod_cols]
  apply natUpTo_congr; intro k _
  unfold highCol lowCol; split <;> simp

theorem highProd_le (da db : Nat → Nat) (ua ub digs : Nat) :
    highProd da db ua ub digs ≤ natUpTo da ua * natUpTo db ub := by
  have := high_add_low da db ua ub digs; omega

/-- A column has at most `k + 1` terms. -/
theorem col_le_succ {da db : Nat → Nat} (ha : ∀ i, da i < radix) (hb : ∀ i, db i < radix) (ua ub k : Nat) :
    col da db ua ub k ≤ (k + 1) * ((radix - 1) * (radix - 1)) := by
  unfold col
  have hz : ∀ i, k + 1 ≤ i → (if i ≤ k ∧ k - i < ub then da i * db (k - i) else 0) = 0 := by
    intro i hi; simp [show ¬ i ≤ k by omega]
  have hle : sumTo (fun i => if i ≤ k ∧ k - i < ub then da i * db (k - i) else 0) ua ≤
      sumTo (fun i => if i ≤ k ∧ k - i < ub then da i * db (k - i) else 0) (k + 1) := by
    rcases Nat.le_total ua (k + 1) with h | h
    · exact sumTo_mono _ h
    · rw [sumTo_zeros _ (k + 1) ua h (fun i h1 _ => hz i h1)]; exact Nat.le_refl _
  refine Nat.le_trans hle (sumTo_le _ fun i _ => ?_)
  split
  · exact Nat.mul_le_mul (by have := ha i; omega) (by have := hb (k - i); omega)
  · exact Nat.zero_le _

/-- `Σ_{i<n} f i radix^i < C radix^n` when every entry is at most `C (radix - 1)`. -/
theorem natUpTo_le_scaled (f : Nat → Nat) (C : Nat) (hf : ∀ i, f i ≤ C * (radix - 1)) :
    ∀ n, natUpTo f n + C ≤ C * radix ^ n
  | 0 => by simp [natUpTo]
  | n + 1 => by
    have ih := natUpTo_le_scaled f C hf n
    have h := hf n
    simp only [natUpTo, Nat.pow_succ]
    have : radix ^ n * f n ≤ radix ^ n * (C * (radix - 1)) := Nat.mul_le_mul_left _ h
    have hc : C * (radix - 1) + C = C * radix := by
      rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ radix_pos)]
    have e : C * radix ^ n + radix ^ n * (C * (radix - 1)) = C * (radix ^ n * radix) :=
      calc C * radix ^ n + radix ^ n * (C * (radix - 1)) = radix ^ n * (C * (radix - 1) + C) := by
            rw [Nat.mul_add]; ac_rfl
        _ = C * (radix ^ n * radix) := by rw [hc]; ac_rfl
    omega

/-- **The left-out columns** (below `digs ≥ 1`) are worth less than `digs * radix^(digs+1)`. -/
theorem lowCols_lt {da db : Nat → Nat} (ha : ∀ i, da i < radix) (hb : ∀ i, db i < radix) (ua ub digs : Nat)
    (hd : 1 ≤ digs) : natUpTo (lowCol da db ua ub digs) (ua + ub) < digs * radix ^ (digs + 1) := by
  have hc : ∀ k, lowCol da db ua ub digs k ≤ (digs * (radix - 1)) * (radix - 1) := by
    intro k; unfold lowCol; split
    · exact Nat.zero_le _
    · refine Nat.le_trans (col_le_succ ha hb ua ub k) ?_
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
  have hz : ∀ k, digs ≤ k → lowCol da db ua ub digs k = 0 := by intro k hk; simp [lowCol, hk]
  have hz2 : ∀ k, ua + ub ≤ k + 1 → lowCol da db ua ub digs k = 0 := by
    intro k hk; unfold lowCol; split
    · rfl
    · exact col_high da db ua ub k hk
  have heq : natUpTo (lowCol da db ua ub digs) (ua + ub) ≤ natUpTo (lowCol da db ua ub digs) digs := by
    rcases Nat.le_total digs (ua + ub) with h | h
    · rw [natUpTo_zeros _ digs (ua + ub) h (fun i h1 _ => hz i h1)]; exact Nat.le_refl _
    · rcases Nat.eq_zero_or_pos (ua + ub) with h0 | h0
      · rw [h0]; exact Nat.zero_le _
      · rw [natUpTo_zeros _ (ua + ub) digs h (fun i h1 _ => hz2 i (by omega))]; exact Nat.le_refl _
  have hs := natUpTo_le_scaled _ _ hc digs
  have hpos : 0 < digs * (radix - 1) := Nat.mul_pos (by omega) (by simp [radix, Layout.digitBits])
  have : digs * (radix - 1) * radix ^ digs ≤ digs * radix ^ (digs + 1) :=
    calc digs * (radix - 1) * radix ^ digs ≤ digs * radix * radix ^ digs :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      _ = digs * radix ^ (digs + 1) := by rw [Nat.pow_succ]; ac_rfl
  omega

/-- The digits `s_mp_mul_high_digs_fast(a, b, c, digs)` leaves: `c`'s old digits below `digs`
(they are not written; `c` may be `a`, as in `mp_reduce`), the comba digits of the columns
`digs .. pa - 1` with the carry starting from zero at `digs`, zero from `pa = a->used + b->used`. -/
def highFastDigit (a b c : MpInt) (digs i : Nat) : Nat :=
  if i < digs then c.digit i
  else if i < a.used + b.used then combaD (fun k => col a.digit b.digit a.used b.used (digs + k)) (i - digs)
  else 0

/-- What `s_mp_mul_high_digs_fast(a, b, c, digs)` leaves in `c` when `c->alloc ≥ a->used + b->used`
(no `mp_grow`, D5): `highFastDigit`, `used` clamped from `pa`, the sign of `c` (reset if
zero), `alloc` unchanged. -/
structure MulHighFastPost (a b c c' : MpInt) (digs : Nat) : Prop where
  alloc : c'.alloc = c.alloc
  len : c'.digits.length = c.alloc
  digit : c'.digit = highFastDigit a b c digs
  used : c'.used = clampUsed (highFastDigit a b c digs) (a.used + b.used)
  sign : c'.sign = if c'.used = 0 then Layout.mpZpos else c.sign

theorem highFastDigit_lt {a b c : MpInt} (hc : c.Shape) (digs i : Nat) : highFastDigit a b c digs i < radix := by
  unfold highFastDigit; split
  · exact hc.digit_lt i
  · split
    · exact combaD_lt _ _
    · exact radix_pos

/-- The value: the old low digits plus the high product (no carry leaves column `pa - 1`). -/
theorem highFast_val {a b c : MpInt} (ha : a.Shape) (hb : b.Shape) (digs : Nat)
    (hd : digs ≤ a.used + b.used) :
    natUpTo (highFastDigit a b c digs) (a.used + b.used) =
      natUpTo c.digit digs + highProd a.digit b.digit a.used b.used digs := by
  obtain ⟨m, hm⟩ : ∃ m, a.used + b.used = digs + m := ⟨a.used + b.used - digs, by omega⟩
  generalize hcl : (fun k => col a.digit b.digit a.used b.used (digs + k)) = cl
  have hlow : natUpTo (highFastDigit a b c digs) digs = natUpTo c.digit digs :=
    natUpTo_congr _ (fun i hi => by simp [highFastDigit, hi])
  have hup : natUpTo (fun i => highFastDigit a b c digs (digs + i)) m = natUpTo (combaD cl) m :=
    natUpTo_congr _ (fun i hi => by
      simp [highFastDigit, show ¬ digs + i < digs by omega, show digs + i < a.used + b.used by omega, ← hcl])
  have hhp : highProd a.digit b.digit a.used b.used digs = radix ^ digs * natUpTo cl m := by
    unfold highProd; rw [hm, natUpTo_split _ digs m,
      natUpTo_congr digs (e := fun _ => 0) (fun i hi => by simp [highCol, show ¬ digs ≤ i by omega]),
      natUpTo_zero_fun, Nat.zero_add, ← hcl]
    congr 1; apply natUpTo_congr; intro i _; simp [highCol]
  have hs := comba_sum cl m
  have hlt : highProd a.digit b.digit a.used b.used digs < radix ^ (digs + m) := by
    rw [← hm, Nat.pow_add]
    exact Nat.lt_of_le_of_lt (highProd_le _ _ _ _ _)
      (Nat.mul_lt_mul'' (MpInt.mag_lt ha) (MpInt.mag_lt hb))
  have hw : combaW cl m = 0 := by
    rcases Nat.eq_zero_or_pos (combaW cl m) with h | h
    · exact h
    · exfalso
      have : radix ^ digs * (radix ^ m * 1) ≤ radix ^ digs * (radix ^ m * combaW cl m) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h)
      rw [Nat.pow_add] at hlt
      have : radix ^ digs * (radix ^ m * combaW cl m) ≤ highProd a.digit b.digit a.used b.used digs := by
        rw [hhp, ← hs]; exact Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
      rw [Nat.mul_one] at *; omega
  rw [hw, Nat.mul_zero, Nat.add_zero] at hs
  rw [hm, natUpTo_split, hlow, hup, hs, hhp]

/-- `s_mp_mul_high_digs_fast` leaves a valid `c` holding the old low digits plus the high
product. -/
theorem MulHighFastPost.spec {a b c c' : MpInt} {digs : Nat} (ha : a.Shape) (hb : b.Shape) (hc : c.Shape)
    (hd : digs ≤ a.used + b.used) (hroom : a.used + b.used ≤ c.alloc)
    (hsign : c.sign = Layout.mpZpos ∨ c.sign = Layout.mpNeg) (h : MulHighFastPost a b c c' digs) :
    c'.Valid ∧ c'.mag = natUpTo c.digit digs + highProd a.digit b.digit a.used b.used digs := by
  have hle := clampUsed_le (highFastDigit a b c digs) (a.used + b.used)
  refine ⟨{ len := ?_, used_le := ?_, alloc_lt := ?_, digit_lt := ?_, high_zero := ?_,
            top := ?_, sign_ok := ?_, zero_pos := ?_ }, ?_⟩
  · rw [h.len, h.alloc]
  · rw [h.used, h.alloc]; omega
  · rw [h.alloc]; exact hc.alloc_lt
  · rw [h.digit]; exact highFastDigit_lt hc digs
  · intro i hi
    rw [h.digit]
    by_cases hlt : i < a.used + b.used
    · exact clampUsed_zero _ _ i (h.used ▸ hi) hlt
    · simp [highFastDigit, show ¬ i < digs by omega, hlt]
  · intro hu; rw [h.digit, h.used]; exact clampUsed_top _ _ (h.used ▸ hu)
  · rw [h.sign]; split
    · exact Or.inl rfl
    · exact hsign
  · intro hu; rw [h.sign, ite_eq_left_iff.2 (fun h => absurd hu h)]
  · unfold MpInt.mag; rw [h.digit, h.used, natUpTo_clampUsed]; exact highFast_val (c := c) ha hb digs hd

/-! ## `s_mp_mul_high_digs`: the rows -/

/-- `Σ_{s ≤ j < ub} db j radix^j`: the part of `b` a row from `digs` on uses. -/
def rowHigh (db : Nat → Nat) (ub s : Nat) : Nat := natUpTo (fun j => if s ≤ j then db j else 0) ub

/-- The high product by rows: `Σ_{ix < ua} radix^ix * a_ix * rowHigh b (digs - ix)`. -/
def highRows (da db : Nat → Nat) (ub digs : Nat) : Nat → Nat
  | 0 => 0
  | ua + 1 => highRows da db ub digs ua + radix ^ ua * (da ua * rowHigh db ub (digs - ua))

/-- **Rows and columns agree** on the high product. -/
theorem highProd_rows (da db : Nat → Nat) (ub digs : Nat) :
    ∀ ua, highProd da db ua ub digs = highRows da db ub digs ua
  | 0 => by
    unfold highProd highRows
    rw [natUpTo_congr _ (e := fun _ => 0) (fun k _ => by simp [highCol, col, sumTo]), natUpTo_zero_fun]
  | ua + 1 => by
    have ih := highProd_rows da db ub digs ua
    unfold highProd at ih ⊢
    simp only [highRows]
    rw [← ih]
    have hsplit : natUpTo (highCol da db (ua + 1) ub digs) (ua + 1 + ub) =
        natUpTo (highCol da db ua ub digs) (ua + 1 + ub) +
          natUpTo (fun k => if ua ≤ k then (if digs ≤ ua + (k - ua) ∧ k - ua < ub then da ua * db (k - ua) else 0)
            else 0) (ua + 1 + ub) := by
      rw [← natUpTo_add]; apply natUpTo_congr; intro k _
      unfold highCol; rw [col_succ]
      by_cases h1 : digs ≤ k
      · by_cases h2 : ua ≤ k
        · simp [h1, h2, show ua + (k - ua) = k by omega]
        · simp [h1, h2]
      · by_cases h2 : ua ≤ k
        · simp [h1, h2]
        · simp [h1, h2]
    have hold : natUpTo (highCol da db ua ub digs) (ua + 1 + ub) = natUpTo (highCol da db ua ub digs) (ua + ub) :=
      natUpTo_zeros _ _ _ (by omega) (fun k h1 _ => by
        unfold highCol; split
        · exact col_high da db ua ub k (by omega)
        · rfl)
    have hnew : natUpTo (fun k => if ua ≤ k then (if digs ≤ ua + (k - ua) ∧ k - ua < ub then da ua * db (k - ua)
        else 0) else 0) (ua + 1 + ub) = radix ^ ua * (da ua * rowHigh db ub (digs - ua)) := by
      rw [show ua + 1 + ub = ua + (ub + 1) by omega,
        natUpTo_shift (fun j => if digs ≤ ua + j ∧ j < ub then da ua * db j else 0) ua (ub + 1)]
      congr 1
      unfold rowHigh
      simp only [natUpTo, Nat.lt_irrefl, and_false, ite_false, Nat.mul_zero, Nat.add_zero]
      rw [← natUpTo_mul]
      apply natUpTo_congr; intro j hj
      by_cases h : digs - ua ≤ j
      · simp [h, hj, show digs ≤ ua + j by omega]
      · simp [h, show ¬ digs ≤ ua + j by omega]
    rw [hsplit, hold, hnew]

/-- The `t` array after row `ix` of `s_mp_mul_high_digs(a, b, c, digs)`: the inner loop from
`iy = digs - ix` (positions `digs ..`, `r = t[ix + iy] + a[ix] * b[iy] + u`), then
`*tmpt = u` at position `digs + (pb - (digs - ix))`. Needs `ix ≤ digs` (the C reads
`b->dp + (digs - ix)`, out of bounds for `ix > digs`, i.e. `a->used > digs + 1`). -/
def highRow (da db : Nat → Nat) (pb digs ix : Nat) (f : Nat → Nat) : Nat → Nat :=
  let s := rowAt (fun j => db (digs - ix + j)) (da ix) digs ⟨f, 0⟩ (pb - (digs - ix))
  upd s.dig (digs + (pb - (digs - ix))) s.u

/-- A row adds `radix^ix * a_ix * rowHigh b (digs - ix)` (when the carry's slot was empty). -/
theorem highRow_val (da db : Nat → Nat) (pb digs ix D : Nat) (f : Nat → Nat) (hix : ix ≤ digs)
    (hD : digs + (pb - (digs - ix)) < D) (h0 : f (digs + (pb - (digs - ix))) = 0) :
    natUpTo (highRow da db pb digs ix f) D = natUpTo f D + radix ^ ix * (da ix * rowHigh db pb (digs - ix)) := by
  unfold highRow
  simp only
  generalize hn : pb - (digs - ix) = n at *
  have hr := rowAt_val (fun j => db (digs - ix + j)) (da ix) digs ⟨f, 0⟩ D n (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at hr
  have hu := natUpTo_upd (rowAt (fun j => db (digs - ix + j)) (da ix) digs ⟨f, 0⟩ n).dig (digs + n)
    (rowAt (fun j => db (digs - ix + j)) (da ix) digs ⟨f, 0⟩ n).u D hD
  rw [rowAt_dig_out _ _ _ _ _ _ (Or.inr (Nat.le_refl _))] at hu
  dsimp only at hu
  rw [h0, Nat.mul_zero, Nat.add_zero] at hu
  rw [hu, hr]
  congr 1
  -- radix^digs * (a * Σ_{j<n} b(digs-ix+j) radix^j) = radix^ix * (a * rowHigh b pb (digs - ix))
  unfold rowHigh
  rcases Nat.le_total (digs - ix) pb with h | h
  · obtain ⟨m, hm⟩ : ∃ m, pb = (digs - ix) + m := ⟨pb - (digs - ix), by omega⟩
    rw [hm, natUpTo_split _ (digs - ix) m,
      natUpTo_congr (digs - ix) (e := fun _ => 0) (fun j hj => by simp [show ¬ digs - ix ≤ j by omega]),
      natUpTo_zero_fun, Nat.zero_add,
      natUpTo_congr m (e := fun j => db (digs - ix + j)) (fun j _ => by simp)]
    rw [show n = m by omega, show digs = ix + (digs - ix) by omega, Nat.pow_add]
    simp only [show ix + (digs - ix) - ix = digs - ix by omega]
    ac_rfl
  · rw [show n = 0 by omega, natUpTo_congr pb (e := fun _ => 0) (fun j hj => by simp [show ¬ digs - ix ≤ j by omega]),
      natUpTo_zero_fun]
    simp [natUpTo]

/-- What `s_mp_mul_high_digs(a, b, c, digs)` leaves in `c` on its own path (`a->used + b->used + 1 ≥
MP_WARRAY` or `min(used) ≥ MP_MAXFAST`, `a->used ≤ digs + 1`): the fresh `t` (zero below
`digs`), clamped, exchanged into `c`. -/
structure MulHighPost (a b c' : MpInt) (digs : Nat) : Prop where
  valid : c'.Valid
  mag : c'.mag = highRows a.digit b.digit b.used digs a.used
  sign : c'.sign = Layout.mpZpos

/-- Both paths of `s_mp_mul_high_digs` give the high product (plus, on the fast path, the old
low digits of `c`). -/
theorem MulHighPost.spec {a b c' : MpInt} {digs : Nat} (h : MulHighPost a b c' digs) :
    c'.Valid ∧ c'.mag = highProd a.digit b.digit a.used b.used digs := by
  rw [highProd_rows]; exact ⟨h.valid, h.mag⟩

/-! ## Barrett's bound (HAC 14.42, with the high-column estimate of 14.44) -/

/-- **Barrett**: with `q1 = ⌊x / radix^(k-1)⌋`, `mu = ⌊radix^(2k) / m⌋`, an estimate
`q2 ≤ q1 * mu < q2 + e radix^(k+1)` and `q3 = ⌊q2 / radix^(k+1)⌋`, the remainder
`x - q3 m` is in `[0, (e + 3) m)`. -/
theorem barrett_bound (x m mu k q2 e : Nat) (hk : 1 ≤ k) (hm1 : radix ^ (k - 1) ≤ m) (hmu : mu = radix ^ (2 * k) / m)
    (hx : x < radix ^ (2 * k)) (hq2 : q2 ≤ x / radix ^ (k - 1) * mu)
    (hq2' : x / radix ^ (k - 1) * mu < q2 + e * radix ^ (k + 1)) :
    q2 / radix ^ (k + 1) * m ≤ x ∧ x < (q2 / radix ^ (k + 1) + e + 3) * m := by
  have hm0 : 0 < m := Nat.lt_of_lt_of_le (Nat.pow_pos radix_pos) hm1
  have hB1 : 0 < radix ^ (k - 1) := Nat.pow_pos radix_pos
  have hBk1 : 0 < radix ^ (k + 1) := Nat.pow_pos radix_pos
  have h2k : radix ^ (2 * k) = radix ^ (k - 1) * radix ^ (k + 1) := by
    rw [← Nat.pow_add]; congr 1; omega
  generalize hq1 : x / radix ^ (k - 1) = q1 at hq2 hq2'
  generalize hq3 : q2 / radix ^ (k + 1) = q3
  have hx1 := Nat.mod_add_div x (radix ^ (k - 1))
  have hx1' := Nat.mod_lt x hB1
  rw [hq1] at hx1
  have hD := Nat.mod_add_div (radix ^ (2 * k)) m
  have hD' := Nat.mod_lt (radix ^ (2 * k)) hm0
  rw [← hmu] at hD
  have hq3a : q3 * radix ^ (k + 1) ≤ q2 := by rw [← hq3]; exact Nat.div_mul_le_self _ _
  have hq3b : q2 < (q3 + 1) * radix ^ (k + 1) := by
    have := Nat.mod_add_div q2 (radix ^ (k + 1)); have := Nat.mod_lt q2 hBk1
    rw [← hq3, Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
  constructor
  · -- q3 m radix^(k+1) ≤ q2 m ≤ q1 mu m ≤ q1 radix^(2k) ≤ x radix^(k+1)
    have h1 : q3 * m * radix ^ (k + 1) ≤ x * radix ^ (k + 1) := by
      have : q3 * m * radix ^ (k + 1) = m * (q3 * radix ^ (k + 1)) := by ac_rfl
      rw [this]
      have a1 : m * (q3 * radix ^ (k + 1)) ≤ m * (q1 * mu) := Nat.mul_le_mul_left _ (Nat.le_trans hq3a hq2)
      have a2 : m * (q1 * mu) = q1 * (mu * m) := by ac_rfl
      have a3 : q1 * (mu * m) ≤ q1 * radix ^ (2 * k) := Nat.mul_le_mul_left _ (by rw [Nat.mul_comm]; omega)
      have a4 : q1 * radix ^ (2 * k) = (radix ^ (k - 1) * q1) * radix ^ (k + 1) := by rw [h2k]; ac_rfl
      have a5 : (radix ^ (k - 1) * q1) * radix ^ (k + 1) ≤ x * radix ^ (k + 1) :=
        Nat.mul_le_mul_right _ (by conv => rhs; rw [← hx1]
                                   exact Nat.le_add_left _ _)
      omega
    exact Nat.le_of_mul_le_mul_right h1 hBk1
  · -- x radix^(2k) = q1 mu m radix^(k-1) + r1 mu m + x r2 < ((q3 + e + 1) m + radix^(k-1) + m) radix^(2k)
    have e1 : x * radix ^ (2 * k) = q1 * mu * m * radix ^ (k - 1) + (x % radix ^ (k - 1)) * (mu * m) +
        x * (radix ^ (2 * k) % m) := by
      have : x * radix ^ (2 * k) = x * (m * mu + radix ^ (2 * k) % m) := by rw [Nat.add_comm, hD]
      rw [this]
      conv => lhs; rw [← hx1]
      grind
    have b1 : q1 * mu * m * radix ^ (k - 1) < (q3 + e + 1) * m * radix ^ (2 * k) := by
      have : q1 * mu < (q3 + e + 1) * radix ^ (k + 1) := by
        have : (q3 + e + 1) * radix ^ (k + 1) = (q3 + 1) * radix ^ (k + 1) + e * radix ^ (k + 1) := by
          rw [Nat.add_right_comm, Nat.add_mul]
        omega
      have h' : q1 * mu * (m * radix ^ (k - 1)) < (q3 + e + 1) * radix ^ (k + 1) * (m * radix ^ (k - 1)) :=
        Nat.mul_lt_mul_of_pos_right this (Nat.mul_pos hm0 hB1)
      have r1 : q1 * mu * m * radix ^ (k - 1) = q1 * mu * (m * radix ^ (k - 1)) := by ac_rfl
      have r2 : (q3 + e + 1) * m * radix ^ (2 * k) = (q3 + e + 1) * radix ^ (k + 1) * (m * radix ^ (k - 1)) := by
        rw [h2k]; ac_rfl
      omega
    have b2 : (x % radix ^ (k - 1)) * (mu * m) ≤ (x % radix ^ (k - 1)) * radix ^ (2 * k) :=
      Nat.mul_le_mul_left _ (by rw [Nat.mul_comm]; omega)
    have b3 : (x % radix ^ (k - 1)) * radix ^ (2 * k) ≤ m * radix ^ (2 * k) :=
      Nat.mul_le_mul_right _ (by omega)
    have b4 : x * (radix ^ (2 * k) % m) ≤ x * m := Nat.mul_le_mul_left _ (Nat.le_of_lt hD')
    have b5 : x * m < radix ^ (2 * k) * m := Nat.mul_lt_mul_of_pos_right hx hm0
    have b6 : x * radix ^ (2 * k) < (q3 + e + 3) * m * radix ^ (2 * k) := by
      have : (q3 + e + 3) * m * radix ^ (2 * k) =
          (q3 + e + 1) * m * radix ^ (2 * k) + m * radix ^ (2 * k) + radix ^ (2 * k) * m := by
        rw [show q3 + e + 3 = (q3 + e + 1) + 1 + 1 by omega, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul]
        ac_rfl
      omega
    exact Nat.lt_of_mul_lt_mul_right b6

/-! ## `mp_reduce_setup`, `mp_reduce` -/

/-- What `mp_reduce_setup(a, b)` leaves in `a` (`mp_2expt(a, 2 * b->used * MP_DIGIT_BIT)`,
`mp_div(a, b, a, NULL)`; `b > 0`): `mu = ⌊radix^(2 b->used) / b⌋`. -/
structure ReduceSetupPost (b a' : MpInt) : Prop where
  valid : a'.Valid
  mag : a'.mag = radix ^ (2 * b.used) / b.mag
  sign : a'.sign = Layout.mpZpos

/-- `mu` has `k + 1` digits: it is at least `radix^k` (for `0 < b < radix^k`). -/
theorem ReduceSetupPost.ge {b a' : MpInt} (hb : b.Shape) (hb0 : 0 < b.mag) (h : ReduceSetupPost b a') :
    radix ^ b.used ≤ a'.mag := by
  rw [h.mag]
  apply (Nat.le_div_iff_mul_le hb0).2
  rw [Nat.two_mul, Nat.pow_add]
  exact Nat.mul_le_mul_left _ (Nat.le_of_lt (MpInt.mag_lt hb))

/-- The digits of `q1 = ⌊x / radix^(k-1)⌋` (`mp_init_copy(&q, x); mp_rshd(&q, um - 1)`). -/
def q1Digit (x : MpInt) (k i : Nat) : Nat := x.digit (k - 1 + i)

def q1Used (x : MpInt) (k : Nat) : Nat := x.used - (k - 1)

theorem q1_val {x : MpInt} (hx : x.Shape) (k : Nat) :
    natUpTo (q1Digit x k) (q1Used x k) = x.mag / radix ^ (k - 1) := by
  unfold q1Digit q1Used MpInt.mag
  rcases Nat.le_total (k - 1) x.used with h | h
  · obtain ⟨m, hm⟩ : ∃ m, x.used = (k - 1) + m := ⟨x.used - (k - 1), by omega⟩
    rw [hm, natUpTo_split, Nat.add_mul_div_left _ _ (Nat.pow_pos radix_pos),
      Nat.div_eq_of_lt (natUpTo_lt _ hx.digit_lt _), Nat.zero_add, Nat.add_sub_cancel_left]
  · rw [show x.used - (k - 1) = 0 by omega, Nat.div_eq_of_lt]
    · rfl
    · exact Nat.lt_of_lt_of_le (natUpTo_lt _ hx.digit_lt _) (Nat.pow_le_pow_right radix_pos h)

/-- The quotient estimate `q3` of `mp_reduce`: `q1 * mu` in full (`mp_mul`, when
`um > 2^(MP_DIGIT_BIT - 1)`) or its columns from `um` on (`s_mp_mul_high_digs(&q, mu, &q, um)`),
then `mp_rshd(&q, um + 1)`. -/
def barrettQ3 (x m mu : MpInt) : Nat :=
  if 2 ^ 27 < m.used then (x.mag / radix ^ (m.used - 1)) * mu.mag / radix ^ (m.used + 1)
  else highProd (q1Digit x m.used) mu.digit (q1Used x m.used) mu.used m.used / radix ^ (m.used + 1)

/-- The remainder before the final subtractions: `mp_mod_2d(x, MP_DIGIT_BIT * (um + 1), x)`,
`s_mp_mul_digs(&q, m, &q, um + 1)` (`q3 * m mod radix^(um+1)`), `mp_sub(x, &q, x)`, and
`radix^(um+1)` added back (`mp_set`, `mp_lshd`, `mp_add`) if that is negative. -/
def barrettR (x m k q3 : Nat) : Nat :=
  (x % radix ^ (k + 1) + radix ^ (k + 1) - q3 * m % radix ^ (k + 1)) % radix ^ (k + 1)

/-- `mp_reduce`'s result: `barrettR`, then `while (mp_cmp(x, m) != MP_LT) s_mp_sub(x, m, x)`. -/
def barrett (x m mu : MpInt) : Nat :=
  redLoop id m.mag (barrettR x.mag m.mag m.used (barrettQ3 x m mu) + 1)
    (barrettR x.mag m.mag m.used (barrettQ3 x m mu))

/-- What `mp_reduce(x, m, mu)` leaves in `x` (for `x ≥ 0`, allocations not failing). -/
structure ReducePost (x m mu x' : MpInt) : Prop where
  valid : x'.Valid
  mag : x'.mag = barrett x m mu
  sign : x'.sign = Layout.mpZpos

/-- With the true remainder in range, `barrettR` is the remainder. -/
theorem barrettR_eq (x m k q3 : Nat) (h1 : q3 * m ≤ x) (h2 : x - q3 * m < radix ^ (k + 1)) :
    barrettR x m k q3 = x - q3 * m := by
  unfold barrettR
  generalize hD : radix ^ (k + 1) = D at h2
  have hD0 : 0 < D := by rw [← hD]; exact Nat.pow_pos radix_pos
  generalize hr : x - q3 * m = r at h2
  have hx : x = q3 * m + r := by omega
  have hs := Nat.mod_lt (q3 * m) hD0
  have hxm : x % D = (q3 * m % D + r) % D := by rw [hx, Nat.add_mod, Nat.mod_eq_of_lt h2]
  rcases Nat.lt_or_ge (q3 * m % D + r) D with h | h
  · rw [hxm, Nat.mod_eq_of_lt h, show q3 * m % D + r + D - q3 * m % D = r + D by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt h2]
  · rw [hxm, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (show q3 * m % D + r - D < D by omega),
      show q3 * m % D + r - D + D - q3 * m % D = r by omega, Nat.mod_eq_of_lt h2]

/-- The high product is a multiple of `radix^digs`. -/
theorem highProd_dvd (da db : Nat → Nat) (ua ub digs : Nat) : radix ^ digs ∣ highProd da db ua ub digs := by
  unfold highProd
  rcases Nat.le_total digs (ua + ub) with h | h
  · obtain ⟨m, hm⟩ : ∃ m, ua + ub = digs + m := ⟨ua + ub - digs, by omega⟩
    rw [hm, natUpTo_split _ digs m,
      natUpTo_congr digs (e := fun _ => 0) (fun i hi => by simp [highCol, show ¬ digs ≤ i by omega]),
      natUpTo_zero_fun, Nat.zero_add]
    exact Nat.dvd_mul_right _ _
  · rw [natUpTo_congr _ (e := fun _ => 0) (fun i hi => by simp [highCol, show ¬ digs ≤ i by omega]),
      natUpTo_zero_fun]
    exact Nat.dvd_zero _

/-- `mp_rshd(&q, um + 1)` after `s_mp_mul_high_digs_fast`: the old low digits drop out. -/
theorem highFast_shift (low H digs : Nat) (hl : low < radix ^ digs) (hH : radix ^ digs ∣ H) :
    (low + H) / radix ^ (digs + 1) = H / radix ^ (digs + 1) := by
  obtain ⟨c, rfl⟩ := hH
  have hp : 0 < radix ^ digs := Nat.pow_pos radix_pos
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hp,
    Nat.div_eq_of_lt hl, Nat.zero_add, Nat.mul_div_cancel_left _ hp]

/-- **Barrett reduction** (`mp_reduce`): for `mu = ⌊radix^(2k) / m⌋` (`k = m->used ≥ 1`) and
`0 ≤ x < radix^(2k)`, `|x'| = |x| mod |m|`; at most `k + 2` (`3` with the full product)
final subtractions. -/
theorem ReducePost.spec {x m mu x' : MpInt} (hx : x.Shape) (hm : m.Valid) (hmuS : mu.Shape) (hk : 0 < m.used)
    (hmu : mu.mag = radix ^ (2 * m.used) / m.mag) (hxb : x.mag < radix ^ (2 * m.used)) (h : ReducePost x m mu x') :
    x'.Valid ∧ x'.mag = x.mag % m.mag ∧ x'.val = ((x.mag % m.mag : Nat) : Int) := by
  have hm1 := MpInt.mag_ge hm hk
  have hmk := MpInt.mag_lt hm.toShape
  have hm0 : 0 < m.mag := Nat.lt_of_lt_of_le (Nat.pow_pos radix_pos) hm1
  -- the estimate and its error
  have hq : barrettQ3 x m mu * m.mag ≤ x.mag ∧ x.mag - barrettQ3 x m mu * m.mag < radix ^ (m.used + 1) := by
    have hfit : ∀ e, e + 3 ≤ radix → x.mag < (barrettQ3 x m mu + e + 3) * m.mag →
        x.mag - barrettQ3 x m mu * m.mag < radix ^ (m.used + 1) := by
      intro e he hlt
      have : (e + 3) * m.mag ≤ radix * radix ^ m.used :=
        Nat.mul_le_mul he (Nat.le_of_lt hmk)
      rw [Nat.pow_succ, Nat.mul_comm (radix ^ m.used)]
      have e2 : (barrettQ3 x m mu + e + 3) * m.mag = barrettQ3 x m mu * m.mag + (e + 3) * m.mag := by
        rw [Nat.add_assoc, Nat.add_mul]
      have h3 : x.mag < barrettQ3 x m mu * m.mag + radix * radix ^ m.used :=
        calc x.mag < (barrettQ3 x m mu + e + 3) * m.mag := hlt
          _ = _ := e2
          _ ≤ _ := Nat.add_le_add_left this _
      have := Nat.mul_pos radix_pos (Nat.pow_pos (n := m.used) radix_pos)
      omega
    by_cases hbig : 2 ^ 27 < m.used
    · have hq3 : barrettQ3 x m mu = x.mag / radix ^ (m.used - 1) * mu.mag / radix ^ (m.used + 1) := by
        simp [barrettQ3, hbig]
      have b := barrett_bound x.mag m.mag mu.mag m.used (x.mag / radix ^ (m.used - 1) * mu.mag) 1 hk hm1 hmu hxb
        (Nat.le_refl _) (by have := Nat.pow_pos (n := m.used + 1) radix_pos; omega)
      rw [← hq3] at b
      exact ⟨b.1, hfit 1 (by simp [radix, Layout.digitBits]) b.2⟩
    · have hq3 : barrettQ3 x m mu =
          highProd (q1Digit x m.used) mu.digit (q1Used x m.used) mu.used m.used / radix ^ (m.used + 1) := by
        simp [barrettQ3, hbig]
      have hl := lowCols_lt (da := q1Digit x m.used) (fun i => hx.digit_lt _) hmuS.digit_lt (q1Used x m.used) mu.used m.used hk
      have ha := high_add_low (q1Digit x m.used) mu.digit (q1Used x m.used) mu.used m.used
      rw [q1_val hx] at ha
      unfold MpInt.mag at ha
      have b := barrett_bound x.mag m.mag mu.mag m.used
        (highProd (q1Digit x m.used) mu.digit (q1Used x m.used) mu.used m.used) m.used hk hm1 hmu hxb
        (by unfold MpInt.mag; omega) (by unfold MpInt.mag; omega)
      rw [← hq3] at b
      exact ⟨b.1, hfit m.used (by simp [radix, Layout.digitBits]; omega) b.2⟩
  have hr := barrettR_eq x.mag m.mag m.used _ hq.1 hq.2
  have hmag : x'.mag = x.mag % m.mag := by
    rw [h.mag]; unfold barrett; rw [hr]
    rw [redLoop_spec id m.mag hm0 _ (x.mag - barrettQ3 x m mu * m.mag) _ ⟨fun _ _ => Nat.le_refl _, fun _ _ => rfl⟩
      (Nat.le_refl _) (Nat.lt_succ_self _)]
    have : x.mag = (x.mag - barrettQ3 x m mu * m.mag) + m.mag * barrettQ3 x m mu := by
      have := Nat.mul_comm m.mag (barrettQ3 x m mu); omega
    conv => rhs; rw [this]
    rw [Nat.add_mul_mod_self_left]
  refine ⟨h.valid, hmag, ?_⟩
  unfold MpInt.val; rw [h.sign, hmag]; simp [Layout.mpZpos, Layout.mpNeg]

/-! ## `mp_mulmod` -/

/-- What `mp_mulmod(a, b, c, d)` leaves in `d` (`mp_mul(a, b, &t)`, `mp_mod(&t, c, d)`), `c > 0`:
the value of `a * b` modulo `c` in `[0, c)`. -/
structure MulmodPost (a b c d' : MpInt) : Prop where
  valid : d'.Valid
  val : d'.val = (a.val * b.val) % c.val

theorem MulmodPost.spec {a b c d' : MpInt} (hc : 0 < c.val) (h : MulmodPost a b c d') :
    d'.Valid ∧ 0 ≤ d'.val ∧ d'.val < c.val ∧ d'.val = (a.val * b.val) % c.val :=
  ⟨h.valid, h.val ▸ Int.emod_nonneg _ (by omega), h.val ▸ Int.emod_lt_of_pos _ hc, h.val⟩

end Reduce

end Tom
