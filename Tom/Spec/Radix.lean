import Tom.Spec.Signed

/-!
# Radix conversions: `mp_read_radix` and `mp_to_radix`

`mp_read_radix(a, str, radix)` (`vendor/libtommath/bn_mp_read_radix.c`) and
`mp_to_radix(a, str, maxlen, written, radix)` (`bn_mp_to_radix.c`), with the
alphabet `mp_s_rmap` and its reverse map `mp_s_rmap_reverse` of
`bn_mp_radix_smap.c` (radix 2..64).

## The tables as the image holds them

* `rmap`: the 64 byte codes of
  `"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz+/"`
  (`.rodata` at `0x80017818`, pointed to by `mp_s_rmap` at `0x80018808`).
* `rmapRev`: the 88 bytes of `mp_s_rmap_reverse` (`0x80017cc0`;
  `mp_s_rmap_reverse_sz = 88` at `0x80018800`), indexed by `ch - '('`.
* `rmapRevPast = 44`: the byte at `0x80017d18`, just past the table. The C
  tests `if (mp_s_rmap_reverse_sz < pos) break;`, so `pos = 88` (the byte
  `0x80`) is **not** rejected and reads one byte past the table (an
  off-by-one in libtommath). In this image that byte is `0x2c = 44`, so for
  `radix ≥ 45` the byte `0x80` is read as the digit 44. The model follows the
  image (`revAt`).

## `mp_read_radix`

`char` is unsigned on RV64 (`lbu`). Per character `c` (`charVal`):
`ch = toUpper c` when `radix ≤ 36` (case folding), else `c`;
`pos = (unsigned)(ch - '(')` (`posOf`, wrapping mod `2^32`); stop if
`88 < pos`; `y = rmap_reverse[pos]`; stop if `y = 0xff` or `y ≥ radix`;
otherwise `a = a * radix` (`mp_mul_d`), `a = a + y` (`mp_add_d`)
(`readLoop`). A leading `'-'` is skipped first (`readSign`). After the loop,
the stopping character must be NUL, `'\r'` or `'\n'` (`readEndOk`),
otherwise `a = 0` and `MP_VAL`. The sign is set only when `a ≠ 0`.
A radix outside `2..64` gives `MP_VAL` with `a = 0`.

## `mp_to_radix`

`maxlen < 2` gives `MP_BUF`; a radix outside `2..64` gives `MP_VAL`
(nothing written in either case). Zero writes `"0\0"`, `written = 2`.
Otherwise: a `'-'` if negative (and `maxlen` decreases by one), then the
digits least significant first by repeated `mp_div_d(t, radix)`
(`digitsLE`), each as `rmap[d]`, then `s_mp_reverse` of the digit bytes,
then NUL; `written` = the bytes written including NUL. Before each digit
`--maxlen < 1` is tested: with `n` digits and `m'` the remaining `maxlen`
(after the `'-'`), the call succeeds iff `n < m'`; otherwise it returns
`MP_BUF` after writing `m' - 1` digits, unreversed and unterminated, and
`written` is not stored (`toRadixOut`, `toRadixRet`).

The callee calls (`mp_mul_d`, `mp_add_d`, `mp_div_d`, `mp_init_copy`) are
taken to succeed (D5: enough `alloc`, no allocation failure), so `MP_MEM`
does not appear.
-/

namespace Tom

namespace Radix

/-! ## Constants and tables -/

/-- `MP_BUF`. -/
def mpBuf : Int := -5

/-- `mp_s_rmap`: the alphabet, as byte codes. -/
@[irreducible] def rmap : List Nat :=
  [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78,
   79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106,
   107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 43, 47]

/-- `mp_s_rmap_reverse` (88 bytes, indexed by `ch - '('`). -/
@[irreducible] def rmapRev : List Nat :=
  [255, 255, 255, 62, 255, 255, 255, 63, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 255, 255, 255, 255, 255,
   255, 255, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
   32, 33, 34, 35, 255, 255, 255, 255, 255, 255, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
   49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 255, 255, 255, 255, 255]

/-- `mp_s_rmap_reverse_sz`. -/
def rmapRevSz : Nat := 88

/-- The byte the image holds just past `mp_s_rmap_reverse` (`0x80017d18`). -/
def rmapRevPast : Nat := 44

theorem rmap_length : rmap.length = 64 := by decide +kernel
theorem rmapRev_length : rmapRev.length = rmapRevSz := by decide +kernel

/-- `mp_s_rmap[d]`. -/
@[irreducible] def rmapAt (d : Nat) : Nat := rmap.getD d 0

/-- `mp_s_rmap_reverse[pos]` for `pos ≤ 88` as the image reads it (index 88 is
the byte past the table). -/
@[irreducible] def revAt (pos : Nat) : Nat := (rmapRev ++ [rmapRevPast]).getD pos 255

/-! ## `mp_read_radix`: the per-character step -/

/-- `MP_TOUPPER` on a byte. -/
@[irreducible] def toUpper (c : Nat) : Nat := if 97 ≤ c ∧ c ≤ 122 then c - 32 else c

/-- `pos = (unsigned)(ch - '(')`. -/
@[irreducible] def posOf (ch : Nat) : Nat := (ch + 2 ^ 32 - 40) % 2 ^ 32

/-- `ch = (radix <= 36) ? MP_TOUPPER(c) : c`. -/
@[irreducible] def foldCh (r c : Nat) : Nat := if r ≤ 36 then toUpper c else c

/-- The value of character `c` in radix `r`, or `none` where the loop stops. -/
def charVal (r c : Nat) : Option Nat :=
  if rmapRevSz < posOf (foldCh r c) then none
  else if revAt (posOf (foldCh r c)) = 255 ∨ r ≤ revAt (posOf (foldCh r c)) then none
  else some (revAt (posOf (foldCh r c)))

/-- The digit loop: per character, `a = a * radix + y` until NUL (`[]`) or a
character `charVal` rejects. Returns the value and the characters from the
stopping one on. -/
def readLoop (r : Nat) : List Nat → Nat → Nat × List Nat
  | [], acc => (acc, [])
  | c :: cs, acc => (charVal r c).elim (acc, c :: cs) (fun y => readLoop r cs (acc * r + y))

theorem readLoop_nil (r acc : Nat) : readLoop r [] acc = (acc, []) := by rw [readLoop]

/-- A digit character: multiply by the radix (`mp_mul_d`), add the digit (`mp_add_d`), go on. -/
theorem readLoop_some {r c y : Nat} (cs : List Nat) (acc : Nat) (h : charVal r c = some y) :
    readLoop r (c :: cs) acc = readLoop r cs (acc * r + y) := by
  rw [readLoop, h]; rfl

/-- A character the map rejects: stop there. -/
theorem readLoop_none {r c : Nat} (cs : List Nat) (acc : Nat) (h : charVal r c = none) :
    readLoop r (c :: cs) acc = (acc, c :: cs) := by
  rw [readLoop, h]; rfl

/-- The leading `'-'`: the sign to set and the rest of the string. -/
def readSign : List Nat → Nat × List Nat
  | 45 :: t => (Layout.mpNeg, t)
  | s => (Layout.mpZpos, s)

/-- The loop stopped at NUL, `'\r'` or `'\n'`. -/
def readEndOk : List Nat → Bool
  | [] => true
  | c :: _ => c == 13 || c == 10

/-- The radix is in `2..64`. -/
def radixOk (radix : Int) : Prop := 2 ≤ radix ∧ radix ≤ 64

instance (radix : Int) : Decidable (radixOk radix) := inferInstanceAs (Decidable (_ ∧ _))

/-- The return code of `mp_read_radix(a, s, radix)`. -/
def readRet (radix : Int) (s : List Nat) : Int :=
  if radixOk radix then
    (if readEndOk (readLoop radix.toNat (readSign s).2 0).2 then Layout.mpOkay else Layout.mpVal)
  else Layout.mpVal

/-- The magnitude `mp_read_radix` leaves. -/
def readMag (radix : Int) (s : List Nat) : Nat :=
  if radixOk radix ∧ readEndOk (readLoop radix.toNat (readSign s).2 0).2 = true then
    (readLoop radix.toNat (readSign s).2 0).1
  else 0

/-- The value `mp_read_radix` leaves. -/
def readVal (radix : Int) (s : List Nat) : Int :=
  if (readSign s).1 = Layout.mpNeg then -(readMag radix s : Int) else readMag radix s

end Radix

open Radix

/-- What `mp_read_radix(a, str, radix)` leaves, where `s` is the bytes of
`str` before its first NUL (all nonzero): `a` valid with the magnitude of the
loop model, the sign of the leading `'-'` when nonzero, and the return code. -/
structure ReadRadixPost (radix : Int) (s : List Nat) (a' : MpInt) (ret : Int) : Prop where
  code : ret = readRet radix s
  valid : a'.Valid
  mag : a'.mag = readMag radix s
  sign : a'.sign = if a'.mag = 0 then Layout.mpZpos else (readSign s).1

theorem ReadRadixPost.spec {radix : Int} {s : List Nat} {a' : MpInt} {ret : Int}
    (h : ReadRadixPost radix s a' ret) : a'.Valid ∧ a'.val = readVal radix s ∧ ret = readRet radix s := by
  refine ⟨h.valid, ?_, h.code⟩
  unfold MpInt.val readVal
  rw [h.sign, ← h.mag]
  by_cases hz : a'.mag = 0
  · simp only [hz, if_true, Layout.mpZpos, Layout.mpNeg]; split <;> simp
  · simp only [hz, if_false]

/-! ## Digit strings: values -/

namespace Radix

/-- The value of a digit list, most significant first (what the read loop
accumulates). -/
def evalMSB (r : Nat) (acc : Nat) (ds : List Nat) : Nat := ds.foldl (fun a d => a * r + d) acc

/-- The value of a digit list, least significant first. -/
def natLE (r : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + r * natLE r ds

theorem evalMSB_cons (r acc d : Nat) (ds : List Nat) :
    evalMSB r acc (d :: ds) = evalMSB r (acc * r + d) ds := rfl

theorem evalMSB_append_single (r acc d : Nat) (ds : List Nat) :
    evalMSB r acc (ds ++ [d]) = evalMSB r acc ds * r + d := by
  simp [evalMSB, List.foldl_append]

/-- Reading the reverse of a least-significant-first list. -/
theorem evalMSB_reverse (r : Nat) : ∀ (ds : List Nat) (acc : Nat),
    evalMSB r acc ds.reverse = acc * r ^ ds.length + natLE r ds
  | [], acc => by simp [evalMSB, natLE]
  | d :: ds, acc => by
    rw [List.reverse_cons, evalMSB_append_single, evalMSB_reverse r ds acc]
    simp only [natLE, List.length_cons, Nat.pow_succ]
    grind

/-! ## `mp_read_radix`: the loop on valid digits -/

/-- The loop consumes valid characters, accumulating their values. -/
theorem readLoop_valid (r : Nat) :
    ∀ (ds : List Nat) (rest : List Nat) (acc : Nat), (∀ d ∈ ds, charVal r (rmapAt d) = some d) →
      readLoop r (ds.map rmapAt ++ rest) acc = readLoop r rest (evalMSB r acc ds)
  | [], rest, acc, _ => by rw [List.map_nil, List.nil_append]; rfl
  | d :: ds, rest, acc, h => by
    have hd := h d (List.mem_cons_self ..)
    rw [List.map_cons, List.cons_append, readLoop_some _ _ hd]
    exact readLoop_valid r ds rest _ (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- The table facts behind the round trip for one digit, as a `Bool`. -/
def rmapFactsB (d : Nat) : Bool :=
  decide (40 ≤ rmapAt d) && decide (rmapAt d ≤ 128) && (revAt (rmapAt d - 40) == d) &&
    (decide (36 ≤ d) || toUpper (rmapAt d) == rmapAt d) && (rmapAt d != 45)

theorem rmapFacts_check : (List.range 64).all rmapFactsB = true := by decide +kernel

/-- The table facts behind the round trip, checked digit by digit: every
character of `mp_s_rmap` lies in `'('..0x80`, maps back to its digit, is kept
by the case folding when the digit is below 36, and is not `'-'`. -/
theorem rmap_facts (d : Nat) (hd : d < 64) :
    40 ≤ rmapAt d ∧ rmapAt d ≤ 128 ∧ revAt (rmapAt d - 40) = d ∧
      (d < 36 → toUpper (rmapAt d) = rmapAt d) ∧ rmapAt d ≠ 45 := by
  have h := List.all_eq_true.1 rmapFacts_check d (List.mem_range.2 hd)
  simp only [rmapFactsB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, fun h36 => h4.resolve_left (by omega), h5⟩

theorem posOf_eq {ch : Nat} (h1 : 40 ≤ ch) (h2 : ch < 2 ^ 32) : posOf ch = ch - 40 := by
  unfold posOf; omega

/-- Every digit's character reads back as that digit. -/
theorem charVal_rmapAt {r d : Nat} (hr : r ≤ 64) (hd : d < r) : charVal r (rmapAt d) = some d := by
  obtain ⟨h1, h2, h3, h4, -⟩ := rmap_facts d (by omega)
  have hch : foldCh r (rmapAt d) = rmapAt d := by
    unfold foldCh
    split
    · exact h4 (by omega)
    · rfl
  simp only [charVal, hch, posOf_eq h1 (by omega), h3]
  rw [if_neg (show ¬ rmapRevSz < rmapAt d - 40 by unfold rmapRevSz; omega), if_neg (by omega)]

/-- **Reading a digit string**: an optional `'-'` and the characters of digits
below the radix give `±Σ`, with `MP_OKAY`. -/
theorem read_digits {radix : Int} (hr : radixOk radix) (neg : Bool) (ds : List Nat)
    (hds : ∀ d ∈ ds, d < radix.toNat) :
    readRet radix ((if neg then [45] else []) ++ ds.map rmapAt) = Layout.mpOkay ∧
      readMag radix ((if neg then [45] else []) ++ ds.map rmapAt) = evalMSB radix.toNat 0 ds ∧
      readVal radix ((if neg then [45] else []) ++ ds.map rmapAt) =
        (if neg then -(evalMSB radix.toNat 0 ds : Int) else evalMSB radix.toNat 0 ds) := by
  have hv : ∀ d ∈ ds, charVal radix.toNat (rmapAt d) = some d :=
    fun d hd => charVal_rmapAt (by unfold radixOk at hr; omega) (hds d hd)
  have hsign : readSign ((if neg then [45] else []) ++ ds.map rmapAt) =
      (if neg then Layout.mpNeg else Layout.mpZpos, ds.map rmapAt) := by
    cases neg
    · cases ds with
      | nil => rfl
      | cons d ds =>
        obtain ⟨-, -, -, -, this⟩ :=
          rmap_facts d (by have := hds d (List.mem_cons_self ..); unfold radixOk at hr; omega)
        simp only [Bool.false_eq_true, if_false, List.nil_append, List.map_cons]
        unfold readSign
        split
        · rename_i t heq; simp at heq; omega
        · rfl
    · rfl
  have hloop := readLoop_valid radix.toNat ds [] 0 hv
  rw [List.append_nil] at hloop
  have hend : readEndOk (readLoop radix.toNat (readSign ((if neg then [45] else []) ++ ds.map rmapAt)).2 0).2
      = true := by rw [hsign, hloop, readLoop_nil]; rfl
  have hmag : readMag radix ((if neg then [45] else []) ++ ds.map rmapAt) = evalMSB radix.toNat 0 ds := by
    unfold readMag; rw [if_pos ⟨hr, hend⟩, hsign, hloop, readLoop_nil]
  refine ⟨by unfold readRet; rw [if_pos hr, if_pos hend], hmag, ?_⟩
  unfold readVal; rw [hmag, hsign]
  cases neg <;> simp [Layout.mpZpos, Layout.mpNeg]

/-! ## `mp_to_radix`: digits by repeated division -/

/-- The digits `mp_div_d` produces, least significant first: `t % r`, then
the digits of `t / r`, until `t = 0`. -/
def digitsLE (r n : Nat) : List Nat :=
  if h : 2 ≤ r ∧ 0 < n then n % r :: digitsLE r (n / r) else []
termination_by n
decreasing_by exact Nat.div_lt_self h.2 (by omega)

/-- One iteration of the C loop (`t ≠ 0`): the next digit is `t % r`. -/
theorem digitsLE_step {r t : Nat} (hr : 2 ≤ r) (ht : 0 < t) :
    digitsLE r t = t % r :: digitsLE r (t / r) := by
  rw [digitsLE, dif_pos ⟨hr, ht⟩]

@[simp] theorem digitsLE_zero (r : Nat) : digitsLE r 0 = [] := by
  rw [digitsLE, dif_neg (by omega)]

/-- The C loop's invariant: the digits emitted so far followed by the digits
of the current `t` are the digits of `n`. It holds initially (`ds = []`,
`t = n`), is kept by an iteration (`digitsLE_step`), and at `t = 0` gives
`ds = digitsLE r n`. -/
def LoopInv (r n t : Nat) (ds : List Nat) : Prop := ds ++ digitsLE r t = digitsLE r n

theorem LoopInv.init (r n : Nat) : LoopInv r n n [] := rfl

theorem LoopInv.step {r n t : Nat} {ds : List Nat} (hr : 2 ≤ r) (ht : 0 < t) (h : LoopInv r n t ds) :
    LoopInv r n (t / r) (ds ++ [t % r]) := by
  unfold LoopInv at *; rw [← h, digitsLE_step hr ht]; simp

theorem LoopInv.done {r n : Nat} {ds : List Nat} (h : LoopInv r n 0 ds) : ds = digitsLE r n := by
  unfold LoopInv at h; simpa using h

theorem natLE_digitsLE {r : Nat} (hr : 2 ≤ r) : ∀ n, natLE r (digitsLE r n) = n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [natLE]
    · rw [digitsLE_step hr hn, natLE, ih (n / r) (Nat.div_lt_self hn (by omega))]
      exact Nat.mod_add_div n r

theorem digitsLE_lt {r : Nat} (hr : 2 ≤ r) : ∀ n, ∀ d ∈ digitsLE r n, d < r := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [digitsLE_step hr hn]
      intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact Nat.mod_lt _ (by omega)
      · exact ih (n / r) (Nat.div_lt_self hn (by omega)) d hd

/-- The top digit (last in the list) is nonzero: no leading zeros. -/
theorem digitsLE_getLast_ne_zero {r : Nat} (hr : 2 ≤ r) :
    ∀ n (h : digitsLE r n ≠ []), (digitsLE r n).getLast h ≠ 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at h
    · have hs := digitsLE_step hr hn
      by_cases hq : n / r = 0
      · have e : digitsLE r n = [n % r] := by rw [hs, hq, digitsLE_zero]
        simp only [e, List.getLast_singleton]
        have := Nat.mod_add_div n r
        rw [hq, Nat.mul_zero, Nat.add_zero] at this
        omega
      · have hne : digitsLE r (n / r) ≠ [] := by
          rw [digitsLE_step hr (Nat.pos_of_ne_zero hq)]; simp
        have := ih (n / r) (Nat.div_lt_self hn (by omega)) hne
        simp only [hs]
        rwa [List.getLast_cons hne]

theorem digitsLE_ne_nil {r n : Nat} (hr : 2 ≤ r) (hn : 0 < n) : digitsLE r n ≠ [] := by
  rw [digitsLE_step hr hn]; simp

/-- **Uniqueness**: a least-significant-first digit list below the radix, with
nonzero top digit, is the `digitsLE` of its value (the standard base-`r`
representation). -/
theorem digitsLE_unique {r : Nat} (hr : 2 ≤ r) :
    ∀ (ds : List Nat), (∀ d ∈ ds, d < r) → (∀ h : ds ≠ [], ds.getLast h ≠ 0) →
      digitsLE r (natLE r ds) = ds
  | [], _, _ => by simp [natLE]
  | d :: ds, hlt, htop => by
    have hd := hlt d (List.mem_cons_self ..)
    have ih := digitsLE_unique hr ds (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
      (fun h => by have := htop (List.cons_ne_nil _ _); rwa [List.getLast_cons h] at this)
    have hpos : 0 < natLE r (d :: ds) := by
      cases ds with
      | nil =>
        have := htop (List.cons_ne_nil _ _)
        simp only [List.getLast_singleton] at this
        simp only [natLE]; omega
      | cons e es =>
        have hne : natLE r (e :: es) ≠ 0 := by
          intro h0
          have := ih
          rw [h0, digitsLE_zero] at this
          exact List.cons_ne_nil _ _ this.symm
        simp only [natLE] at hne ⊢
        have : 0 < r * (e + r * natLE r es) := Nat.mul_pos (by omega) (by omega)
        omega
    rw [digitsLE_step hr hpos]
    simp only [natLE]
    have hm : (d + r * natLE r ds) % r = d := by
      rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hd
    have hq : (d + r * natLE r ds) / r = natLE r ds := by
      rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hd, Nat.zero_add]
    rw [hm, hq, ih]

/-- The number of digits is at most `k` when `n < r ^ k` (buffer sizing). -/
theorem length_digitsLE_le {r : Nat} (hr : 2 ≤ r) : ∀ k n, n < r ^ k → (digitsLE r n).length ≤ k
  | 0, n, h => by
    have : n = 0 := by simp at h; omega
    subst this; simp
  | k + 1, n, h => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [digitsLE_step hr hn, List.length_cons]
      have : n / r < r ^ k := by
        apply Nat.div_lt_of_lt_mul; rw [Nat.pow_succ, Nat.mul_comm] at h; exact h
      have := length_digitsLE_le hr k (n / r) this
      omega

/-- With `k` digits, `n < r ^ k`. -/
theorem lt_pow_length_digitsLE {r : Nat} (hr : 2 ≤ r) (n : Nat) : n < r ^ (digitsLE r n).length := by
  have h := natLE_digitsLE hr n
  have hlt : ∀ (ds : List Nat), (∀ d ∈ ds, d < r) → natLE r ds < r ^ ds.length := by
    intro ds
    induction ds with
    | nil => intro _; simp [natLE]
    | cons d ds ih =>
      intro hd
      have h1 := hd d (List.mem_cons_self ..)
      have h2 := ih (fun x hx => hd x (List.mem_cons_of_mem _ hx))
      simp only [natLE, List.length_cons, Nat.pow_succ]
      have : r * natLE r ds + r ≤ r * r ^ ds.length := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h2
      rw [Nat.mul_comm (r ^ ds.length)]; omega
  have := hlt _ (digitsLE_lt hr n)
  rwa [h] at this

end Radix

/-! ## `mp_to_radix`: the output -/

namespace Radix

/-- The most-significant-first digits `mp_to_radix` prints for `a`: `[0]` for
zero, else the reversed `digitsLE` of `|a|` (after `s_mp_reverse`). -/
def msbDigits (a : MpInt) (r : Nat) : List Nat :=
  if a.used = 0 then [0] else (digitsLE r a.mag).reverse

/-- The `'-'` prefix. -/
def signPrefix (a : MpInt) : List Nat :=
  if a.used = 0 then [] else if a.sign = Layout.mpNeg then [45] else []

/-- The string a successful `mp_to_radix` writes, NUL included. -/
def toRadixStr (a : MpInt) (r : Nat) : List Nat :=
  signPrefix a ++ (msbDigits a r).map rmapAt ++ [0]

/-- The digit count limit: `maxlen` after the `'-'`. -/
def roomAfterSign (a : MpInt) (maxlen : Nat) : Nat :=
  if a.sign = Layout.mpNeg then maxlen - 1 else maxlen

/-- The return code of `mp_to_radix(a, str, maxlen, written, radix)`. -/
def toRadixRet (a : MpInt) (maxlen : Nat) (radix : Int) : Int :=
  if maxlen < 2 then mpBuf
  else if ¬ radixOk radix then Layout.mpVal
  else if a.used = 0 then Layout.mpOkay
  else if (digitsLE radix.toNat a.mag).length < roomAfterSign a maxlen then Layout.mpOkay
  else mpBuf

/-- The bytes `mp_to_radix` writes from `str[0]` on: none on an early error,
the string on success, and on `MP_BUF` from the loop the `'-'` and the first
`m' - 1` digit characters, least significant first, unterminated. -/
def toRadixOut (a : MpInt) (maxlen : Nat) (radix : Int) : List Nat :=
  if maxlen < 2 ∨ ¬ radixOk radix then []
  else if a.used = 0 then [48, 0]
  else if (digitsLE radix.toNat a.mag).length < roomAfterSign a maxlen then toRadixStr a radix.toNat
  else signPrefix a ++ ((digitsLE radix.toNat a.mag).take (roomAfterSign a maxlen - 1)).map rmapAt

end Radix

/-- What `mp_to_radix(a, str, maxlen, written, radix)` leaves: `buf`/`buf'` are
the bytes at `str + i` before and after, `w`/`w'` the `size_t` at `written`
before and after (`hasW`: `written ≠ NULL`). Bytes past `toRadixOut` are
unchanged; `written` is stored only on success. -/
structure ToRadixPost (a : MpInt) (maxlen : Nat) (radix : Int) (hasW : Bool)
    (buf buf' : Nat → Nat) (w w' : Nat) (ret : Int) : Prop where
  code : ret = toRadixRet a maxlen radix
  bytes : ∀ i, buf' i = (toRadixOut a maxlen radix).getD i (buf i)
  written : w' = if hasW = true ∧ ret = Layout.mpOkay then (toRadixOut a maxlen radix).length else w

namespace Radix

theorem toRadixStr_zero {a : MpInt} (h : a.used = 0) (r : Nat) : toRadixStr a r = [48, 0] := by
  simp [toRadixStr, signPrefix, msbDigits, h, rmapAt, rmap]

/-- The string length (the C's `written`): sign, digits, NUL. -/
theorem length_toRadixStr {a : MpInt} (hu : a.used ≠ 0) (r : Nat) :
    (toRadixStr a r).length =
      (if a.sign = Layout.mpNeg then 1 else 0) + (digitsLE r a.mag).length + 1 := by
  simp only [toRadixStr, signPrefix, msbDigits, hu, if_false, List.length_append, List.length_map,
    List.length_reverse, List.length_cons, List.length_nil]
  split <;> simp

/-- `mp_to_radix` succeeds exactly when the string fits in `maxlen`. -/
theorem toRadixRet_ok_iff {a : MpInt} (ha : a.Valid) {maxlen : Nat} {radix : Int} (hr : radixOk radix)
    (hm : 2 ≤ maxlen) :
    toRadixRet a maxlen radix = Layout.mpOkay ↔ (toRadixStr a radix.toNat).length ≤ maxlen := by
  unfold toRadixRet
  rw [if_neg (by omega), if_neg (by simpa using hr)]
  by_cases hu : a.used = 0
  · rw [if_pos hu, toRadixStr_zero hu]; simp; omega
  · rw [if_neg hu, length_toRadixStr hu]
    unfold roomAfterSign
    split
    · split <;> simp_all [mpBuf, Layout.mpOkay] <;> omega
    · split <;> simp_all [mpBuf, Layout.mpOkay] <;> omega

end Radix

/-- **`mp_to_radix`, success**: when the string fits, the C writes
`toRadixStr a radix` (sign, digits most significant first, NUL), leaves the
bytes after it, and stores its length in `written`. -/
theorem ToRadixPost.spec_ok {a : MpInt} {maxlen : Nat} {radix : Int} {hasW : Bool}
    {buf buf' : Nat → Nat} {w w' : Nat} {ret : Int} (ha : a.Valid) (hr : radixOk radix)
    (hfit : (toRadixStr a radix.toNat).length ≤ maxlen) (hm : 2 ≤ maxlen)
    (h : ToRadixPost a maxlen radix hasW buf buf' w w' ret) :
    ret = Layout.mpOkay ∧
      (∀ i, buf' i = (toRadixStr a radix.toNat).getD i (buf i)) ∧
      w' = (if hasW = true then (toRadixStr a radix.toNat).length else w) := by
  have hok : ret = Layout.mpOkay := by rw [h.code]; exact (toRadixRet_ok_iff ha hr hm).2 hfit
  have hout : toRadixOut a maxlen radix = toRadixStr a radix.toNat := by
    have hret := (toRadixRet_ok_iff ha hr hm).2 hfit
    unfold toRadixRet at hret
    unfold toRadixOut
    rw [if_neg (fun h => h.elim (fun h => by omega) (fun h => h hr))]
    by_cases hu : a.used = 0
    · rw [if_pos hu, toRadixStr_zero hu]
    · rw [if_neg hu]
      rw [if_neg (by omega), if_neg (by simpa using hr), if_neg hu] at hret
      split
      · rfl
      · rename_i hlt; rw [if_neg hlt] at hret; simp [mpBuf, Layout.mpOkay] at hret
  refine ⟨hok, fun i => by rw [h.bytes, hout], ?_⟩
  rw [h.written, hok, hout]
  cases hasW <;> simp

/-- **`mp_to_radix`, errors**: `maxlen < 2` gives `MP_BUF` and writes nothing;
a bad radix gives `MP_VAL` and writes nothing; a string longer than `maxlen`
gives `MP_BUF`. `written` is unchanged in each case. -/
theorem ToRadixPost.spec_err {a : MpInt} {maxlen : Nat} {radix : Int} {hasW : Bool}
    {buf buf' : Nat → Nat} {w w' : Nat} {ret : Int} (ha : a.Valid)
    (h : ToRadixPost a maxlen radix hasW buf buf' w w' ret) :
    (maxlen < 2 → ret = mpBuf ∧ buf' = buf ∧ w' = w) ∧
      (2 ≤ maxlen → ¬ radixOk radix → ret = Layout.mpVal ∧ buf' = buf ∧ w' = w) ∧
      (2 ≤ maxlen → radixOk radix → maxlen < (toRadixStr a radix.toNat).length → ret = mpBuf ∧ w' = w) := by
  refine ⟨fun hm => ?_, fun hm hr => ?_, fun hm hr hlong => ?_⟩
  · have hret : ret = mpBuf := by rw [h.code]; unfold toRadixRet; rw [if_pos hm]
    have hout : toRadixOut a maxlen radix = [] := by unfold toRadixOut; rw [if_pos (Or.inl hm)]
    refine ⟨hret, funext fun i => by rw [h.bytes, hout]; rfl, ?_⟩
    rw [h.written, hret]; simp [mpBuf, Layout.mpOkay]
  · have hret : ret = Layout.mpVal := by
      rw [h.code]; unfold toRadixRet; rw [if_neg (by omega), if_pos hr]
    have hout : toRadixOut a maxlen radix = [] := by unfold toRadixOut; rw [if_pos (Or.inr hr)]
    refine ⟨hret, funext fun i => by rw [h.bytes, hout]; rfl, ?_⟩
    rw [h.written, hret]; simp [Layout.mpVal, Layout.mpOkay]
  · have hne : toRadixRet a maxlen radix ≠ Layout.mpOkay :=
      fun e => absurd ((toRadixRet_ok_iff ha hr hm).1 e) (by omega)
    have hret : ret = mpBuf := by
      rw [h.code]
      unfold toRadixRet at hne ⊢
      rw [if_neg (by omega), if_neg (by simpa using hr)] at hne ⊢
      by_cases hu : a.used = 0
      · rw [if_pos hu] at hne; exact absurd rfl hne
      · rw [if_neg hu] at hne ⊢
        split
        · rename_i hlt; rw [if_pos hlt] at hne; exact absurd rfl hne
        · rfl
    refine ⟨hret, ?_⟩
    rw [h.written, hret]; simp [mpBuf, Layout.mpOkay]

namespace Radix

/-- **The meaning of the string**: its digits are below the radix, have no
leading zero (or are the single `0`), and are the base-`r` digits of `|a|`. -/
theorem msbDigits_spec {a : MpInt} (ha : a.Valid) {r : Nat} (hr : 2 ≤ r) :
    evalMSB r 0 (msbDigits a r) = a.mag ∧ (∀ d ∈ msbDigits a r, d < r) ∧
      (msbDigits a r = [0] ∨ (msbDigits a r).head? ≠ some 0) ∧ msbDigits a r ≠ [] := by
  unfold msbDigits
  by_cases hu : a.used = 0
  · simp only [hu, if_true]
    refine ⟨by simp [evalMSB, MpInt.mag_used_zero hu], by simp; omega, Or.inl (by simp), by simp⟩
  · simp only [hu, if_false]
    have hpos : 0 < a.mag := by
      have := MpInt.mag_ge ha (by omega)
      have : 0 < radix ^ (a.used - 1) := Nat.pow_pos radix_pos
      omega
    refine ⟨?_, fun d hd => digitsLE_lt hr _ d (List.mem_reverse.1 hd), Or.inr ?_, ?_⟩
    · rw [evalMSB_reverse, Nat.zero_mul, Nat.zero_add, natLE_digitsLE hr]
    · have hne := digitsLE_ne_nil hr hpos
      have htop := digitsLE_getLast_ne_zero hr a.mag hne
      rw [List.head?_reverse, List.getLast?_eq_some_getLast hne]
      simpa using htop
    · simpa using digitsLE_ne_nil hr hpos

/-- **Round trip**: reading back the string `mp_to_radix` writes (without its
NUL) gives `MP_OKAY` and the value `a`. -/
theorem read_toRadixStr {a : MpInt} (ha : a.Valid) {radix : Int} (hr : radixOk radix) :
    readRet radix (toRadixStr a radix.toNat).dropLast = Layout.mpOkay ∧
      readVal radix (toRadixStr a radix.toNat).dropLast = a.val := by
  have hr2 : 2 ≤ radix.toNat := by unfold radixOk at hr; omega
  have hstr : (toRadixStr a radix.toNat).dropLast =
      (if a.used ≠ 0 ∧ a.sign = Layout.mpNeg then [45] else []) ++ (msbDigits a radix.toNat).map rmapAt := by
    unfold toRadixStr signPrefix
    rw [List.dropLast_concat]
    by_cases hu : a.used = 0 <;> simp [hu]
  obtain ⟨hev, hlt, -, -⟩ := msbDigits_spec ha hr2
  have hneg := read_digits hr (decide (a.used ≠ 0 ∧ a.sign = Layout.mpNeg)) (msbDigits a radix.toNat) hlt
  have e : (if decide (a.used ≠ 0 ∧ a.sign = Layout.mpNeg) = true then [45] else []) =
      (if a.used ≠ 0 ∧ a.sign = Layout.mpNeg then [45] else ([] : List Nat)) := by
    simp only [decide_eq_true_eq]
  rw [e, ← hstr, hev] at hneg
  refine ⟨hneg.1, ?_⟩
  rw [hneg.2.2]
  unfold MpInt.val
  by_cases hu : a.used = 0
  · simp [hu, MpInt.mag_used_zero hu, ha.zero_pos hu, Layout.mpZpos, Layout.mpNeg]
  · by_cases hs : a.sign = Layout.mpNeg <;> simp [hu, hs]

/-- The round trip through the two contracts. -/
theorem readRadix_of_toRadix {a a' : MpInt} (ha : a.Valid) {radix : Int} (hr : radixOk radix) {ret : Int}
    (h : ReadRadixPost radix (toRadixStr a radix.toNat).dropLast a' ret) :
    ret = Layout.mpOkay ∧ a'.Valid ∧ a'.val = a.val := by
  obtain ⟨hv, hval, hret⟩ := h.spec
  obtain ⟨h1, h2⟩ := read_toRadixStr ha hr
  exact ⟨hret.trans h1, hv, hval.trans h2⟩

/-! ## Bounds the machine proof needs -/

/-- A read digit is below the radix (so `mp_add_d`'s operand is a digit and
`y < 64`). -/
theorem charVal_lt {r c y : Nat} (h : charVal r c = some y) : y < r := by
  unfold charVal at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i h1; cases h; omega

/-- A read digit is below 64 whenever the radix is at most 64. -/
theorem charVal_lt64 {r c y : Nat} (hr : r ≤ 64) (h : charVal r c = some y) : y < 64 :=
  Nat.lt_of_lt_of_le (charVal_lt h) hr

/-- `pos ≤ 88` exactly for the bytes `'('..0x80` (so the read is in the image's
`.rodata`, one byte past the table at most). -/
theorem posOf_le_iff {ch : Nat} (hch : ch < 256) : posOf ch ≤ rmapRevSz ↔ 40 ≤ ch ∧ ch ≤ 128 := by
  unfold posOf rmapRevSz; omega

/-- The case folding keeps bytes in `0..255`. -/
theorem toUpper_lt {c : Nat} (hc : c < 256) : toUpper c < 256 := by
  unfold toUpper; split <;> omega

/-- The loop's value: below `(acc + 1) * r ^ len` (the size of `a` grows by at
most one radix power per character). -/
theorem readLoop_lt (r : Nat) (hr : 1 ≤ r) :
    ∀ (s : List Nat) (acc : Nat), (readLoop r s acc).1 < (acc + 1) * r ^ s.length
  | [], acc => by rw [readLoop_nil]; simp
  | c :: cs, acc => by
    cases hc : charVal r c with
    | none =>
      rw [readLoop_none _ _ hc]
      simp only [List.length_cons, Nat.pow_succ]
      have h1 : (acc + 1) * 1 ≤ (acc + 1) * (r ^ cs.length * r) :=
        Nat.mul_le_mul_left _ (Nat.mul_pos (Nat.pow_pos hr) hr)
      omega
    | some y =>
      rw [readLoop_some _ _ hc]
      have := readLoop_lt r hr cs (acc * r + y)
      have hy' := charVal_lt hc
      simp only [List.length_cons, Nat.pow_succ]
      have : (acc * r + y + 1) * r ^ cs.length ≤ (acc + 1) * (r ^ cs.length * r) := by
        have : acc * r + y + 1 ≤ (acc + 1) * r := by rw [Nat.add_mul]; omega
        calc (acc * r + y + 1) * r ^ cs.length ≤ ((acc + 1) * r) * r ^ cs.length :=
              Nat.mul_le_mul_right _ this
          _ = (acc + 1) * (r ^ cs.length * r) := by rw [Nat.mul_assoc, Nat.mul_comm r]
      omega

/-- The radix as an `mp_digit` operand of `mp_mul_d`/`mp_div_d`: below the
digit radix. -/
theorem radix_toNat_lt {radix : Int} (hr : radixOk radix) : radix.toNat < Tom.radix := by
  unfold radixOk at hr; simp only [Tom.radix, Layout.digitBits]; omega

/-- A printed digit indexes `mp_s_rmap` in range. -/
theorem digit_lt_rmap {a : MpInt} {r : Nat} (hr : 2 ≤ r) (hr64 : r ≤ 64) :
    ∀ d ∈ digitsLE r a.mag, d < rmap.length := fun d hd => by
  have := digitsLE_lt hr _ d hd; rw [rmap_length]; omega

end Radix

end Tom
