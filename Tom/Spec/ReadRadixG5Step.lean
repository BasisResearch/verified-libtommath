import Tom.Spec.Radix
import Tom.Spec.Canon
import Tom.Spec.Digit

/-!
# `mp_read_radix`'s loop: the model steps (case cost of H1)

`t = (readSign s).2` is the string after the sign (`sgnLen s` bytes of it); the loop head
holds `i` characters of `t` read into `a` (`LI`), the end (`FI`) the loop's value with a
stopping character `readEndOk` accepts. One lemma per step and per exit's `ReadRadixPost`.
-/

namespace Tom.ReadRadixG5

open MpInt Radix

/-- The sign's length: one byte for a leading `'-'`. -/
def sgnLen (s : List Nat) : Nat := if s.getD 0 0 = 45 then 1 else 0

theorem sgnLen_le (s : List Nat) : sgnLen s ≤ 1 := by unfold sgnLen; split <;> omega

theorem readSign_eq (s : List Nat) : readSign s = (sgnLen s, s.drop (sgnLen s)) := by
  unfold sgnLen
  match s with
  | [] => rfl
  | c :: t =>
    by_cases h : c = 45
    · subst h; rfl
    · simp only [List.getD_cons_zero, h, if_false, List.drop_zero]
      unfold readSign; split <;> simp_all <;> rfl

theorem getD_in {s : List Nat} {j : Nat} (hj : j < s.length) : s.getD j 0 = s[j] := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem getD_out {s : List Nat} {j : Nat} (hj : s.length ≤ j) : s.getD j 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, hj]

/-- A byte of the string: zero exactly past its end. -/
theorem getD_zero_iff {s : List Nat} (hs : ∀ c ∈ s, 0 < c ∧ c < 256) (j : Nat) :
    s.getD j 0 = 0 ↔ s.length ≤ j := by
  constructor
  · intro h; refine Nat.not_lt.1 fun hj => ?_
    have := (hs _ (List.getElem_mem hj)).1
    rw [getD_in hj] at h; omega
  · intro h; exact getD_out h

theorem getD_lt {s : List Nat} (hs : ∀ c ∈ s, 0 < c ∧ c < 256) (j : Nat) : s.getD j 0 < 256 := by
  by_cases hj : j < s.length
  · rw [getD_in hj]; exact (hs _ (List.getElem_mem hj)).2
  · rw [getD_out (by omega)]; decide

/-- At the loop head: `i` characters of `t` read into `a`. -/
structure LI (r : Nat) (t : List Nat) (al i : Nat) (a : MpInt) : Prop where
  va : a.Valid
  pos : a.sign = Layout.mpZpos
  alloc : a.alloc = al
  run : readLoop r t 0 = readLoop r (t.drop i) a.mag
  lt : a.mag < r ^ i

/-- At the end: the loop's value and its stopping character accepted. -/
structure FI (r : Nat) (t : List Nat) (al : Nat) (a : MpInt) : Prop where
  va : a.Valid
  pos : a.sign = Layout.mpZpos
  alloc : a.alloc = al
  val : (readLoop r t 0).1 = a.mag
  ok : readEndOk (readLoop r t 0).2 = true

theorem pow_le_64 {r : Nat} (hr : r ≤ 64) (i : Nat) : r ^ i ≤ 2 ^ (6 * i) := by
  rw [Nat.pow_mul]; exact Nat.pow_le_pow_left (by omega) i

/-- No `mp_grow`: a value below `2^(6k)`, `k ≤ |s|`, leaves a digit of room. -/
theorem room_of {x : MpInt} {k len al : Nat} (hx : x.Valid) (hlt : x.mag < 2 ^ (6 * k)) (hk : k ≤ len)
    (hroom : 6 * len ≤ Layout.digitBits * (al - 1)) (hal : 2 ≤ al) : x.used + 1 ≤ al := by
  by_cases hu : x.used = 0
  · omega
  have h1 := MpInt.mag_ge hx (by omega)
  have h2 : 2 ^ (28 * (x.used - 1)) < 2 ^ (6 * k) := by
    have : radix ^ (x.used - 1) = 2 ^ (28 * (x.used - 1)) := by rw [← Nat.pow_mul]; rfl
    omega
  have := (Nat.pow_lt_pow_iff_right (by decide)).1 h2
  simp only [Layout.digitBits] at hroom
  omega

theorem zero_valid {a z : MpInt} (hz : ZeroPost a z) (hs : z.Shape) : z.Valid :=
  { hs with top := fun h => absurd hz.used (by omega), sign_ok := Or.inl hz.sign, zero_pos := fun _ => hz.sign }

theorem zero_mag {a z : MpInt} (hz : ZeroPost a z) : z.mag = 0 := by unfold MpInt.mag; rw [hz.used]; rfl

/-- The loop's start: `a` zeroed. -/
theorem LI.start {r al : Nat} {t : List Nat} {a z : MpInt} (hz : ZeroPost a z) (hs : z.Shape) (hal : a.alloc = al) :
    LI r t al 0 z :=
  { va := zero_valid hz hs, pos := hz.sign, alloc := hz.alloc.trans hal
    run := by rw [zero_mag hz]; rfl, lt := by rw [zero_mag hz, Nat.pow_zero]; exact Nat.one_pos }

/-- `mp_mul_d(a, r, a)` keeps a digit of room (`|s| ≥ 1`). -/
theorem LI.room {r : Nat} {t : List Nat} {al i len : Nat} {a : MpInt} (h : LI r t al i a) (hr : r ≤ 64)
    (hi : i < len) (hroom : 6 * len ≤ Layout.digitBits * (al - 1)) : a.used + 1 ≤ al :=
  room_of h.va (Nat.lt_of_lt_of_le h.lt (pow_le_64 hr i)) (Nat.le_of_lt hi) hroom
    (by simp only [Layout.digitBits] at hroom; omega)

/-- After `mp_mul_d`: valid, nonnegative, `a * r`. -/
structure MI (r : Nat) (al i : Nat) (a a2 : MpInt) : Prop where
  va : a2.Valid
  pos : a2.sign = Layout.mpZpos
  alloc : a2.alloc = al
  mag : a2.mag = a.mag * r

theorem LI.mul {r : Nat} {t : List Nat} {al i len : Nat} {a a2 : MpInt} (h : LI r t al i a) (hr : r ≤ 64)
    (hi : i < len) (hroom : 6 * len ≤ Layout.digitBits * (al - 1)) (hal : al < 2 ^ 31)
    (hm : MulDPost a r a a2) : MI r al i a a2 := by
  have hro := h.room hr hi hroom
  obtain ⟨hv, hmag, -⟩ := hm.spec h.va (by unfold radix Layout.digitBits; omega) (by rw [h.alloc]; exact hro)
    (by rw [h.alloc]; exact hal)
  refine ⟨hv, ?_, by rw [hm.alloc, h.alloc], hmag⟩
  rw [hm.sign]; split
  · rfl
  · exact h.pos

theorem MI.room {r : Nat} {al i len : Nat} {a a2 : MpInt} {t : List Nat} (h : MI r al i a a2) (hl : LI r t al i a)
    (hr2 : 2 ≤ r) (hr : r ≤ 64) (hi : i + 1 ≤ len) (hroom : 6 * len ≤ Layout.digitBits * (al - 1)) :
    a2.used + 1 ≤ al := by
  have : a2.mag < r ^ (i + 1) := by
    rw [h.mag, Nat.pow_succ]; exact Nat.mul_lt_mul_of_pos_right hl.lt (by omega)
  exact room_of h.va (Nat.lt_of_lt_of_le this (pow_le_64 hr _)) hi hroom (by simp only [Layout.digitBits] at hroom; omega)

theorem drop_cons {t : List Nat} {i : Nat} (hi : i < t.length) : t.drop i = t.getD i 0 :: t.drop (i + 1) := by
  rw [getD_in hi]; exact List.drop_eq_getElem_cons hi

/-- A digit: `mp_mul_d`, `mp_add_d`, the next character. -/
theorem LI.step {r y : Nat} {t : List Nat} {al i : Nat} {a a2 a3 : MpInt} (h : LI r t al i a) (hi : i < t.length)
    (hc : charVal r (t.getD i 0) = some y) (hy : y < r) (hr : r ≤ 64) (hm : MI r al i a a2)
    (hroom : a2.used + 1 ≤ al) (hal : al < 2 ^ 31) (ha : AddDPost a2 y a2 a3) : LI r t al (i + 1) a3 := by
  have hd := ha.pos hm.pos
  obtain ⟨hv, hval⟩ := ha.spec hm.va (by unfold radix Layout.digitBits; omega) (by rw [hm.alloc]; exact hroom)
    (by rw [hm.alloc]; exact hal)
  have hs : a3.sign = Layout.mpZpos := by rw [hd.sign]; split <;> rfl
  have hmag : a3.mag = a2.mag + y := by
    have e1 : a3.val = a3.mag := by simp [MpInt.val, hs, Layout.mpZpos, Layout.mpNeg]
    have e2 : a2.val = a2.mag := by simp [MpInt.val, hm.pos, Layout.mpZpos, Layout.mpNeg]
    rw [e1, e2] at hval; omega
  refine ⟨hv, hs, by rw [hd.alloc, hm.alloc], ?_, ?_⟩
  · rw [h.run, drop_cons hi, readLoop_some _ _ hc, hmag, hm.mag]
  · rw [hmag, hm.mag, Nat.pow_succ]
    have := h.lt
    have : a.mag * r + r ≤ r ^ i * r := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ this
    omega

/-- The end of the string. -/
theorem LI.fin {r : Nat} {t : List Nat} {al i : Nat} {a : MpInt} (h : LI r t al i a) (hi : t.length ≤ i) :
    FI r t al a :=
  { va := h.va, pos := h.pos, alloc := h.alloc
    val := by rw [h.run, List.drop_eq_nil_of_le hi, readLoop_nil]
    ok := by rw [h.run, List.drop_eq_nil_of_le hi, readLoop_nil]; rfl }

/-- A stopping `'\r'` or `'\n'`. -/
theorem LI.stop {r : Nat} {t : List Nat} {al i : Nat} {a : MpInt} (h : LI r t al i a) (hi : i < t.length)
    (hc : charVal r (t.getD i 0) = none) (hok : t.getD i 0 = 10 ∨ t.getD i 0 = 13) : FI r t al a :=
  { va := h.va, pos := h.pos, alloc := h.alloc
    val := by rw [h.run, drop_cons hi, readLoop_none _ _ hc]
    ok := by
      rw [h.run, drop_cons hi, readLoop_none _ _ hc]
      simp only [readEndOk]; rcases hok with e | e <;> rw [e] <;> rfl }

/-- Any other stopping character. -/
theorem LI.bad {r : Nat} {t : List Nat} {al i : Nat} {a : MpInt} (h : LI r t al i a) (hi : i < t.length)
    (hc : charVal r (t.getD i 0) = none) (h10 : t.getD i 0 ≠ 10) (h13 : t.getD i 0 ≠ 13) :
    readEndOk (readLoop r t 0).2 = false := by
  rw [h.run, drop_cons hi, readLoop_none _ _ hc]; simp only [readEndOk]
  generalize t.getD i 0 = c at h10 h13; simp; omega

/-! ## The character map, branch by branch -/

theorem fold_hi {r c : Nat} (h : 36 < r) : foldCh r c = c := by unfold foldCh; rw [if_neg (by omega)]

theorem fold_lo {r c : Nat} (h : r ≤ 36) (hc : c < 97 ∨ 122 < c) : foldCh r c = c := by
  unfold foldCh toUpper; rw [if_pos h, if_neg (by omega)]

theorem fold_up {r c : Nat} (h : r ≤ 36) (h1 : 97 ≤ c) (h2 : c ≤ 122) : foldCh r c = c - 32 := by
  unfold foldCh toUpper; rw [if_pos h, if_pos ⟨h1, h2⟩]

theorem cv_oor {r c u : Nat} (hu : foldCh r c = u) (h : u < 40 ∨ 88 < u - 40) (hu2 : u < 2 ^ 32) :
    charVal r c = none := by
  unfold charVal; rw [hu, if_pos]
  unfold posOf rmapRevSz; omega

theorem cv_tab {r c u : Nat} (hu : foldCh r c = u) (h1 : 40 ≤ u) (h2 : u - 40 ≤ 88) (h3 : u < 2 ^ 32) :
    charVal r c = if revAt (u - 40) = 255 ∨ r ≤ revAt (u - 40) then none else some (revAt (u - 40)) := by
  unfold charVal; rw [hu, posOf_eq h1 h3, if_neg (by unfold rmapRevSz; omega)]

theorem cv_ff {r c u : Nat} (hu : foldCh r c = u) (h1 : 40 ≤ u) (h2 : u - 40 ≤ 88) (h3 : u < 2 ^ 32)
    (hy : revAt (u - 40) = 255) : charVal r c = none := by rw [cv_tab hu h1 h2 h3, if_pos (.inl hy)]

theorem cv_ge {r c u : Nat} (hu : foldCh r c = u) (h1 : 40 ≤ u) (h2 : u - 40 ≤ 88) (h3 : u < 2 ^ 32)
    (hy : r ≤ revAt (u - 40)) : charVal r c = none := by rw [cv_tab hu h1 h2 h3, if_pos (.inr hy)]

theorem cv_dig {r c u : Nat} (hu : foldCh r c = u) (h1 : 40 ≤ u) (h2 : u - 40 ≤ 88) (h3 : u < 2 ^ 32)
    (hy1 : revAt (u - 40) ≠ 255) (hy2 : revAt (u - 40) < r) : charVal r c = some (revAt (u - 40)) := by
  rw [cv_tab hu h1 h2 h3, if_neg (by omega)]

theorem revAt_lt (j : Nat) : revAt j < 256 := by
  unfold revAt
  by_cases hj : j < (rmapRev ++ [rmapRevPast]).length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    have : ∀ x ∈ rmapRev ++ [rmapRevPast], x < 256 := by unfold rmapRev rmapRevPast; decide
    exact this _ (List.getElem_mem hj)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide

/-! ## The exits (the radix a natural number below `2^31`) -/

theorem rok {r : Nat} (h : 2 ≤ r ∧ r ≤ 64) : radixOk (r : Int) := ⟨by omega, by omega⟩

theorem t_len (s : List Nat) : (readSign s).2.length = s.length - sgnLen s := by rw [readSign_eq]; simp

theorem t_getD (s : List Nat) (i : Nat) : (readSign s).2.getD i 0 = s.getD (sgnLen s + i) 0 := by
  rw [readSign_eq]; simp [List.getD_eq_getElem?_getD]

theorem readRet_bad {r : Nat} {s : List Nat} (hr : ¬ (2 ≤ r ∧ r ≤ 64)) : readRet (r : Int) s = -3 := by
  unfold readRet; rw [if_neg (fun h => hr ⟨by have := h.1; omega, by have := h.2; omega⟩)]; rfl

/-- `radix` out of range: `a` zeroed, `MP_VAL`. -/
theorem post_bad {r : Nat} {s : List Nat} {a z : MpInt} (hr : ¬ (2 ≤ r ∧ r ≤ 64)) (hz : ZeroPost a z)
    (hs : z.Shape) : ReadRadixPost (r : Int) s z (-3) :=
  { code := (readRet_bad hr).symm, valid := zero_valid hz hs
    mag := by
      rw [zero_mag hz]; unfold readMag
      rw [if_neg (fun h => hr ⟨by have := h.1.1; omega, by have := h.1.2; omega⟩)]
    sign := by rw [zero_mag hz, if_pos rfl]; exact hz.sign }

/-- An illegal character: `a` zeroed, `MP_VAL`. -/
theorem post_zr {r : Nat} {s : List Nat} {a z : MpInt} (hr : 2 ≤ r ∧ r ≤ 64)
    (hb : readEndOk (readLoop r (readSign s).2 0).2 = false)
    (hz : ZeroPost a z) (hs : z.Shape) : ReadRadixPost (r : Int) s z (-3) :=
  { code := by unfold readRet; rw [if_pos (rok hr), Int.toNat_natCast, hb]; rfl
    valid := zero_valid hz hs
    mag := by
      rw [zero_mag hz]; unfold readMag
      rw [if_neg (fun h => by rw [Int.toNat_natCast, hb] at h; exact absurd h.2 (by decide))]
    sign := by rw [zero_mag hz, if_pos rfl]; exact hz.sign }

theorem readRet_ok {r : Nat} {s : List Nat} {al : Nat} {a : MpInt} (hr : 2 ≤ r ∧ r ≤ 64)
    (h : FI r (readSign s).2 al a) : readRet (r : Int) s = 0 := by
  unfold readRet; rw [if_pos (rok hr), Int.toNat_natCast, if_pos h.ok]; rfl

/-- Done, `a->used ≠ 0`: the sign set. -/
theorem post_ok1 {r : Nat} {s : List Nat} {al : Nat} {a : MpInt} (hr : 2 ≤ r ∧ r ≤ 64)
    (h : FI r (readSign s).2 al a) (hu : a.used ≠ 0) (hng : sgnLen s < 2) :
    ReadRadixPost (r : Int) s { a with sign := sgnLen s } 0 :=
  { code := (readRet_ok hr h).symm
    valid := ⟨⟨h.va.len, h.va.used_le, h.va.alloc_lt, h.va.digit_lt, h.va.high_zero⟩, h.va.top,
      by unfold Layout.mpZpos Layout.mpNeg; simp only; omega, fun e => absurd e hu⟩
    mag := by show a.mag = _; unfold readMag; rw [if_pos ⟨rok hr, by rw [Int.toNat_natCast]; exact h.ok⟩,
      Int.toNat_natCast, h.val]
    sign := by
      have : a.mag ≠ 0 := by have := MpInt.mag_ge h.va (by omega); have := Nat.pow_pos (n := a.used - 1) radix_pos; omega
      show sgnLen s = if a.mag = 0 then _ else _; rw [if_neg this, readSign_eq] }

/-- Done, `a->used = 0`. -/
theorem post_ok0 {r : Nat} {s : List Nat} {al : Nat} {a : MpInt} (hr : 2 ≤ r ∧ r ≤ 64)
    (h : FI r (readSign s).2 al a) (hu : a.used = 0) : ReadRadixPost (r : Int) s a 0 :=
  { code := (readRet_ok hr h).symm, valid := h.va
    mag := by unfold readMag; rw [if_pos ⟨rok hr, by rw [Int.toNat_natCast]; exact h.ok⟩, Int.toNat_natCast, h.val]
    sign := by rw [h.pos]; split <;> first | rfl | (exfalso; unfold MpInt.mag at *; rw [hu] at *; simp_all [natUpTo]) }

end Tom.ReadRadixG5
