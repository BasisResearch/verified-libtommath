import Tom.Spec.Ledger
import Tom.Spec.Radix

/-!
# `mp_to_radix`: the model steps over the Ledger

`bn_mp_to_radix.c` at `0x80001f80`. After the early exits (`maxlen < 2`: `MP_BUF`; a radix
outside `2..64`: `MP_VAL`; `a = 0`: `"0\0"`), `mp_init_copy(&t, a)`, the `'-'` at `str[0]` and
`t.sign = MP_ZPOS` when negative, then the loop at `0x80002094`: stop with `MP_BUF` when
`--maxlen < 1` (the machine: `digs = maxlen' - 1`), else `mp_div_d(&t, radix, &t, &d)` in place
and `*str++ = mp_s_rmap[d]`, until `t = 0`; then `s_mp_reverse(_s, digs)` and the NUL.

The cut premise `LI` is a Ledger account (`Acct t 1 |a| (|a| / r^i)`: `xfer_copy`,
`xfer_setZpos`, `xfer_divD`) and a tape of the digit bytes (`Tape`: `out a r j`, the `j`-th
base-`r` digit of `|a|` through `mp_s_rmap`) after the sign prefix. The callee Posts are the
frozen contracts': `CopyPost a (zeroN (initPrec a.used)) t` (`Api/MpInitCopy.lean`),
`DivDQuot t r t t'` and `*d = |t| mod r` (`Api/MpDivD.lean`: `Q`, `rem`), and `RevPost`, the
reading of `Api/Reverse.lean`'s `Post` (`BytesAt M s l.reverse` and the frame) over the byte
function. Own: the digit list (`digitsLE_getD`) and the string's bytes (`getD_*`).
-/

namespace Tom.ToRadixStepL

open MpInt Radix Ledger
open Mont (upd)

/-! ## The string -/

/-- Digit `j` of `|a|` in base `r`, as `mp_s_rmap` prints it. -/
def out (a : MpInt) (r j : Nat) : Nat := rmapAt (a.mag / r ^ j % r)

/-- Where the digits start: after the `'-'`. -/
def pre (a : MpInt) : Nat := if a.sign = Layout.mpNeg then 1 else 0

/-- The bytes before the loop: the `'-'` stored when negative. -/
def buf1 (a : MpInt) (buf : Nat → Nat) : Nat → Nat := if a.sign = Layout.mpNeg then upd buf 0 45 else buf

theorem buf1_eq (a : MpInt) (buf : Nat → Nat) (j : Nat) : buf1 a buf j = if j < pre a then 45 else buf j := by
  unfold buf1 pre; split
  · unfold upd; split <;> split <;> first | rfl | omega
  · rfl

theorem digitsLE_getD {r : Nat} (hr : 2 ≤ r) : ∀ j n, (digitsLE r n).getD j 0 = n / r ^ j % r
  | j, n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [digitsLE_step hr hn]
      cases j with
      | zero => simp
      | succ j => simp only [List.getD_cons_succ]; rw [digitsLE_getD hr j (n / r), Nat.div_div_eq_div_mul,
          Nat.pow_succ, Nat.mul_comm]

theorem getD_sign {a : MpInt} (hu : a.used ≠ 0) (L : List Nat) (j d : Nat) :
    (signPrefix a ++ L).getD j d = if j < pre a then 45 else L.getD (j - pre a) d := by
  unfold signPrefix pre; rw [if_neg hu]
  split
  · cases j <;> simp
  · simp

theorem getD_map_take (ds : List Nat) (m k d : Nat) (hm : m ≤ ds.length) :
    ((ds.take m).map rmapAt).getD k d = if k < m then rmapAt (ds.getD k 0) else d := by
  split
  · simp [List.getD_eq_getElem?_getD, *, List.getElem?_eq_getElem (show k < ds.length by omega)]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl

theorem getD_rev_nul (ds : List Nat) (k d : Nat) :
    (ds.reverse.map rmapAt ++ [0]).getD k d =
      if k < ds.length then rmapAt (ds.getD (ds.length - 1 - k) 0) else if k = ds.length then 0 else d := by
  rw [List.getD_eq_getElem?_getD]
  split
  · rename_i hk
    rw [List.getElem?_append_left (by simpa using hk), List.getElem?_map, List.getElem?_reverse hk,
      List.getElem?_eq_getElem (show ds.length - 1 - k < ds.length by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show ds.length - 1 - k < ds.length by omega)]
  · rw [List.getElem?_append_right (by simp; omega)]
    split
    · rename_i e; simp [e]
    · rw [List.getElem?_eq_none (by simp; omega)]; rfl

/-- `s_mp_reverse(s, n)`'s Post (`Api/Reverse.lean`: `BytesAt M s l.reverse`, frame `[s, s + n)`)
over the byte function. -/
structure RevPost (s n : Nat) (f g : Nat → Nat) : Prop where
  bytes : ∀ j, j < n → g (s + j) = f (s + (n - 1 - j))
  frame : ∀ j, (j < s ∨ s + n ≤ j) → g j = f j

theorem RevPost.fin {s n : Nat} {f g : Nat → Nat} (h : RevPost s n f g) (j : Nat) :
    g j = if s ≤ j ∧ j < s + n then f (s + (n - 1 - (j - s))) else f j := by
  split
  · have := h.bytes (j - s) (by omega); rwa [show s + (j - s) = j by omega] at this
  · exact h.frame j (by omega)

/-! ## The run -/

variable {a t t' : MpInt} {maxlen : Nat} {radix : Int} {buf f g : Nat → Nat} {i n w : Nat} {hasW : Bool}

/-- The run's fixed facts past the early exits. -/
structure Env (a : MpInt) (maxlen : Nat) (radix : Int) : Prop where
  va : a.Valid
  nz : a.used ≠ 0
  ml : 2 ≤ maxlen
  rok : radixOk radix

theorem Env.r2 (e : Env a maxlen radix) : 2 ≤ radix.toNat := by have := e.rok; unfold radixOk at this; omega

/-- The loop head (`0x80002094`, `i` digits stored). -/
structure LI (a : MpInt) (maxlen r : Nat) (buf : Nat → Nat) (t : MpInt) (f : Nat → Nat) (i : Nat) : Prop where
  acct : Acct t 1 a.used ((a.mag / r ^ i : Nat) : Int) True
  nz : t.used ≠ 0
  tape : Tape (pre a) (out a r) (buf1 a buf) i f
  room : i + 1 ≤ roomAfterSign a maxlen

theorem initPrec_ok (e : Env a maxlen radix) : a.used ≤ initPrec a.used ∧ initPrec a.used < 2 ^ 31 ∧ 1 ≤ initPrec a.used := by
  have := e.va.used_le; have := e.va.alloc_lt; have := e.nz; unfold initPrec; rw [minPrec_eq]; omega

/-- `a ≥ 0`: no `'-'`. -/
theorem start_pos (e : Env a maxlen radix) (hc : CopyPost a (MpInt.zeroN (initPrec a.used)) t)
    (hs : t.sign ≠ Layout.mpNeg) : LI a maxlen radix.toNat buf t buf 0 := by
  have hsa : a.sign ≠ Layout.mpNeg := by rw [← hc.sign]; exact hs
  obtain ⟨p1, p2, p3⟩ := initPrec_ok e
  have h := xfer_copy e.va p1 p2 hc
  refine ⟨⟨h.valid, by have := h.room; omega, h.used, ?_, trivial⟩, by rw [hc.used]; exact e.nz, ?_, ?_⟩
  · rw [h.val, Nat.pow_zero, Nat.div_one]; unfold MpInt.val; rw [if_neg hsa]
  · rw [show buf1 a buf = buf by unfold buf1; rw [if_neg hsa]]; exact Tape.start _ _ _
  · have := e.ml; unfold roomAfterSign; rw [if_neg hsa]; omega

/-- `a < 0`: `*str++ = '-'`, `t.sign = MP_ZPOS`, `--maxlen`. -/
theorem start_neg (e : Env a maxlen radix) (hc : CopyPost a (MpInt.zeroN (initPrec a.used)) t)
    (hs : t.sign = Layout.mpNeg) : LI a maxlen radix.toNat buf (t.withSign Layout.mpZpos) (upd buf 0 45) 0 := by
  have hsa : a.sign = Layout.mpNeg := by rw [← hc.sign]; exact hs
  obtain ⟨p1, p2, p3⟩ := initPrec_ok e
  have h := xfer_setZpos (xfer_copy e.va p1 p2 hc)
  refine ⟨⟨h.valid, by have := h.room; omega, h.used, ?_, trivial⟩, by show t.used ≠ 0; rw [hc.used]; exact e.nz, ?_, ?_⟩
  · rw [h.val, Nat.pow_zero, Nat.div_one, natAbs_val]
  · rw [show upd buf 0 45 = buf1 a buf by unfold buf1; rw [if_pos hsa]]; exact Tape.start _ _ _
  · have := e.ml; unfold roomAfterSign; rw [if_pos hsa]; omega

/-- At the head a digit is left: `i` is below the digit count. -/
theorem LI.lt_len (e : Env a maxlen radix) (h : LI a maxlen radix.toNat buf t f i) :
    i < (digitsLE radix.toNat a.mag).length := by
  refine Nat.lt_of_not_le fun hle => h.nz (h.acct.valid.used_zero ?_)
  rw [h.acct.magN]
  exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (lt_pow_length_digitsLE e.r2 a.mag)
    (Nat.pow_le_pow_right (by have := e.r2; omega) hle))

theorem LI.post (e : Env a maxlen radix) (h : LI a maxlen radix.toNat buf t f i) (hq : DivDQuot t radix.toNat t t') :
    Acct t' 1 a.used ((a.mag / radix.toNat ^ (i + 1) : Nat) : Int) True ∧
      Tape (pre a) (out a radix.toNat) (buf1 a buf) (i + 1) (upd f (pre a + i) (rmapAt (t.mag % radix.toNat))) :=
  ⟨by rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]; exact xfer_divD h.acct (Nat.le_refl 1) (by have := e.r2; omega) hq,
   h.tape.step (by unfold out; rw [h.acct.magN])⟩

/-- One digit (`mp_div_d`, the store), `t ≠ 0` after: back to the head. -/
theorem LI.step (e : Env a maxlen radix) (h : LI a maxlen radix.toNat buf t f i) (hi : i ≠ roomAfterSign a maxlen - 1)
    (hq : DivDQuot t radix.toNat t t') (hnz : t'.used ≠ 0) :
    LI a maxlen radix.toNat buf t' (upd f (pre a + i) (rmapAt (t.mag % radix.toNat))) (i + 1) :=
  have p := h.post e hq
  ⟨p.1, hnz, p.2, by have := h.room; omega⟩

/-- After the loop: `n` digits, all of them, and room for the NUL. -/
structure Done (a : MpInt) (maxlen r : Nat) (buf : Nat → Nat) (f : Nat → Nat) (n : Nat) : Prop where
  tape : Tape (pre a) (out a r) (buf1 a buf) n f
  len : (digitsLE r a.mag).length = n
  fit : n < roomAfterSign a maxlen

/-- The last digit (`t = 0` after `mp_div_d`). -/
theorem LI.last (e : Env a maxlen radix) (h : LI a maxlen radix.toNat buf t f i) (hi : i ≠ roomAfterSign a maxlen - 1)
    (hq : DivDQuot t radix.toNat t t') (hz : t'.used = 0) :
    Done a maxlen radix.toNat buf (upd f (pre a + i) (rmapAt (t.mag % radix.toNat))) (i + 1) := by
  have p := h.post e hq
  have hlt : a.mag < radix.toNat ^ (i + 1) := Nat.lt_of_not_le fun hle => by
    have := Nat.div_pos hle (Nat.pow_pos (by have := e.r2; omega)); rw [← p.1.magN, MpInt.mag_used_zero hz] at this; omega
  have := length_digitsLE_le e.r2 (i + 1) a.mag hlt; have := h.lt_len e; have := h.room
  exact ⟨p.2, by omega, by omega⟩

/-- `--maxlen < 1`: `MP_BUF`, the sign and `maxlen' - 1` digits written, `written` untouched. -/
theorem LI.full (e : Env a maxlen radix) (h : LI a maxlen radix.toNat buf t f i) (hi : i = roomAfterSign a maxlen - 1) :
    ToRadixPost a maxlen radix hasW buf f w w mpBuf := by
  have hl := h.lt_len e; have hr := h.room; have := e.ml
  have hne : ¬ (maxlen < 2 ∨ ¬ radixOk radix) := fun c => c.elim (by omega) (· e.rok)
  refine ⟨?_, fun j => ?_, by simp [mpBuf, Layout.mpOkay]⟩
  · unfold toRadixRet; rw [if_neg (by omega), if_neg (by simpa using e.rok), if_neg e.nz, if_neg (by omega)]
  · unfold toRadixOut
    rw [if_neg hne, if_neg e.nz, if_neg (by omega), getD_sign e.nz, getD_map_take _ _ _ _ (by omega), h.tape.fin j,
      buf1_eq, digitsLE_getD e.r2]
    unfold out; (repeat' split) <;> first | rfl | omega | (congr 2; omega)

/-- `s_mp_reverse(_s, digs)`, `*str = '\0'`, `written`: `MP_OKAY` and the string. -/
theorem Done.fin (e : Env a maxlen radix) (h : Done a maxlen radix.toNat buf f n) (hrev : RevPost (pre a) n f g) :
    ToRadixPost a maxlen radix hasW buf (upd g (pre a + n) 0) w
      (if hasW = true then (if a.sign = Layout.mpNeg then n + 2 else n + 1) else w) Layout.mpOkay := by
  have hne : ¬ (maxlen < 2 ∨ ¬ radixOk radix) := fun c => c.elim (by have := e.ml; omega) (· e.rok)
  have hout : toRadixOut a maxlen radix = toRadixStr a radix.toNat := by
    unfold toRadixOut; rw [if_neg hne, if_neg e.nz, if_pos (by rw [h.len]; exact h.fit)]
  refine ⟨?_, fun j => ?_, ?_⟩
  · unfold toRadixRet
    rw [if_neg (by have := e.ml; omega), if_neg (by simpa using e.rok), if_neg e.nz, if_pos (by rw [h.len]; exact h.fit)]
  · rw [hout]; unfold toRadixStr msbDigits
    rw [List.append_assoc, getD_sign e.nz, if_neg e.nz, getD_rev_nul, h.len, digitsLE_getD e.r2]
    unfold upd; rw [hrev.fin j]
    by_cases hj : pre a ≤ j ∧ j < pre a + n
    · have h1 : ¬ j = pre a + n := by omega
      have h2 : ¬ j < pre a := by omega
      have h3 : j - pre a < n := by omega
      rw [if_pos hj, h.tape.done _ (by omega), if_neg h1, if_neg h2, if_pos h3]; rfl
    · rw [if_neg hj, h.tape.rest j (by omega), buf1_eq]; (repeat' split) <;> first | rfl | omega
  · rw [hout, length_toRadixStr e.nz, h.len]; cases hasW <;> simp; split <;> omega

/-! ## The early exits -/

theorem post_small (hm : maxlen < 2) : ToRadixPost a maxlen radix hasW buf buf w w mpBuf :=
  ⟨by unfold toRadixRet; rw [if_pos hm], fun j => by unfold toRadixOut; rw [if_pos (Or.inl hm)]; rfl,
   by simp [mpBuf, Layout.mpOkay]⟩

theorem post_val (hm : 2 ≤ maxlen) (hr : ¬ radixOk radix) : ToRadixPost a maxlen radix hasW buf buf w w Layout.mpVal :=
  ⟨by unfold toRadixRet; rw [if_neg (by omega), if_pos hr], fun j => by unfold toRadixOut; rw [if_pos (Or.inr hr)]; rfl,
   by simp [Layout.mpVal, Layout.mpOkay]⟩

/-- `a = 0`: `"0\0"` (`str[1]` first), `written = 2`. -/
theorem post_zero (hm : 2 ≤ maxlen) (hr : radixOk radix) (hu : a.used = 0) :
    ToRadixPost a maxlen radix hasW buf (upd (upd buf 1 0) 0 48) w (if hasW = true then 2 else w) Layout.mpOkay := by
  have hne : ¬ (maxlen < 2 ∨ ¬ radixOk radix) := fun c => c.elim (by omega) (· hr)
  have hout : toRadixOut a maxlen radix = [48, 0] := by unfold toRadixOut; rw [if_neg hne, if_pos hu]
  refine ⟨by unfold toRadixRet; rw [if_neg (by omega), if_neg (by simpa using hr), if_pos hu], fun j => ?_, ?_⟩
  · rw [hout]; unfold upd; rcases j with _ | _ | j <;> simp
  · rw [hout]; cases hasW <;> simp

/-! ## Readings for the machine side: the byte functions given by an equation

The machine holds the string as a memory snapshot; its byte function after a store is
`upd` of the one before (`Kit/ByteBuf.lean`'s `bytesOf_store`), handed in as `hf`. -/

theorem rmapAt_lt (j : Nat) : rmapAt j < 256 := by
  unfold rmapAt
  rw [List.getD_eq_getElem?_getD]
  rcases h : rmap[j]? with _ | x
  · simp
  · have hm : x ∈ rmap := List.mem_of_getElem? h
    have hall : ∀ y ∈ rmap, y < 256 := by unfold rmap; decide
    simpa using hall x hm

theorem room_eq (a : MpInt) (maxlen : Nat) : roomAfterSign a maxlen = maxlen - pre a := by
  unfold roomAfterSign pre; split <;> rfl

theorem pre_le (a : MpInt) : pre a ≤ 1 := by unfold pre; split <;> omega

theorem start_negE {f' : Nat → Nat} (e : Env a maxlen radix) (hc : CopyPost a (MpInt.zeroN (initPrec a.used)) t)
    (hs : t.sign = Layout.mpNeg) (hf : f' = upd buf 0 45) :
    LI a maxlen radix.toNat buf (t.withSign Layout.mpZpos) f' 0 := hf ▸ start_neg e hc hs

theorem LI.stepE {f' : Nat → Nat} (e : Env a maxlen radix) (h : LI a maxlen radix.toNat buf t f i)
    (hi : i ≠ roomAfterSign a maxlen - 1) (hq : DivDQuot t radix.toNat t t') (hnz : t'.used ≠ 0)
    (hf : f' = upd f (pre a + i) (rmapAt (t.mag % radix.toNat))) : LI a maxlen radix.toNat buf t' f' (i + 1) :=
  hf ▸ h.step e hi hq hnz

theorem LI.lastE {f' : Nat → Nat} (e : Env a maxlen radix) (h : LI a maxlen radix.toNat buf t f i)
    (hi : i ≠ roomAfterSign a maxlen - 1) (hq : DivDQuot t radix.toNat t t') (hz : t'.used = 0)
    (hf : f' = upd f (pre a + i) (rmapAt (t.mag % radix.toNat))) : Done a maxlen radix.toNat buf f' (i + 1) :=
  hf ▸ h.last e hi hq hz

/-- `s_mp_reverse` of the digits from `s = pre a`, the NUL, `written = NULL`. -/
theorem Done.finE {g' : Nat → Nat} {s : Nat} (e : Env a maxlen radix) (h : Done a maxlen radix.toNat buf f n)
    (hrev : RevPost s n f g) (hs : s = pre a) (hg : g' = upd g (pre a + n) 0) :
    ToRadixPost a maxlen radix false buf g' w w Layout.mpOkay := by
  subst hs hg; simpa using h.fin (hasW := false) (w := w) e hrev

/-- `a = 0` with `written = NULL`. -/
theorem post_zeroE {f' : Nat → Nat} (hm : 2 ≤ maxlen) (hr : radixOk radix) (hu : a.used = 0)
    (hf : f' = upd (upd buf 1 0) 0 48) : ToRadixPost a maxlen radix false buf f' w w Layout.mpOkay := by
  subst hf; simpa using post_zero (hasW := false) (w := w) (buf := buf) hm hr hu

end Tom.ToRadixStepL
