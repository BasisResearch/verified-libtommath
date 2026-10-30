import Tom.Spec.WindowStep

/-!
# The window loop of `s_mp_exptmod(_fast)` in the machine's registers

`Tom/Spec/WindowStep.lean` states the loop's model positions (`Hd`, `Bt`, `Fw`, `TL`, `TM`) over the C
values. The compiled loop (gcc -O2, rv64, `bn_s_mp_exptmod.c` at `0x8000261c`; `s_mp_exptmod_fast`'s
is the same shape) keeps them in registers: `buf` sign-extended from its 32 bits (`slliw`, `lw`),
`digidx` as a 64-bit `addiw` value (`2^64 - 1` for `-1`), `bitcnt` counted down, `mode` only in some
paths (the leading zeros of mode 0 and the first two bits after a refill are unrolled), and bits tested
by `slli rd, buf, 36 (37); bltz`. One structure per cut of the compiled loop, over those register
values, and one lemma per row group between them:

* `WK0` (mode 0 head, `bitcnt` before `--`), `WQ` (mode 0, bit test pending), `WZ1` (mode 0 after a
  refill whose top bit was zero: bit 26 tested), `WRG` (refill: `bitcnt == 0`, `digidx != -1`), `WR`
  (`bitcnt == 0`, any mode), `WB` (a bit read, `y` and the unshifted `buf`), `WK2` (the bit into the
  window), `WH` (mode 1, after a squaring or a window's product), `WSq` (the window's squarings).

The bit tests in the registers' terms: `sxN` (a 32-bit word sign-extended, as `slliw`/`lw` leave it),
`dvN` (`digidx = i - 1` as an `addiw` value).
-/

namespace Tom.WinRegs

open MpInt Ledger Window WindowStep

/-- A 32-bit word sign-extended to 64 bits (`Kit/WinVal.lean`'s `sx`). -/
def sxN (b : Nat) : Nat := if b < 2 ^ 31 then b else b + 18446744069414584320

/-- `digidx = i - 1` as a 64-bit register (`addiw a3, a3, -1`). -/
def dvN (i : Nat) : Nat := (i + 18446744073709551615) % 18446744073709551616

theorem sxN_mod2 {b : Nat} (_hb : b < 2 ^ 32) : sxN b * 2 % 4294967296 = b * 2 % 4294967296 := by
  unfold sxN; split <;> omega

theorem sxN_small {b : Nat} (hb : b < 2 ^ 31) : sxN b = b := by unfold sxN; split <;> omega

/-- `slli a4, s3, 36; bltz a4`: bit 27 of the word. -/
theorem bit27 {b : Nat} (_hb : b < 2 ^ 32) :
    2 ^ 63 ≤ sxN b * 68719476736 % 2 ^ 64 ↔ b / 2 ^ 27 % 2 = 1 := by
  unfold sxN; split <;> omega

/-- `slli a5, s3, 37; bltz a5` on a digit: its bit 26. -/
theorem bit26 {d : Nat} (_hd : d < 268435456) : 2 ^ 63 ≤ d * 137438953472 % 2 ^ 64 ↔ d / 2 ^ 26 % 2 = 1 := by
  omega

theorem dvN_zero {i : Nat} (hi : i < 2 ^ 63) : dvN i = 18446744073709551615 ↔ i = 0 := by
  unfold dvN; omega

theorem dvN_pred {i : Nat} (h0 : 0 < i) (hi : i < 2 ^ 63) : dvN i = i - 1 := by unfold dvN; omega

/-- The machine's `buf` at digit `i` with `t` bits read. -/
abbrev bufN (r : Run) (i t : Nat) : Nat := r.dig i * 2 ^ t % 2 ^ 32

theorem bufN_lt (r : Run) (i t : Nat) : bufN r i t < 2 ^ 32 := Nat.mod_lt _ (by decide)

theorem bufN_succ (r : Run) (i t : Nat) : bufN r i t * 2 % 2 ^ 32 = bufN r i (t + 1) := buf_shift _ _

/-- The mode-0 state: idle. -/
theorem md_idle {w res0 : Nat} {s : St} (h : Md w res0 s) (hm : s.mode = 0) : Idle res0 s := by
  rcases h with h | h | h
  · exact h
  · rw [h.mode] at hm; cases hm
  · rw [h.mode] at hm; cases hm

theorem md_mode_le {w res0 : Nat} {s : St} (h : Md w res0 s) : s.mode ≤ 2 := by
  rcases h with h | h | h <;> rw [h.mode] <;> decide

theorem md_cpy_lt {w res0 : Nat} {s : St} (h : Md w res0 s) (hw : 2 ≤ w) : s.bitcpy < w := by
  rcases h with h | h | h
  · rw [h.cpy]; omega
  · rw [h.cpy]; omega
  · exact h.cw

theorem md_buf_lt {w res0 : Nat} {s : St} (h : Md w res0 s) : s.bitbuf < 2 ^ w := by
  rcases h with h | h | h
  · rw [h.buf]; exact Nat.two_pow_pos _
  · rw [h.buf]; exact Nat.two_pow_pos _
  · exact h.hi

theorem md_sqr {w res0 : Nat} {s : St} (h : Md w res0 s) (hm : s.mode = 1) : Sqr s := by
  rcases h with h | h | h
  · rw [h.mode] at hm; cases hm
  · exact h
  · rw [h.mode] at hm; cases hm

theorem shr_bit (x : Nat) : x % 4294967296 / 134217728 % 4294967296 &&& 1 = x % 4294967296 / 134217728 % 2 := by
  rw [Nat.and_one_is_mod]; omega

theorem int_pred {i : Nat} (h : 0 < i) : (i : Int) - 1 - 1 = ((i - 1 : Nat) : Int) - 1 := by omega

/-! ## The cuts -/

section
variable (r : Run) (B U : Nat)

/-- **`K0`**: the head in mode 0 (`bitcnt` in `a5` before `--bitcnt`). -/
structure WK0 (i t bc dv bm : Nat) (s : St) (res : MpInt) : Prop where
  hd : Hd r B U i t bc ((i : Int) - 1) (bufN r i t) s res
  m0 : s.mode = 0
  hbm : bm = sxN (bufN r i t)
  hdv : dv = dvN i

/-- **`Q`**: mode 0, `--bitcnt != 0` (`bc` the decremented count), bit 27 of `buf` to test. -/
structure WQ (i t bc dv bm : Nat) (s : St) (res : MpInt) : Prop where
  hd : Hd r B U i t (bc + 1) ((i : Int) - 1) (bufN r i t) s res
  bc1 : 1 ≤ bc
  m0 : s.mode = 0
  hbm : bm = sxN (bufN r i t)
  hdv : dv = dvN i

/-- **`R`**: `--bitcnt == 0` (`t = 28`), the mode in a register. -/
structure WR (i dv mo cp bb : Nat) (s : St) (res : MpInt) : Prop where
  hd : Hd r B U i 28 1 ((i : Int) - 1) (bufN r i 28) s res
  hdv : dv = dvN i
  hmo : mo = s.mode
  hcp : cp = s.bitcpy
  hbb : bb = s.bitbuf

/-- **`RG`**: the refill (`digidx != -1`). -/
structure WRG (i dv mo cp bb : Nat) (s : St) (res : MpInt) : Prop extends WR r B U i dv mo cp bb s res where
  i0 : 0 < i

/-- **`Z1`**: after a refill in mode 0 with the digit's top bit zero: bit 26 to test. -/
structure WZ1 (i d dv : Nat) (s : St) (res : MpInt) : Prop where
  hd : Hd r B U i 1 28 ((i : Int) - 1) (bufN r i 1) s res
  m0 : s.mode = 0
  hdg : d = r.dig i
  dl : d < 268435456
  hdv : dv = dvN i

/-- **`B`**: a bit `y` read (`buf` unshifted in its register), not a leading zero. -/
structure WB (i t bc dv bm y mo cp bb : Nat) (s : St) (res : MpInt) : Prop where
  bt : Bt r B U i t bc ((i : Int) - 1) (bufN r i (t + 1)) y s res
  hbm : bm = sxN (bufN r i t)
  hdv : dv = dvN i
  hmo : mo = s.mode
  hcp : cp = s.bitcpy
  hbb : bb = s.bitbuf
  nz : ¬ (s.mode = 0 ∧ y = 0)

/-- **`K2`**: the bit into the window (not a squaring in mode 1). -/
structure WK2 (i t bc dv bm y cp bb : Nat) (s : St) (res : MpInt) : Prop where
  bt : Bt r B U i t bc ((i : Int) - 1) (bufN r i (t + 1)) y s res
  hbm : bm = sxN (bufN r i t)
  hdv : dv = dvN i
  hcp : cp = s.bitcpy
  hbb : bb = s.bitbuf
  n0 : ¬ (s.mode = 0 ∧ y = 0)
  n1 : ¬ (s.mode = 1 ∧ y = 0)

/-- **`H`**: mode 1 at the head after a bit (`buf` of the bit before in its register). -/
structure WH (i t bc dv bm : Nat) (s : St) (res : MpInt) : Prop where
  hd : Hd r B U i t bc ((i : Int) - 1) (bufN r i t) s res
  hbm : bm = sxN (bufN r i (t - 1))
  hdv : dv = dvN i
  m1 : s.mode = 1
  t1 : 1 ≤ t

/-- **`T`**: the tail, `x` of its rounds done (`bb` the C's shifted `bitbuf`, `cp` the window's size). -/
structure WT (s : St) (x bb cp : Nat) (res : MpInt) : Prop where
  tl : TL r B U s x bb res
  hcp : cp = s.bitcpy
  hx : x < cp

/-- **`TX`**: the tail after a round's squaring (`bb` the C's `bitbuf` before its shift). -/
structure WTX (s : St) (x bb cp : Nat) (res : MpInt) : Prop where
  tm : TM r B U s x (bb * 2) res
  hcp : cp = s.bitcpy
  hx : x < cp

/-- **`F`**: `x` of the window's squarings done (`bb` the window with the bit, `cp` the old `bitcpy`). -/
structure WSq (i t bc dv bm y cp bb x : Nat) (s : St) (res : MpInt) : Prop where
  fw : Fw r B U i t bc ((i : Int) - 1) (bufN r i (t + 1)) y s x res
  hbm : bm = sxN (bufN r i t)
  hdv : dv = dvN i
  hcp : cp = s.bitcpy
  hbb : bb = s.bitbuf + y * 2 ^ (r.w - (s.bitcpy + 1))
  xle : x ≤ cp + 1

end

/-! ## The rows -/

section
variable {RP : MpInt → MpInt → Prop} {r : Run} {B U : Nat} {Mt : Nat → MpInt} {i t bc dv bm y mo cp bb d x : Nat}
  {s : St} {res : MpInt}

theorem WK0.start (env : Env RP r B U Mt) (h : Rs B U res r.res0) :
    WK0 r B U r.u 28 1 (dvN r.u) 0 (start r.res0) res := by
  have hz : bufN r r.u 28 = 0 := by simp [bufN, env.top]
  have := Hd.start env h
  exact ⟨by rw [hz]; exact this, rfl, by rw [hz]; rfl, rfl⟩

/-- `--bitcnt != 0` in mode 0 (row `k0n`). -/
theorem WK0.next (h : WK0 r B U i t bc dv bm s res) (h1 : 1 < bc) : WQ r B U i t (bc - 1) dv bm s res :=
  ⟨by rw [show bc - 1 + 1 = bc by omega]; exact h.hd, by omega, h.m0, h.hbm, h.hdv⟩

/-- `bitcnt == 0`, `digidx == -1` in mode 0 (row `k0x`): done. -/
theorem WK0.exit (env : Env RP r B U Mt) (h : WK0 r B U i t bc dv bm s res) (hb : bc = 1)
    (hd : dv = 18446744073709551615) (hu : r.u < 2 ^ 63) : Done r B U res := by
  have hi := h.hd.iu
  have i0 : i = 0 := (dvN_zero (by omega)).1 (h.hdv ▸ hd)
  have t28 : t = 28 := by have := h.hd.cnt; omega
  subst t28
  exact (Hd.exit env h.hd (by rw [i0]; rfl)).skip (by rw [h.m0]; omega)

/-- `bitcnt == 0`, `digidx != -1` in mode 0 (row `k0l`): the refill. -/
theorem WK0.refill (h : WK0 r B U i t bc dv bm s res) (hb : bc = 1) (hd : dv ≠ 18446744073709551615) :
    WRG r B U i dv 0 0 0 s res := by
  have hi := h.hd.iu
  have t28 : t = 28 := by have := h.hd.cnt; omega
  subst t28
  have hid := md_idle h.hd.md h.m0
  exact ⟨⟨by rw [hb] at h; exact h.hd, h.hdv, h.m0.symm, hid.cpy.symm, hid.buf.symm⟩,
    Nat.pos_of_ne_zero fun e => hd (by rw [h.hdv, e]; rfl)⟩

/-- Bit 27 set in mode 0 (row `qy`): the window opens. -/
theorem WQ.yes (h : WQ r B U i t bc dv bm s res) (hy : 2 ^ 63 ≤ bm * 68719476736 % 2 ^ 64) :
    WB r B U i t bc dv bm 1 0 0 0 s res := by
  have ht : t < 28 := by have := h.hd.cnt; have := h.bc1; omega
  have hn := Hd.next h.hd ht
  have hbit : (bufN r i t >>> 27) &&& 1 = 1 := by
    rw [shr_and_one]; exact (bit27 (bufN_lt r i t)).1 (h.hbm ▸ hy)
  rw [hbit, bufN_succ, show bc + 1 - 1 = bc by omega] at hn
  have hid := md_idle h.hd.md h.m0
  exact ⟨hn, h.hbm, h.hdv, h.m0.symm, hid.cpy.symm, hid.buf.symm, by omega⟩

/-- Bit 27 clear in mode 0 (row `qn`): a leading zero, the next bit. -/
theorem WQ.no (env : Env RP r B U Mt) (h : WQ r B U i t bc dv bm s res) (hy : bm * 68719476736 % 2 ^ 64 < 2 ^ 63)
    {bm2 : Nat} (hb2 : bm2 = sxN (bm * 2 % 4294967296)) : WK0 r B U i (t + 1) bc dv bm2 s res := by
  have ht : t < 28 := by have := h.hd.cnt; have := h.bc1; omega
  have hn := Hd.next h.hd ht
  have hbit : (bufN r i t >>> 27) &&& 1 = 0 := by
    rw [shr_and_one]
    rcases Nat.mod_two_eq_zero_or_one (bufN r i t / 2 ^ 27) with h0 | h1
    · exact h0
    · have := (bit27 (bufN_lt r i t)).2 h1; rw [← h.hbm] at this; omega
  rw [hbit, bufN_succ, show bc + 1 - 1 = bc by omega] at hn
  exact ⟨Bt.skip env hn h.m0 rfl, h.m0, by rw [hb2, h.hbm, sxN_mod2 (bufN_lt r i t), bufN_succ], h.hdv⟩

/-- `bitcnt == 0`, `digidx == -1`, not a pending window (rows `rx1`, `rx2`): done. -/
theorem WR.done (env : Env RP r B U Mt) (h : WR r B U i dv mo cp bb s res) (hd : dv = 18446744073709551615)
    (hn : ¬ (mo = 2 ∧ cp ≠ 0)) (hu : r.u < 2 ^ 63) : Done r B U res := by
  have hi := h.hd.iu
  have i0 : i = 0 := (dvN_zero (by omega)).1 (h.hdv ▸ hd)
  exact (Hd.exit env h.hd (by rw [i0]; rfl)).skip (by rw [← h.hmo, ← h.hcp]; omega)

/-- `bitcnt == 0`, `digidx == -1`, a window pending (row `rx3`): the tail. -/
theorem WR.tail (env : Env RP r B U Mt) (h : WR r B U i dv mo cp bb s res) (hd : dv = 18446744073709551615)
    (hm : mo = 2) (hc : cp ≠ 0) (hu : r.u < 2 ^ 63) : WT r B U s 0 bb cp res := by
  have hi := h.hd.iu
  have i0 : i = 0 := (dvN_zero (by omega)).1 (h.hdv ▸ hd)
  have := (Hd.exit env h.hd (by rw [i0]; rfl)).tail (by rw [← h.hmo, ← h.hcp]; omega)
  exact ⟨by rw [h.hbb]; exact this, h.hcp, by omega⟩

/-- `bitcnt == 0`, `digidx != -1` (row `rl`): the refill. -/
theorem WR.refill (h : WR r B U i dv mo cp bb s res) (hd : dv ≠ 18446744073709551615) :
    WRG r B U i dv mo cp bb s res :=
  ⟨h, Nat.pos_of_ne_zero fun e => hd (by rw [h.hdv, e]; rfl)⟩

/-- The refill's digit with its top bit a leading zero (rows `rf1`–`rf3a`). -/
theorem WRG.zero (env : Env RP r B U Mt) (h : WRG r B U i dv mo cp bb s res) (hdg : d = r.dig dv)
    (hdl : d < 268435456) (hyo : (d % 4294967296 / 134217728 % 4294967296 &&& 1) ||| mo = 0)
    (hu : r.u < 2 ^ 63) : WZ1 r B U (i - 1) d ((dv + 18446744073709551615) % 18446744073709551616) s res := by
  have hi := h.hd.iu
  have hdv : dv = i - 1 := by rw [h.hdv]; exact dvN_pred h.i0 (by omega)
  subst hdv; subst hdg
  have ⟨hy0, hm0⟩ := Nat.or_eq_zero_iff.1 hyo
  rw [shr_bit] at hy0
  have hr := Hd.refill env h.hd (by have := h.i0; rw [h.hd.idx]; omega)
  have hb : (r.dig (i - 1) >>> 27) &&& 1 = 0 := by rw [shr_and_one]; simp only [Nat.reducePow] at hy0 ⊢; omega
  rw [hb, int_pred h.i0] at hr
  have hsk := Bt.skip env hr (by rw [← h.hmo, hm0]) rfl
  exact ⟨by rw [show bufN r (i - 1) 1 = r.dig (i - 1) * 2 % 2 ^ 32 by simp [bufN]]; exact hsk,
    by rw [← h.hmo, hm0], rfl, hdl, by unfold dvN; omega⟩

/-- The refill's digit, a bit to process (rows `rf1`–`rf3b`). -/
theorem WRG.bit (env : Env RP r B U Mt) (h : WRG r B U i dv mo cp bb s res) (hdg : d = r.dig dv)
    (hdl : d < 268435456) (hyo : (d % 4294967296 / 134217728 % 4294967296 &&& 1) ||| mo ≠ 0)
    (hu : r.u < 2 ^ 63) :
    WB r B U (i - 1) 0 28 ((dv + 18446744073709551615) % 18446744073709551616) d
      (d % 4294967296 / 134217728 % 4294967296 &&& 1) mo cp bb s res := by
  have hi := h.hd.iu
  have hdv : dv = i - 1 := by rw [h.hdv]; exact dvN_pred h.i0 (by omega)
  subst hdv; subst hdg
  have hr := Hd.refill env h.hd (by have := h.i0; rw [h.hd.idx]; omega)
  have hb : (r.dig (i - 1) >>> 27) &&& 1 = r.dig (i - 1) % 4294967296 / 134217728 % 4294967296 &&& 1 := by
    rw [shr_and_one, shr_bit]; simp only [Nat.reducePow]; omega
  rw [hb, int_pred h.i0] at hr
  refine ⟨by rw [show bufN r (i - 1) (0 + 1) = r.dig (i - 1) * 2 % 2 ^ 32 by simp [bufN]]; exact hr,
    by rw [show bufN r (i - 1) 0 = r.dig (i - 1) by simp [bufN]; omega]; exact (sxN_small (by omega)).symm,
    by unfold dvN; omega, h.hmo, h.hcp, h.hbb, ?_⟩
  intro ⟨h1, h2⟩
  apply hyo
  rw [h2, h.hmo, h1]; rfl

/-- Bit 26 set after a zero top bit in mode 0 (row `z1t`). -/
theorem WZ1.yes (h : WZ1 r B U i d dv s res) (hb : 2 ^ 63 ≤ d * 137438953472 % 2 ^ 64) :
    WB r B U i 1 27 dv (2 * d) 1 0 0 0 s res := by
  have hn := Hd.next h.hd (by decide)
  have e1 : bufN r i 1 = 2 * d := by simp only [bufN, ← h.hdg]; have := h.dl; omega
  have hbit : (bufN r i 1 >>> 27) &&& 1 = 1 := by
    rw [shr_and_one, e1]; have := (bit26 h.dl).1 hb; omega
  rw [hbit, bufN_succ] at hn
  have hid := md_idle h.hd.md h.m0
  exact ⟨hn, by rw [e1]; exact (sxN_small (by have := h.dl; omega)).symm, h.hdv, h.m0.symm,
    hid.cpy.symm, hid.buf.symm, by omega⟩

/-- Bit 26 clear after a zero top bit in mode 0 (row `z1f`): bit 25 to test. -/
theorem WZ1.no (env : Env RP r B U Mt) (h : WZ1 r B U i d dv s res) (hb : d * 137438953472 % 2 ^ 64 < 2 ^ 63) :
    WQ r B U i 2 26 dv (4 * d) s res := by
  have hn := Hd.next h.hd (by decide)
  have e1 : bufN r i 1 = 2 * d := by simp only [bufN, ← h.hdg]; have := h.dl; omega
  have hbit : (bufN r i 1 >>> 27) &&& 1 = 0 := by
    rw [shr_and_one, e1]
    rcases Nat.mod_two_eq_zero_or_one (d / 2 ^ 26) with h0 | h1
    · omega
    · have := (bit26 h.dl).2 h1; omega
  rw [hbit, bufN_succ] at hn
  have e2 : bufN r i 2 = 4 * d := by simp only [bufN, ← h.hdg]; have := h.dl; omega
  exact ⟨Bt.skip env hn h.m0 rfl, by decide, h.m0, by rw [e2]; exact (sxN_small (by have := h.dl; omega)).symm, h.hdv⟩

/-- A bit into the window (rows `bw`, `bw1`). -/
theorem WB.toK2 (h : WB r B U i t bc dv bm y mo cp bb s res) (hm : mo ≠ 1 ∨ y ≠ 0) :
    WK2 r B U i t bc dv bm y cp bb s res :=
  ⟨h.bt, h.hbm, h.hdv, h.hcp, h.hbb, h.nz, by rw [← h.hmo]; omega⟩

/-- Mode 1, a zero bit: `mp_sqr(&res, &res)`, `redux(&res, P, mp)` (row `bs`, its calls). -/
theorem WB.sqr (env : Env RP r B U Mt) (h : WB r B U i t bc dv bm y mo cp bb s res) (hm : mo = 1) (hy : y = 0)
    {r1 r2 : MpInt} (hs : SqrPost res r1) (hp : RP r1 r2) :
    WH r B U i (t + 1) bc dv bm { s with res := r.red (s.res * s.res) } r2 :=
  ⟨Bt.sqr env h.bt (by rw [← h.hmo, hm]) hy hs hp, by rw [Nat.add_sub_cancel]; exact h.hbm, h.hdv,
    by show s.mode = 1; rw [← h.hmo, hm], by omega⟩

/-- Mode 1 at the head, `--bitcnt != 0` (rows `bs2`, `fm3a`): the next bit. -/
theorem WH.next (h : WH r B U i t bc dv bm s res) (h1 : 1 < bc) {bm2 y2 : Nat}
    (hb2 : bm2 = sxN (bm * 2 % 4294967296)) (hy2 : y2 = sxN (bm * 2 % 4294967296) % 4294967296 / 134217728 % 2) :
    WB r B U i t (bc - 1) dv bm2 y2 1 0 0 s res := by
  have ht : t < 28 := by have := h.hd.cnt; omega
  have e1 : bm * 2 % 4294967296 = bufN r i t := by
    rw [h.hbm, sxN_mod2 (bufN_lt r i _), bufN_succ, show t - 1 + 1 = t by have := h.t1; omega]
  have hn := Hd.next h.hd ht
  rw [shr_and_one, bufN_succ, show (2 : Nat) ^ 27 = 134217728 from rfl] at hn
  have hsq := md_sqr h.hd.md h.m1
  refine ⟨?_, by rw [hb2, e1], h.hdv, h.m1.symm, hsq.cpy.symm, hsq.buf.symm, by rw [h.m1]; omega⟩
  rw [hy2, e1]
  have : sxN (bufN r i t) % 4294967296 = bufN r i t := by unfold sxN; split <;> have := bufN_lt r i t <;> omega
  rw [this]; exact hn

/-- Mode 1, `bitcnt == 0`, `digidx != -1` (rows `bs2r`, `fm3b` + `rl`): the refill. -/
theorem WH.refill (h : WH r B U i t bc dv bm s res) (hb : bc = 1) (hd : dv ≠ 18446744073709551615) :
    WRG r B U i dv 1 0 0 s res := by
  have t28 : t = 28 := by have := h.hd.cnt; omega
  subst t28; subst hb
  have hsq := md_sqr h.hd.md h.m1
  exact ⟨⟨h.hd, h.hdv, h.m1.symm, hsq.cpy.symm, hsq.buf.symm⟩, Nat.pos_of_ne_zero fun e => hd (by rw [h.hdv, e]; rfl)⟩

/-- Mode 1 at the head as `R` (row `fm3b`). -/
theorem WH.toR (h : WH r B U i t bc dv bm s res) (hb : bc = 1) : WR r B U i dv 1 0 0 s res := by
  have t28 : t = 28 := by have := h.hd.cnt; omega
  subst t28; subst hb
  have hsq := md_sqr h.hd.md h.m1
  exact ⟨h.hd, h.hdv, h.m1.symm, hsq.cpy.symm, hsq.buf.symm⟩

/-- Mode 1, `bitcnt == 0`, `digidx == -1` (row `bs2x`): done. -/
theorem WH.done (env : Env RP r B U Mt) (h : WH r B U i t bc dv bm s res) (hb : bc = 1)
    (hd : dv = 18446744073709551615) (hu : r.u < 2 ^ 63) : Done r B U res := by
  have hsq := md_sqr h.hd.md h.m1
  exact (WH.toR h hb).done env hd (by omega) hu

/-- The bit fills the window (row `wf`): the squarings start. -/
theorem WK2.full (h : WK2 r B U i t bc dv bm y cp bb s res) (hf : cp + 1 = r.w) {bb2 : Nat}
    (hb2 : bb2 = bb ||| y * 2 ^ (r.w - (cp + 1))) : WSq r B U i t bc dv bm y cp bb2 0 s res := by
  have hy := h.bt.pt.y_le
  refine ⟨Bt.fill h.bt h.n0 h.n1 (by rw [← h.hcp]; exact hf), h.hbm, h.hdv, h.hcp, ?_, Nat.zero_le _⟩
  rw [hb2, h.hbb, h.hcp, ← Md.or_eq h.bt.pt.md hy (by rw [← h.hcp]; omega), Nat.shiftLeft_eq]

/-- The bit into the window, more to come in this digit (row `wn`). -/
theorem WK2.add (env : Env RP r B U Mt) (h : WK2 r B U i t bc dv bm y cp bb s res) (hf : cp + 1 < r.w)
    (h1 : 1 < bc) {bb2 bm2 y2 : Nat} (hb2 : bb2 = bb ||| y * 2 ^ (r.w - (cp + 1)))
    (hbm2 : bm2 = sxN (bm * 2 % 4294967296)) (hy2 : y2 = sxN (bm * 2 % 4294967296) % 4294967296 / 134217728 % 2) :
    WK2 r B U i (t + 1) (bc - 1) dv bm2 y2 (cp + 1) bb2 ⟨2, cp + 1, bb2, s.res⟩ res := by
  have hy := h.bt.pt.y_le
  have hor : bb2 = s.bitbuf + y * 2 ^ (r.w - (s.bitcpy + 1)) := by
    rw [hb2, h.hbb, h.hcp, ← Md.or_eq h.bt.pt.md hy (by rw [← h.hcp]; omega), Nat.shiftLeft_eq]
  have ha := Bt.add env h.bt h.n0 h.n1 (by rw [← h.hcp]; omega)
  rw [← hor, ← h.hcp] at ha
  have ht : t + 1 < 28 := by have := h.bt.pt.cnt; omega
  have hn := Hd.next ha ht
  have e1 : bm * 2 % 4294967296 = bufN r i (t + 1) := by rw [h.hbm, sxN_mod2 (bufN_lt r i _), bufN_succ]
  have e2 : sxN (bufN r i (t + 1)) % 4294967296 = bufN r i (t + 1) := by
    unfold sxN; split <;> have := bufN_lt r i (t + 1) <;> omega
  rw [shr_and_one, bufN_succ, show (2 : Nat) ^ 27 = 134217728 from rfl] at hn
  refine ⟨?_, by rw [hbm2, e1], h.hdv, rfl, rfl, by simp, by simp⟩
  rw [hy2, e1, e2]; exact hn

/-- The bit into the window, the digit's last (row `wr`). -/
theorem WK2.last (env : Env RP r B U Mt) (h : WK2 r B U i t bc dv bm y cp bb s res) (hf : cp + 1 < r.w)
    (hb : bc = 1) {bb2 : Nat} (hb2 : bb2 = bb ||| y * 2 ^ (r.w - (cp + 1))) :
    WR r B U i dv 2 (cp + 1) bb2 ⟨2, cp + 1, bb2, s.res⟩ res := by
  have hy := h.bt.pt.y_le
  have hor : bb2 = s.bitbuf + y * 2 ^ (r.w - (s.bitcpy + 1)) := by
    rw [hb2, h.hbb, h.hcp, ← Md.or_eq h.bt.pt.md hy (by rw [← h.hcp]; omega), Nat.shiftLeft_eq]
  have ha := Bt.add env h.bt h.n0 h.n1 (by rw [← h.hcp]; omega)
  rw [← hor, ← h.hcp] at ha
  have t27 : t = 27 := by have := h.bt.pt.cnt; omega
  subst t27; subst hb
  exact ⟨ha, h.hdv, rfl, rfl, rfl⟩

/-- One of the window's squarings (rows `fs`, `fr`). -/
theorem WSq.sq (env : Env RP r B U Mt) (h : WSq r B U i t bc dv bm y cp bb x s res) (hx : x ≤ cp) {r1 r2 : MpInt}
    (hs : SqrPost res r1) (hp : RP r1 r2) : WSq r B U i t bc dv bm y cp bb (x + 1) s r2 :=
  ⟨Fw.sqr env h.fw (by have := h.fw.full; rw [← h.hcp] at this; omega) hs hp, h.hbm, h.hdv, h.hcp, h.hbb, Nat.succ_le_succ hx⟩

/-- The window's product (rows `fm`, `fm2`): mode 1 at the head. -/
theorem WSq.mul (env : Env RP r B U Mt) (h : WSq r B U i t bc dv bm y cp bb x s res) (hx : x = cp + 1) {r1 r2 : MpInt}
    (hm : MulPost res (Mt bb) r1) (hp : RP r1 r2) :
    WH r B U i (t + 1) bc dv bm ⟨1, 0, 0, r.red (sqIter r.red r.w s.res * r.tab (s.bitbuf + y * 2 ^ (r.w - (s.bitcpy + 1))))⟩ r2 :=
  ⟨Fw.mul env h.fw (by have := h.fw.full; rw [← h.hcp] at this; omega) (by rw [← h.hbb]; exact hm) hp,
    by rw [Nat.add_sub_cancel]; exact h.hbm, h.hdv, rfl, by omega⟩

/-- The window's table index (row `fm`): `M[bitbuf]` is in the table's upper half. -/
theorem WSq.idx (env : Env RP r B U Mt) (h : WSq r B U i t bc dv bm y cp bb x s res) :
    2 ^ (r.w - 1) ≤ bb ∧ bb < 2 ^ r.w := by
  rw [h.hbb]; exact Md.fill env.w2 h.fw.pt.md h.fw.pt.y_le h.fw.full

/-- `M[bitbuf]`'s residue account (the product's operand, row `fm`). -/
theorem WSq.tabR (env : Env RP r B U Mt) (h : WSq r B U i t bc dv bm y cp bb x s res) :
    Rs B U (Mt bb) (r.tab bb) :=
  env.tab.upper _ (h.idx env).1 (h.idx env).2

/-- A round of the tail: its squaring (rows `ts`, `tr`). -/
theorem WT.sq (env : Env RP r B U Mt) (h : WT r B U s x bb cp res) {r1 r2 : MpInt} (hs : SqrPost res r1) (hp : RP r1 r2) :
    WTX r B U s x bb cp r2 :=
  ⟨TL.sqr env h.tl (by rw [← h.hcp]; exact h.hx) hs hp, h.hcp, h.hx⟩

theorem tail_buf_lt {w b x : Nat} (hb : b < 2 ^ w) (hx : x ≤ w) (hw8 : w ≤ 8) : b * 2 ^ x < 65536 := by
  have h1 : b * 2 ^ x < 2 ^ w * 2 ^ w :=
    Nat.mul_lt_mul_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) hx) (Nat.two_pow_pos _)
  have h2 : 2 ^ w * 2 ^ w ≤ 2 ^ 8 * 2 ^ 8 :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hw8) (Nat.pow_le_pow_right (by decide) hw8)
  have h3 : (2 : Nat) ^ 8 * 2 ^ 8 = 65536 := rfl
  omega

/-- The tail's `bitbuf` below `2^16` (rows `tm*`). -/
theorem WT.bb_lt (h : WT r B U s x bb cp res) (hw8 : r.w ≤ 8) : bb < 65536 := by
  rw [h.tl.buf, tailLoop_snd]
  exact tail_buf_lt h.tl.win.hi (by have := h.tl.x_le; have := h.tl.win.cw; omega) hw8

theorem WTX.bb_lt (h : WTX r B U s x bb cp res) (hw8 : r.w ≤ 8) : bb < 65536 := by
  have hb : bb = (tailLoop r.red r.tab r.w x (s.res, s.bitbuf)).2 := by have := h.tm.buf; omega
  rw [hb, tailLoop_snd]
  exact tail_buf_lt h.tm.win.hi (by have := h.tm.x_lt; have := h.tm.win.cw; omega) hw8

/-- The tail's window size below `w` (`cp = bitcpy`). -/
theorem WT.cp_lt (h : WT r B U s x bb cp res) : cp < r.w := by rw [h.hcp]; exact h.tl.win.cw

theorem WTX.cp_lt (h : WTX r B U s x bb cp res) : cp < r.w := by rw [h.hcp]; exact h.tm.win.cw

theorem tbit {bb w h : Nat} (hh : 2 * h = 2 ^ w) (hb : bb < 2 ^ 31) :
    bb * 2 % 4294967296 &&& 2 * h = bb * 2 &&& (1 <<< w) := by
  rw [hh, Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt (by omega)]

/-- No product in this round, the last (row `tm0`): done. -/
theorem WTX.skipDone (h : WTX r B U s x bb cp res) {w hh : Nat} (hw : w = r.w) (h2 : 2 * hh = 2 ^ w)
    (hz : bb * 2 % 4294967296 &&& 2 * hh = 0) (hb : bb < 2 ^ 31) (hl : cp ≤ x + 1) : Done r B U res := by
  rw [tbit h2 hb, hw] at hz
  exact (TM.skip h.tm (by simp [hz])).fin (by rw [← h.hcp]; omega)

/-- No product in this round, more to come (row `tm1`). -/
theorem WTX.skipNext (h : WTX r B U s x bb cp res) {w hh : Nat} (hw : w = r.w) (h2 : 2 * hh = 2 ^ w)
    (hz : bb * 2 % 4294967296 &&& 2 * hh = 0) (hb : bb < 2 ^ 31) (hl : x + 1 < cp) : WT r B U s (x + 1) (2 * bb) cp res := by
  rw [tbit h2 hb, hw] at hz
  exact ⟨by rw [Nat.mul_comm]; exact TM.skip h.tm (by simp [hz]), h.hcp, hl⟩

/-- The round's product by `M[1]` (rows `tmm`, `tm2`). -/
theorem WTX.mul (env : Env RP r B U Mt) (h : WTX r B U s x bb cp res) {w hh : Nat} (hw : w = r.w) (h2 : 2 * hh = 2 ^ w)
    (hnz : bb * 2 % 4294967296 &&& 2 * hh ≠ 0) (hb : bb < 2 ^ 31) {r1 r2 : MpInt} (hm : MulPost res (Mt 1) r1)
    (hp : RP r1 r2) : TL r B U s (x + 1) (2 * bb) r2 := by
  rw [tbit h2 hb, hw] at hnz
  rw [Nat.mul_comm]; exact TM.mul env h.tm hnz hm hp

/-- After the product, the last round (row `tm3a`) or more (row `tm3b`). -/
theorem TL.toWT {x bb cp : Nat} (h : TL r B U s x bb res) (hc : cp = s.bitcpy) (hl : x < cp) : WT r B U s x bb cp res :=
  ⟨h, hc, hl⟩

theorem TL.done {x cp : Nat} {bb : Nat} (h : TL r B U s x bb res) (hc : cp = s.bitcpy) (hl : cp ≤ x) : Done r B U res :=
  h.fin (by rw [← hc]; omega)

end

end Tom.WinRegs
