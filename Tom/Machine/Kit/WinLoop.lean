import Tom.Spec.WindowStep
import Tom.Machine.Kit.WinVal
import Tom.Machine.Kit.StackCall
import Tom.Machine.Kit.Meet

/-!
# The window loop of `s_mp_exptmod(_fast)` on the machine

`Tom/Spec/WindowStep.lean`'s loop states (`Hd`, `Bt`, `Fw`, `TL`, `TM`) at the compiled loop's
registers, one lemma per kind of edge, shared by both exponentiation workers (the same C loop):
the C's `buf` is `bm << 1` (the compiled loop shifts at the next bit: `bm` is the unshifted word,
sign-extended by `slliw`, `sx`), `digidx` the 64-bit word `DV i` of digit `i`, the spilled words read
back from the frame's snapshots (`rd8_self`, `rd8_out`), the bit tests (`q_one`, `z1_one`, …), and
the residue bounds a square or a product hands to `redux` (`sq_bounds`, `prod_bounds`, `rs_sq`).
-/

namespace Tom.Machine.WinLoop

open Tom Tom.Machine Tom.WindowStep Tom.Ledger

/-- A product of two residues below `B ≤ radix^U`: valid, below `(B-1)^2`, at most `2U` digits. -/
theorem prod_bounds {B U v w : Nat} {x e y : MpInt} (hfit : B ≤ radix ^ U) (hx : Rs B U x v) (he : Rs B U e w)
    (hm : MulPost x e y) : y.Valid ∧ y.mag ≤ (B - 1) * (B - 1) ∧ y.used ≤ 2 * U := by
  have s := xfer_mul hx.val he.val hm
  have hle : v * w ≤ (B - 1) * (B - 1) := Window.mul_le_sq hx.aux he.aux
  have hp : 0 < radix ^ U := Nat.pow_pos radix_pos
  refine ⟨s.valid, by rw [s.mag]; exact hle, ?_⟩
  refine used_le_of_lt s.valid ?_
  rw [s.mag, Nat.two_mul, Nat.pow_add]
  exact Nat.lt_of_le_of_lt hle (Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) hp)

theorem sq_bounds {B U v : Nat} {x y : MpInt} (hfit : B ≤ radix ^ U) (hx : Rs B U x v) (hs : SqrPost x y) :
    y.Valid ∧ y.mag ≤ (B - 1) * (B - 1) ∧ y.used ≤ 2 * U :=
  prod_bounds hfit hx hx ⟨hs.valid, hs.val⟩

section Loop
open Tom.WindowStep Tom.Window Tom.Machine.WV.Win Vsa.Sim
variable {RP : MpInt → MpInt → Prop} {r : Run} {B U : Nat} {Mt : Nat → MpInt}
  {i t bc bm y : Nat} {d : Int} {s : Window.St} {res : MpInt}

/-- `digidx = i - 1` as the machine's 64-bit word. -/
abbrev DV (i : Nat) : Nat := (i + 18446744073709551615) % 18446744073709551616

theorem rd8_out {M : Mem} {a x : Nat} {v w : BitVec 64} (h : bytesT8 M x = w) (hd : x + 8 ≤ a ∨ a + 8 ≤ x) :
    bytesT8 (writeLog M [(a, 8, v)]) x = w := by
  rw [Api.Two.bytesT8_log_out _ _ _ (by simp only [OutLRange, and_true, true_and]; omega)]; exact h

theorem rd8_self {M : Mem} {a : Nat} {v : BitVec 64} : bytesT8 (writeLog M [(a, 8, v)]) a = v := by
  rd_log

theorem q_one {bm : Nat} (h : 2 ^ 63 ≤ bm * 68719476736 % 2 ^ 64) : (bm % 2 ^ 32) >>> 27 &&& 1 = 1 := by
  rw [shr_and_one]; omega

theorem q_zero {bm : Nat} (h : bm * 68719476736 % 2 ^ 64 < 2 ^ 63) : (bm % 2 ^ 32) >>> 27 &&& 1 = 0 := by
  rw [shr_and_one]; omega

theorem sxb (bm : Nat) : sx (bm * 2 % 4294967296) % 2 ^ 32 = bm % 2 ^ 32 * 2 % 2 ^ 32 := by
  rw [show (2 : Nat) ^ 32 = 4294967296 from rfl, sx_mod _ (Nat.mod_lt _ (by decide))]; omega

theorem sxl (bm : Nat) : sx (bm * 2 % 4294967296) < 2 ^ 64 := sx_lt _ (Nat.mod_lt _ (by decide))

theorem md_idle {w r0 : Nat} (h : Md w r0 s) (hm : s.mode = 0) : s.bitcpy = 0 ∧ s.bitbuf = 0 := by
  rcases h with h | h | h
  · exact ⟨h.cpy, h.buf⟩
  · rw [h.mode] at hm; omega
  · rw [h.mode] at hm; omega

theorem md_win {w r0 : Nat} (h : Md w r0 s) (hm : s.mode = 2) : 0 < s.bitcpy := by
  rcases h with h | h | h
  · rw [h.mode] at hm; omega
  · rw [h.mode] at hm; omega
  · exact h.c0

/-- At the head with `bitcnt = 1`: the digit's last bit was read. -/
theorem hd_28 {b : Nat} (h : Hd r B U i t 1 d b s res) : Hd r B U i 28 1 d b s res := by
  obtain rfl : t = 28 := by have := h.cnt; have := h.t28; omega
  exact h

/-- `--bitcnt != 0`, the word not yet shifted (`K0`). -/
theorem hd_next0 (h : Hd r B U i t bc d (bm % 2 ^ 32) s res) (hbc : 1 < bc) :
    Bt r B U i t (bc - 1) d (bm % 2 ^ 32 * 2 % 2 ^ 32) ((bm % 2 ^ 32) >>> 27 &&& 1) s res :=
  h.next (by have := h.cnt; omega)

/-- `--bitcnt != 0` after a bit (`bm2 = slliw bm 1`, `y2` its bit 27). -/
theorem hd_next_sx (h : Hd r B U i t bc d (bm % 2 ^ 32 * 2 % 2 ^ 32) s res) (hbc : 1 < bc) :
    Bt r B U i t (bc - 1) d (sx (bm * 2 % 4294967296) % 2 ^ 32 * 2 % 2 ^ 32)
      (sx (bm * 2 % 4294967296) % 4294967296 / 134217728 % 2) s res := by
  have := h.next (by have := h.cnt; omega)
  rw [shr_and_one] at this
  rw [sxb]; exact this

/-- A zero bit in mode 0 (`Q`): `continue` with the word shifted. -/
theorem q_skip (env : Env RP r B U Mt)
    (h : Bt r B U i t bc d (bm % 2 ^ 32 * 2 % 2 ^ 32) ((bm % 2 ^ 32) >>> 27 &&& 1) s res) (hs0 : s.mode = 0)
    (hq : bm * 68719476736 % 2 ^ 64 < 2 ^ 63) : Hd r B U i (t + 1) bc d (sx (bm * 2 % 4294967296) % 2 ^ 32) s res := by
  rw [sxb]; exact h.skip env hs0 (q_zero hq)

/-- A one bit in mode 0 (`Q`): into the body. -/
theorem q_take (h : Bt r B U i t bc d (bm % 2 ^ 32 * 2 % 2 ^ 32) ((bm % 2 ^ 32) >>> 27 &&& 1) s res)
    (hq : 2 ^ 63 ≤ bm * 68719476736 % 2 ^ 64) : Bt r B U i t bc d (bm % 2 ^ 32 * 2 % 2 ^ 32) 1 s res := by
  rw [q_one hq] at h; exact h

/-- The next digit (`buf = X->dp[digidx]`, `digidx--`, `bitcnt = 28`): its first bit. -/
theorem rg_take (env : Env RP r B U Mt) {b dg : Nat} (h : Hd r B U i 28 1 (↑i - 1) b s res) (hi : 0 < i)
    (hd : dg = r.dig (i - 1)) (hdl : dg < 268435456) :
    Bt r B U (i - 1) 0 28 (↑(i - 1) - 1) (dg % 2 ^ 32 * 2 % 2 ^ 32)
      (dg % 4294967296 / 134217728 % 4294967296 &&& 1) s res := by
  have := h.refill env (by omega)
  rw [show (↑i : Int) - 1 - 1 = ↑(i - 1) - 1 by omega, ← hd, shr_and_one,
    show dg % 4294967296 / 134217728 % 4294967296 &&& 1 = dg / 2 ^ 27 % 2 by rw [Nat.and_one_is_mod]; omega,
    show dg % 2 ^ 32 = dg by omega] at *
  exact this

/-- The next digit's first bit zero in mode 0: skipped (`Z1`'s head). -/
theorem rg_skip (env : Env RP r B U Mt) {b dg : Nat} (h : Hd r B U i 28 1 (↑i - 1) b s res) (hi : 0 < i)
    (hd : dg = r.dig (i - 1)) (hdl : dg < 268435456) (hs0 : s.mode = 0)
    (hy : dg % 4294967296 / 134217728 % 4294967296 &&& 1 = 0) :
    Hd r B U (i - 1) 1 28 (↑(i - 1) - 1) (dg * 2 % 2 ^ 32) s res := by
  have := (rg_take env h hi hd hdl).skip env hs0 hy
  rw [show dg % 2 ^ 32 = dg by omega] at this; exact this

theorem z1_one {dg : Nat} (_hdl : dg < 268435456) (h : 2 ^ 63 ≤ dg * 137438953472 % 2 ^ 64) :
    (dg * 2 % 2 ^ 32) >>> 27 &&& 1 = 1 := by
  rw [shr_and_one]; omega

theorem z1_zero {dg : Nat} (_hdl : dg < 268435456) (h : dg * 137438953472 % 2 ^ 64 < 2 ^ 63) :
    (dg * 2 % 2 ^ 32) >>> 27 &&& 1 = 0 := by
  rw [shr_and_one]; omega

/-- `Z1`: the digit's second bit one: the body (`bm = 2 d`). -/
theorem z1_take {dg : Nat} (h : Hd r B U i 1 28 d (dg * 2 % 2 ^ 32) s res) (hdl : dg < 268435456)
    (hq : 2 ^ 63 ≤ dg * 137438953472 % 2 ^ 64) : Bt r B U i 1 27 d (2 * dg % 2 ^ 32 * 2 % 2 ^ 32) 1 s res := by
  have := h.next (by decide)
  rw [z1_one hdl hq, show dg * 2 % 2 ^ 32 = 2 * dg % 2 ^ 32 by omega] at this; exact this

/-- `Z1`: the second bit zero too: to `Q` with `bm = 4 d`. -/
theorem z1_skip (env : Env RP r B U Mt) {dg : Nat} (h : Hd r B U i 1 28 d (dg * 2 % 2 ^ 32) s res)
    (hdl : dg < 268435456) (hs0 : s.mode = 0) (hq : dg * 137438953472 % 2 ^ 64 < 2 ^ 63) :
    Bt r B U i 2 26 d (4 * dg % 2 ^ 32 * 2 % 2 ^ 32) ((4 * dg % 2 ^ 32) >>> 27 &&& 1) s res := by
  have h2 := (h.next (by decide)).skip env hs0 (z1_zero hdl hq)
  have := h2.next (by decide)
  rw [show dg * 2 % 2 ^ 32 * 2 % 2 ^ 32 = 4 * dg % 2 ^ 32 by omega] at this; exact this

/-- `bitbuf |= y << (winsize - ++bitcpy)` is the model's `+` (`Md.or_eq`). -/
theorem or_add {w r0 : Nat} (h : Md w r0 s) (hy : y ≤ 1) (hc : s.bitcpy + 1 ≤ w) :
    s.bitbuf ||| y * 2 ^ (w - (s.bitcpy + 1)) = s.bitbuf + y * 2 ^ (w - (s.bitcpy + 1)) := by
  have := h.or_eq hy hc; rwa [Nat.shiftLeft_eq] at this

theorem md_le {w r0 : Nat} (h : Md w r0 s) : s.mode ≤ 2 := by
  rcases h with h | h | h <;> rw [h.mode] <;> decide

theorem md_buf {w r0 : Nat} (h : Md w r0 s) : s.bitbuf < 2 ^ w := by
  rcases h with h | h | h
  · rw [h.buf]; exact Nat.two_pow_pos _
  · rw [h.buf]; exact Nat.two_pow_pos _
  · exact h.hi

theorem md_cpy {w r0 : Nat} (h : Md w r0 s) : s.bitcpy < w ∨ s.bitcpy = 0 := by
  rcases h with h | h | h
  · exact .inr h.cpy
  · exact .inr h.cpy
  · exact .inl h.cw

theorem ybit_le {w c : Nat} (hy : y ≤ 1) (hw : w ≤ 8) : y * 2 ^ (w - (c + 1)) ≤ 128 := by
  have : 2 ^ (w - (c + 1)) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> simp at this ⊢ <;> omega

/-- At the head with `bitcnt = 1`. -/
theorem hd_28b {b : Nat} (h : Hd r B U i t bc d b s res) (hbc : bc = 1) : Hd r B U i 28 1 d b s res := by
  subst hbc; exact hd_28 h

/-- `digidx == -1`, not in a window: the result. -/
theorem hd_done (env : Env RP r B U Mt) {b : Nat} (h : Hd r B U i t bc (↑i - 1) b s res) (hbc : bc = 1)
    (hi : i = 0) (hm : ¬ (s.mode = 2 ∧ 0 < s.bitcpy)) : Done r B U res := by
  subst hbc hi; exact ((hd_28 h).exit env (by simp)).skip hm

/-- `digidx == -1` in a window: the tail starts. -/
theorem hd_tail (env : Env RP r B U Mt) {b : Nat} (h : Hd r B U i t bc (↑i - 1) b s res) (hbc : bc = 1)
    (hi : i = 0) (hm : s.mode = 2) : TL r B U s 0 s.bitbuf res := by
  subst hbc hi; exact ((hd_28 h).exit env (by simp)).tail ⟨hm, md_win h.md hm⟩

/-- The bit into the window, the window not full (`Bt.add`) at the machine's `winsize`. -/
theorem k2_add (env : Env RP r B U Mt) {w buf : Nat} (hw : w = r.w) (h : Bt r B U i t bc d buf y s res)
    (h0 : ¬ (s.mode = 0 ∧ y = 0)) (h1 : ¬ (s.mode = 1 ∧ y = 0)) (hf : s.bitcpy + 1 ≠ w) :
    Hd r B U i (t + 1) bc d buf ⟨2, s.bitcpy + 1, s.bitbuf + y * 2 ^ (w - (s.bitcpy + 1)), s.res⟩ res := by
  subst hw; exact h.add env h0 h1 hf

theorem k2_bb {w buf : Nat} (hw : w = r.w) (h : Bt r B U i t bc d buf y s res) (hc : s.bitcpy + 1 ≤ w) :
    s.bitbuf ||| y * 2 ^ (w - (s.bitcpy + 1)) = s.bitbuf + y * 2 ^ (w - (s.bitcpy + 1)) := by
  subst hw; exact or_add h.pt.md h.pt.y_le hc

theorem k2_fill {w buf : Nat} (hw : w = r.w) (h : Bt r B U i t bc d buf y s res)
    (h0 : ¬ (s.mode = 0 ∧ y = 0)) (h1 : ¬ (s.mode = 1 ∧ y = 0)) (hf : s.bitcpy + 1 = w) :
    Fw r B U i t bc d buf y s 0 res := by
  subst hw; exact h.fill h0 h1 hf

theorem md_buf8 {w r0 : Nat} (h : Md w r0 s) (hw : w ≤ 8) : s.bitbuf < 256 :=
  Nat.lt_of_lt_of_le (md_buf h) (Nat.pow_le_pow_right (by decide) hw)

/-- The window's table entry: a residue of the table, its index in the upper half. -/
theorem fw_tab (env : Env RP r B U Mt) {w buf x bb : Nat} (hw : w = r.w) (h : Fw r B U i t bc d buf y s x res)
    (hbb : bb = s.bitbuf + y * 2 ^ (w - (s.bitcpy + 1))) :
    Rs B U (Mt bb) (r.tab bb) ∧ 2 ^ (w - 1) ≤ bb ∧ bb < 2 ^ w := by
  subst hw hbb
  have hi := Md.fill env.w2 h.pt.md h.pt.y_le h.full
  exact ⟨env.tab.upper _ hi.1 hi.2, hi.1, hi.2⟩

/-- The window's multiplication (`Fw.mul`) at the machine's `winsize` and index. -/
theorem fw_mul (env : Env RP r B U Mt) {w buf x bb : Nat} {r1 r2 : MpInt} (hw : w = r.w)
    (h : Fw r B U i t bc d buf y s x res) (hx : ¬ x < w) (hbb : bb = s.bitbuf + y * 2 ^ (w - (s.bitcpy + 1)))
    (hm : MulPost res (Mt bb) r1) (hp : RP r1 r2) :
    Hd r B U i (t + 1) bc d buf ⟨1, 0, 0, r.red (sqIter r.red w s.res * r.tab bb)⟩ r2 := by
  subst hw hbb; exact h.mul env hx hm hp

theorem tl_buf16 {w x bb : Nat} (hw : w = r.w) (hw8 : w ≤ 8) (h : TL r B U s x bb res) : bb < 65536 := by
  subst hw
  have : 2 ^ (2 * r.w) ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.lt_of_lt_of_le h.buf_lt this

theorem tl_sqr2 (env : Env RP r B U Mt) {x bb : Nat} {r1 r2 : MpInt} (h : TL r B U s x bb res) (hx : x < s.bitcpy)
    (hs : SqrPost res r1) (hp : RP r1 r2) : TM r B U s x (2 * bb) r2 := by
  rw [Nat.mul_comm]; exact h.sqr env hx hs hp

theorem shl_two {w h : Nat} (hw : w = r.w) (hh : 2 * h = 2 ^ w) : 1 <<< r.w = 2 * h := by
  subst hw; rw [Nat.shiftLeft_eq, Nat.one_mul, hh]

theorem tm_skip2 {w h x bb : Nat} (hw : w = r.w) (hh : 2 * h = 2 ^ w) (h' : TM r B U s x bb res)
    (hb : bb &&& 2 * h = 0) : TL r B U s (x + 1) bb res :=
  h'.skip (by rw [shl_two hw hh]; omega)

theorem tm_mul2 (env : Env RP r B U Mt) {w h x bb : Nat} {r1 r2 : MpInt} (hw : w = r.w) (hh : 2 * h = 2 ^ w)
    (h' : TM r B U s x bb res) (hb : bb &&& 2 * h ≠ 0) (hm : MulPost res (Mt 1) r1) (hp : RP r1 r2) :
    TL r B U s (x + 1) bb r2 :=
  h'.mul env (by rw [shl_two hw hh]; exact hb) hm hp

/-- A residue is a square's bound (`redux` once more on `res`, Montgomery's fixup). -/
theorem rs_sq {B U v : Nat} {x : MpInt} (h : Rs B U x v) (hB : 1 < B) :
    x.Valid ∧ x.mag ≤ (B - 1) * (B - 1) ∧ x.used ≤ 2 * U := by
  have hm : x.mag = v := h.magN
  have hv : v < B := h.aux
  refine ⟨h.valid, ?_, by have := h.used; omega⟩
  rw [hm]
  exact Nat.le_trans (by omega : v ≤ B - 1) (Nat.le_mul_of_pos_right _ (by omega))

end Loop

end Tom.Machine.WinLoop
