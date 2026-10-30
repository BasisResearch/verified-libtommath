import Tom.Machine.Api.Std
import Tom.Machine.Api.MpMod2d

/-!
# `mp_mod_2d` on the machine: the whole function

The segments of `Tom.Machine.Fn.MpMod2d` and the contracts of `mp_zero`,
`mp_copy` (called, and tail-called), `__divdi3`, `__moddi3`, `memset` (over
`c`'s digits) and `mp_clamp`, by `call_std`/`tail_std` (`Kit/Meet.lean`,
`Api/Std.lean`). The regions are `Two`'s with the stack cut into our 48-byte
frame and the callees' 32 below (`Split`); the state `St` carries every
region's witness, and each segment's facts are `facts h`.
-/



namespace Tom.Machine.Fn.MpMod2d

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api Tom.Machine.Std
open Tom.Machine.Api.Two (R isW)

/-! ## The value -/

theorem clampUsed_congr {f g : Nat → Nat} : ∀ n, (∀ i, i < n → f i = g i) → clampUsed f n = clampUsed g n
  | 0, _ => rfl
  | n + 1, h => by simp only [clampUsed, h n (by omega), clampUsed_congr n fun i hi => h i (by omega)]

theorem mod2d_zero {a c c' : MpInt} (h : ZeroPost c c') : Mod2dPost a 0 c c' := by
  have hd : ∀ j, mod2dDigit a 0 j = 0 := fun j => by simp [mod2dDigit, Nat.mod_one]
  have hz : clampUsed (mod2dDigit a 0) a.used = 0 := by
    rw [clampUsed_congr (g := fun _ => 0) _ fun i _ => hd i]
    exact clampUsed_eq _ 0 (Or.inl rfl) _ (Nat.zero_le _) fun _ _ _ => rfl
  exact { alloc := h.alloc, len := h.len, digit := funext fun j => by rw [h.digit, hd], used := by rw [h.used, hz]
          sign := by rw [h.sign, h.used]; rfl }

theorem copy_lo {a c c' : MpInt} (h : CopyPost a c c') {j : Nat} (hj : j < a.used) : c'.digit j = a.digit j := by
  rw [h.digit, if_pos hj]

theorem copy_hi {a c c' : MpInt} (hc : c.Shape) (h : CopyPost a c c') {j : Nat} (hj : a.used ≤ j) : c'.digit j = 0 := by
  rw [h.digit, if_neg (by omega)]; split
  · rfl
  · exact hc.high_zero j (by omega)

theorem mod2d_lo {a : MpInt} {b j : Nat} (hj : j < b / 28) : mod2dDigit a b j = a.digit j := by
  simp [mod2dDigit, Layout.digitBits, hj]

theorem mod2d_copy {a c c' : MpInt} {b : Nat} (ha : a.Valid) (hc : c.Shape) (hge : 28 * a.used ≤ b)
    (h : CopyPost a c c') : Mod2dPost a b c c' := by
  have hd : ∀ j, c'.digit j = mod2dDigit a b j := fun j => by
    by_cases hj : j < a.used
    · rw [copy_lo h hj, mod2d_lo (by omega)]
    · rw [copy_hi hc h (by omega)]
      simp [mod2dDigit, ha.high_zero j (by omega)]
  have hu : clampUsed (mod2dDigit a b) a.used = a.used := by
    rw [← clampUsed_congr _ fun i hi => (mod2d_lo (a := a) (b := b) (by omega) : mod2dDigit a b i = a.digit i).symm]
    exact ha.clampUsed_self
  exact { alloc := h.alloc, len := h.len, digit := funext hd, used := by rw [h.used, hu]
          sign := by rw [h.sign, h.used]; split <;> first | exact ha.zero_pos ‹_› | rfl }

/-- The digits after the copy, the zero fill from `⌈b / 28⌉` and the mask of digit `b / 28`. -/
theorem mod2d_G {a : MpInt} {b : Nat} {F : Nat → Nat} (hF1 : ∀ j, j < b / 28 → F j = a.digit j)
    (hF2 : b % 28 ≠ 0 → F (b / 28) = a.digit (b / 28)) (hF3 : ∀ j, b / 28 < j → F j = 0) :
    (fun j => if j = b / 28 then F (b / 28) % 2 ^ (b % 28) else F j) = mod2dDigit a b := by
  funext j
  by_cases h1 : j < b / 28
  · have : j ≠ b / 28 := by omega
    simp [mod2dDigit, Layout.digitBits, h1, this, hF1 j h1]
  · by_cases h2 : j = b / 28
    · subst h2
      by_cases hd : b % 28 = 0
      · simp [mod2dDigit, Layout.digitBits, hd, Nat.mod_one]
      · simp [mod2dDigit, Layout.digitBits, hF2 hd]
    · simp [mod2dDigit, Layout.digitBits, h1, h2, hF3 j (by omega)]

theorem zfill_lt {f : Nat → Nat} (h : ∀ j, f j < radix) (i k j : Nat) : zfill f i k j < 2 ^ 31 := by
  unfold zfill; split
  · exact Nat.two_pow_pos _
  · exact Nat.lt_of_lt_of_le (h j) (by decide)

theorem zfill_lo {f : Nat → Nat} {i k j : Nat} (h : j < i) : zfill f i k j = f j := by
  simp [zfill, show ¬ i ≤ j by omega]

theorem zfill_mid {f : Nat → Nat} {i k j : Nat} (h1 : i ≤ j) (h2 : j < k) : zfill f i k j = 0 := by
  simp [zfill, h1, h2]

theorem zfill_hi {f : Nat → Nat} {i k j : Nat} (h : k ≤ j) : zfill f i k j = f j := by
  simp [zfill, show ¬ j < k by omega]

/-- What `mp_clamp` is handed. -/
def mid (a c' : MpInt) (b : Nat) : MpInt := MpInt.ofDigits c'.used c'.alloc c'.sign (mod2dDigit a b)

theorem mod2d_hi {a : MpInt} {b j : Nat} (ha : a.Shape) (hj : a.used ≤ j) : mod2dDigit a b j = 0 := by
  simp [mod2dDigit, ha.high_zero j hj]

theorem mid_digit {a c c' : MpInt} {b : Nat} (ha : a.Shape) (hroom : a.used ≤ c.alloc) (h : CopyPost a c c') :
    (mid a c' b).digit = mod2dDigit a b := by
  funext j; simp only [mid, MpInt.ofDigits_digit, h.alloc]; split
  · rfl
  · exact (mod2d_hi ha (by omega)).symm

theorem mid_shape {a c c' : MpInt} {b : Nat} (ha : a.Valid) (hc : c.Shape) (hroom : a.used ≤ c.alloc)
    (h : CopyPost a c c') : (mid a c' b).Shape :=
  { len := MpInt.ofDigits_len _ _ _ _
    used_le := by simp only [mid, MpInt.ofDigits, h.used, h.alloc]; exact hroom
    alloc_lt := by simp only [mid, MpInt.ofDigits, h.alloc]; exact hc.alloc_lt
    digit_lt := fun i => by
      rw [mid_digit ha.toShape hroom h]; simp only [mod2dDigit]
      split
      · exact ha.digit_lt _
      · split
        · exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (ha.digit_lt _)
        · exact radix_pos
    high_zero := fun i hi => by
      rw [mid_digit ha.toShape hroom h]
      exact mod2d_hi ha.toShape (by simpa [mid, MpInt.ofDigits, h.used] using hi) }

theorem mod2d_main {a c c' c₂ : MpInt} {b : Nat} (ha : a.Valid) (hroom : a.used ≤ c.alloc)
    (h : CopyPost a c c') (hcl : ClampPost (mid a c' b) c₂) : Mod2dPost a b c c₂ :=
  { alloc := by rw [hcl.alloc]; simp only [mid, MpInt.ofDigits, h.alloc]
    len := by rw [hcl.digits]; simp only [mid, MpInt.ofDigits_len, h.alloc]
    digit := by rw [hcl.digit, mid_digit ha.toShape hroom h]
    used := by rw [hcl.used, mid_digit ha.toShape hroom h]; simp only [mid, MpInt.ofDigits, h.used]
    sign := by rw [hcl.sign]; simp only [mid, MpInt.ofDigits, h.sign] }

/-! ## The machine -/



/-- `x2L` with `s0 = 4 D` (`x1_step` shifts it; `mp_clamp` keeps it). -/
def x2L' (sp pc d q D : Nat) : GRegs := (8, BitVec.ofNat 64 (4 * D)) :: x2L sp pc d q

def clL' (sp pc D : Nat) : GRegs := (8, BitVec.ofNat 64 (4 * D)) :: clL sp pc

/-- `x1_step`, keeping `s0`. -/
theorem x1_step' (v : Abi) (outp : Array String) (sp D pc d dp : Nat) (M : Mem)
    (hc : CodeAt M mpMod2dBase mpMod2dCode) :
    Triple (At 0x80005840#64 (xL sp D pc d dp) M v.keepR1 outp)
      (At 0x80005848#64 (x2L' sp pc d (dp + 4 * D) D) (writeLog M []) v.keepR1 outp) := by
  mmod2d_ctx
  seg_step mod2dX1 0x80005848#64 ([] : List (List (BitVec 8))) [2, 8, 9, 13, 14] abiKeysR1 [xL] [x2L', x2L] [] hc

/-- `x2_step`, keeping `s0`. -/
theorem x2_step' (v : Abi) (outp : Array String) (sp pc d q y D : Nat) (M : Mem)
    (hc : CodeAt M mpMod2dBase mpMod2dCode) (hf : XFacts M q y) (hd : d < 28) :
    Triple (At 0x80005848#64 (x2L' sp pc d q D) M v.keepR1 outp)
      (At 0x80005864#64 (clL' sp pc D) (writeLog M [(q, 4, BitVec.ofNat 64 (y % 2 ^ d))]) v.keepR1 outp) := by
  mmod2d_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M q) = BitVec.ofNat 64 y := by
    rw [hf.y_v, signExtend_ofNat32 _ hf.y_lt]
  have hm := BitW.mask_and y d (by omega)
  seg_step mod2dX2 0x80005864#64 [rd4 M q] [8, 2, 9, 13, 14] abiKeysR1 [x2L', x2L] [clL', clL] [h1, hm] hc


def σz : Ob → Option R
  | .S => some .bS
  | .D => some .bD
  | .code => some .code

def σd : Dz → Option R
  | .D => some .bD
  | .code => some .code

def σc : Cd → Option R := fun _ => some .code

/-- The tail call reuses our frame. -/
def σt : R → Option R
  | .stk => none
  | r => some r

theorem cd {sp pa adp pc cdp : Nat} {a c : MpInt} {W : List (Option R)} {κ : Option R → Kind} {m M : Mem}
    (h : St (Split.lay (Two.lay 80 sp pa adp pc cdp a c) .stk 48) (Split.wr isW) W κ m M)
    (hk : κ (some .code) = .code := by rfl) : CodeAt M mpMod2dBase mpMod2dCode := (h.img (some .code) hk).mpMod2d

/-- **`mp_mod_2d` on the machine** (distinct operands). -/
theorem correct : Api.MpMod2d.Statement := by
  intro m v outp sp pa adp pc cdp a b c ra s0 hP
  have h0 := St.two (f := 48) hP.ra_ hP.ga hP.rc hP.gc hP.rs hP.img hP.lay (by decide)
  have := hP.sp_ge; have := hP.sp_al; have hra := hP.ra_al; have hb := hP.b_lt; have hroom := hP.room
  have hbits : 28 * a.used < 2 ^ 31 := hP.bits
  have := hP.va.used_le; have := hP.va.alloc_lt; have := hP.sc.used_le; have := hP.sc.alloc_lt
  refine Triple.lmap (fun cf h => h.sub (L' := entry1 ra s0 v.s.s1 sp pa b pc) (K' := v.keepR1) rfl rfl) ?_
  rcases Nat.eq_zero_or_pos b with rfl | hb0
  · -- `b = 0`: `mp_zero(c)`
    refine h0.seqW none rfl (z_step ra s0 v.s.s1 v outp sp pa pc m (cd h0) (by facts h0)) fun M1 h1 => ?_
    refine call_std mpZero ⟨pc, cdp, c⟩ σz h1 (cd h1) 0x8cdfc0ef#32 0x1fc8cc#21 0x800058b0#64 hP.sc fun c' M2 hq h2 => ?_
    exact (Triple.rmap (fun cf h => ⟨c', M2, h.sub rfl rfl, ⟨h2.mpAt (some .bS) (some .bD) rfl rfl,
      mod2d_zero (And.left hq), h2.unsplit (by simp [Two.lay])⟩⟩) (zr_step ra s0 v.s.s1 v outp sp pc M2 (cd h2) (by facts h2))).pre
  refine h0.seqW none rfl (p1_step ra s0 v.s.s1 v outp sp pa b pc m (cd h0) (by facts h0) hb0 hb) fun M1 h1 => ?_
  refine h1.seqW none rfl (p2_step s0 v outp sp pa b pc a.used M1 (cd h1) (by facts h1) (by facts h1)) fun M2 h2 => ?_
  refine St.seq0 (p3_step v outp sp pa b pc a.used M2 (cd h2) hbits) ?_
  by_cases hge : 28 * a.used ≤ b
  · -- `b ≥ 28 a->used`: tail-call `mp_copy(a, c)`
    refine St.seq0 (c_step ra s0 v.s.s1 v outp sp pa b pc a.used M2 (cd h2) (by facts h2) hb hbits hge) ?_
    exact tail_std mpCopy ⟨sp, pa, adp, pc, cdp, a, c⟩ σt (h2.forget none rfl)
      ⟨hP.va.toShape, hP.sc, hP.va.sign_ok, hroom, hP.sp_al, by (try dsimp only); omega⟩ hra fun c' M3 cf hq h3 hat =>
        ⟨c', M3, hat, ⟨h3.mpAt (some .bS) (some .bD) rfl rfl, mod2d_copy hP.va hP.sc hge hq.1, h3.unsplit (by simp [Two.lay])⟩⟩
  have hlt : b < 28 * a.used := by omega
  refine St.seq0 (k_step v outp sp pa b pc a.used M2 (cd h2) hb hbits hlt) ?_
  refine call_std mpCopy ⟨sp - 48, pa, adp, pc, cdp, a, c⟩ some h2 (cd h2) 0x808fb0ef#32 0x1fb008#21 0x800057dc#64
    ⟨hP.va.toShape, hP.sc, hP.va.sign_ok, hroom, by (try dsimp only); omega, by (try dsimp only); omega⟩ fun c' M3 hq h3 => ?_
  have hcp : CopyPost a c c' := hq.1; have hsh := hq.2; have hu := hcp.used; have hal := hcp.alloc; have := hsh.used_le
  refine St.seq0 (d1_step v outp sp b pc M3 (cd h3)) ?_
  refine call_std divdi3 ⟨b, 28⟩ σc h3 (cd h3) 0x5bd110ef#32 0x11dbc#21 0x800057ec#64 (DivRes.of (by omega) (by decide) (by decide))
    fun _ M4 _ h4 => ?_
  refine St.seq0 (d2_step v outp sp b pc M4 (cd h4) hb) ?_
  refine call_std moddi3 ⟨b, 28⟩ σc h4 (cd h4) 0x62d110ef#32 0x11e2c#21 0x80005800#64 (DivRes.of (by omega) (by decide) (by decide))
    fun _ M5 _ h5 => ?_
  have hd : b % 28 < 28 := Nat.mod_lt _ (by decide)
  refine St.seq0 (m1_step v outp sp (b / 28) pc c'.used cdp (b % 28) M5 (cd h5) (by facts h5) hd) ?_
  refine Triple.seq (snez_step v outp sp (b / 28) pc c'.used (b % 28) M5 (cd h5) hd) ?_
  have he : (if b % 28 = 0 then 0 else 1) ≤ 1 := by split <;> omega
  have hx : b / 28 + (if b % 28 = 0 then 0 else 1) ≤ c'.used := by split <;> omega
  by_cases hxe : b / 28 + (if b % 28 = 0 then 0 else 1) = c'.used
  · -- nothing to zero
    refine St.seq0 (m2t_step v outp sp (b / 28) pc c'.used (b % 28) _ cdp M5 (cd h5) (by facts h5) he hxe) ?_
    refine St.seq0 (x1_step' v outp sp (b / 28) pc (b % 28) cdp M5 (cd h5)) ?_
    have hy : c'.digit (b / 28) < 2 ^ 31 := Nat.lt_of_lt_of_le (hsh.digit_lt _) (by decide)
    refine h5.seqD (some .bD) rfl (x2_step' v outp sp pc (b % 28) (cdp + 4 * (b / 28)) (c'.digit (b / 28)) (b / 28) M5 (cd h5)
      (by facts h5) hd) (by omega) (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)) fun M6 h6 => ?_
    have hG := mod2d_G (a := a) (b := b) (F := c'.digit) (fun j hj => copy_lo hcp (by omega))
      (fun _ => copy_lo hcp (by omega)) (fun j hj => copy_hi hP.sc hcp (by split at hxe <;> omega))
    have h7 := h6.setMp (some .bS) (some .bD) rfl rfl (mid a c' b) rfl rfl rfl rfl
      (fun j hj => by simp only [mid, MpInt.ofDigits_digit, if_pos hj]; rw [← hG])
    have : (mid a c' b).alloc = c'.alloc := rfl
    refine call_std clamp ⟨pc, cdp, mid a c' b⟩ σz h7 (cd h7) 0xf74ff0ef#32 0x1ff774#21 0x80005868#64
      (mid_shape hP.va hP.sc hroom hcp) fun c₂ M8 hcl h8 => ?_
    exact (Triple.rmap (fun cf h => ⟨c₂, M8, h.sub rfl rfl, ⟨(h8.hdr (some .bS) rfl).mpAt (by
        rw [hcl.alloc, hcl.digit]; exact h8.dig (some .bD) rfl), mod2d_main hP.va hroom hcp hcl,
      h8.unsplit (by simp [Two.lay])⟩⟩) (e_step ra s0 v.s.s1 v outp sp pc M8 (cd h8) (by facts h8))).pre
  · -- `memset` the digits `[⌈b / 28⌉, c->used)`
    have hx' : b / 28 + (if b % 28 = 0 then 0 else 1) < c'.used := by omega
    refine h5.seqW none rfl (m2f_step v outp sp (b / 28) pc c'.used (b % 28) _ cdp M5 (cd h5) (by facts h5)
      (by facts h5) he hx' (by facts h5)) fun M6 h6 => ?_
    refine call_std memsetD ⟨cdp, c'.alloc, c'.digit, b / 28 + (if b % 28 = 0 then 0 else 1), c'.used, _⟩ σd h6 (cd h6)
      0x371030ef#32 0x3b70#21 0x80005838#64 ⟨by (try dsimp only); omega, by (try dsimp only); omega, rfl⟩ fun _ M7 _ h7 => ?_
    refine St.seq0 (r_step v outp sp (b / 28) pc (b % 28) cdp M7 (cd h7) (by facts h7)) ?_
    refine St.seq0 (x1_step' v outp sp (b / 28) pc (b % 28) cdp M7 (cd h7)) ?_
    have hy : zfill c'.digit (b / 28 + (if b % 28 = 0 then 0 else 1)) c'.used (b / 28) < 2 ^ 31 := zfill_lt hsh.digit_lt _ _ _
    refine h7.seqD (some .bD) rfl (x2_step' v outp sp pc (b % 28) (cdp + 4 * (b / 28))
      (zfill c'.digit (b / 28 + (if b % 28 = 0 then 0 else 1)) c'.used (b / 28)) (b / 28) M7 (cd h7) (by facts h7) hd)
      (by omega) (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)) fun M8 h8 => ?_
    have hG := mod2d_G (a := a) (b := b) (F := zfill c'.digit (b / 28 + (if b % 28 = 0 then 0 else 1)) c'.used)
      (fun j hj => by rw [zfill_lo (by omega), copy_lo hcp (by omega)])
      (fun h0 => by rw [zfill_lo (by rw [if_neg h0]; omega), copy_lo hcp (by omega)])
      (fun j hj => by
        by_cases hju : j < c'.used
        · exact zfill_mid (by omega) hju
        · rw [zfill_hi (by omega), copy_hi hP.sc hcp (by omega)])
    have h9 := h8.setMp (some .bS) (some .bD) rfl rfl (mid a c' b) rfl rfl rfl rfl
      (fun j hj => by simp only [mid, MpInt.ofDigits_digit, if_pos hj]; rw [← hG])
    have : (mid a c' b).alloc = c'.alloc := rfl
    refine call_std clamp ⟨pc, cdp, mid a c' b⟩ σz h9 (cd h9) 0xf74ff0ef#32 0x1ff774#21 0x80005868#64
      (mid_shape hP.va hP.sc hroom hcp) fun c₂ M9 hcl h10 => ?_
    exact (Triple.rmap (fun cf h => ⟨c₂, M9, h.sub rfl rfl, ⟨(h10.hdr (some .bS) rfl).mpAt (by
        rw [hcl.alloc, hcl.digit]; exact h10.dig (some .bD) rfl), mod2d_main hP.va hroom hcp hcl,
      h10.unsplit (by simp [Two.lay])⟩⟩) (e_step ra s0 v.s.s1 v outp sp pc M9 (cd h10) (by facts h10))).pre

end Tom.Machine.Fn.MpMod2d
