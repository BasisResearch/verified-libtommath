import Tom.Machine.Seg.MpMontSetup
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Jal
import Tom.Machine.Kit.Frame
import Tom.Machine.Kit.Keep
import Tom.Spec.Mont

/-!
# `mp_montgomery_setup` on the machine: the segments

`mp_montgomery_setup(n, rho)` at `0x80005be0` (48 instructions). Load
`b = n->dp[0]`; even: `MP_VAL` (`msV1`, `msV2`). Odd: save `s0`, `ra`, `s1`,
`s2` and `x₀` in a 48-byte frame, `x₀ = (((b + 2) & 4) << 1) + b` (`msP`), then
three Newton steps `x := x * (2 - b * x)` in 32 bits, each two `__muldi3`
calls around `msA*` (`2 - b x`) and `msB*` (`x := sext₃₂ (…)`), and finally
`*rho := (-x) & MP_MASK` (`msE1`) and `MP_OKAY` (`msE2`). The register values
stay as the evaluator computes them (`x0v`, `sub2`, `sx`, `rhov`); their
meaning in `Nat` is `x0v_lo`, `sub2_lo`, `sx_lo`, `rhov_lo`.
-/


namespace Tom.Machine.Fn.MpMontSetup

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "ms_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpMontgomerySetupBase = 0x80005be0 := rfl
   have : mpMontgomerySetupCode.length = 48 := rfl))

/-- `x₀` as the machine computes it. -/
def x0v (b : Nat) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.signExtend 64 (BitVec.ofNat 32 ((b * 2 + 4) % 4294967296)) &&&
    8#64) + BitVec.ofNat 32 (b % 4294967296))

/-- `2 - y` in 32 bits, sign-extended (`subw`). -/
def sub2 (y : BitVec 64) : BitVec 64 := BitVec.signExtend 64 (2#32 - BitVec.extractLsb 31 0 y)

/-- `y`'s low word, sign-extended (`sext.w`). -/
def sx (y : BitVec 64) : BitVec 64 := BitVec.signExtend 64 (BitVec.extractLsb 31 0 y)

/-- `(-y) & MP_MASK` (`negw`, `slli 36`, `srli 36`). -/
def rhov (y : BitVec 64) : BitVec 64 :=
  Sail.shift_bits_right (Sail.shift_bits_left (BitVec.signExtend 64 (0#32 - BitVec.extractLsb 31 0 y)) 36#6) 36#6

def entry : BitVec 64 := 0x80005be0#64

/-- Registers at the entry: `ra`, `sp`, `s0`, `s1`, `s2`, `a0 = n`, `a1 = rho`. -/
def entryL (ra s0 s1 s2 : BitVec 64) (sp p rp : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (18, s2), (10, BitVec.ofNat 64 p), (11, BitVec.ofNat 64 rp)]

/-- The loads: `n->dp`, `dp[0]`. -/
structure LFacts (m : Mem) (p dp b : Nat) : Prop where
  rp : Ram p 24
  rd : Ram dp 4
  dpv : bytesT8 m (p + 16) = BitVec.ofNat 64 dp
  bv : BitVec.signExtend 64 (bytesT4 m dp) = BitVec.ofNat 64 b
  b28 : b < 2 ^ 28

/-- The stack frame. -/
structure SFacts (sp : Nat) : Prop where
  rs : Ram (sp - 48) 48
  sp_al : sp % 16 = 0
  sp_ge : 48 ≤ sp
  code_off : mpMontgomerySetupBase + 192 ≤ sp - 48

/-- `b` even: the frame's first stores, `a0 = MP_VAL` (`5c88`). -/
def evenL (ra s0 s1 s2 : BitVec 64) (sp : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (9, s1), (18, s2), (10, 0xfffffffffffffffd#64)]

def evenLog (ra s0 : BitVec 64) (sp : Nat) : List WEntry := [(sp - 16, 8, s0), (sp - 8, 8, ra)]

theorem even_step (ra s0 s1 s2 : BitVec 64) (v : Abi) (outp : Array String) (sp p dp b rp : Nat) (m : Mem)
    (hc : CodeAt m mpMontgomerySetupBase mpMontgomerySetupCode) (hs : SFacts sp) (hl : LFacts m p dp b)
    (hd : dp + 4 ≤ sp - 48 ∨ sp ≤ dp) (he : (BitVec.ofNat 64 b &&& 1#64 == 0#64) = true) :
    Triple (At entry (entryL ra s0 s1 s2 sp p rp) m v.keepR2 outp)
      (At 0x80005c88#64 (evenL ra s0 s1 s2 sp) (writeLog m (evenLog ra s0 sp)) v.keepR2 outp) := by
  ms_ctx
  have h1 := hl.dpv; have h2 := hl.bv
  seg_step msV1 0x80005c88#64 [rd8 m (p + 16), rd4 m dp] [1, 2, 8, 9, 18, 10, 11] abiKeysR2
    [entry, entryL, evenLog] [evenL] [h1, h2, he] hc

/-- A return with `a0 = r`. -/
def retL (ra s0 s1 s2 : BitVec 64) (sp : Nat) (r : BitVec 64) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (18, s2), (10, r)]

theorem even_ret (ra s0 s1 s2 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M mpMontgomerySetupBase mpMontgomerySetupCode) (hra : ra.toNat % 4 = 0) (hs : SFacts sp)
    (h40 : bytesT8 M (sp - 48 + 40) = ra) (h32 : bytesT8 M (sp - 48 + 32) = s0) :
    Triple (At 0x80005c88#64 (evenL ra s0 s1 s2 sp) M v.keepR2 outp)
      (At ra (retL ra s0 s1 s2 sp 0xfffffffffffffffd#64) (writeLog M []) v.keepR2 outp) := by
  ms_ctx
  seg_step msV2 ra [rd8 M (sp - 48 + 40), rd8 M (sp - 48 + 32)] [2, 9, 18, 10] abiKeysR2 [evenL] [retL]
    [h40, h32] hc

/-- At the first `__muldi3(b, x₀)` call (`5c20`). -/
def mulL (ra : BitVec 64) (sp b rp : Nat) (s2 x : BitVec 64) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 rp), (18, s2),
   (10, BitVec.ofNat 64 b), (11, x)]

/-- The frame stores: `s0`, `ra`, then `s1`, `s2`, `x₀`. -/
def proLog2 (s1 s2 : BitVec 64) (sp b : Nat) : List WEntry :=
  [(sp - 24, 8, s1), (sp - 32, 8, s2), (sp - 40, 8, x0v b)]

def proLog (ra s0 s1 s2 : BitVec 64) (sp b : Nat) : List WEntry := evenLog ra s0 sp ++ proLog2 s1 s2 sp b

/-- `b` odd (`5bfc`). -/
def oddL (ra s1 s2 : BitVec 64) (sp b rp : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 b), (9, s1), (18, s2), (11, BitVec.ofNat 64 rp)]

theorem pro1_step (ra s0 s1 s2 : BitVec 64) (v : Abi) (outp : Array String) (sp p dp b rp : Nat) (m : Mem)
    (hc : CodeAt m mpMontgomerySetupBase mpMontgomerySetupCode) (hs : SFacts sp) (hl : LFacts m p dp b)
    (hd : dp + 4 ≤ sp - 48 ∨ sp ≤ dp) (ho : (BitVec.ofNat 64 b &&& 1#64 == 0#64) = false) :
    Triple (At entry (entryL ra s0 s1 s2 sp p rp) m v.keepR2 outp)
      (At 0x80005bfc#64 (oddL ra s1 s2 sp b rp) (writeLog m (evenLog ra s0 sp)) v.keepR2 outp) := by
  ms_ctx
  have h1 := hl.dpv; have h2 := hl.bv
  seg_step msP1 0x80005bfc#64 [rd8 m (p + 16), rd4 m dp] [1, 2, 8, 9, 18, 10, 11] abiKeysR2
    [entry, entryL, evenLog] [oddL] [h1, h2, ho] hc

theorem pro2_step (ra s1 s2 : BitVec 64) (v : Abi) (outp : Array String) (sp b rp : Nat) (M : Mem)
    (hc : CodeAt M mpMontgomerySetupBase mpMontgomerySetupCode) (hs : SFacts sp) :
    Triple (At 0x80005bfc#64 (oddL ra s1 s2 sp b rp) M v.keepR2 outp)
      (At 0x80005c20#64 (mulL ra sp b rp s2 (x0v b)) (writeLog M (proLog2 s1 s2 sp b)) v.keepR2 outp) := by
  ms_ctx
  have e1 : (sp - 48 + 24) % 18446744073709551616 = sp - 24 := by omega
  have e2 : (sp - 48 + 16) % 18446744073709551616 = sp - 32 := by omega
  have e3 : (sp - 48 + 8) % 18446744073709551616 = sp - 40 := by omega
  seg_step msP2 0x80005c20#64 ([] : List (List (BitVec 8))) [1, 2, 8, 9, 18, 11] abiKeysR2
    [oddL, proLog2, x0v] [mulL, x0v] [e1, e2, e3] hc

theorem pro_step (ra s0 s1 s2 : BitVec 64) (v : Abi) (outp : Array String) (sp p dp b rp : Nat) (m : Mem)
    (hc : CodeAt m mpMontgomerySetupBase mpMontgomerySetupCode) (hs : SFacts sp) (hl : LFacts m p dp b)
    (hd : dp + 4 ≤ sp - 48 ∨ sp ≤ dp) (ho : (BitVec.ofNat 64 b &&& 1#64 == 0#64) = false) :
    Triple (At entry (entryL ra s0 s1 s2 sp p rp) m v.keepR2 outp)
      (At 0x80005c20#64 (mulL ra sp b rp s2 (x0v b)) (writeLog m (proLog ra s0 s1 s2 sp b)) v.keepR2 outp) := by
  have hc1 : CodeAt (writeLog m (evenLog ra s0 sp)) mpMontgomerySetupBase mpMontgomerySetupCode :=
    hc.of_eq fun x h1 h2 => writeLog_out _ _ _ (by
      have := hs.code_off; have e : mpMontgomerySetupCode.length = 48 := rfl
      rw [e] at h2
      exact ⟨by simp only; omega, by simp only; omega, trivial⟩)
  rw [proLog, writeLog_append]
  exact Triple.seq (pro1_step ra s0 s1 s2 v outp sp p dp b rp m hc hs hl hd ho) (pro2_step ra s1 s2 v outp sp b rp _ hc1 hs)

/-- Back from a `__muldi3` with `a0 = y`. -/
def backL (sp b rp : Nat) (s2 y : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 rp), (18, s2), (10, y)]

/-- At a `__muldi3(2 - y, x)` call. -/
def mul2L (sp b rp : Nat) (y x : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 rp), (18, 2#64),
   (10, sub2 y), (11, x)]

theorem a1_step (v : Abi) (outp : Array String) (sp b rp : Nat) (s2 y x : BitVec 64) (M : Mem)
    (hc : CodeAt M mpMontgomerySetupBase mpMontgomerySetupCode) (hs : SFacts sp) (h8 : bytesT8 M (sp - 48 + 8) = x) :
    Triple (At 0x80005c24#64 (backL sp b rp s2 y) M v.keepR2 outp)
      (At 0x80005c30#64 (mul2L sp b rp y x) (writeLog M []) v.keepR2 outp) := by
  ms_ctx
  seg_step msA1 0x80005c30#64 [rd8 M (sp - 48 + 8)] [2, 8, 9, 18, 10] abiKeysR2 [backL] [mul2L, sub2] [h8] hc

theorem a2_step (v : Abi) (outp : Array String) (sp b rp : Nat) (y x : BitVec 64) (M : Mem)
    (hc : CodeAt M mpMontgomerySetupBase mpMontgomerySetupCode) (hs : SFacts sp) (h8 : bytesT8 M (sp - 48 + 8) = x) :
    Triple (At 0x80005c44#64 (backL sp b rp 2#64 y) M v.keepR2 outp)
      (At 0x80005c4c#64 (mul2L sp b rp y x) (writeLog M []) v.keepR2 outp) := by
  ms_ctx
  seg_step msA2 0x80005c4c#64 [rd8 M (sp - 48 + 8)] [2, 8, 9, 18, 10] abiKeysR2 [backL] [mul2L, sub2] [h8] hc

theorem a3_step (v : Abi) (outp : Array String) (sp b rp : Nat) (y x : BitVec 64) (M : Mem)
    (hc : CodeAt M mpMontgomerySetupBase mpMontgomerySetupCode) (hs : SFacts sp) (h8 : bytesT8 M (sp - 48 + 8) = x) :
    Triple (At 0x80005c60#64 (backL sp b rp 2#64 y) M v.keepR2 outp)
      (At 0x80005c68#64 (mul2L sp b rp y x) (writeLog M []) v.keepR2 outp) := by
  ms_ctx
  seg_step msA3 0x80005c68#64 [rd8 M (sp - 48 + 8)] [2, 8, 9, 18, 10] abiKeysR2 [backL] [mul2L, sub2] [h8] hc

/-- At a `__muldi3(b, x)` call after a step. -/
def mul1L (sp b rp : Nat) (x : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 rp), (18, 2#64),
   (10, BitVec.ofNat 64 b), (11, x)]

theorem b1_step (v : Abi) (outp : Array String) (sp b rp : Nat) (z : BitVec 64) (M : Mem)
    (hc : CodeAt M mpMontgomerySetupBase mpMontgomerySetupCode) (hs : SFacts sp) :
    Triple (At 0x80005c34#64 (backL sp b rp 2#64 z) M v.keepR2 outp)
      (At 0x80005c40#64 (mul1L sp b rp (sx z)) (writeLog M [(sp - 40, 8, sx z)]) v.keepR2 outp) := by
  ms_ctx
  seg_step msB1 0x80005c40#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 10] abiKeysR2 [backL, sx] [mul1L, sx] [] hc

theorem b2_step (v : Abi) (outp : Array String) (sp b rp : Nat) (z : BitVec 64) (M : Mem)
    (hc : CodeAt M mpMontgomerySetupBase mpMontgomerySetupCode) (hs : SFacts sp) :
    Triple (At 0x80005c50#64 (backL sp b rp 2#64 z) M v.keepR2 outp)
      (At 0x80005c5c#64 (mul1L sp b rp (sx z)) (writeLog M [(sp - 40, 8, sx z)]) v.keepR2 outp) := by
  ms_ctx
  seg_step msB2 0x80005c5c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 10] abiKeysR2 [backL, sx] [mul1L, sx] [] hc

/-- After the last `__muldi3`: `*rho := (-y) & MP_MASK` (`5c7c`). -/
def endL (sp b rp : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 rp), (18, 2#64)]

theorem e1_step (v : Abi) (outp : Array String) (sp b rp : Nat) (y : BitVec 64) (M : Mem)
    (hc : CodeAt M mpMontgomerySetupBase mpMontgomerySetupCode) (hr : Ram rp 4) (hra : rp % 4 = 0)
    (hrc : rp + 4 ≤ mpMontgomerySetupBase ∨ mpMontgomerySetupBase + 192 ≤ rp) :
    Triple (At 0x80005c6c#64 (backL sp b rp 2#64 y) M v.keepR2 outp)
      (At 0x80005c7c#64 (endL sp b rp) (writeLog M [(rp, 4, rhov y)]) v.keepR2 outp) := by
  ms_ctx
  have h0 : rp % 18446744073709551616 = rp := Nat.mod_eq_of_lt (by omega)
  seg_step msE1 0x80005c7c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 10] abiKeysR2 [backL, rhov] [endL]
    [h0] hc

theorem e2_step (ra s0 s1 s2 : BitVec 64) (v : Abi) (outp : Array String) (sp b rp : Nat) (M : Mem)
    (hc : CodeAt M mpMontgomerySetupBase mpMontgomerySetupCode) (hra : ra.toNat % 4 = 0) (hs : SFacts sp)
    (h16 : bytesT8 M (sp - 48 + 16) = s2) (h24 : bytesT8 M (sp - 48 + 24) = s1)
    (h40 : bytesT8 M (sp - 48 + 40) = ra) (h32 : bytesT8 M (sp - 48 + 32) = s0) :
    Triple (At 0x80005c7c#64 (endL sp b rp) M v.keepR2 outp)
      (At ra (retL ra s0 s1 s2 sp 0#64) (writeLog M []) v.keepR2 outp) := by
  ms_ctx
  seg_step msE2 ra [rd8 M (sp - 48 + 16), rd8 M (sp - 48 + 24), rd8 M (sp - 48 + 40), rd8 M (sp - 48 + 32)]
    [2, 8, 9, 18] abiKeysR2 [endL] [retL] [h16, h24, h40, h32] hc

/-! ## The values in `Nat` -/

open Tom.Mont in
section
theorem sext_lo (z : BitVec 32) : (BitVec.signExtend 64 z).toNat % 2^32 = z.toNat := by
  rw [BitVec.toNat_signExtend]
  have := z.isLt
  split <;> simp <;> omega
theorem ext_lo (y : BitVec 64) : (BitVec.extractLsb 31 0 y).toNat = y.toNat % 2^32 := by
  simp [BitVec.extractLsb_toNat]
theorem rhov_lo (y : BitVec 64) : (rhov y).toNat % 2^32 = (2^32 - y.toNat % 2^32) % 2^32 % 2^28 := by
  unfold rhov Sail.shift_bits_right Sail.shift_bits_left
  rw [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  have h := sext_lo (0#32 - BitVec.extractLsb 31 0 y)
  rw [BitVec.toNat_sub, ext_lo] at h
  generalize (BitVec.signExtend 64 (0#32 - BitVec.extractLsb 31 0 y)).toNat = t at h ⊢
  have e6 : (36#6 : BitVec 6).toNat = 36 := rfl
  rw [e6, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 64 = 2 ^ 28 * 2 ^ 36 from rfl, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.two_pow_pos 36)]
  simp only [BitVec.toNat_ofNat] at h
  omega
theorem and_eight (n : Nat) : n &&& 8 = (n % 16) &&& 8 := by
  have h1 : (n &&& 8) % 2 ^ 4 = (n % 2 ^ 4) &&& (8 % 2 ^ 4) := Nat.and_mod_two_pow
  have h2 : n &&& 8 < 2 ^ 4 := Nat.and_lt_two_pow n (by decide)
  rw [Nat.mod_eq_of_lt h2] at h1
  exact h1
theorem small : ∀ r, r < 8 → (2 * r) &&& 8 = (r &&& 4) * 2 := by decide
theorem x0v_lo (b : Nat) (hb : b < 2 ^ 28) : (x0v b).toNat % 2^32 = setupX0 b := by
  unfold x0v setupX0
  rw [sext_lo, BitVec.toNat_add, ext_lo, BitVec.toNat_and]
  have hA : (BitVec.signExtend 64 (BitVec.ofNat 32 ((b * 2 + 4) % 4294967296))).toNat = b * 2 + 4 := by
    rw [BitVec.toNat_signExtend]
    have hm : (BitVec.ofNat 32 ((b * 2 + 4) % 4294967296)).msb = false := by
      rw [BitVec.msb_eq_decide]; simp; omega
    simp [hm]; omega
  rw [hA, show (8#64 : BitVec 64).toNat = 8 from rfl, and_eight, Nat.shiftLeft_eq, and_four (b + 2)]
  rw [show (b * 2 + 4) % 16 = 2 * ((b + 2) % 8) by omega, small _ (by omega)]
  have : (b + 2) % 8 &&& 4 ≤ 4 := Nat.and_le_right
  simp only [BitVec.toNat_ofNat]
  omega

theorem sx_lo (y : BitVec 64) : (sx y).toNat % 2^32 = y.toNat % 2^32 := by
  rw [sx, sext_lo, ext_lo]

theorem sub2_lo (y : BitVec 64) : (sub2 y).toNat % 2^32 = (2 + 2^32 - y.toNat % 2^32) % 2^32 := by
  rw [sub2, sext_lo, BitVec.toNat_sub, ext_lo]
  simp; omega

theorem mul_lo (x y : BitVec 64) : (x * y).toNat % 2^32 = x.toNat % 2^32 * (y.toNat % 2^32) % 2^32 := by
  rw [BitVec.toNat_mul, Nat.mod_mod_of_dvd _ (by decide : 2^32 ∣ 2^64), Nat.mul_mod]

/-- One machine Newton step is `newton`. -/
theorem step_lo (b : Nat) (hb : b < 2 ^ 32) (x : BitVec 64) :
    (sub2 (BitVec.ofNat 64 b * x) * x).toNat % 2 ^ 32 = newton b (x.toNat % 2 ^ 32) := by
  rw [mul_lo, sub2_lo, mul_lo]
  simp only [BitVec.toNat_ofNat, newton, Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega), Nat.mod_eq_of_lt hb,
    Nat.mod_mod]
  rw [Nat.mul_comm]

/-- The value the machine stores in `*rho` is `setupRho b`. -/
theorem rho_lo (b : Nat) (hb : b < 2 ^ 28) :
    (rhov (sub2 (BitVec.ofNat 64 b * sx (sub2 (BitVec.ofNat 64 b * sx (sub2 (BitVec.ofNat 64 b * x0v b) * x0v b)) *
      sx (sub2 (BitVec.ofNat 64 b * x0v b) * x0v b))) *
      sx (sub2 (BitVec.ofNat 64 b * sx (sub2 (BitVec.ofNat 64 b * x0v b) * x0v b)) *
        sx (sub2 (BitVec.ofNat 64 b * x0v b) * x0v b)))).toNat % 2 ^ 32 = setupRho b := by
  have h32 : b < 2 ^ 32 := by omega
  rw [rhov_lo, step_lo b h32, sx_lo, step_lo b h32, sx_lo, step_lo b h32, x0v_lo b hb, setupRho_eq]
  have hx : setupX b < 2 ^ 32 := Nat.mod_lt _ (by decide)
  unfold setupX at hx ⊢
  simp only [radix, Layout.digitBits]
  omega

end

/-- The word `sw` leaves at `rp`. -/
theorem rho_read (M : Mem) (rp : Nat) (y : BitVec 64) :
    bytesT4 (writeLog M [(rp, 4, y)]) rp = BitVec.ofNat 32 (y.toNat % 2 ^ 32) := by
  rw [writeLog_sw, bytesT4_wm4_self]
  apply BitVec.eq_of_toNat_eq
  simp [swData, Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]

/-- A doubleword read past a later store. -/
theorem bytesT8_past (X : Mem) (a t w : Nat) (y : BitVec 64) (h : a + 8 ≤ t ∨ t + w ≤ a) :
    bytesT8 (writeLog X [(t, w, y)]) a = bytesT8 X a :=
  bytesT8_congr fun x h1 h2 => writeLog_out _ _ _ ⟨by simp only; omega, trivial⟩

/-- The machine's Newton iterates. -/
def zz1 (b : Nat) : BitVec 64 := sub2 (BitVec.ofNat 64 b * x0v b) * x0v b
def xx1 (b : Nat) : BitVec 64 := sx (zz1 b)
def zz2 (b : Nat) : BitVec 64 := sub2 (BitVec.ofNat 64 b * xx1 b) * xx1 b
def xx2 (b : Nat) : BitVec 64 := sx (zz2 b)
def zz3 (b : Nat) : BitVec 64 := sub2 (BitVec.ofNat 64 b * xx2 b) * xx2 b

theorem rho_zz (b : Nat) (hb : b < 2 ^ 28) : (rhov (zz3 b)).toNat % 2 ^ 32 = Tom.Mont.setupRho b := by
  unfold zz3 xx2 zz2 xx1 zz1; exact rho_lo b hb

end Tom.Machine.Fn.MpMontSetup
