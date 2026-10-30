import Tom.Machine.Seg.Reduce2k
import Tom.Machine.Repr
import Tom.Machine.Kit.Leaf
import Tom.Machine.Code
import Tom.Machine.Kit.Word
import Vsa.Sim.TripleCat

/-!
# `mp_reduce_is_2k` on the machine: the segments

`mp_reduce_is_2k(a)` at `0x80001d14` (40 instructions, a 16-byte frame, one call):
```
1d14 lw a3,0(a0); beqz a3,1d98                          -- used == 0: MP_NO
1d1c li a5,1; blt a5,a3,1d2c; li a0,1; ret              -- used <= 1: MP_YES
1d2c addi sp,sp,-16; sd s0,0(sp); sd ra,8(sp); mv s0,a0; jal mp_count_bits
1d40 li a3,28; bge a3,a0,1d84                           -- iy <= 28: MP_YES
1d48 ld a1,16(s0); li a5,1; mv a2,a5; lui a6,0x10000    -- iz = 1, iw = 1
1d58 slli a4,a2,2; add a4,a1,a4; lw a4,0(a4)            -- loop head (ix in a3)
     addiw a3,a3,1; and a4,a4,a5; slliw a5,a5,1; beqz a4,1da0   -- bit clear: MP_NO
1d74 bltu a5,a6,1d80; addiw a2,a2,1; li a5,1            -- iz past the digit: next digit
1d80 bne a0,a3,1d58
1d84 ld ra,8(sp); ld s0,0(sp); li a0,1; addi sp,sp,16; ret
1d98 li a0,0; ret
1da0 ld ra,8(sp); ld s0,0(sp); li a0,0; addi sp,sp,16; ret
```
-/


namespace Tom.Machine.Fn.Reduce2k

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "r2k_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpReduceIs2kBase = 0x80001d14 := rfl
   have : mpReduceIs2kCode.length = 40 := rfl))

def entryL (ra s0 : BitVec 64) (sp pa : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa)]

/-- Registers at the return with result `r`. -/
def retL (ra s0 : BitVec 64) (sp : Nat) (r : BitVec 64) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, r)]

/-- At the `mp_count_bits` call (`1d3c`). -/
def callL (ra : BitVec 64) (sp pa : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 16)), (8, BitVec.ofNat 64 pa), (10, BitVec.ofNat 64 pa)]

/-- After it (`1d40`), with `a0 = iy`. -/
def aftL (sp pa iy : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 16)), (8, BitVec.ofNat 64 pa), (10, BitVec.ofNat 64 iy)]

/-- The loop head (`1d58`): `ix`, `iw`, `iz`. -/
def headL (sp pa iy adp ix iw iz : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 16)), (8, BitVec.ofNat 64 pa), (10, BitVec.ofNat 64 iy), (11, BitVec.ofNat 64 adp),
   (12, BitVec.ofNat 64 iw), (13, BitVec.ofNat 64 ix), (15, BitVec.ofNat 64 iz), (16, BitVec.ofNat 64 268435456)]

/-- The frame stores. -/
def frameLog (ra s0 : BitVec 64) (sp : Nat) : List WEntry := [(sp - 16, 8, s0), (sp - 16 + 8, 8, ra)]

/-- The stack frame. -/
structure FFacts (sp : Nat) : Prop where
  rs : Ram (sp - 16) 16
  sp_al : sp % 16 = 0
  sp_ge : 16 ≤ sp
  code_off : sp ≤ mpReduceIs2kBase ∨ mpReduceIs2kBase + 160 ≤ sp - 16

/-- The saved frame. -/
structure RFacts (M : Mem) (ra s0 : BitVec 64) (sp : Nat) : Prop where
  rs : Ram (sp - 16) 16
  sp_ge : 16 ≤ sp
  s0_v : bytesT8 M (sp - 16) = s0
  ra_v : bytesT8 M (sp - 16 + 8) = ra

/-- Digit `iw`'s load and the loop bounds. -/
structure DFacts (M : Mem) (adp iy ix iw iz d : Nat) : Prop where
  rd : Ram (adp + 4 * iw) 4
  d_v : bytesT4 M (adp + 4 * iw) = BitVec.ofNat 32 d
  d_lt : d < 2 ^ 31
  iy_lt : iy < 2 ^ 31
  ix_lt : ix < iy
  iw_lt : iw < 2 ^ 31
  iz_le : iz ≤ 2 ^ 27

theorem DFacts.sx {M : Mem} {adp iy ix iw iz d : Nat} (h : DFacts M adp iy ix iw iz d) :
    BitVec.signExtend 64 (bytesT4 M (adp + 4 * iw)) = BitVec.ofNat 64 d := by
  rw [h.d_v, signExtend_ofNat32 _ h.d_lt]

/-- `slli a4,a2,2`: the digit offset. -/
theorem shl2 (iw : Nat) : Sail.shift_bits_left (BitVec.ofNat 64 iw) (2#6) = BitVec.ofNat 64 (4 * iw) := by
  rw [shl_ofNatW' iw 2 4 (by decide) (by decide), Nat.mul_comm]

/-- `slliw a5,a5,1`: `iz` doubled. -/
theorem shlw1 (iz : Nat) (h : iz ≤ 2 ^ 27) :
    BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.extractLsb 31 0 (BitVec.ofNat 64 iz)) (1#5)) =
      BitVec.ofNat 64 (2 * iz) := by
  rw [extractLsb_ofNatW _ (by omega), shl_ofNatW' _ _ 2 (by decide) (by decide), sext_ofNatW (by decide) _ (by omega),
    Nat.mul_comm]

section
variable (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa : Nat)

theorem zero_step (m : Mem) (hc : CodeAt m mpReduceIs2kBase mpReduceIs2kCode) (hra : ra.toNat % 4 = 0)
    (hf : UFacts m pa 0) :
    Triple (At 0x80001d14#64 (entryL ra s0 sp pa) m v.keepR outp)
      (At ra (retL ra s0 sp 0#64) (writeLog m []) v.keepR outp) := by
  r2k_ctx
  have h1 := hf.sx
  seg_step tZero ra [rd4 m pa] [1, 2, 8, 10] abiKeysR [entryL] [retL] [h1] hc

theorem one_step (m : Mem) (hc : CodeAt m mpReduceIs2kBase mpReduceIs2kCode) (hra : ra.toNat % 4 = 0)
    (hf : UFacts m pa 1) :
    Triple (At 0x80001d14#64 (entryL ra s0 sp pa) m v.keepR outp)
      (At ra (retL ra s0 sp 1#64) (writeLog m []) v.keepR outp) := by
  r2k_ctx
  have h1 := hf.sx
  seg_step tOne ra [rd4 m pa] [1, 2, 8, 10] abiKeysR [entryL] [retL] [h1] hc

theorem call_step (m : Mem) (hc : CodeAt m mpReduceIs2kBase mpReduceIs2kCode) (u : Nat) (hf : UFacts m pa u)
    (hu : 2 ≤ u) (hs : FFacts sp) :
    Triple (At 0x80001d14#64 (entryL ra s0 sp pa) m v.keepR outp)
      (At 0x80001d3c#64 (callL ra sp pa) (writeLog m (frameLog ra s0 sp)) v.keepR outp) := by
  r2k_ctx
  have h1 := hf.sx
  seg_step tCall 0x80001d3c#64 [rd4 m pa] [1, 2, 8, 10] abiKeysR [entryL, frameLog] [callL] [h1] hc

variable (M : Mem) (hc : CodeAt M mpReduceIs2kBase mpReduceIs2kCode) (hr : RFacts M ra s0 sp)
include hc hr

theorem short_step (hra : ra.toNat % 4 = 0) (iy : Nat) (hy : iy ≤ 28) (hy' : iy < 2 ^ 31) :
    Triple (At 0x80001d40#64 (aftL sp pa iy) M v.keepR outp)
      (At ra (retL ra s0 sp 1#64) (writeLog M []) v.keepR outp) := by
  r2k_ctx
  have := hy'
  have h1 := hr.s0_v; have h2 := hr.ra_v
  seg_step tShort ra [rd8 M (sp - 16 + 8), rd8 M (sp - 16)] [2, 8, 10] abiKeysR [aftL] [retL] [h1, h2] hc

omit hr in
theorem enter_step (iy adp : Nat) (hy : 28 < iy) (hy' : iy < 2 ^ 31) (hpa : Ram pa 24)
    (hdp : bytesT8 M (pa + 16) = BitVec.ofNat 64 adp) :
    Triple (At 0x80001d40#64 (aftL sp pa iy) M v.keepR outp)
      (At 0x80001d58#64 (headL sp pa iy adp 28 1 1) (writeLog M []) v.keepR outp) := by
  r2k_ctx
  seg_step tEnter 0x80001d58#64 [rd8 M (pa + 16)] [2, 8, 10] abiKeysR [aftL] [headL] [hdp] hc

omit hr in
/-- Bit `ix` set, `iz` still inside the digit, more bits to test. -/
theorem next_step (iy adp ix iw iz d : Nat) (hf : DFacts M adp iy ix iw iz d)
    (hand : BitVec.ofNat 64 d &&& BitVec.ofNat 64 iz = BitVec.ofNat 64 iz) (hz : 0 < iz) (hz2 : 2 * iz < 2 ^ 28)
    (hn : ix + 1 ≠ iy) :
    Triple (At 0x80001d58#64 (headL sp pa iy adp ix iw iz) M v.keepR outp)
      (At 0x80001d58#64 (headL sp pa iy adp (ix + 1) iw (2 * iz)) (writeLog M []) v.keepR outp) := by
  r2k_ctx
  have h1 := hf.sx
  have h2 := shl2 iw
  have h3 := shlw1 iz hf.iz_le
  seg_stepw tNext 0x80001d58#64 [rd4 M (adp + 4 * iw)] [2, 8, 10, 11, 12, 13, 15, 16] abiKeysR [headL] [headL]
    [h1, h2, h3, hand, Vsa.Sim.shamtOf, Vsa.Sim.shamt5Of, BitVec.reduceExtractLsb', BitVec.reduceExtractLsb] hc using
    ((repeat' apply And.intro) <;> first | exact True.intro | (congr 1; omega))


omit hr in
/-- Bit `ix` set, the last bit of digit `iw`, more bits to test. -/
theorem nextW_step (iy adp ix iw iz d : Nat) (hf : DFacts M adp iy ix iw iz d)
    (hand : BitVec.ofNat 64 d &&& BitVec.ofNat 64 iz = BitVec.ofNat 64 iz) (hz2 : 2 * iz = 2 ^ 28)
    (hn : ix + 1 ≠ iy) :
    Triple (At 0x80001d58#64 (headL sp pa iy adp ix iw iz) M v.keepR outp)
      (At 0x80001d58#64 (headL sp pa iy adp (ix + 1) (iw + 1) 1) (writeLog M []) v.keepR outp) := by
  r2k_ctx
  have h1 := hf.sx
  have h2 := shl2 iw
  have h3 := shlw1 iz hf.iz_le
  seg_stepw tNextW 0x80001d58#64 [rd4 M (adp + 4 * iw)] [2, 8, 10, 11, 12, 13, 15, 16] abiKeysR [headL] [headL]
    [h1, h2, h3, hand, Vsa.Sim.shamtOf, Vsa.Sim.shamt5Of, BitVec.reduceExtractLsb', BitVec.reduceExtractLsb] hc using
    ((repeat' apply And.intro) <;> first | exact True.intro | (congr 1; omega))

/-- Bit `ix` set, inside the digit, the last bit: `MP_YES`. -/
theorem yes_step (hra : ra.toNat % 4 = 0) (iy adp ix iw iz d : Nat) (hf : DFacts M adp iy ix iw iz d)
    (hand : BitVec.ofNat 64 d &&& BitVec.ofNat 64 iz = BitVec.ofNat 64 iz) (hz : 0 < iz) (hz2 : 2 * iz < 2 ^ 28)
    (hn : ix + 1 = iy) :
    Triple (At 0x80001d58#64 (headL sp pa iy adp ix iw iz) M v.keepR outp)
      (At ra (retL ra s0 sp 1#64) (writeLog M []) v.keepR outp) := by
  r2k_ctx
  have h1 := hf.sx
  have h2 := shl2 iw
  have h3 := shlw1 iz hf.iz_le
  have h4 := hr.s0_v; have h5 := hr.ra_v
  seg_stepw tYes ra [rd4 M (adp + 4 * iw), rd8 M (sp - 16 + 8), rd8 M (sp - 16)] [2, 8, 10, 11, 12, 13, 15, 16] abiKeysR
    [headL] [retL] [h1, h2, h3, h4, h5, hand, Vsa.Sim.shamtOf, Vsa.Sim.shamt5Of, BitVec.reduceExtractLsb', BitVec.reduceExtractLsb] hc using
    ((repeat' apply And.intro) <;> first | exact True.intro | (congr 1; omega))

/-- Bit `ix` set, the last bit of the digit, the last bit: `MP_YES`. -/
theorem yesW_step (hra : ra.toNat % 4 = 0) (iy adp ix iw iz d : Nat) (hf : DFacts M adp iy ix iw iz d)
    (hand : BitVec.ofNat 64 d &&& BitVec.ofNat 64 iz = BitVec.ofNat 64 iz) (hz2 : 2 * iz = 2 ^ 28)
    (hn : ix + 1 = iy) :
    Triple (At 0x80001d58#64 (headL sp pa iy adp ix iw iz) M v.keepR outp)
      (At ra (retL ra s0 sp 1#64) (writeLog M []) v.keepR outp) := by
  r2k_ctx
  have h1 := hf.sx
  have h2 := shl2 iw
  have h3 := shlw1 iz hf.iz_le
  have h4 := hr.s0_v; have h5 := hr.ra_v
  seg_stepw tYesW ra [rd4 M (adp + 4 * iw), rd8 M (sp - 16 + 8), rd8 M (sp - 16)] [2, 8, 10, 11, 12, 13, 15, 16] abiKeysR
    [headL] [retL] [h1, h2, h3, h4, h5, hand, Vsa.Sim.shamtOf, Vsa.Sim.shamt5Of, BitVec.reduceExtractLsb', BitVec.reduceExtractLsb] hc using
    ((repeat' apply And.intro) <;> first | exact True.intro | (congr 1; omega))

/-- Bit `ix` clear: `MP_NO`. -/
theorem no_step (hra : ra.toNat % 4 = 0) (iy adp ix iw iz d : Nat) (hf : DFacts M adp iy ix iw iz d)
    (hand : BitVec.ofNat 64 d &&& BitVec.ofNat 64 iz = BitVec.ofNat 64 0) :
    Triple (At 0x80001d58#64 (headL sp pa iy adp ix iw iz) M v.keepR outp)
      (At ra (retL ra s0 sp 0#64) (writeLog M []) v.keepR outp) := by
  r2k_ctx
  have h1 := hf.sx
  have h2 := shl2 iw
  have h3 := shlw1 iz hf.iz_le
  have h4 := hr.s0_v; have h5 := hr.ra_v
  seg_stepw tNo ra [rd4 M (adp + 4 * iw), rd8 M (sp - 16 + 8), rd8 M (sp - 16)] [2, 8, 10, 11, 12, 13, 15, 16] abiKeysR
    [headL] [retL] [h1, h2, h3, h4, h5, hand, Vsa.Sim.shamtOf, Vsa.Sim.shamt5Of, BitVec.reduceExtractLsb', BitVec.reduceExtractLsb] hc using
    ((repeat' apply And.intro) <;> first | exact True.intro | (congr 1; omega))

end

end Tom.Machine.Fn.Reduce2k
