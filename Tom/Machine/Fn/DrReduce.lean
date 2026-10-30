import Tom.Machine.Seg.DrReduce
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.MulCall
import Vsa.Sim.TripleCat

/-!
# `mp_dr_reduce` on the machine: the segments

`mp_dr_reduce(x, n, k)` at `0x800055e4` (106 instructions), frame `128` bytes:
the spills `4 m` at `sp - 128` and `4 (m - 1)` at `sp - 120` (`m = n->used`),
the saved `ra`, `s0`–`s11` at `[sp - 104, sp)`.

* prologue `d1`–`d4b` (`x->alloc ≥ 2 m`: the `mp_grow` branch is excluded, D5);
* `top` (`5664`): `t0` (`m > 0`) into the digit loop at `5680`: `iA` (load
  `x[m + i]`) → `jal __muldi3(x[m + i], k)` at `568c` → `iBt`/`iBf` (`r = x[m +
  i] k + x[i] + mu`, store `x[i]`, the carry); `f1` (`x[m] := mu`), `f2t`
  (`x->used - m ≤ 1`) / `f2m` → `jal memset(&x[m + 1], 0, …)` at `56e8`; `f3`
  → `jal mp_clamp(x)` at `56f0`; `f4` → `jal mp_cmp_mag(x, n)` at `56fc`;
  `f5t` (`MP_LT`: return) / `f5f` → `jal s_mp_sub(x, n, x)` at `5710` → `f6`
  (`MP_OKAY`: back to `top`);
* the epilogue `e`.

All of `s0`–`s11` are locals: the segments keep only `gp` and `tp` (`kF`);
between the calls the loop's registers are `uL` (`s1 = k`, `s2 = MP_MASK`,
`s4 = x`, `s5 = m`, `s6 = n`, `s8 = -1`, `s9 = 1`; the others are parameters).
-/


namespace Tom.Machine.Fn.DrReduce

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "dr_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpDrReduceBase = 0x800055e4 := rfl
   have : mpDrReduceCode.length = 106 := rfl))

/-- The registers every segment keeps. -/
def kF (v : Abi) : GRegs := [(3, v.gp), (4, v.tp)]

abbrev kFKeys : List Nat := [3, 4]

/-- `MP_MASK`, `-1`. -/
abbrev mask : BitVec 64 := 268435455#64
abbrev m1 : BitVec 64 := 18446744073709551615#64

/-- The frame (with the 48 bytes of `s_mp_sub` below it). -/
structure KF (sp : Nat) : Prop where
  rs : Ram (sp - 176) 176
  sp_al : sp % 16 = 0
  sp_ge : 176 ≤ sp
  code_off : sp ≤ mpDrReduceBase ∨ mpDrReduceBase + 424 ≤ sp - 176

/-! ## The prologue -/

def entL (ra s0 : BitVec 64) (v : Abi) (sp px pn k : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, v.s.s1), (10, BitVec.ofNat 64 px), (11, BitVec.ofNat 64 pn),
   (12, BitVec.ofNat 64 k), (18, v.s.s2), (19, v.s.s3), (20, v.s.s4), (21, v.s.s5), (22, v.s.s6), (23, v.s.s7),
   (24, v.s.s8), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

def d1L (ra s0 : BitVec 64) (v : Abi) (sp px pn k : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 128)), (8, s0), (9, v.s.s1), (10, BitVec.ofNat 64 px),
   (11, BitVec.ofNat 64 pn), (12, BitVec.ofNat 64 k), (18, v.s.s2), (19, v.s.s3), (20, v.s.s4), (21, v.s.s5),
   (22, v.s.s6), (23, v.s.s7), (24, v.s.s8), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

theorem d1_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp px pn k : Nat) (m : Mem)
    (hc : CodeAt m mpDrReduceBase mpDrReduceCode) (hk : KF sp) :
    Triple (At 0x800055e4#64 (entL ra s0 v sp px pn k) m (kF v) outp)
      (At 0x800055ec#64 (d1L ra s0 v sp px pn k) (writeLog m [(sp - 56, 8, v.s.s5)]) (kF v) outp) := by
  dr_ctx
  seg_step drD1 0x800055ec#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [entL] [d1L] [] hc

def d2L (ra s0 : BitVec 64) (v : Abi) (sp px pn k nm al : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 128)), (8, s0), (9, v.s.s1), (10, BitVec.ofNat 64 px),
   (11, BitVec.ofNat 64 pn), (12, BitVec.ofNat 64 k), (15, BitVec.ofNat 64 al), (18, v.s.s2), (19, v.s.s3),
   (20, v.s.s4), (21, BitVec.ofNat 64 nm), (22, v.s.s6), (23, v.s.s7), (24, v.s.s8), (25, v.s.s9), (26, v.s.s10),
   (27, v.s.s11)]

/-- `n->used`, `x->alloc`. -/
structure D2Facts (m : Mem) (px pn nm al : Nat) : Prop where
  rx : Ram px 24
  rn : Ram pn 24
  m_v : bytesT4 m pn = BitVec.ofNat 32 nm
  al_v : bytesT4 m (px + 4) = BitVec.ofNat 32 al
  m_lt : nm < 2 ^ 30
  al_lt : al < 2 ^ 31

theorem d2_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp px pn k nm al : Nat) (m : Mem)
    (hc : CodeAt m mpDrReduceBase mpDrReduceCode) (hf : D2Facts m px pn nm al) :
    Triple (At 0x800055ec#64 (d1L ra s0 v sp px pn k) m (kF v) outp)
      (At 0x800055f4#64 (d2L ra s0 v sp px pn k nm al) (writeLog m []) (kF v) outp) := by
  dr_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 m pn) = BitVec.ofNat 64 nm := by
    rw [hf.m_v, signExtend_ofNat32 _ (by have := hf.m_lt; omega)]
  have h2 : BitVec.signExtend 64 (bytesT4 m (px + 4)) = BitVec.ofNat 64 al := by
    rw [hf.al_v, signExtend_ofNat32 _ hf.al_lt]
  seg_step drD2 0x800055f4#64 [rd4 m pn, rd4 m (px + 4)]
    [1, 2, 8, 9, 10, 11, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [d1L] [d2L] [h1, h2] hc

def d3L (s0 : BitVec 64) (v : Abi) (sp px pn k nm : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 128)), (8, s0), (9, v.s.s1), (12, BitVec.ofNat 64 k), (18, v.s.s2), (19, v.s.s3),
   (20, BitVec.ofNat 64 px), (21, BitVec.ofNat 64 nm), (22, BitVec.ofNat 64 pn), (23, v.s.s7), (24, v.s.s8),
   (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

/-- The saves of `s4`, `s6`, `ra`; `x->alloc ≥ 2 m` (no `mp_grow`). -/
def log3 (ra : BitVec 64) (v : Abi) (sp : Nat) : List WEntry :=
  [(sp - 48, 8, v.s.s4), (sp - 64, 8, v.s.s6), (sp - 8, 8, ra)]

theorem d3_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp px pn k nm al : Nat) (m : Mem)
    (hc : CodeAt m mpDrReduceBase mpDrReduceCode) (hk : KF sp) (hnm : nm < 2 ^ 29) :
    Triple (At 0x800055f4#64 (d2L ra s0 v sp px pn k nm al) m (kF v) outp)
      (At 0x8000560c#64 ((11, BitVec.ofNat 64 (2 * nm)) :: (15, BitVec.ofNat 64 al) :: d3L s0 v sp px pn k nm)
        (writeLog m (log3 ra v sp)) (kF v) outp) := by
  dr_ctx
  seg_stepx drD3 0x8000560c#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 12, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [d2L, log3] [d3L] [] hc

/-- `x->alloc ≥ 2 m`: no `mp_grow`. -/
theorem d3b_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (sp px pn k nm al : Nat) (m : Mem)
    (hc : CodeAt m mpDrReduceBase mpDrReduceCode) (hnm : nm < 2 ^ 29) (hal : al < 2 ^ 31) (hroom : 2 * nm ≤ al) :
    Triple (At 0x8000560c#64 ((11, BitVec.ofNat 64 (2 * nm)) :: (15, BitVec.ofNat 64 al) :: d3L s0 v sp px pn k nm)
        m (kF v) outp)
      (At 0x80005610#64 (d3L s0 v sp px pn k nm) (writeLog m []) (kF v) outp) := by
  dr_ctx
  seg_step drD3b 0x80005610#64 ([] : List (List (BitVec 8)))
    [11, 15, 2, 8, 9, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [d3L] [d3L] [] hc

def d4L (s0 : BitVec 64) (v : Abi) (sp px pn k nm : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 128)), (8, s0), (9, BitVec.ofNat 64 (k * 4294967296)), (12, BitVec.ofNat 64 k),
   (14, BitVec.ofNat 64 (4 * (nm - 1))), (15, BitVec.ofNat 64 (4 * nm)), (18, 268435456#64), (19, v.s.s3),
   (20, BitVec.ofNat 64 px), (21, BitVec.ofNat 64 nm), (22, BitVec.ofNat 64 pn), (23, BitVec.ofNat 64 (nm - 1)),
   (24, v.s.s8), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

/-- The saves of `s7`, `s1`, `s2`. -/
def log4a (v : Abi) (sp : Nat) : List WEntry := [(sp - 72, 8, v.s.s7), (sp - 24, 8, v.s.s1), (sp - 32, 8, v.s.s2)]

theorem d4a_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (sp px pn k nm : Nat) (m : Mem)
    (hc : CodeAt m mpDrReduceBase mpDrReduceCode) (hk : KF sp) (hnm : 1 ≤ nm) (hnm' : nm < 2 ^ 29)
    (hk' : k < 2 ^ 32) :
    Triple (At 0x80005610#64 (d3L s0 v sp px pn k nm) m (kF v) outp)
      (At 0x80005634#64 (d4L s0 v sp px pn k nm) (writeLog m (log4a v sp)) (kF v) outp) := by
  dr_ctx
  seg_stepx drD4a 0x80005634#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [d3L, log4a] [d4L] [] hc

/-- Between the calls: `s1 = k`, `s2 = MP_MASK`, `s4 = x`, `s5 = m`, `s6 = n`, `s8 = -1`, `s9 = 1`. -/
def uL (sp px pn k nm : Nat) (j0 j3 j7 j10 j11 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 128)), (8, j0), (9, BitVec.ofNat 64 k), (18, mask), (19, j3), (20, BitVec.ofNat 64 px),
   (21, BitVec.ofNat 64 nm), (22, BitVec.ofNat 64 pn), (23, j7), (24, m1), (25, 1#64), (26, j10), (27, j11)]

/-- The saves of `s8`, `s9`, `s0`, `s3`, `s10`, `s11`. -/
def log4b (s0 : BitVec 64) (v : Abi) (sp : Nat) : List WEntry :=
  [(sp - 80, 8, v.s.s8), (sp - 88, 8, v.s.s9), (sp - 16, 8, s0), (sp - 40, 8, v.s.s3), (sp - 96, 8, v.s.s10),
   (sp - 104, 8, v.s.s11)]

def d4bL (s0 : BitVec 64) (v : Abi) (sp px pn k nm : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 128)), (8, s0), (9, BitVec.ofNat 64 k), (12, BitVec.ofNat 64 k),
   (14, BitVec.ofNat 64 (4 * (nm - 1))), (15, BitVec.ofNat 64 (4 * nm)), (18, 268435456#64), (19, v.s.s3),
   (20, BitVec.ofNat 64 px), (21, BitVec.ofNat 64 nm), (22, BitVec.ofNat 64 pn), (23, BitVec.ofNat 64 (nm - 1)),
   (24, v.s.s8), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

theorem d4b_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (sp px pn k nm : Nat) (m : Mem)
    (hc : CodeAt m mpDrReduceBase mpDrReduceCode) (hk : KF sp) (hk' : k < 2 ^ 32) :
    Triple (At 0x80005634#64 (d4L s0 v sp px pn k nm) m (kF v) outp)
      (At 0x80005650#64 (d4bL s0 v sp px pn k nm) (writeLog m (log4b s0 v sp)) (kF v) outp) := by
  dr_ctx
  seg_stepx drD4b 0x80005650#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 12, 14, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [d4L, log4b] [d4bL] [] hc

/-- The spills `4 (m - 1)`, `4 m`. -/
def log4c (sp nm : Nat) : List WEntry :=
  [(sp - 128 + 8, 8, BitVec.ofNat 64 (4 * (nm - 1))), (sp - 128, 8, BitVec.ofNat 64 (4 * nm))]

theorem d4c_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (sp px pn k nm : Nat) (m : Mem)
    (hc : CodeAt m mpDrReduceBase mpDrReduceCode) (hk : KF sp) :
    Triple (At 0x80005650#64 (d4bL s0 v sp px pn k nm) m (kF v) outp)
      (At 0x80005664#64 (uL sp px pn k nm s0 v.s.s3 (BitVec.ofNat 64 (nm - 1)) v.s.s10 v.s.s11)
        (writeLog m (log4c sp nm)) (kF v) outp) := by
  dr_ctx
  seg_step drD4c 0x80005664#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 12, 14, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [d4bL, log4c] [uL] [] hc

/-! ## The digit loop -/

/-- The digit loop's head `5680`, index `i`, carry `mu`. -/
abbrev iL (sp px pn k nm xdp i mu : Nat) : GRegs :=
  uL sp px pn k nm (BitVec.ofNat 64 (xdp + 4 * nm)) (BitVec.ofNat 64 xdp) (BitVec.ofNat 64 (xdp + 4 * (nm + i)))
    (BitVec.ofNat 64 mu) (BitVec.ofNat 64 (xdp + 4 * i))

/-- `x->dp`, the spill `4 m`. -/
structure T0Facts (M : Mem) (sp px xdp nm : Nat) : Prop where
  k : KF sp
  rx : Ram px 24
  xdp_v : bytesT8 M (px + 16) = BitVec.ofNat 64 xdp
  m4_v : bytesT8 M (sp - 128) = BitVec.ofNat 64 (4 * nm)
  m_pos : 1 ≤ nm
  m_lt : nm < 2 ^ 29

theorem t0_step (v : Abi) (outp : Array String) (sp px pn k nm xdp : Nat) (j0 j3 j7 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M mpDrReduceBase mpDrReduceCode) (hf : T0Facts M sp px xdp nm) :
    Triple (At 0x80005664#64 (uL sp px pn k nm j0 j3 j7 j10 j11) M (kF v) outp)
      (At 0x80005680#64 (iL sp px pn k nm xdp 0 0) (writeLog M []) (kF v) outp) := by
  dr_ctx
  have h1 := hf.xdp_v; have h2 := hf.m4_v
  seg_step drT0 0x80005680#64 [rd8 M (px + 16), rd8 M (sp - 128)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [uL] [iL, uL] [h1, h2] hc

/-- Across the `__muldi3` call: `s11` advanced. -/
abbrev kI (sp px pn k nm xdp i mu : Nat) : GRegs :=
  uL sp px pn k nm (BitVec.ofNat 64 (xdp + 4 * nm)) (BitVec.ofNat 64 xdp) (BitVec.ofNat 64 (xdp + 4 * (nm + i)))
    (BitVec.ofNat 64 mu) (BitVec.ofNat 64 (xdp + 4 * (i + 1)))

def jI (sp px pn k nm xdp i mu y : Nat) : GRegs :=
  (10, BitVec.ofNat 64 y) :: (11, BitVec.ofNat 64 k) :: kI sp px pn k nm xdp i mu

def rI (sp px pn k nm xdp i mu p : Nat) : GRegs := (10, BitVec.ofNat 64 p) :: kI sp px pn k nm xdp i mu

/-- A digit read. -/
structure DRead (M : Mem) (a y : Nat) : Prop where
  r : Ram a 4
  v : bytesT4 M a = BitVec.ofNat 32 y
  lt : y < 2 ^ 32

/-- The load `x[m + i]`, `a1 = k`, `s11 += 4`. -/
theorem iA_step (v : Abi) (outp : Array String) (sp px pn k nm xdp i mu y : Nat) (M : Mem)
    (hc : CodeAt M mpDrReduceBase mpDrReduceCode) (hf : DRead M (xdp + 4 * (nm + i)) y) :
    Triple (At 0x80005680#64 (iL sp px pn k nm xdp i mu) M (kF v) outp)
      (At 0x8000568c#64 (jI sp px pn k nm xdp i mu y) (writeLog M []) (kF v) outp) := by
  dr_ctx
  have h1 : zero_extend (m := 64) (bytesT4 M (xdp + 4 * (nm + i))) = BitVec.ofNat 64 y := by
    rw [hf.v, zext32_ofNat _ hf.lt]
  seg_step drIA 0x8000568c#64 [rd4 M (xdp + 4 * (nm + i))]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [iL, uL] [jI, kI, uL] [h1] hc

/-- `r = x[m + i] k + x[i] + mu`. -/
def sI (sp px pn k nm xdp i mu r : Nat) : GRegs := (10, BitVec.ofNat 64 r) :: kI sp px pn k nm xdp i mu

theorem iB1_step (v : Abi) (outp : Array String) (sp px pn k nm xdp i mu p xi : Nat) (M : Mem)
    (hc : CodeAt M mpDrReduceBase mpDrReduceCode) (hf : DRead M (xdp + 4 * i) xi) (hmu : mu < 2 ^ 32)
    (hr : p + xi + mu < 2 ^ 64) :
    Triple (At 0x80005690#64 (rI sp px pn k nm xdp i mu p) M (kF v) outp)
      (At 0x800056a4#64 (sI sp px pn k nm xdp i mu (p + xi + mu)) (writeLog M []) (kF v) outp) := by
  dr_ctx
  have h1 : zero_extend (m := 64) (bytesT4 M (xdp + 4 * i)) = BitVec.ofNat 64 xi := by
    rw [hf.v, zext32_ofNat _ hf.lt]
  seg_stepx drIB1 0x800056a4#64 [rd4 M (xdp + 4 * i)]
    [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [rI, kI, uL] [sI, kI, uL] [h1] hc

/-- `x[i]`'s digit array off the code. -/
structure BFacts (xdp i al : Nat) : Prop where
  rx : Ram xdp (4 * al)
  al4 : xdp % 4 = 0
  i_lt : i < al
  code_d : xdp + 4 * al ≤ mpDrReduceBase ∨ mpDrReduceBase + 424 ≤ xdp

/-- `x[i] := r & MP_MASK`, `mu := r >> 28`; the back edge. -/
theorem iBt_step (v : Abi) (outp : Array String) (sp px pn k nm xdp i mu r al : Nat) (M : Mem)
    (hc : CodeAt M mpDrReduceBase mpDrReduceCode) (hf : BFacts xdp i al) (hr : r < 2 ^ 64)
    (hr' : r / 268435456 < 2 ^ 31) (hi : i + 1 < nm) (hm : xdp + 4 * nm ≤ 2 ^ 32) :
    Triple (At 0x800056a4#64 (sI sp px pn k nm xdp i mu r) M (kF v) outp)
      (At 0x80005680#64 (iL sp px pn k nm xdp (i + 1) (r / 268435456))
        (writeLog M [(xdp + 4 * i, 4, BitVec.ofNat 64 (r % 268435456))]) (kF v) outp) := by
  dr_ctx
  seg_step drIBt 0x80005680#64 ([] : List (List (BitVec 8)))
    [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [sI, kI, uL] [iL, uL] [] hc

/-- After the digit loop (`56bc`): the carry `mu`. -/
abbrev fL (sp px pn k nm xdp mu : Nat) : GRegs :=
  uL sp px pn k nm (BitVec.ofNat 64 (xdp + 4 * nm)) (BitVec.ofNat 64 xdp) (BitVec.ofNat 64 (xdp + 4 * (nm + nm)))
    (BitVec.ofNat 64 mu) (BitVec.ofNat 64 (xdp + 4 * nm))

/-- The last digit: the exit. -/
theorem iBf_step (v : Abi) (outp : Array String) (sp px pn k nm xdp i mu r al : Nat) (M : Mem)
    (hc : CodeAt M mpDrReduceBase mpDrReduceCode) (hf : BFacts xdp i al) (hr : r < 2 ^ 64)
    (hr' : r / 268435456 < 2 ^ 31) (hi : i + 1 = nm) :
    Triple (At 0x800056a4#64 (sI sp px pn k nm xdp i mu r) M (kF v) outp)
      (At 0x800056bc#64 (fL sp px pn k nm xdp (r / 268435456))
        (writeLog M [(xdp + 4 * i, 4, BitVec.ofNat 64 (r % 268435456))]) (kF v) outp) := by
  dr_ctx
  seg_step drIBf 0x800056bc#64 ([] : List (List (BitVec 8)))
    [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [sI, kI, uL] [fL, uL] [] hc

/-! ## After the digit loop -/

/-- At `56cc`: `s3 = &x[m]`. -/
abbrev f1L (sp px pn k nm xdp mu : Nat) : GRegs :=
  uL sp px pn k nm (BitVec.ofNat 64 (xdp + 4 * nm)) (BitVec.ofNat 64 (xdp + 4 * nm))
    (BitVec.ofNat 64 (xdp + 4 * (nm + nm))) (BitVec.ofNat 64 mu) (BitVec.ofNat 64 (xdp + 4 * nm))

/-- The spill `4 (m - 1)`, `x`'s digit `m`. -/
structure F1Facts (M : Mem) (sp xdp nm al : Nat) : Prop where
  k : KF sp
  m4_v : bytesT8 M (sp - 128 + 8) = BitVec.ofNat 64 (4 * (nm - 1))
  rx : Ram xdp (4 * al)
  m_lt : nm < al
  m_pos : 1 ≤ nm
  code_d : xdp + 4 * al ≤ mpDrReduceBase ∨ mpDrReduceBase + 424 ≤ xdp
  al4 : xdp % 4 = 0

/-- `x[m] := mu`. -/
theorem f1_step (v : Abi) (outp : Array String) (sp px pn k nm xdp mu al : Nat) (M : Mem)
    (hc : CodeAt M mpDrReduceBase mpDrReduceCode) (hf : F1Facts M sp xdp nm al) :
    Triple (At 0x800056bc#64 (fL sp px pn k nm xdp mu) M (kF v) outp)
      (At 0x800056cc#64 (f1L sp px pn k nm xdp mu) (writeLog M [(xdp + 4 * nm, 4, BitVec.ofNat 64 mu)])
        (kF v) outp) := by
  dr_ctx
  have h1 := hf.m4_v
  seg_step drF1 0x800056cc#64 [rd8 M (sp - 128 + 8)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [fL, uL] [f1L, uL] [h1] hc

/-- `x->used`. -/
structure UFacts (M : Mem) (px u : Nat) : Prop where
  rx : Ram px 24
  u_v : bytesT4 M px = BitVec.ofNat 32 u
  u_lt : u < 2 ^ 30


/-- `bge 1, rs` with `rs` a sign-extended word (`subw`), negative or not. -/
theorem bge_one_sextW {w : Nat} (hw : w = 32) (d : Nat) :
    zopz0zKzJ_s (1#64) (BitVec.signExtend 64 (BitVec.ofNat w d)) =
      decide (2 ^ 31 ≤ d % 4294967296 ∨ d % 4294967296 ≤ 1) := by
  by_cases h : d % 4294967296 < 2 ^ 31
  · rw [signExtend_ofNatW hw d h, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      bge_ofNat _ _ (by omega) (by omega)]
    simp only [decide_eq_decide]; omega
  · subst hw; unfold zopz0zKzJ_s
    rw [BitVec.toInt_signExtend_of_le (by decide)]
    have hneg : (BitVec.ofNat (32) d).toInt < 0 := by
      rw [BitVec.toInt_neg_iff]; simp; omega
    simp only [decide_eq_decide]
    have : (1#64 : BitVec 64).toInt = 1 := by decide
    rw [this]; omega

/-- `x->used - m` as `subw` leaves it (negative or not). -/
abbrev dW (u nm : Nat) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.ofNat 32 (4294967296 - nm % 4294967296 % 4294967296 + u % 4294967296))

/-- `a2 = x->used - m`. -/
theorem f2a_step (v : Abi) (outp : Array String) (sp px pn k nm u : Nat) (j0 j3 j7 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M mpDrReduceBase mpDrReduceCode) (hf : UFacts M px u) (hnm : nm < 2 ^ 29) :
    Triple (At 0x800056cc#64 (uL sp px pn k nm j0 j3 j7 j10 j11) M (kF v) outp)
      (At 0x800056d4#64 ((12, dW u nm) :: uL sp px pn k nm j0 j3 j7 j10 j11) (writeLog M []) (kF v) outp) := by
  dr_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M px) = BitVec.ofNat 64 u := by
    rw [hf.u_v, signExtend_ofNat32 _ (by have := hf.u_lt; omega)]
  seg_step drF2a 0x800056d4#64 [rd4 M px]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [uL] [uL] [h1] hc

theorem dW_le {u nm : Nat} (hnm : nm < 2 ^ 29) (hu : u < 2 ^ 30) (hle : u ≤ nm + 1) :
    zopz0zKzJ_s (1#64) (dW u nm) = true := by
  rw [dW, bge_one_sextW rfl]; simp only [decide_eq_true_eq]; omega

/-- `x->used - m ≤ 1`: no `memset`. -/
theorem f2t_step (v : Abi) (outp : Array String) (sp px pn k nm u : Nat) (j0 j3 j7 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M mpDrReduceBase mpDrReduceCode) (hg : zopz0zKzJ_s (1#64) (dW u nm) = true) :
    Triple (At 0x800056d4#64 ((12, dW u nm) :: uL sp px pn k nm j0 j3 j7 j10 j11) M (kF v) outp)
      (At 0x800056ec#64 (uL sp px pn k nm j0 j3 j7 j10 j11) (writeLog M []) (kF v) outp) := by
  dr_ctx
  seg_step drF2t 0x800056ec#64 ([] : List (List (BitVec 8)))
    [12, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [uL, dW] [uL] [hg] hc

/-- `x->used - m > 1`. -/
theorem f2m_step (v : Abi) (outp : Array String) (sp px pn k nm xdp mu u : Nat) (M : Mem)
    (hc : CodeAt M mpDrReduceBase mpDrReduceCode) (hf : UFacts M px u) (hnm : nm < 2 ^ 29) (hgt : nm + 1 < u) :
    Triple (At 0x800056cc#64 (f1L sp px pn k nm xdp mu) M (kF v) outp)
      (At 0x800056d8#64 ((12, BitVec.ofNat 64 (u - nm)) :: f1L sp px pn k nm xdp mu) (writeLog M []) (kF v) outp) := by
  dr_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M px) = BitVec.ofNat 64 u := by
    rw [hf.u_v, signExtend_ofNat32 _ (by have := hf.u_lt; omega)]
  seg_stepx drF2m 0x800056d8#64 [rd4 M px]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [f1L, uL] [f1L, uL] [h1] hc

/-- Set up `memset(&x[m + 1], 0, 4 (x->used - m - 1))`. -/
theorem f2n_step (v : Abi) (outp : Array String) (sp px pn k nm xdp mu u : Nat) (M : Mem)
    (hc : CodeAt M mpDrReduceBase mpDrReduceCode) (hnm : nm < 2 ^ 29) (hgt : nm + 1 < u) (hu : u < 2 ^ 30)
    (hx : xdp + 4 * u ≤ 2 ^ 32) :
    Triple (At 0x800056d8#64 ((12, BitVec.ofNat 64 (u - nm)) :: f1L sp px pn k nm xdp mu) M (kF v) outp)
      (At 0x800056e8#64 ((10, BitVec.ofNat 64 (xdp + 4 * (nm + 1))) :: (11, 0#64) ::
          (12, BitVec.ofNat 64 (4 * (u - (nm + 1)))) :: f1L sp px pn k nm xdp mu) (writeLog M []) (kF v) outp) := by
  dr_ctx
  seg_stepx drF2n 0x800056e8#64 ([] : List (List (BitVec 8)))
    [12, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [f1L, uL] [f1L, uL] [] hc

/-- At the `mp_clamp(x)` call. -/
theorem f3_step (v : Abi) (outp : Array String) (sp px pn k nm : Nat) (j0 j3 j7 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M mpDrReduceBase mpDrReduceCode) :
    Triple (At 0x800056ec#64 (uL sp px pn k nm j0 j3 j7 j10 j11) M (kF v) outp)
      (At 0x800056f0#64 ((10, BitVec.ofNat 64 px) :: uL sp px pn k nm j0 j3 j7 j10 j11) (writeLog M []) (kF v) outp) := by
  dr_ctx
  seg_step drF3 0x800056f0#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [uL] [uL] [] hc

/-- At the `mp_cmp_mag(x, n)` call. -/
theorem f4_step (v : Abi) (outp : Array String) (sp px pn k nm : Nat) (j0 j3 j7 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M mpDrReduceBase mpDrReduceCode) :
    Triple (At 0x800056f4#64 (uL sp px pn k nm j0 j3 j7 j10 j11) M (kF v) outp)
      (At 0x800056fc#64 ((10, BitVec.ofNat 64 px) :: (11, BitVec.ofNat 64 pn) :: uL sp px pn k nm j0 j3 j7 j10 j11)
        (writeLog M []) (kF v) outp) := by
  dr_ctx
  seg_step drF4 0x800056fc#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [uL] [uL] [] hc

/-- `x < n`: return `MP_OKAY`. -/
theorem f5t_step (v : Abi) (outp : Array String) (sp px pn k nm : Nat) (r j0 j3 j7 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M mpDrReduceBase mpDrReduceCode) (hr : r = m1) :
    Triple (At 0x80005700#64 ((10, r) :: uL sp px pn k nm j0 j3 j7 j10 j11) M (kF v) outp)
      (At 0x80005718#64 ((10, 0#64) :: uL sp px pn k nm j0 j3 j7 j10 j11) (writeLog M []) (kF v) outp) := by
  dr_ctx
  subst hr
  seg_step drF5t 0x80005718#64 ([] : List (List (BitVec 8)))
    [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [uL] [uL] [] hc

/-- `x ≥ n`: set up `s_mp_sub(x, n, x)`. -/
theorem f5f_step (v : Abi) (outp : Array String) (sp px pn k nm : Nat) (r j0 j3 j7 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M mpDrReduceBase mpDrReduceCode) (hr : r ≠ m1) :
    Triple (At 0x80005700#64 ((10, r) :: uL sp px pn k nm j0 j3 j7 j10 j11) M (kF v) outp)
      (At 0x80005710#64 ((10, BitVec.ofNat 64 px) :: (11, BitVec.ofNat 64 pn) :: (12, BitVec.ofNat 64 px) ::
        uL sp px pn k nm j0 j3 j7 j10 j11) (writeLog M []) (kF v) outp) := by
  dr_ctx
  have hb : (r == m1) = false := by simpa using hr
  seg_step drF5f 0x80005710#64 ([] : List (List (BitVec 8)))
    [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [uL] [uL] [hb] hc

/-- `s_mp_sub` returned `MP_OKAY`: back to `top`. -/
theorem f6_step (v : Abi) (outp : Array String) (sp px pn k nm : Nat) (j0 j3 j7 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M mpDrReduceBase mpDrReduceCode) :
    Triple (At 0x80005714#64 ((10, 0#64) :: uL sp px pn k nm j0 j3 j7 j10 j11) M (kF v) outp)
      (At 0x80005664#64 (uL sp px pn k nm j0 j3 j7 j10 j11) (writeLog M []) (kF v) outp) := by
  dr_ctx
  seg_step drF6 0x80005664#64 ([] : List (List (BitVec 8)))
    [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [uL] [uL] [] hc

/-- The return: `a0 = MP_OKAY`, `s0`–`s11` restored. -/
def rL (ra s0 : BitVec 64) (v : Abi) (sp : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64), (9, v.s.s1), (18, v.s.s2), (19, v.s.s3), (20, v.s.s4),
   (21, v.s.s5), (22, v.s.s6), (23, v.s.s7), (24, v.s.s8), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

/-- The saved registers. -/
structure HFacts (M : Mem) (ra s0 : BitVec 64) (v : Abi) (sp : Nat) : Prop where
  k : KF sp
  ra_al : ra.toNat % 4 = 0
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  s1_v : bytesT8 M (sp - 24) = v.s.s1
  s2_v : bytesT8 M (sp - 32) = v.s.s2
  s3_v : bytesT8 M (sp - 40) = v.s.s3
  s4_v : bytesT8 M (sp - 48) = v.s.s4
  s5_v : bytesT8 M (sp - 56) = v.s.s5
  s6_v : bytesT8 M (sp - 64) = v.s.s6
  s7_v : bytesT8 M (sp - 72) = v.s.s7
  s8_v : bytesT8 M (sp - 80) = v.s.s8
  s9_v : bytesT8 M (sp - 88) = v.s.s9
  s10_v : bytesT8 M (sp - 96) = v.s.s10
  s11_v : bytesT8 M (sp - 104) = v.s.s11

theorem e_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M mpDrReduceBase mpDrReduceCode) (hf : HFacts M ra s0 v sp) :
    Triple (At 0x80005718#64 [(2, BitVec.ofNat 64 (sp - 128)), (10, 0#64)] M (kF v) outp)
      (At ra (rL ra s0 v sp) (writeLog M []) (kF v) outp) := by
  dr_ctx
  have hra := hf.ra_al
  seg_step drE ra [rd8 M (sp - 16), rd8 M (sp - 8), rd8 M (sp - 24), rd8 M (sp - 32), rd8 M (sp - 40),
      rd8 M (sp - 72), rd8 M (sp - 80), rd8 M (sp - 88), rd8 M (sp - 96), rd8 M (sp - 104), rd8 M (sp - 48),
      rd8 M (sp - 56), rd8 M (sp - 64)]
    [2, 10] kFKeys [] [rL]
    [hf.ra_v, hf.s0_v, hf.s1_v, hf.s2_v, hf.s3_v, hf.s4_v, hf.s5_v, hf.s6_v, hf.s7_v, hf.s8_v, hf.s9_v,
     hf.s10_v, hf.s11_v] hc

end Tom.Machine.Fn.DrReduce
