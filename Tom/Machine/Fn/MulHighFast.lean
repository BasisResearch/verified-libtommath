import Tom.Machine.Seg.MulHighFast
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.MulCall
import Vsa.Sim.TripleCat

/-!
# `s_mp_mul_high_digs_fast` on the machine: the segments

`s_mp_mul_high_digs_fast(a, b, c, digs)` at `0x80006be4` (156 instructions),
frame `2192` bytes: the spills at `[sp - 2192, sp - 2160)` (`digs`, `c`,
`4 digs`, `a->used + b->used`), the column array `W[MP_WARRAY]` (`512` digits)
at `[sp - 2160, sp - 112)`, the saved `ra`, `s0`–`s11` at `[sp - 104, sp)`.

* prologue `p1`–`p3` (`digs ≥ 0`; the `mp_grow` branch `c->alloc < pa` is
  excluded, D5), `p4t` (`digs ≥ pa`: no column, `z1`, `z2`) / `p4f`, `p5t`
  (`digs < b->used`: into the column at `6ca4`) / `p5f` (into `6c84`);
* a column: `cA` at `6c84` (`ix ≥ b->used`: `tx = ix + 1 - b->used`,
  `ty = b->used - 1`), `cBt`/`cBf` at `6ca4` (`iy = min(a->used - tx, ty + 1)`,
  the mask), `cCz` (`iy = 0`) / `cCn` at `6cb4`, `cD` at `6cb8`; the inner
  loop `iLd` (the loads) → `jal __muldi3` at `6cd8` → `iAt` (back edge) /
  `iAf`; at `6ce4` the store `W[ix] := _W & MP_MASK` and the next column
  (`eA` → `6c84`, `eB` → `6cb4`, `eC` → `6cb8`) or the exit `eX`;
* after the loop: `t1` (`c->used := pa`) → `jal memcpy(c->dp + digs,
  W + digs, 4 (pa - digs))` at `6d88` → `t2`; at `6d98` `t3z` (`olduse ≤ pa`:
  no `memset`) → `t4` → `jal mp_clamp(c)` at `6db4` → `t5` (the epilogue).

All of `s0`–`s11` are locals: the segments keep only `gp` and `tp` (`kF`) and
carry the others in their lists; values the C does not need are parameters.
-/


namespace Tom.Machine.Fn.MulHighFast

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mh_ctx" : tactic => `(tactic|
  (facts_ctx
   have : sMpMulHighDigsFastBase = 0x80006be4 := rfl
   have : sMpMulHighDigsFastCode.length = 156 := rfl))

/-- The registers every segment keeps. -/
def kF (v : Abi) : GRegs := [(3, v.gp), (4, v.tp)]

abbrev kFKeys : List Nat := [3, 4]

/-- The callee-saved registers as a list (for the calls after the loop). -/
def abiL (u : Abi) : GRegs := (2, u.sp) :: (8, u.s0) :: sKeepL u.s

/-- `MP_MASK`. -/
abbrev mask : BitVec 64 := 268435455#64

/-- The frame. -/
structure KF (sp : Nat) : Prop where
  rs : Ram (sp - 2192) 2192
  sp_al : sp % 16 = 0
  sp_ge : 2192 ≤ sp
  code_off : sp ≤ sMpMulHighDigsFastBase ∨ sMpMulHighDigsFastBase + 624 ≤ sp - 2192

/-! ## The prologue -/

def entL (ra s0 : BitVec 64) (v : Abi) (sp pa pb pc dg : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, v.s.s1), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb),
   (12, BitVec.ofNat 64 pc), (13, BitVec.ofNat 64 dg), (18, v.s.s2), (19, v.s.s3), (20, v.s.s4), (21, v.s.s5),
   (22, v.s.s6), (23, v.s.s7), (24, v.s.s8), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

def p1L (ra s0 : BitVec 64) (v : Abi) (sp pa pb pc dg : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 2032)), (8, s0), (9, v.s.s1), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 pb), (12, BitVec.ofNat 64 pc), (13, BitVec.ofNat 64 dg), (18, v.s.s2), (19, v.s.s3),
   (20, v.s.s4), (21, v.s.s5), (22, v.s.s6), (23, v.s.s7), (24, v.s.s8), (25, v.s.s9), (26, v.s.s10),
   (27, v.s.s11)]

/-- The saves of `s5`, `s9`. -/
def log1 (v : Abi) (sp : Nat) : List WEntry := [(sp - 56, 8, v.s.s5), (sp - 88, 8, v.s.s9)]

/-- `digs ≥ 0`: the frame, save `s5`, `s9`. -/
theorem p1_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc dg : Nat) (m : Mem)
    (hc : CodeAt m sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hk : KF sp) (hdg : dg < 2 ^ 31) :
    Triple (At 0x80006be4#64 (entL ra s0 v sp pa pb pc dg) m (kF v) outp)
      (At 0x80006bf4#64 (p1L ra s0 v sp pa pb pc dg) (writeLog m (log1 v sp)) (kF v) outp) := by
  mh_ctx
  seg_step mhP1 0x80006bf4#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 12, 13, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [entL, log1] [p1L] [] hc

def p1bL (ra s0 : BitVec 64) (v : Abi) (sp pa pb pc dg ua ub al : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 2032)), (8, s0), (9, v.s.s1), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 pb), (12, BitVec.ofNat 64 pc), (13, BitVec.ofNat 64 dg), (15, BitVec.ofNat 64 al),
   (18, v.s.s2), (19, v.s.s3), (20, v.s.s4), (21, BitVec.ofNat 64 ub), (22, v.s.s6), (23, v.s.s7), (24, v.s.s8),
   (25, BitVec.ofNat 64 ua), (26, v.s.s10), (27, v.s.s11)]

/-- `b->used`, `a->used`, `c->alloc`. -/
structure P1Facts (m : Mem) (pa pb pc ua ub al : Nat) : Prop where
  ra_ : Ram pa 24
  rb : Ram pb 24
  rc : Ram pc 24
  ua_v : bytesT4 m pa = BitVec.ofNat 32 ua
  ub_v : bytesT4 m pb = BitVec.ofNat 32 ub
  al_v : bytesT4 m (pc + 4) = BitVec.ofNat 32 al
  ua_lt : ua < 2 ^ 30
  ub_lt : ub < 2 ^ 30
  al_lt : al < 2 ^ 31

theorem p1b_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc dg ua ub al : Nat) (m : Mem)
    (hc : CodeAt m sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hf : P1Facts m pa pb pc ua ub al) :
    Triple (At 0x80006bf4#64 (p1L ra s0 v sp pa pb pc dg) m (kF v) outp)
      (At 0x80006c00#64 (p1bL ra s0 v sp pa pb pc dg ua ub al) (writeLog m []) (kF v) outp) := by
  mh_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 m pb) = BitVec.ofNat 64 ub := by
    rw [hf.ub_v, signExtend_ofNat32 _ (by have := hf.ub_lt; omega)]
  have h2 : BitVec.signExtend 64 (bytesT4 m pa) = BitVec.ofNat 64 ua := by
    rw [hf.ua_v, signExtend_ofNat32 _ (by have := hf.ua_lt; omega)]
  have h3 : BitVec.signExtend 64 (bytesT4 m (pc + 4)) = BitVec.ofNat 64 al := by
    rw [hf.al_v, signExtend_ofNat32 _ hf.al_lt]
  seg_step mhP1b 0x80006c00#64 [rd4 m pb, rd4 m pa, rd4 m (pc + 4)]
    [1, 2, 8, 9, 10, 11, 12, 13, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [p1L] [p1bL] [h1, h2, h3] hc

/-- The saves of `s0`, `s1`, `s4`, `ra`, `s2`. -/
def log2a (ra s0 : BitVec 64) (v : Abi) (sp : Nat) : List WEntry :=
  [(sp - 16, 8, s0), (sp - 24, 8, v.s.s1), (sp - 48, 8, v.s.s4), (sp - 8, 8, ra), (sp - 32, 8, v.s.s2)]

/-- The saves of `s3`, `s6`, `s7`, `s8`, `s10`, `s11`. -/
def log2b (v : Abi) (sp : Nat) : List WEntry :=
  [(sp - 40, 8, v.s.s3), (sp - 64, 8, v.s.s6), (sp - 72, 8, v.s.s7), (sp - 80, 8, v.s.s8),
   (sp - 96, 8, v.s.s10), (sp - 104, 8, v.s.s11)]

theorem p2a_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc dg ua ub al : Nat) (m : Mem)
    (hc : CodeAt m sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hk : KF sp) :
    Triple (At 0x80006c00#64 (p1bL ra s0 v sp pa pb pc dg ua ub al) m (kF v) outp)
      (At 0x80006c14#64 (p1bL ra s0 v sp pa pb pc dg ua ub al) (writeLog m (log2a ra s0 v sp)) (kF v) outp) := by
  mh_ctx
  seg_step mhP2a 0x80006c14#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 12, 13, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [p1bL, log2a] [p1bL] [] hc

theorem p2b_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc dg ua ub al : Nat) (m : Mem)
    (hc : CodeAt m sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hk : KF sp) :
    Triple (At 0x80006c14#64 (p1bL ra s0 v sp pa pb pc dg ua ub al) m (kF v) outp)
      (At 0x80006c2c#64 (p1bL ra s0 v sp pa pb pc dg ua ub al) (writeLog m (log2b v sp)) (kF v) outp) := by
  mh_ctx
  seg_step mhP2b 0x80006c2c#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 12, 13, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [p1bL, log2b] [p1bL] [] hc

/-- After the spills: `s0 = b`, `s1 = a`, `s4 = pa`, `s5 = b->used`, `s9 = a->used`. -/
def p3L (v : Abi) (sp pa pb ua ub : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, BitVec.ofNat 64 pb), (9, BitVec.ofNat 64 pa), (18, v.s.s2), (19, v.s.s3),
   (20, BitVec.ofNat 64 (ua + ub)), (21, BitVec.ofNat 64 ub), (22, v.s.s6), (23, v.s.s7), (24, v.s.s8),
   (25, BitVec.ofNat 64 ua), (26, v.s.s10), (27, v.s.s11)]

/-- The spills of `c`, `digs`, `pa`. -/
def log3 (sp pc dg ua ub : Nat) : List WEntry :=
  [(sp - 2192 + 8, 8, BitVec.ofNat 64 pc), (sp - 2192, 8, BitVec.ofNat 64 dg),
   (sp - 2192 + 24, 8, BitVec.ofNat 64 (ua + ub))]

/-- `pa = a->used + b->used`, the spills; `c->alloc ≥ pa` (no `mp_grow`). -/
theorem p3_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc dg ua ub al : Nat) (m : Mem)
    (hc : CodeAt m sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hk : KF sp) (hua : ua < 2 ^ 30)
    (hub : ub < 2 ^ 30) (hal : al < 2 ^ 31) (hroom : ua + ub ≤ al) :
    Triple (At 0x80006c2c#64 (p1bL ra s0 v sp pa pb pc dg ua ub al) m (kF v) outp)
      (At 0x80006c4c#64 (p3L v sp pa pb ua ub) (writeLog m (log3 sp pc dg ua ub)) (kF v) outp) := by
  mh_ctx
  seg_stepx mhP3 0x80006c4c#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 12, 13, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [p1bL, log3] [p3L] [] hc

/-- The spill `4 digs`. -/
def log4 (sp dg : Nat) : List WEntry := [(sp - 2192 + 16, 8, BitVec.ofNat 64 (4 * dg))]

/-- `digs` from its spill. -/
structure DFacts (M : Mem) (sp dg : Nat) : Prop where
  k : KF sp
  dg_v : bytesT8 M (sp - 2192) = BitVec.ofNat 64 dg
  dg_lt : dg < 2 ^ 31

/-- `digs ≥ pa`: no column. -/
theorem p4t_step (v : Abi) (outp : Array String) (sp pa pb ua ub dg : Nat) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hf : DFacts M sp dg) (hua : ua < 2 ^ 30)
    (hub : ub < 2 ^ 30) (hge : ua + ub ≤ dg) :
    Triple (At 0x80006c4c#64 (p3L v sp pa pb ua ub) M (kF v) outp)
      (At 0x80006e20#64 (p3L v sp pa pb ua ub) (writeLog M (log4 sp dg)) (kF v) outp) := by
  mh_ctx
  have h1 := hf.dg_v
  seg_step mhP4t 0x80006e20#64 [rd8 M (sp - 2192), rd8 M (sp - 2192)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [p3L, log4] [p3L] [h1] hc

/-- `digs < pa`: on to the columns. -/
theorem p4f_step (v : Abi) (outp : Array String) (sp pa pb ua ub dg : Nat) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hf : DFacts M sp dg) (hua : ua < 2 ^ 30)
    (hub : ub < 2 ^ 30) (hlt : dg < ua + ub) :
    Triple (At 0x80006c4c#64 (p3L v sp pa pb ua ub) M (kF v) outp)
      (At 0x80006c60#64 (p3L v sp pa pb ua ub) (writeLog M (log4 sp dg)) (kF v) outp) := by
  mh_ctx
  have h1 := hf.dg_v
  seg_step mhP4f 0x80006c60#64 [rd8 M (sp - 2192), rd8 M (sp - 2192)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [p3L, log4] [p3L] [h1] hc

/-! ## The column heads -/

/-- `W + 4 ix`. -/
abbrev wp (sp ix : Nat) : BitVec 64 := BitVec.ofNat 64 (sp - 2160 + 4 * ix)

/-- Head A (`6c84`, `ix ≥ b->used`): column `ix`, carry `w` (`a4 = ix`). -/
def aL (sp ua ub adp bdp ix w : Nat) (j0 j2 j3 j8 j11 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, j0), (9, wp sp ix), (14, BitVec.ofNat 64 ix), (18, j2), (19, j3),
   (20, BitVec.ofNat 64 (ua + ub)), (21, BitVec.ofNat 64 ub), (22, BitVec.ofNat 64 w), (23, BitVec.ofNat 64 adp),
   (24, j8), (25, BitVec.ofNat 64 ua), (26, BitVec.ofNat 64 bdp), (27, j11)]

/-- Head B (`6ca4`): `a4 = ty`, `s0 = a->used - tx`, `s3 = ix`, `s11 = a->dp + tx`. -/
def bL (sp ua ub adp bdp ix w ty s0v tx : Nat) (j2 j8 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, BitVec.ofNat 64 s0v), (9, wp sp ix), (14, BitVec.ofNat 64 ty), (18, j2),
   (19, BitVec.ofNat 64 ix), (20, BitVec.ofNat 64 (ua + ub)), (21, BitVec.ofNat 64 ub), (22, BitVec.ofNat 64 w),
   (23, BitVec.ofNat 64 adp), (24, j8), (25, BitVec.ofNat 64 ua), (26, BitVec.ofNat 64 bdp),
   (27, BitVec.ofNat 64 (adp + 4 * tx))]

/-- Heads C (`6cb4`) and D (`6cb8`): `s0 = iy`, the mask in `s2`. -/
def cL (sp ua ub adp bdp ix w ty iy tx : Nat) (j8 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, BitVec.ofNat 64 iy), (9, wp sp ix), (14, BitVec.ofNat 64 ty), (18, mask),
   (19, BitVec.ofNat 64 ix), (20, BitVec.ofNat 64 (ua + ub)), (21, BitVec.ofNat 64 ub), (22, BitVec.ofNat 64 w),
   (23, BitVec.ofNat 64 adp), (24, j8), (25, BitVec.ofNat 64 ua), (26, BitVec.ofNat 64 bdp),
   (27, BitVec.ofNat 64 (adp + 4 * tx))]

/-- The store point E (`6ce4`) and the loop's exit (`6d44`): the column's sum `S`. -/
def eL (sp ua ub adp bdp ix S : Nat) (j0 j8 j11 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, j0), (9, wp sp ix), (18, mask), (19, BitVec.ofNat 64 ix),
   (20, BitVec.ofNat 64 (ua + ub)), (21, BitVec.ofNat 64 ub), (22, BitVec.ofNat 64 S), (23, BitVec.ofNat 64 adp),
   (24, j8), (25, BitVec.ofNat 64 ua), (26, BitVec.ofNat 64 bdp), (27, j11)]

/-- `a->dp`, `b->dp`, the spills. -/
structure P5Facts (M : Mem) (sp pa pb adp bdp dg : Nat) : Prop where
  k : KF sp
  ra_ : Ram pa 24
  rb : Ram pb 24
  adp_v : bytesT8 M (pa + 16) = BitVec.ofNat 64 adp
  bdp_v : bytesT8 M (pb + 16) = BitVec.ofNat 64 bdp
  dg_v : bytesT8 M (sp - 2192) = BitVec.ofNat 64 dg
  dg4_v : bytesT8 M (sp - 2192 + 16) = BitVec.ofNat 64 (4 * dg)
  dg_lt : dg < 2 ^ 30

/-- `digs < b->used`: the first column at B (`tx = 0`, `ty = digs`). -/
theorem p5t_step (v : Abi) (outp : Array String) (sp pa pb ua ub adp bdp dg : Nat) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hf : P5Facts M sp pa pb adp bdp dg)
    (hua : ua < 2 ^ 30) (hub : ub < 2 ^ 30) (hlt : dg < ub) :
    Triple (At 0x80006c60#64 (p3L v sp pa pb ua ub) M (kF v) outp)
      (At 0x80006ca4#64 (bL sp ua ub adp bdp dg 0 dg ua 0 v.s.s2 v.s.s8) (writeLog M []) (kF v) outp) := by
  mh_ctx
  have h1 := hf.dg_v; have h2 := hf.dg4_v; have h3 := hf.adp_v; have h4 := hf.bdp_v
  seg_step mhP5t 0x80006ca4#64 [rd8 M (sp - 2192 + 16), rd8 M (pa + 16), rd8 M (pb + 16), rd8 M (sp - 2192),
      rd8 M (sp - 2192)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [p3L] [bL, wp] [h1, h2, h3, h4] hc

/-- `digs ≥ b->used`: the first column at A. -/
theorem p5f_step (v : Abi) (outp : Array String) (sp pa pb ua ub adp bdp dg : Nat) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hf : P5Facts M sp pa pb adp bdp dg)
    (hua : ua < 2 ^ 30) (hub : ub < 2 ^ 30) (hge : ub ≤ dg) :
    Triple (At 0x80006c60#64 (p3L v sp pa pb ua ub) M (kF v) outp)
      (At 0x80006c84#64 (aL sp ua ub adp bdp dg 0 (BitVec.ofNat 64 pb) v.s.s2 v.s.s3 v.s.s8 v.s.s11)
        (writeLog M []) (kF v) outp) := by
  mh_ctx
  have h1 := hf.dg_v; have h2 := hf.dg4_v; have h3 := hf.adp_v; have h4 := hf.bdp_v
  seg_step mhP5f 0x80006c84#64 [rd8 M (sp - 2192 + 16), rd8 M (pa + 16), rd8 M (pb + 16), rd8 M (sp - 2192)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [p3L] [aL, wp] [h1, h2, h3, h4] hc

/-! ## A column -/

/-- `ix ≥ b->used`: `tx = ix + 1 - b->used`, `ty = b->used - 1`, `s0 = pa - 1 - ix`. -/
theorem cA_step (v : Abi) (outp : Array String) (sp ua ub adp bdp ix w : Nat) (j0 j2 j3 j8 j11 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hua : ua < 2 ^ 30)
    (hub : ub < 2 ^ 30) (hub1 : 1 ≤ ub) (hge : ub ≤ ix) (hix : ix < ua + ub) (hadp : adp + 4 * ua ≤ 2 ^ 32) :
    Triple (At 0x80006c84#64 (aL sp ua ub adp bdp ix w j0 j2 j3 j8 j11) M (kF v) outp)
      (At 0x80006ca4#64 (bL sp ua ub adp bdp ix w (ub - 1) (ua + ub - 1 - ix) (ix + 1 - ub) j2 j8)
        (writeLog M []) (kF v) outp) := by
  mh_ctx
  seg_stepx mhCA 0x80006ca4#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [aL, wp] [bL, wp] [] hc

/-- `ty ≥ a->used - tx`: `iy = a->used - tx`; the mask. -/
theorem cBt_step (v : Abi) (outp : Array String) (sp ua ub adp bdp ix w ty s0v tx : Nat) (j2 j8 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hty : ty < 2 ^ 30)
    (hs0 : s0v < 2 ^ 30) (hle : s0v ≤ ty) :
    Triple (At 0x80006ca4#64 (bL sp ua ub adp bdp ix w ty s0v tx j2 j8) M (kF v) outp)
      (At 0x80006cb4#64 (cL sp ua ub adp bdp ix w ty s0v tx j8) (writeLog M []) (kF v) outp) := by
  mh_ctx
  seg_step mhCBt 0x80006cb4#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [bL, wp] [cL, wp] [] hc

/-- `ty < a->used - tx`: `iy = ty + 1`; the mask. -/
theorem cBf_step (v : Abi) (outp : Array String) (sp ua ub adp bdp ix w ty s0v tx : Nat) (j2 j8 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hty : ty < 2 ^ 30)
    (hs0 : s0v < 2 ^ 30) (hlt : ty < s0v) :
    Triple (At 0x80006ca4#64 (bL sp ua ub adp bdp ix w ty s0v tx j2 j8) M (kF v) outp)
      (At 0x80006cb4#64 (cL sp ua ub adp bdp ix w ty (ty + 1) tx j8) (writeLog M []) (kF v) outp) := by
  mh_ctx
  seg_stepx mhCBf 0x80006cb4#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [bL, wp] [cL, wp] [] hc

/-- `iy = 0`: an empty column. -/
theorem cCz_step (v : Abi) (outp : Array String) (sp ua ub adp bdp ix w ty tx : Nat) (j8 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) :
    Triple (At 0x80006cb4#64 (cL sp ua ub adp bdp ix w ty 0 tx j8) M (kF v) outp)
      (At 0x80006ce4#64 (eL sp ua ub adp bdp ix w (BitVec.ofNat 64 0) j8 (BitVec.ofNat 64 (adp + 4 * tx)))
        (writeLog M []) (kF v) outp) := by
  mh_ctx
  seg_step mhCCz 0x80006ce4#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [cL, wp] [eL, wp] [] hc

/-- The inner loop's head `6cc8`, term `iz`, sum `S`. -/
def iL (sp ua ub adp bdp ix tx ty iy iz S : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, BitVec.ofNat 64 (adp + 4 * tx + 4 * iy)), (9, wp sp ix), (18, mask),
   (19, BitVec.ofNat 64 ix), (20, BitVec.ofNat 64 (ua + ub)), (21, BitVec.ofNat 64 ub), (22, BitVec.ofNat 64 S),
   (23, BitVec.ofNat 64 adp), (24, BitVec.ofNat 64 (bdp + 4 * ty - 4 * iz)), (25, BitVec.ofNat 64 ua),
   (26, BitVec.ofNat 64 bdp), (27, BitVec.ofNat 64 (adp + 4 * tx + 4 * iz))]

/-- `iy > 0`: `s8 = b->dp + ty`, `s0 = a->dp + tx + iy`. -/
theorem cCn_step (v : Abi) (outp : Array String) (sp ua ub adp bdp ix w ty iy tx : Nat) (j8 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hiy : 0 < iy) (hiy' : iy < 2 ^ 30)
    (hty : ty < 2 ^ 30) :
    Triple (At 0x80006cb4#64 (cL sp ua ub adp bdp ix w ty iy tx j8) M (kF v) outp)
      (At 0x80006cc8#64 (iL sp ua ub adp bdp ix tx ty iy 0 w) (writeLog M []) (kF v) outp) := by
  mh_ctx
  seg_step mhCCn 0x80006cc8#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [cL, wp] [iL, wp] [] hc

/-- At D (`iy > 0` known): as `cCn`. -/
theorem cD_step (v : Abi) (outp : Array String) (sp ua ub adp bdp ix w ty iy tx : Nat) (j8 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hiy' : iy < 2 ^ 30)
    (hty : ty < 2 ^ 30) :
    Triple (At 0x80006cb8#64 (cL sp ua ub adp bdp ix w ty iy tx j8) M (kF v) outp)
      (At 0x80006cc8#64 (iL sp ua ub adp bdp ix tx ty iy 0 w) (writeLog M []) (kF v) outp) := by
  mh_ctx
  seg_step mhCD 0x80006cc8#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [cL, wp] [iL, wp] [] hc

/-! ## The inner loop -/

/-- Across the `__muldi3` call: the pointers advanced. -/
def kI (sp ua ub adp bdp ix tx ty iy iz S : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, BitVec.ofNat 64 (adp + 4 * tx + 4 * iy)), (9, wp sp ix), (18, mask),
   (19, BitVec.ofNat 64 ix), (20, BitVec.ofNat 64 (ua + ub)), (21, BitVec.ofNat 64 ub), (22, BitVec.ofNat 64 S),
   (23, BitVec.ofNat 64 adp), (24, BitVec.ofNat 64 (bdp + 4 * ty - 4 * (iz + 1))), (25, BitVec.ofNat 64 ua),
   (26, BitVec.ofNat 64 bdp), (27, BitVec.ofNat 64 (adp + 4 * tx + 4 * (iz + 1)))]

def jI (sp ua ub adp bdp ix tx ty iy iz S x y : Nat) : GRegs :=
  (10, BitVec.ofNat 64 x) :: (11, BitVec.ofNat 64 y) :: kI sp ua ub adp bdp ix tx ty iy iz S

def rI (sp ua ub adp bdp ix tx ty iy iz S p : Nat) : GRegs :=
  (10, BitVec.ofNat 64 p) :: kI sp ua ub adp bdp ix tx ty iy iz S

/-- The two digits a term reads. -/
structure LFacts (M : Mem) (adp bdp tx ty iz x y : Nat) : Prop where
  ra_ : Ram (adp + 4 * tx + 4 * iz) 4
  rb : Ram (bdp + 4 * ty - 4 * iz) 4
  x_v : bytesT4 M (adp + 4 * tx + 4 * iz) = BitVec.ofNat 32 x
  y_v : bytesT4 M (bdp + 4 * ty - 4 * iz) = BitVec.ofNat 32 y
  x_lt : x < 2 ^ 32
  y_lt : y < 2 ^ 32
  iz_le : iz ≤ ty
  b4 : 4 ≤ bdp

/-- The loads `b->dp[ty - iz]`, `a->dp[tx + iz]`, the pointers advanced. -/
theorem iLd_step (v : Abi) (outp : Array String) (sp ua ub adp bdp ix tx ty iy iz S x y : Nat) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hf : LFacts M adp bdp tx ty iz x y) :
    Triple (At 0x80006cc8#64 (iL sp ua ub adp bdp ix tx ty iy iz S) M (kF v) outp)
      (At 0x80006cd8#64 (jI sp ua ub adp bdp ix tx ty iy iz S x y) (writeLog M []) (kF v) outp) := by
  mh_ctx
  have h1 : zero_extend (m := 64) (bytesT4 M (bdp + 4 * ty - 4 * iz)) = BitVec.ofNat 64 y := by
    rw [hf.y_v, zext32_ofNat _ hf.y_lt]
  have h2 : zero_extend (m := 64) (bytesT4 M (adp + 4 * tx + 4 * iz)) = BitVec.ofNat 64 x := by
    rw [hf.x_v, zext32_ofNat _ hf.x_lt]
  seg_step mhIL 0x80006cd8#64 [rd4 M (bdp + 4 * ty - 4 * iz), rd4 M (adp + 4 * tx + 4 * iz)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [iL, wp] [jI, kI, wp] [h1, h2] hc

/-- Accumulate; the back edge (`iz + 1 < iy`). -/
theorem iAt_step (v : Abi) (outp : Array String) (sp ua ub adp bdp ix tx ty iy iz S p : Nat) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hS : S + p < 2 ^ 64) (hi : iz + 1 < iy)
    (ha : adp + 4 * tx + 4 * iy ≤ 2 ^ 32) :
    Triple (At 0x80006cdc#64 (rI sp ua ub adp bdp ix tx ty iy iz S p) M (kF v) outp)
      (At 0x80006cc8#64 (iL sp ua ub adp bdp ix tx ty iy (iz + 1) (S + p)) (writeLog M []) (kF v) outp) := by
  mh_ctx
  seg_step mhIAt 0x80006cc8#64 ([] : List (List (BitVec 8)))
    [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [rI, kI, wp] [iL, wp] [] hc

/-- Accumulate; the exit (`iz + 1 = iy`). -/
theorem iAf_step (v : Abi) (outp : Array String) (sp ua ub adp bdp ix tx ty iy iz S p : Nat) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hS : S + p < 2 ^ 64) (hi : iz + 1 = iy) :
    Triple (At 0x80006cdc#64 (rI sp ua ub adp bdp ix tx ty iy iz S p) M (kF v) outp)
      (At 0x80006ce4#64 (eL sp ua ub adp bdp ix (S + p) (BitVec.ofNat 64 (adp + 4 * tx + 4 * iy))
          (BitVec.ofNat 64 (bdp + 4 * ty - 4 * iy)) (BitVec.ofNat 64 (adp + 4 * tx + 4 * iy)))
        (writeLog M []) (kF v) outp) := by
  mh_ctx
  seg_step mhIAf 0x80006ce4#64 ([] : List (List (BitVec 8)))
    [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [rI, kI, wp] [eL, wp] [] hc

/-! ## The column store, the next column -/

/-- The store of `W[ix]`. -/
abbrev wlog (sp ix S : Nat) : List WEntry := [(sp - 2160 + 4 * ix, 4, BitVec.ofNat 64 (S % 268435456))]

/-- The store `W[ix]` stays in the frame. -/
structure WFacts (sp ix : Nat) : Prop where
  k : KF sp
  ix_lt : ix < 512

/-- The last column (`ix + 1 = pa`). -/
theorem eX_step (v : Abi) (outp : Array String) (sp ua ub adp bdp ix S : Nat) (j0 j8 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hf : WFacts sp ix) (hS : S < 2 ^ 64)
    (hi : ix + 1 = ua + ub) (hp : ua + ub < 2 ^ 30) :
    Triple (At 0x80006ce4#64 (eL sp ua ub adp bdp ix S j0 j8 j11) M (kF v) outp)
      (At 0x80006d44#64 (eL sp ua ub adp bdp ix S j0 j8 j11) (writeLog M (wlog sp ix S)) (kF v) outp) := by
  mh_ctx
  seg_step mhEX 0x80006d44#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [eL, wp] [eL, wp] [] hc

/-- The next column at A (`ix + 1 ≥ b->used`). -/
theorem eA_step (v : Abi) (outp : Array String) (sp ua ub adp bdp ix S : Nat) (j0 j8 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hf : WFacts sp ix) (hS : S < 2 ^ 64)
    (hi : ix + 1 < ua + ub) (hp : ua + ub < 2 ^ 30) (hb : ub ≤ ix + 1) :
    Triple (At 0x80006ce4#64 (eL sp ua ub adp bdp ix S j0 j8 j11) M (kF v) outp)
      (At 0x80006c84#64 (aL sp ua ub adp bdp (ix + 1) (S / 268435456) j0 mask (BitVec.ofNat 64 ix) j8 j11)
        (writeLog M (wlog sp ix S)) (kF v) outp) := by
  mh_ctx
  seg_step mhEA 0x80006c84#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [eL, wp] [aL, wp] [] hc

/-- The next column at C (`ix + 1 < b->used`, `ix + 1 ≥ a->used`: `iy = a->used`). -/
theorem eB_step (v : Abi) (outp : Array String) (sp ua ub adp bdp ix S : Nat) (j0 j8 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hf : WFacts sp ix) (hS : S < 2 ^ 64)
    (hi : ix + 1 < ua + ub) (hp : ua + ub < 2 ^ 30) (hb : ix + 1 < ub) (ha : ua ≤ ix + 1) :
    Triple (At 0x80006ce4#64 (eL sp ua ub adp bdp ix S j0 j8 j11) M (kF v) outp)
      (At 0x80006cb4#64 (cL sp ua ub adp bdp (ix + 1) (S / 268435456) (ix + 1) ua 0 j8)
        (writeLog M (wlog sp ix S)) (kF v) outp) := by
  mh_ctx
  seg_step mhEB 0x80006cb4#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [eL, wp] [cL, wp] [] hc

/-- The next column at D (`ix + 1 < b->used`, `ix + 1 < a->used`: `iy = ix + 2`). -/
theorem eC_step (v : Abi) (outp : Array String) (sp ua ub adp bdp ix S : Nat) (j0 j8 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hf : WFacts sp ix) (hS : S < 2 ^ 64)
    (hi : ix + 1 < ua + ub) (hp : ua + ub < 2 ^ 30) (hb : ix + 1 < ub) (ha : ix + 1 < ua) :
    Triple (At 0x80006ce4#64 (eL sp ua ub adp bdp ix S j0 j8 j11) M (kF v) outp)
      (At 0x80006cb8#64 (cL sp ua ub adp bdp (ix + 1) (S / 268435456) (ix + 1) (ix + 2) 0 j8)
        (writeLog M (wlog sp ix S)) (kF v) outp) := by
  mh_ctx
  seg_step mhEC 0x80006cb8#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [eL, wp] [cL, wp] [] hc

/-! ## After the loop -/

/-- At the `memcpy` call (`6d88`): `memcpy(c->dp + digs, W + digs, 4 (pa - digs))`, `s1 = olduse`. -/
def mcL (sp ua ub adp bdp ix S dg cdp ou : Nat) (j8 j11 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, BitVec.ofNat 64 (ua + ub - dg - 1)), (9, BitVec.ofNat 64 ou),
   (10, BitVec.ofNat 64 (cdp + 4 * dg)), (11, BitVec.ofNat 64 (sp - 2160 + 4 * dg)),
   (12, BitVec.ofNat 64 (4 * (ua + ub - dg))), (18, mask), (19, BitVec.ofNat 64 ix), (20, BitVec.ofNat 64 (ua + ub)),
   (21, BitVec.ofNat 64 ub), (22, BitVec.ofNat 64 S), (23, BitVec.ofNat 64 adp), (24, j8), (25, BitVec.ofNat 64 ua),
   (26, BitVec.ofNat 64 bdp), (27, j11)]

/-- `c` and the spills, after the loop. -/
structure TFacts (M : Mem) (sp pc cdp ou dg : Nat) : Prop where
  k : KF sp
  rc : Ram pc 24
  pc_al : pc % 8 = 0
  dg_v : bytesT8 M (sp - 2192) = BitVec.ofNat 64 dg
  dg4_v : bytesT8 M (sp - 2192 + 16) = BitVec.ofNat 64 (4 * dg)
  pc_v : bytesT8 M (sp - 2192 + 8) = BitVec.ofNat 64 pc
  cdp_v : bytesT8 M (pc + 16) = BitVec.ofNat 64 cdp
  ou_v : bytesT4 M pc = BitVec.ofNat 32 ou
  ou_lt : ou < 2 ^ 31
  code_c : pc + 24 ≤ sMpMulHighDigsFastBase ∨ sMpMulHighDigsFastBase + 624 ≤ pc

/-- At `6d64`: `s0 = pa - digs`, `a1 = W + digs`, `a4 = 4 digs`, `a5 = c->dp`. -/
def t1L (sp ua ub adp bdp ix S dg cdp : Nat) (j8 j11 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, BitVec.ofNat 64 (ua + ub - dg)), (9, wp sp ix),
   (11, BitVec.ofNat 64 (sp - 2160 + 4 * dg)), (14, BitVec.ofNat 64 (4 * dg)), (15, BitVec.ofNat 64 cdp),
   (18, mask), (19, BitVec.ofNat 64 ix), (20, BitVec.ofNat 64 (ua + ub)), (21, BitVec.ofNat 64 ub),
   (22, BitVec.ofNat 64 S), (23, BitVec.ofNat 64 adp), (24, j8), (25, BitVec.ofNat 64 ua), (26, BitVec.ofNat 64 bdp),
   (27, j11)]

/-- The spills and `c->dp`. -/
theorem t1a_step (v : Abi) (outp : Array String) (sp ua ub adp bdp ix S dg pc cdp ou : Nat)
    (j0 j8 j11 : BitVec 64) (M : Mem) (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode)
    (hf : TFacts M sp pc cdp ou dg) (hp : ua + ub < 2 ^ 30) (hdg : dg < ua + ub) :
    Triple (At 0x80006d44#64 (eL sp ua ub adp bdp ix S j0 j8 j11) M (kF v) outp)
      (At 0x80006d64#64 (t1L sp ua ub adp bdp ix S dg cdp j8 j11) (writeLog M []) (kF v) outp) := by
  mh_ctx
  have h1 := hf.dg_v; have h2 := hf.dg4_v; have h3 := hf.pc_v; have h4 := hf.cdp_v
  seg_stepx mhT1a 0x80006d64#64 [rd8 M (sp - 2192), rd8 M (sp - 2192 + 16), rd8 M (sp - 2192 + 8), rd8 M (pc + 16),
      rd8 M (sp - 2192 + 16)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [eL, wp] [t1L, wp] [h1, h2, h3, h4] hc

/-- `olduse := c->used`, `c->used := pa`, set up `memcpy`. -/
theorem t1b_step (v : Abi) (outp : Array String) (sp ua ub adp bdp ix S dg pc cdp ou : Nat)
    (j8 j11 : BitVec 64) (M : Mem) (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode)
    (hf : TFacts M sp pc cdp ou dg) (hp : ua + ub < 2 ^ 30) (hdg : dg < ua + ub) (hcd : cdp + 4 * dg < 2 ^ 32) :
    Triple (At 0x80006d64#64 (t1L sp ua ub adp bdp ix S dg cdp j8 j11) M (kF v) outp)
      (At 0x80006d88#64 (mcL sp ua ub adp bdp ix S dg cdp ou j8 j11)
        (writeLog M [(pc, 4, BitVec.ofNat 64 (ua + ub))]) (kF v) outp) := by
  mh_ctx
  have h3 := hf.pc_v
  have h5 : BitVec.signExtend 64 (bytesT4 M pc) = BitVec.ofNat 64 ou := by
    rw [hf.ou_v, signExtend_ofNat32 _ hf.ou_lt]
  seg_stepx mhT1b 0x80006d88#64 [rd8 M (sp - 2192 + 8), rd4 M pc]
    [2, 8, 9, 11, 14, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [t1L, wp] [mcL] [h3, h5] hc

/-- After `memcpy` (`6d8c`): `a0 = c->dp + digs + 4 (pa - digs)`. -/
theorem t2_step (v : Abi) (outp : Array String) (u : Abi) (cdp dg P : Nat) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (h0 : u.s0 = BitVec.ofNat 64 (P - dg - 1))
    (hdg : dg < P) (hP : P < 2 ^ 30) (hcd : cdp + 4 * P ≤ 2 ^ 32) :
    Triple (At 0x80006d8c#64 ((10, BitVec.ofNat 64 (cdp + 4 * dg)) :: abiL u) M (kF v) outp)
      (At 0x80006d98#64 ((10, BitVec.ofNat 64 (cdp + 4 * P)) :: abiL { u with s0 := BitVec.ofNat 64 (4 * (P - dg - 1)) })
        (writeLog M []) (kF v) outp) := by
  mh_ctx
  seg_step mhT2 0x80006d98#64 ([] : List (List (BitVec 8)))
    [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [abiL, sKeepL] [abiL, sKeepL] [h0] hc

/-- `olduse ≤ pa`: no `memset`. -/
theorem t3z_step (v : Abi) (outp : Array String) (u : Abi) (sp x ou P : Nat) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hsp : u.sp = BitVec.ofNat 64 (sp - 2192))
    (h1 : u.s.s1 = BitVec.ofNat 64 ou) (hk : KF sp) (hpv : bytesT8 M (sp - 2192 + 24) = BitVec.ofNat 64 P)
    (hou : ou ≤ P) (hP : P < 2 ^ 30) :
    Triple (At 0x80006d98#64 ((10, BitVec.ofNat 64 x) :: abiL u) M (kF v) outp)
      (At 0x80006db0#64 (abiL u) (writeLog M []) (kF v) outp) := by
  mh_ctx
  seg_stepx mhT3z 0x80006db0#64 [rd8 M (sp - 2192 + 24)]
    [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [abiL, sKeepL] [abiL, sKeepL] [hsp, h1, hpv] hc

/-- At the `mp_clamp(c)` call (`6db4`). -/
theorem t4_step (v : Abi) (outp : Array String) (u : Abi) (sp pc : Nat) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hsp : u.sp = BitVec.ofNat 64 (sp - 2192))
    (hk : KF sp) (hpv : bytesT8 M (sp - 2192 + 8) = BitVec.ofNat 64 pc) :
    Triple (At 0x80006db0#64 (abiL u) M (kF v) outp)
      (At 0x80006db4#64 ((10, BitVec.ofNat 64 pc) :: abiL u) (writeLog M []) (kF v) outp) := by
  mh_ctx
  seg_step mhT4 0x80006db4#64 [rd8 M (sp - 2192 + 8)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [abiL, sKeepL] [abiL, sKeepL] [hsp, hpv] hc

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

theorem t5_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hf : HFacts M ra s0 v sp) :
    Triple (At 0x80006db8#64 [(2, BitVec.ofNat 64 (sp - 2192))] M (kF v) outp)
      (At ra (rL ra s0 v sp) (writeLog M []) (kF v) outp) := by
  mh_ctx
  have hra := hf.ra_al
  seg_step mhT5 ra [rd8 M (sp - 8), rd8 M (sp - 16), rd8 M (sp - 24), rd8 M (sp - 32), rd8 M (sp - 40),
      rd8 M (sp - 48), rd8 M (sp - 56), rd8 M (sp - 64), rd8 M (sp - 72), rd8 M (sp - 80), rd8 M (sp - 88),
      rd8 M (sp - 96), rd8 M (sp - 104)]
    [2] kFKeys [] [rL]
    [hf.ra_v, hf.s0_v, hf.s1_v, hf.s2_v, hf.s3_v, hf.s4_v, hf.s5_v, hf.s6_v, hf.s7_v, hf.s8_v, hf.s9_v,
     hf.s10_v, hf.s11_v] hc

/-! ## No column (`digs = pa`) -/

/-- `c`'s digits, `digs` spilled at `pa`'s slot. -/
theorem z1_step (v : Abi) (outp : Array String) (sp pa pb ua ub dg pc cdp ou : Nat) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hf : TFacts M sp pc cdp ou dg) :
    Triple (At 0x80006e20#64 (p3L v sp pa pb ua ub) M (kF v) outp)
      (At 0x80006e30#64 ((10, BitVec.ofNat 64 cdp) :: p3L v sp pa pb ua ub)
        (writeLog M [(sp - 2192 + 24, 8, BitVec.ofNat 64 dg)]) (kF v) outp) := by
  mh_ctx
  have h1 := hf.dg_v; have h3 := hf.pc_v; have h4 := hf.cdp_v
  seg_step mhZ1 0x80006e30#64 [rd8 M (sp - 2192 + 8), rd8 M (pc + 16), rd8 M (sp - 2192)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [p3L] [p3L] [h1, h3, h4] hc

/-- The callee-saved registers on the `digs = pa` path (`s1 = olduse`). -/
def zu (v : Abi) (sp pb ua ub ou : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 2192), s0 := BitVec.ofNat 64 pb,
           s := { v.s with s1 := BitVec.ofNat 64 ou, s4 := BitVec.ofNat 64 (ua + ub), s5 := BitVec.ofNat 64 ub,
                           s9 := BitVec.ofNat 64 ua } }


/-- `olduse := c->used`, `c->used := pa`. -/
theorem z2_step (v : Abi) (outp : Array String) (sp pa pb ua ub dg pc cdp ou : Nat) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) (hf : TFacts M sp pc cdp ou dg)
    (hdg : dg = ua + ub) (hp : ua + ub < 2 ^ 30) (hcd : cdp + 4 * dg ≤ 2 ^ 32) :
    Triple (At 0x80006e30#64 ((10, BitVec.ofNat 64 cdp) :: p3L v sp pa pb ua ub) M (kF v) outp)
      (At 0x80006e48#64 ((10, BitVec.ofNat 64 (cdp + 4 * (ua + ub))) :: abiL (zu v sp pb ua ub ou))
        (writeLog M [(pc, 4, BitVec.ofNat 64 (ua + ub))]) (kF v) outp) := by
  mh_ctx
  have h2 := hf.dg4_v; have h3 := hf.pc_v
  have h5 : BitVec.signExtend 64 (bytesT4 M pc) = BitVec.ofNat 64 ou := by
    rw [hf.ou_v, signExtend_ofNat32 _ hf.ou_lt]
  seg_step mhZ2 0x80006e48#64 [rd8 M (sp - 2192 + 8), rd4 M pc, rd8 M (sp - 2192 + 16), rd8 M (sp - 2192 + 8)]
    [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [p3L] [abiL, zu, sKeepL] [h2, h3, h5] hc
/-- To `6d98`. -/
theorem z3_step (v : Abi) (outp : Array String) (u : Abi) (x : Nat) (M : Mem)
    (hc : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode) :
    Triple (At 0x80006e48#64 ((10, BitVec.ofNat 64 x) :: abiL u) M (kF v) outp)
      (At 0x80006d98#64 ((10, BitVec.ofNat 64 x) :: abiL u) (writeLog M []) (kF v) outp) := by
  mh_ctx
  seg_step mhZ3 0x80006d98#64 ([] : List (List (BitVec 8)))
    [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [abiL, sKeepL] [abiL, sKeepL] [] hc

end Tom.Machine.Fn.MulHighFast
