import Tom.Machine.Seg.MulFast
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.MulCall
import Vsa.Sim.TripleCat

/-!
# `s_mp_mul_digs_fast` on the machine: the segments

`s_mp_mul_digs_fast(a, b, c, digs)` at `0x800042f0` (142 instructions), frame
`2192` bytes: the saved `ra`, `s0`–`s11` at `[sp - 104, sp)`, the column
array `W[MP_WARRAY]` (`512` digits) at `[sp - 2160, sp - 112)`, spills at
`sp - 2192` (`b->dp`), `sp - 2184` (`c`), `sp - 2176` (`a->used + b->used - 1`)
and `sp - 2168` (`1 - b->used`, a negative word).

* prologue `mfP1a`–`mfP1c` (`digs ≥ 0`; the `mp_grow` branch `c->alloc < digs`
  is excluded, D5), `pa = min(digs, a->used + b->used)` (`mfP2t`/`mfP2f`),
  `pa = 0` (`mfP3z`) or the loop set-up (`mfP3`);
* the column head `439c` (`oH`): `ty = min(b->used - 1, ix)`, `tx = ix - ty`,
  `iy = min(a->used - tx, ty + 1)` by three paths (`mfCA`: `ix < b->used`,
  `ix < a->used`; `mfCB`: `ix < b->used ≤ … `, `ix ≥ a->used`; `mfCC0` +
  `mfCCt`/`mfCCf`: `ix ≥ b->used`), the test `iy > 0` (`mfG1`/`mfG0`);
* the inner loop `43c8` (`mfI0` set-up, `mfL1` loads, `jal __muldi3`, `mfL2`
  accumulate / `mfL2e` exit);
* the column store `W[ix] := _W & MP_MASK`, `_W >>= 28` (`mfE1a`/`mfE1b`/
  `mfE1x` after the inner loop, `mfE2*` for an empty column);
* `c->used := pa`, `memcpy(c->dp, W, 4 pa)` (`mfF1`), `memset` of the old
  digits above (`mfF2t`/`mfF2m`; `pa = 0`: `mfZt`/`mfZm`), `mp_clamp(c)`
  (`mfGc`), the epilogue (`mfH`).

All of `s0`–`s11` are locals, so the segments keep only `gp` and `tp` (`kF`)
and carry the others in their lists; registers whose values the C does not
need (`s0`, `s2`, `s9`, `s10` between columns) are parameters (`j0`, …).
-/


namespace Tom.Machine.Fn.MulFast

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mf_ctx" : tactic => `(tactic|
  (facts_ctx
   have : sMpMulDigsFastBase = 0x800042f0 := rfl
   have : sMpMulDigsFastCode.length = 142 := rfl))

/-- The registers every segment keeps. -/
def kF (v : Abi) : GRegs := [(3, v.gp), (4, v.tp)]

abbrev kFKeys : List Nat := [3, 4]

/-- The callee-saved registers as a list (for the calls after the loop). -/
def abiL (u : Abi) : GRegs := (2, u.sp) :: (8, u.s0) :: sKeepL u.s

/-- `b->used - 1` as `addiw` leaves it (all ones for `b->used = 0`). -/
abbrev s6Of (ub : Nat) : BitVec 64 := BitVec.ofNat 64 (ub + 18446744073709551615)

/-! ## The prologue -/

def entL (ra s0 : BitVec 64) (v : Abi) (sp pa pb pc dg : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, v.s.s1), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb),
   (12, BitVec.ofNat 64 pc), (13, BitVec.ofNat 64 dg), (18, v.s.s2), (19, v.s.s3), (20, v.s.s4), (21, v.s.s5),
   (22, v.s.s6), (23, v.s.s7), (24, v.s.s8), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

def p1L (ra s0 : BitVec 64) (v : Abi) (sp pa pb pc dg al : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 2032)), (8, s0), (9, v.s.s1), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 pb), (12, BitVec.ofNat 64 pc), (13, BitVec.ofNat 64 dg), (15, BitVec.ofNat 64 al),
   (18, v.s.s2), (19, v.s.s3), (20, v.s.s4), (21, v.s.s5), (22, v.s.s6), (23, v.s.s7), (24, v.s.s8),
   (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

def p2L (ra s0 : BitVec 64) (v : Abi) (sp pa pb pc dg al : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 2192)), (8, s0), (9, v.s.s1), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 pb), (12, BitVec.ofNat 64 pc), (13, BitVec.ofNat 64 dg), (15, BitVec.ofNat 64 al),
   (18, v.s.s2), (19, v.s.s3), (20, v.s.s4), (21, v.s.s5), (22, v.s.s6), (23, v.s.s7), (24, v.s.s8),
   (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

/-- The saves of `s0`, `s1`, then `s2`, `ra`, `s3`–`s5`. -/
def log1a (s0 : BitVec 64) (v : Abi) (sp : Nat) : List WEntry := [(sp - 16, 8, s0), (sp - 24, 8, v.s.s1)]

def log1b (ra : BitVec 64) (v : Abi) (sp : Nat) : List WEntry :=
  [(sp - 32, 8, v.s.s2), (sp - 8, 8, ra), (sp - 40, 8, v.s.s3), (sp - 48, 8, v.s.s4), (sp - 56, 8, v.s.s5)]

/-- The saves of `s6`–`s11`. -/
def log2 (v : Abi) (sp : Nat) : List WEntry :=
  [(sp - 64, 8, v.s.s6), (sp - 72, 8, v.s.s7), (sp - 80, 8, v.s.s8), (sp - 88, 8, v.s.s9),
   (sp - 96, 8, v.s.s10), (sp - 104, 8, v.s.s11)]

/-- The frame. -/
structure KF (sp : Nat) : Prop where
  rs : Ram (sp - 2192) 2192
  sp_al : sp % 16 = 0
  sp_ge : 2192 ≤ sp
  code_off : sp ≤ sMpMulDigsFastBase ∨ sMpMulDigsFastBase + 568 ≤ sp - 2192

/-- `c->alloc`, `digs ≥ 0`. -/
structure P1Facts (m : Mem) (pc dg al : Nat) : Prop where
  rc : Ram pc 24
  al_v : bytesT4 m (pc + 4) = BitVec.ofNat 32 al
  al_lt : al < 2 ^ 31
  dg_lt : dg < 2 ^ 31

theorem p1a_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc dg al : Nat) (m : Mem)
    (hc : CodeAt m sMpMulDigsFastBase sMpMulDigsFastCode) (hk : KF sp) (hf : P1Facts m pc dg al) :
    Triple (At 0x800042f0#64 (entL ra s0 v sp pa pb pc dg) m (kF v) outp)
      (At 0x80004304#64 (p1L ra s0 v sp pa pb pc dg al) (writeLog m (log1a s0 v sp)) (kF v) outp) := by
  mf_ctx
  have hal : BitVec.signExtend 64 (bytesT4 m (pc + 4)) = BitVec.ofNat 64 al := by
    rw [hf.al_v, signExtend_ofNat32 _ hf.al_lt]
  seg_step mfP1a 0x80004304#64 [rd4 m (pc + 4)] [1, 2, 8, 9, 10, 11, 12, 13, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [entL, log1a] [p1L] [hal] hc

theorem p1d_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc dg al : Nat) (m : Mem)
    (hc : CodeAt m sMpMulDigsFastBase sMpMulDigsFastCode) (hk : KF sp) :
    Triple (At 0x80004304#64 (p1L ra s0 v sp pa pb pc dg al) m (kF v) outp)
      (At 0x80004318#64 (p1L ra s0 v sp pa pb pc dg al) (writeLog m (log1b ra v sp)) (kF v) outp) := by
  mf_ctx
  seg_step mfP1d 0x80004318#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 12, 13, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [p1L, log1b] [p1L] [] hc

theorem p1b_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc dg al : Nat) (m : Mem)
    (hc : CodeAt m sMpMulDigsFastBase sMpMulDigsFastCode) (hk : KF sp) :
    Triple (At 0x80004318#64 (p1L ra s0 v sp pa pb pc dg al) m (kF v) outp)
      (At 0x80004334#64 (p2L ra s0 v sp pa pb pc dg al) (writeLog m (log2 v sp)) (kF v) outp) := by
  mf_ctx
  seg_step mfP1b 0x80004334#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 12, 13, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [p1L, log2] [p2L] [] hc

/-- At `4348`: `s0 = digs`, `s1 = b`, `s2 = a`. -/
def p3L (v : Abi) (sp pa pb dg : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, BitVec.ofNat 64 dg), (9, BitVec.ofNat 64 pb), (18, BitVec.ofNat 64 pa),
   (19, v.s.s3), (20, v.s.s4), (21, v.s.s5), (22, v.s.s6), (23, v.s.s7), (24, v.s.s8), (25, v.s.s9),
   (26, v.s.s10), (27, v.s.s11)]

/-- Save `c`; `c->alloc ≥ digs` (no `mp_grow`). -/
theorem p1c_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc dg al : Nat) (m : Mem)
    (hc : CodeAt m sMpMulDigsFastBase sMpMulDigsFastCode) (hk : KF sp) (hal : al < 2 ^ 31) (hdg : dg ≤ al) :
    Triple (At 0x80004334#64 (p2L ra s0 v sp pa pb pc dg al) m (kF v) outp)
      (At 0x80004348#64 (p3L v sp pa pb dg) (writeLog m [(sp - 2184, 8, BitVec.ofNat 64 pc)]) (kF v) outp) := by
  mf_ctx
  seg_step mfP1c 0x80004348#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 12, 13, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [p2L] [p3L] [] hc

/-- At `435c`: `a4 = pa`. -/
def p4L (v : Abi) (sp pa pb dg ua ub q : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, BitVec.ofNat 64 dg), (9, BitVec.ofNat 64 pb), (14, BitVec.ofNat 64 q),
   (18, BitVec.ofNat 64 pa), (19, BitVec.ofNat 64 ub), (20, v.s.s4), (21, v.s.s5), (22, v.s.s6), (23, v.s.s7),
   (24, BitVec.ofNat 64 ua), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

/-- `a->used`, `b->used`. -/
structure P2Facts (m : Mem) (pa pb ua ub : Nat) : Prop where
  ra_ : Ram pa 24
  rb : Ram pb 24
  ua_v : bytesT4 m pa = BitVec.ofNat 32 ua
  ub_v : bytesT4 m pb = BitVec.ofNat 32 ub
  ua_lt : ua < 2 ^ 30
  ub_lt : ub < 2 ^ 30

theorem P2Facts.sx {m : Mem} {pa pb ua ub : Nat} (h : P2Facts m pa pb ua ub) :
    BitVec.signExtend 64 (bytesT4 m pa) = BitVec.ofNat 64 ua ∧
      BitVec.signExtend 64 (bytesT4 m pb) = BitVec.ofNat 64 ub :=
  ⟨by rw [h.ua_v, signExtend_ofNat32 _ (by have := h.ua_lt; omega)],
   by rw [h.ub_v, signExtend_ofNat32 _ (by have := h.ub_lt; omega)]⟩

/-- `digs < a->used + b->used`: `pa = digs`. -/
theorem p2t_step (v : Abi) (outp : Array String) (sp pa pb dg ua ub : Nat) (m : Mem)
    (hc : CodeAt m sMpMulDigsFastBase sMpMulDigsFastCode) (hf : P2Facts m pa pb ua ub) (hdg : dg < 2 ^ 31)
    (hlt : dg < ua + ub) :
    Triple (At 0x80004348#64 (p3L v sp pa pb dg) m (kF v) outp)
      (At 0x8000435c#64 (p4L v sp pa pb dg ua ub dg) (writeLog m []) (kF v) outp) := by
  mf_ctx
  have ⟨hsa, hsb⟩ := hf.sx
  seg_step mfP2t 0x8000435c#64 [rd4 m pa, rd4 m pb] [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [p3L] [p4L] [hsa, hsb] hc

/-- `digs ≥ a->used + b->used`: `pa = a->used + b->used`. -/
theorem p2f_step (v : Abi) (outp : Array String) (sp pa pb dg ua ub : Nat) (m : Mem)
    (hc : CodeAt m sMpMulDigsFastBase sMpMulDigsFastCode) (hf : P2Facts m pa pb ua ub) (hdg : dg < 2 ^ 31)
    (hge : ua + ub ≤ dg) :
    Triple (At 0x80004348#64 (p3L v sp pa pb dg) m (kF v) outp)
      (At 0x8000435c#64 (p4L v sp pa pb dg ua ub (ua + ub)) (writeLog m []) (kF v) outp) := by
  mf_ctx
  have ⟨hsa, hsb⟩ := hf.sx
  seg_step mfP2f 0x8000435c#64 [rd4 m pa, rd4 m pb] [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [p3L] [p4L] [hsa, hsb] hc

/-- At `450c` (`pa = 0`). -/
def zL (v : Abi) (sp pa pb dg ua ub : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, BitVec.ofNat 64 dg), (9, BitVec.ofNat 64 pb), (14, 0#64),
   (18, BitVec.ofNat 64 pa), (19, BitVec.ofNat 64 ub), (20, 0#64), (21, v.s.s5), (22, v.s.s6), (23, v.s.s7),
   (24, BitVec.ofNat 64 ua), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

theorem p3z_step (v : Abi) (outp : Array String) (sp pa pb dg ua ub : Nat) (m : Mem)
    (hc : CodeAt m sMpMulDigsFastBase sMpMulDigsFastCode) :
    Triple (At 0x8000435c#64 (p4L v sp pa pb dg ua ub 0) m (kF v) outp)
      (At 0x8000450c#64 (zL v sp pa pb dg ua ub) (writeLog m []) (kF v) outp) := by
  mf_ctx
  seg_step mfP3z 0x8000450c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [p4L] [zL] [] hc

/-- The column head `439c`: column `ix`, carry `w`; `s0`, `s2`, `s9`, `s10` are junk. -/
def oH (sp ua ub pa adp ix w : Nat) (j0 j2 j9 j10 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, j0), (9, BitVec.ofNat 64 (sp - 2160 + 4 * ix)), (12, BitVec.ofNat 64 ix),
   (18, j2), (19, BitVec.ofNat 64 ub), (20, BitVec.ofNat 64 pa), (21, 268435455#64), (22, s6Of ub),
   (23, BitVec.ofNat 64 adp), (24, BitVec.ofNat 64 ua), (25, j9), (26, j10), (27, BitVec.ofNat 64 w)]

/-- The spills: `b->dp`, `a->used + b->used - 1`, `1 - b->used`. -/
def spLog (sp ua ub bdp : Nat) : List WEntry :=
  [(sp - 2192, 8, BitVec.ofNat 64 bdp), (sp - 2176, 8, BitVec.ofNat 64 (ua + ub - 1)),
   (sp - 2168, 8, BitVec.ofNat 64 (18446744073709551617 - ub))]

/-- `a->dp`, `b->dp`. -/
structure P3Facts (m : Mem) (pa pb adp bdp : Nat) : Prop where
  ra_ : Ram pa 24
  rb : Ram pb 24
  adp_v : bytesT8 m (pa + 16) = BitVec.ofNat 64 adp
  bdp_v : bytesT8 m (pb + 16) = BitVec.ofNat 64 bdp

/-- `pa > 0`: the loop's set-up. -/
theorem p3_step (v : Abi) (outp : Array String) (sp pa pb dg ua ub q adp bdp : Nat) (m : Mem)
    (hc : CodeAt m sMpMulDigsFastBase sMpMulDigsFastCode) (hk : KF sp) (hf : P3Facts m pa pb adp bdp)
    (hq : 0 < q) (hq' : q < 2 ^ 31) (hua : ua < 2 ^ 30) (hub : ub < 2 ^ 30) (hu : 1 ≤ ua + ub) :
    Triple (At 0x8000435c#64 (p4L v sp pa pb dg ua ub q) m (kF v) outp)
      (At 0x8000439c#64 (oH sp ua ub q adp 0 0 (BitVec.ofNat 64 dg) (BitVec.ofNat 64 pa) v.s.s9 v.s.s10)
        (writeLog m (spLog sp ua ub bdp)) (kF v) outp) := by
  mf_ctx
  seg_stepx mfP3 0x8000439c#64 [rd8 m (pb + 16), rd8 m (pa + 16)]
    [2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [p4L, spLog] [oH, s6Of] [hf.bdp_v, hf.adp_v] hc

/-! ## A column: `tx`, `ty`, `iy` -/

/-- At the inner loop's set-up `43b4`: `s0 = iy`, `a4 = ty`, `s9 = a->dp + tx`, `s2 = ix + 1`. -/
def sL (sp ua ub pa adp ix w tx ty iy : Nat) (j10 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, BitVec.ofNat 64 iy), (9, BitVec.ofNat 64 (sp - 2160 + 4 * ix)),
   (14, BitVec.ofNat 64 ty), (18, BitVec.ofNat 64 (ix + 1)), (19, BitVec.ofNat 64 ub), (20, BitVec.ofNat 64 pa),
   (21, 268435455#64), (22, s6Of ub), (23, BitVec.ofNat 64 adp), (24, BitVec.ofNat 64 ua),
   (25, BitVec.ofNat 64 (adp + 4 * tx)), (26, j10), (27, BitVec.ofNat 64 w)]

/-- At `44b4`/`44bc`: `s0 = iy` (before the `iy > 0` test), `a4 = ty`. -/
def gL (sp ua ub pa adp ix w s0v : Nat) (a4v : BitVec 64) (tx : Nat) (j2 j10 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, BitVec.ofNat 64 s0v), (9, BitVec.ofNat 64 (sp - 2160 + 4 * ix)),
   (12, BitVec.ofNat 64 ix), (14, a4v), (18, j2), (19, BitVec.ofNat 64 ub), (20, BitVec.ofNat 64 pa),
   (21, 268435455#64), (22, s6Of ub), (23, BitVec.ofNat 64 adp), (24, BitVec.ofNat 64 ua),
   (25, BitVec.ofNat 64 (adp + 4 * tx)), (26, j10), (27, BitVec.ofNat 64 w)]

/-- At the column store (`43e4`/`44c4`): the sum `w`; `s0`, `s9`, `s10` junk. -/
def xL (sp ua ub pa adp ix w : Nat) (j0 j9 j10 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, j0), (9, BitVec.ofNat 64 (sp - 2160 + 4 * ix)),
   (18, BitVec.ofNat 64 (ix + 1)), (19, BitVec.ofNat 64 ub), (20, BitVec.ofNat 64 pa), (21, 268435455#64),
   (22, s6Of ub), (23, BitVec.ofNat 64 adp), (24, BitVec.ofNat 64 ua), (25, j9), (26, j10), (27, BitVec.ofNat 64 w)]

/-- `ix < b->used`, `ix < a->used`: `tx = 0`, `ty = ix`, `iy = ix + 1`. -/
theorem ca_step (v : Abi) (outp : Array String) (sp ua ub pa adp ix w : Nat) (j0 j2 j9 j10 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hb : ix < ub) (ha : ix < ua) (hua : ua < 2 ^ 30)
    (hub : ub < 2 ^ 30) :
    Triple (At 0x8000439c#64 (oH sp ua ub pa adp ix w j0 j2 j9 j10) M (kF v) outp)
      (At 0x800043b4#64 (sL sp ua ub pa adp ix w 0 ix (ix + 1) j10) (writeLog M []) (kF v) outp) := by
  mf_ctx
  seg_step mfCA 0x800043b4#64 ([] : List (List (BitVec 8))) [2, 8, 9, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [oH] [sL] [] hc

/-- `ix < b->used`, `ix ≥ a->used`: `tx = 0`, `ty = ix`, `iy = a->used`. -/
theorem cb_step (v : Abi) (outp : Array String) (sp ua ub pa adp ix w : Nat) (j0 j2 j9 j10 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hb : ix < ub) (ha : ua ≤ ix) (hub : ub < 2 ^ 30) :
    Triple (At 0x8000439c#64 (oH sp ua ub pa adp ix w j0 j2 j9 j10) M (kF v) outp)
      (At 0x800044bc#64 (gL sp ua ub pa adp ix w ua (BitVec.ofNat 64 ix) 0 j2 j10) (writeLog M []) (kF v) outp) := by
  mf_ctx
  seg_step mfCB 0x800044bc#64 ([] : List (List (BitVec 8))) [2, 8, 9, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [oH] [gL] [] hc

/-- The spills, as the column set-up reads them. -/
structure SpFacts (M : Mem) (sp ua ub bdp : Nat) : Prop where
  bdp_v : bytesT8 M (sp - 2192) = BitVec.ofNat 64 bdp
  s16_v : bytesT8 M (sp - 2176) = BitVec.ofNat 64 (ua + ub - 1)
  s24_v : bytesT8 M (sp - 2168) = BitVec.ofNat 64 (18446744073709551617 - ub)

/-- `ix ≥ b->used`: `tx = ix + 1 - b->used`, `s0 = a->used - tx`, `a4 = b->used - 1`. -/
theorem cc0_step (v : Abi) (outp : Array String) (sp ua ub pa adp bdp ix w : Nat) (j0 j2 j9 j10 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hk : KF sp) (hs : SpFacts M sp ua ub bdp)
    (hb : ub ≤ ix) (hix : ix < ua + ub) (hua : ua < 2 ^ 30) (hub : ub < 2 ^ 30) :
    Triple (At 0x8000439c#64 (oH sp ua ub pa adp ix w j0 j2 j9 j10) M (kF v) outp)
      (At 0x800044b4#64 (gL sp ua ub pa adp ix w (ua + ub - 1 - ix) (s6Of ub) (ix + 1 - ub) j2 j10)
        (writeLog M []) (kF v) outp) := by
  mf_ctx
  have h1 : bytesT8 M (sp - 2192 + 24) = BitVec.ofNat 64 (18446744073709551617 - ub) := by
    rw [show sp - 2192 + 24 = sp - 2168 by omega]; exact hs.s24_v
  have h2 : bytesT8 M (sp - 2192 + 16) = BitVec.ofNat 64 (ua + ub - 1) := by
    rw [show sp - 2192 + 16 = sp - 2176 by omega]; exact hs.s16_v
  seg_step mfCC0 0x800044b4#64 [rd8 M (sp - 2192 + 24), rd8 M (sp - 2192 + 16)]
    [2, 8, 9, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [oH] [gL] [h1, h2] hc

/-- `ty ≥ a->used - tx`: `iy = a->used - tx`. -/
theorem cct_step (v : Abi) (outp : Array String) (sp ua ub pa adp ix w s0v tx : Nat) (j2 j10 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode)
    (hg : zopz0zKzJ_s (s6Of ub) (BitVec.ofNat 64 s0v) = true) :
    Triple (At 0x800044b4#64 (gL sp ua ub pa adp ix w s0v (s6Of ub) tx j2 j10) M (kF v) outp)
      (At 0x800044bc#64 (gL sp ua ub pa adp ix w s0v (s6Of ub) tx j2 j10) (writeLog M []) (kF v) outp) := by
  mf_ctx
  seg_step mfCCt 0x800044bc#64 ([] : List (List (BitVec 8))) [2, 8, 9, 12, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [gL] [gL] [hg] hc

/-- `ty < a->used - tx`: `iy = b->used`. -/
theorem ccf_step (v : Abi) (outp : Array String) (sp ua ub pa adp ix w s0v tx : Nat) (j2 j10 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode)
    (hg : zopz0zKzJ_s (s6Of ub) (BitVec.ofNat 64 s0v) = false) :
    Triple (At 0x800044b4#64 (gL sp ua ub pa adp ix w s0v (s6Of ub) tx j2 j10) M (kF v) outp)
      (At 0x800044bc#64 (gL sp ua ub pa adp ix w ub (s6Of ub) tx j2 j10) (writeLog M []) (kF v) outp) := by
  mf_ctx
  seg_step mfCCf 0x800044bc#64 ([] : List (List (BitVec 8))) [2, 8, 9, 12, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [gL] [gL] [hg] hc

/-- `iy > 0`: into the inner loop's set-up. -/
theorem g1_step (v : Abi) (outp : Array String) (sp ua ub pa adp ix w s0v ty tx : Nat) (j2 j10 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (h0 : 0 < s0v) (h1 : s0v < 2 ^ 31)
    (hix : ix < 2 ^ 30) :
    Triple (At 0x800044bc#64 (gL sp ua ub pa adp ix w s0v (BitVec.ofNat 64 ty) tx j2 j10) M (kF v) outp)
      (At 0x800043b4#64 (sL sp ua ub pa adp ix w tx ty s0v j10) (writeLog M []) (kF v) outp) := by
  mf_ctx
  seg_step mfG1 0x800043b4#64 ([] : List (List (BitVec 8))) [2, 8, 9, 12, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [gL] [sL] [] hc

/-- `iy = 0`: an empty column. -/
theorem g0_step (v : Abi) (outp : Array String) (sp ua ub pa adp ix w tx : Nat) (a4v j2 j10 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hix : ix < 2 ^ 30) :
    Triple (At 0x800044bc#64 (gL sp ua ub pa adp ix w 0 a4v tx j2 j10) M (kF v) outp)
      (At 0x800044c4#64 (xL sp ua ub pa adp ix w 0#64 (BitVec.ofNat 64 (adp + 4 * tx)) j10) (writeLog M []) (kF v) outp) := by
  mf_ctx
  seg_step mfG0 0x800044c4#64 ([] : List (List (BitVec 8))) [2, 8, 9, 12, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [gL] [xL] [] hc

/-! ## The inner loop -/

/-- The inner loop's head `43c8`, term `iz`, sum `S`. -/
def iH (sp ua ub pa adp ix tx ty iy bdp iz S : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, BitVec.ofNat 64 (adp + 4 * tx + 4 * iy)),
   (9, BitVec.ofNat 64 (sp - 2160 + 4 * ix)), (18, BitVec.ofNat 64 (ix + 1)), (19, BitVec.ofNat 64 ub),
   (20, BitVec.ofNat 64 pa), (21, 268435455#64), (22, s6Of ub), (23, BitVec.ofNat 64 adp), (24, BitVec.ofNat 64 ua),
   (25, BitVec.ofNat 64 (adp + 4 * tx + 4 * iz)), (26, BitVec.ofNat 64 (bdp + 4 * ty - 4 * iz)), (27, BitVec.ofNat 64 S)]

/-- The live registers across the `__muldi3` call: the pointers advanced. -/
def kI (sp ua ub pa adp ix tx ty iy bdp iz S : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2192)), (8, BitVec.ofNat 64 (adp + 4 * tx + 4 * iy)),
   (9, BitVec.ofNat 64 (sp - 2160 + 4 * ix)), (18, BitVec.ofNat 64 (ix + 1)), (19, BitVec.ofNat 64 ub),
   (20, BitVec.ofNat 64 pa), (21, 268435455#64), (22, s6Of ub), (23, BitVec.ofNat 64 adp), (24, BitVec.ofNat 64 ua),
   (25, BitVec.ofNat 64 (adp + 4 * tx + 4 * (iz + 1))), (26, BitVec.ofNat 64 (bdp + 4 * ty - 4 * (iz + 1))),
   (27, BitVec.ofNat 64 S)]

def jI (sp ua ub pa adp ix tx ty iy bdp iz S x y : Nat) : GRegs :=
  (10, BitVec.ofNat 64 x) :: (11, BitVec.ofNat 64 y) :: kI sp ua ub pa adp ix tx ty iy bdp iz S

def rI (sp ua ub pa adp ix tx ty iy bdp iz S p : Nat) : GRegs :=
  (10, BitVec.ofNat 64 p) :: kI sp ua ub pa adp ix tx ty iy bdp iz S

/-- The set-up: `s10 = b->dp + ty`, `s0 = a->dp + tx + iy`. -/
theorem i0_step (v : Abi) (outp : Array String) (sp ua ub pa adp bdp ix w tx ty iy : Nat) (j10 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hk : KF sp)
    (hs : bytesT8 M (sp - 2192) = BitVec.ofNat 64 bdp) (hty : ty < 2 ^ 30) (hiy : iy < 2 ^ 30) :
    Triple (At 0x800043b4#64 (sL sp ua ub pa adp ix w tx ty iy j10) M (kF v) outp)
      (At 0x800043c8#64 (iH sp ua ub pa adp ix tx ty iy bdp 0 w) (writeLog M []) (kF v) outp) := by
  mf_ctx
  seg_step mfI0 0x800043c8#64 [rd8 M (sp - 2192)] [2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [sL] [iH] [hs] hc

/-- A digit read. -/
structure DRead (M : Mem) (a x : Nat) : Prop where
  r : Ram a 4
  v : bytesT4 M a = BitVec.ofNat 32 x
  lt : x < 268435456

theorem zext_ofNat32 (x : Nat) (h : x < 2 ^ 32) :
    zero_extend (m := 64) (BitVec.ofNat 32 x) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  simp [zero_extend, Sail.BitVec.zeroExtend, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega)]

/-- The loads `b->dp[ty - iz]`, `a->dp[tx + iz]`. -/
theorem l1_step (v : Abi) (outp : Array String) (sp ua ub pa adp ix tx ty iy bdp iz S x y : Nat) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hx : DRead M (adp + 4 * tx + 4 * iz) x)
    (hy : DRead M (bdp + 4 * ty - 4 * iz) y) (hb4 : 4 ≤ bdp + 4 * ty - 4 * iz) :
    Triple (At 0x800043c8#64 (iH sp ua ub pa adp ix tx ty iy bdp iz S) M (kF v) outp)
      (At 0x800043d8#64 (jI sp ua ub pa adp ix tx ty iy bdp iz S x y) (writeLog M []) (kF v) outp) := by
  mf_ctx
  have h1 : zero_extend (m := 64) (bytesT4 M (bdp + 4 * ty - 4 * iz)) = BitVec.ofNat 64 y := by
    rw [hy.v, zext_ofNat32 _ (by have := hy.lt; omega)]
  have h2 : zero_extend (m := 64) (bytesT4 M (adp + 4 * tx + 4 * iz)) = BitVec.ofNat 64 x := by
    rw [hx.v, zext_ofNat32 _ (by have := hx.lt; omega)]
  seg_step mfL1 0x800043d8#64 [rd4 M (bdp + 4 * ty - 4 * iz), rd4 M (adp + 4 * tx + 4 * iz)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [iH] [jI, kI] [h1, h2] hc

/-- Accumulate; the back edge (`iz + 1 < iy`). -/
theorem l2_step (v : Abi) (outp : Array String) (sp ua ub pa adp ix tx ty iy bdp iz S p : Nat) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hS : S + p < 2 ^ 64) (hi : iz + 1 < iy)
    (ha : adp + 4 * tx + 4 * iy ≤ 2 ^ 32) :
    Triple (At 0x800043dc#64 (rI sp ua ub pa adp ix tx ty iy bdp iz S p) M (kF v) outp)
      (At 0x800043c8#64 (iH sp ua ub pa adp ix tx ty iy bdp (iz + 1) (S + p)) (writeLog M []) (kF v) outp) := by
  mf_ctx
  seg_step mfL2 0x800043c8#64 ([] : List (List (BitVec 8))) [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [rI, kI] [iH] [] hc

/-- Accumulate; the exit (`iz + 1 = iy`). -/
theorem l2e_step (v : Abi) (outp : Array String) (sp ua ub pa adp ix tx ty iy bdp iz S p : Nat) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hS : S + p < 2 ^ 64) (hi : iz + 1 = iy) :
    Triple (At 0x800043dc#64 (rI sp ua ub pa adp ix tx ty iy bdp iz S p) M (kF v) outp)
      (At 0x800043e4#64 (xL sp ua ub pa adp ix (S + p) (BitVec.ofNat 64 (adp + 4 * tx + 4 * iy))
          (BitVec.ofNat 64 (adp + 4 * tx + 4 * iy)) (BitVec.ofNat 64 (bdp + 4 * ty - 4 * iy)))
        (writeLog M []) (kF v) outp) := by
  mf_ctx
  seg_step mfL2e 0x800043e4#64 ([] : List (List (BitVec 8))) [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [rI, kI] [xL] [] hc

/-! ## The column store -/

/-- The store of `W[ix]`. -/
structure WFacts (sp ix : Nat) : Prop where
  k : KF sp
  ix_lt : ix < 512

theorem e1a_step (v : Abi) (outp : Array String) (sp ua ub pa adp ix w : Nat) (j0 j9 j10 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hf : WFacts sp ix) (hw : w < 2 ^ 64) :
    Triple (At 0x800043e4#64 (xL sp ua ub pa adp ix w j0 j9 j10) M (kF v) outp)
      (At 0x800043ec#64 (xL sp ua ub pa adp ix w j0 j9 j10)
        (writeLog M [(sp - 2160 + 4 * ix, 4, BitVec.ofNat 64 (w % 268435456))]) (kF v) outp) := by
  mf_ctx
  seg_step mfE1a 0x800043ec#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [xL] [xL] [] hc

theorem e1b_step (v : Abi) (outp : Array String) (sp ua ub pa adp ix w : Nat) (j0 j9 j10 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hw : w < 2 ^ 64) (hi : ix + 1 < pa) (hpa : pa < 2 ^ 30) :
    Triple (At 0x800043ec#64 (xL sp ua ub pa adp ix w j0 j9 j10) M (kF v) outp)
      (At 0x8000439c#64 (oH sp ua ub pa adp (ix + 1) (w / 268435456) j0 (BitVec.ofNat 64 (ix + 1)) j9 j10)
        (writeLog M []) (kF v) outp) := by
  mf_ctx
  seg_step mfE1b 0x8000439c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [xL] [oH] [] hc

theorem e1x_step (v : Abi) (outp : Array String) (sp ua ub pa adp ix w : Nat) (j0 j9 j10 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hw : w < 2 ^ 64) (hi : ix + 1 = pa) (hpa : pa < 2 ^ 30) :
    Triple (At 0x800043ec#64 (xL sp ua ub pa adp ix w j0 j9 j10) M (kF v) outp)
      (At 0x800043fc#64 (oH sp ua ub pa adp pa (w / 268435456) j0 (BitVec.ofNat 64 pa) j9 j10)
        (writeLog M []) (kF v) outp) := by
  mf_ctx
  seg_step mfE1x 0x800043fc#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [xL] [oH] [] hc

theorem e2a_step (v : Abi) (outp : Array String) (sp ua ub pa adp ix w : Nat) (j0 j9 j10 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hf : WFacts sp ix) (hw : w < 2 ^ 64) :
    Triple (At 0x800044c4#64 (xL sp ua ub pa adp ix w j0 j9 j10) M (kF v) outp)
      (At 0x800044cc#64 (xL sp ua ub pa adp ix w j0 j9 j10)
        (writeLog M [(sp - 2160 + 4 * ix, 4, BitVec.ofNat 64 (w % 268435456))]) (kF v) outp) := by
  mf_ctx
  seg_step mfE2a 0x800044cc#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [xL] [xL] [] hc

theorem e2b_step (v : Abi) (outp : Array String) (sp ua ub pa adp ix w : Nat) (j0 j9 j10 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hw : w < 2 ^ 64) (hi : ix + 1 < pa) (hpa : pa < 2 ^ 30) :
    Triple (At 0x800044cc#64 (xL sp ua ub pa adp ix w j0 j9 j10) M (kF v) outp)
      (At 0x8000439c#64 (oH sp ua ub pa adp (ix + 1) (w / 268435456) j0 (BitVec.ofNat 64 (ix + 1)) j9 j10)
        (writeLog M []) (kF v) outp) := by
  mf_ctx
  seg_step mfE2b 0x8000439c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [xL] [oH] [] hc

theorem e2x_step (v : Abi) (outp : Array String) (sp ua ub pa adp ix w : Nat) (j0 j9 j10 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hw : w < 2 ^ 64) (hi : ix + 1 = pa) (hpa : pa < 2 ^ 30) :
    Triple (At 0x800044cc#64 (xL sp ua ub pa adp ix w j0 j9 j10) M (kF v) outp)
      (At 0x800043fc#64 (oH sp ua ub pa adp pa (w / 268435456) j0 (BitVec.ofNat 64 pa) j9 j10)
        (writeLog M []) (kF v) outp) := by
  mf_ctx
  seg_step mfE2x 0x800043fc#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [xL] [oH] [] hc

/-! ## After the loop -/

/-- The callee-saved registers after the loop (`s0 = olduse`). -/
def fAbi (v : Abi) (sp ua ub pa adp w ou : Nat) (j2 j9 j10 : BitVec 64) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 2192), s0 := BitVec.ofNat 64 ou,
           s := ⟨BitVec.ofNat 64 (sp - 2160 + 4 * pa), j2, BitVec.ofNat 64 ub, BitVec.ofNat 64 pa, 268435455#64,
                 s6Of ub, BitVec.ofNat 64 adp, BitVec.ofNat 64 ua, j9, j10, BitVec.ofNat 64 w⟩ }

/-- The callee-saved registers on the `pa = 0` path. -/
def zAbi (v : Abi) (sp pa pb dg ua ub : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 2192), s0 := BitVec.ofNat 64 dg,
           s := { v.s with s1 := BitVec.ofNat 64 pb, s2 := BitVec.ofNat 64 pa, s3 := BitVec.ofNat 64 ub,
                           s4 := 0#64, s8 := BitVec.ofNat 64 ua } }

/-- `c`'s struct, from the saved pointer. -/
structure CFacts (M : Mem) (sp pc ou cdp : Nat) : Prop where
  rc : Ram pc 24
  pc_al : pc % 8 = 0
  pc_v : bytesT8 M (sp - 2184) = BitVec.ofNat 64 pc
  ou_v : bytesT4 M pc = BitVec.ofNat 32 ou
  cdp_v : bytesT8 M (pc + 16) = BitVec.ofNat 64 cdp
  ou_lt : ou < 2 ^ 31
  code_c : pc + 24 ≤ sMpMulDigsFastBase ∨ sMpMulDigsFastBase + 568 ≤ pc

theorem CFacts.sx {M : Mem} {sp pc ou cdp : Nat} (h : CFacts M sp pc ou cdp) :
    BitVec.signExtend 64 (bytesT4 M pc) = BitVec.ofNat 64 ou := by
  rw [h.ou_v, signExtend_ofNat32 _ h.ou_lt]

/-- At the `memcpy` call (`4420`): `memcpy(c->dp, W, 4 pa)`. -/
def mcL (v : Abi) (sp ua ub pa adp w ou cdp : Nat) (j2 j9 j10 : BitVec 64) : GRegs :=
  (10, BitVec.ofNat 64 cdp) :: (11, BitVec.ofNat 64 (sp - 2160)) :: (12, BitVec.ofNat 64 (4 * pa)) ::
    abiL (fAbi v sp ua ub pa adp w ou j2 j9 j10)

/-- At `4410`: `a4 = c`, `a5 = c->dp`, `s0 = olduse`. -/
def f1L (v : Abi) (sp ua ub pa adp w ou pc cdp : Nat) (j2 j9 j10 : BitVec 64) : GRegs :=
  (14, BitVec.ofNat 64 pc) :: (15, BitVec.ofNat 64 cdp) :: (11, BitVec.ofNat 64 (sp - 2160)) ::
    abiL (fAbi v sp ua ub pa adp w ou j2 j9 j10)

/-- `olduse := c->used`. -/
theorem f1_step (v : Abi) (outp : Array String) (sp ua ub pa adp w pc ou cdp : Nat) (j0 j2 j9 j10 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hk : KF sp) (hf : CFacts M sp pc ou cdp)
    (hpa : pa < 2 ^ 30) :
    Triple (At 0x800043fc#64 (oH sp ua ub pa adp pa w j0 j2 j9 j10) M (kF v) outp)
      (At 0x80004410#64 (f1L v sp ua ub pa adp w ou pc cdp j2 j9 j10) (writeLog M []) (kF v) outp) := by
  mf_ctx
  have hs := hf.sx
  have h1 : bytesT8 M (sp - 2192 + 8) = BitVec.ofNat 64 pc := by
    rw [show sp - 2192 + 8 = sp - 2184 by omega]; exact hf.pc_v
  seg_step mfF1 0x80004410#64 [rd8 M (sp - 2192 + 8), rd8 M (sp - 2192 + 8), rd8 M (pc + 16), rd4 M pc]
    [2, 8, 9, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [oH] [f1L, abiL, fAbi, sKeepL]
    [h1, hf.cdp_v, hs] hc

/-- `c->used := pa`, set up `memcpy`. -/
theorem f1b_step (v : Abi) (outp : Array String) (sp ua ub pa adp w pc ou cdp : Nat) (j2 j9 j10 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hf : CFacts M sp pc ou cdp)
    (hpa : pa < 2 ^ 30) :
    Triple (At 0x80004410#64 (f1L v sp ua ub pa adp w ou pc cdp j2 j9 j10) M (kF v) outp)
      (At 0x80004420#64 (mcL v sp ua ub pa adp w ou cdp j2 j9 j10)
        (writeLog M [(pc, 4, BitVec.ofNat 64 pa)]) (kF v) outp) := by
  mf_ctx
  seg_step mfF1b 0x80004420#64 ([] : List (List (BitVec 8)))
    [14, 15, 11, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [f1L, abiL, fAbi, sKeepL]
    [mcL, abiL, fAbi, sKeepL] [] hc

/-- After `memcpy` (`4424`): `a0 = c->dp`. -/
def m1L (u : Abi) (cdp : Nat) : GRegs := (10, BitVec.ofNat 64 cdp) :: abiL u

/-- At the `memset` call (`4448`): `memset(c->dp + pa, 0, 4 (olduse - pa))`. -/
def msL (u : Abi) (cdp pa ou : Nat) : GRegs :=
  (10, BitVec.ofNat 64 (cdp + 4 * pa)) :: (11, 0#64) :: (12, BitVec.ofNat 64 (4 * (ou - pa))) :: abiL u

/-- `olduse ≤ pa`: no `memset`. -/
theorem f2t_step (v : Abi) (outp : Array String) (u : Abi) (cdp pa ou : Nat) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (h0 : u.s0 = BitVec.ofNat 64 ou)
    (h4 : u.s.s4 = BitVec.ofNat 64 pa) (hou : ou ≤ pa) (hpa : 1 ≤ pa) (hpa' : pa < 2 ^ 30) (hou' : ou < 2 ^ 31) :
    Triple (At 0x80004424#64 (m1L u cdp) M (kF v) outp) (At 0x8000444c#64 (abiL u) (writeLog M []) (kF v) outp) := by
  mf_ctx
  seg_step mfF2t 0x8000444c#64 ([] : List (List (BitVec 8))) [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [m1L, abiL, sKeepL] [abiL, sKeepL] [h0, h4] hc

/-- `olduse > pa`: set up the `memset`. -/
theorem f2m_step (v : Abi) (outp : Array String) (u : Abi) (cdp pa ou : Nat) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (h0 : u.s0 = BitVec.ofNat 64 ou)
    (h4 : u.s.s4 = BitVec.ofNat 64 pa) (hou : pa < ou) (hpa : 1 ≤ pa) (hou' : ou < 2 ^ 31)
    (hcd : cdp + 4 * ou ≤ 2 ^ 32) :
    Triple (At 0x80004424#64 (m1L u cdp) M (kF v) outp)
      (At 0x80004448#64 (msL u cdp pa ou) (writeLog M []) (kF v) outp) := by
  mf_ctx
  seg_step mfF2m 0x80004448#64 ([] : List (List (BitVec 8))) [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [m1L, abiL, sKeepL] [msL, abiL, sKeepL] [h0, h4] hc

/-- At `4518` (`pa = 0`): `a5 = c`, `a2 = olduse`, `a0 = c->dp`. -/
def z1L (v : Abi) (sp pa pb dg ua ub pc ou cdp : Nat) : GRegs :=
  (15, BitVec.ofNat 64 pc) :: (12, BitVec.ofNat 64 ou) :: (10, BitVec.ofNat 64 cdp) :: zL v sp pa pb dg ua ub

theorem z_step (v : Abi) (outp : Array String) (sp pa pb dg ua ub pc ou cdp : Nat) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hk : KF sp) (hf : CFacts M sp pc ou cdp) :
    Triple (At 0x8000450c#64 (zL v sp pa pb dg ua ub) M (kF v) outp)
      (At 0x80004518#64 (z1L v sp pa pb dg ua ub pc ou cdp) (writeLog M []) (kF v) outp) := by
  mf_ctx
  have hs := hf.sx
  have h1 : bytesT8 M (sp - 2192 + 8) = BitVec.ofNat 64 pc := by
    rw [show sp - 2192 + 8 = sp - 2184 by omega]; exact hf.pc_v
  seg_step mfZ 0x80004518#64 [rd8 M (sp - 2192 + 8), rd4 M pc, rd8 M (pc + 16)]
    [2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [zL] [z1L, zL] [h1, hs, hf.cdp_v] hc

/-- The `c->used` store of the `pa = 0` path. -/
structure UFacts (pc : Nat) : Prop where
  rc : Ram pc 24
  pc_al : pc % 8 = 0
  code_c : pc + 24 ≤ sMpMulDigsFastBase ∨ sMpMulDigsFastBase + 568 ≤ pc

/-- `pa = 0`, `olduse = 0`: `c->used := 0`, no `memset`. -/
theorem zt_step (v : Abi) (outp : Array String) (sp pa pb dg ua ub pc cdp : Nat) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hf : UFacts pc) :
    Triple (At 0x80004518#64 (z1L v sp pa pb dg ua ub pc 0 cdp) M (kF v) outp)
      (At 0x8000444c#64 (abiL (zAbi v sp pa pb dg ua ub)) (writeLog M [(pc, 4, 0#64)]) (kF v) outp) := by
  mf_ctx
  seg_step mfZt 0x8000444c#64 ([] : List (List (BitVec 8)))
    [15, 12, 10, 2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [z1L, zL]
    [abiL, zAbi, sKeepL] [] hc

/-- `pa = 0`, `olduse > 0`: `c->used := 0`, set up `memset(c->dp, 0, 4 olduse)`. -/
theorem zm_step (v : Abi) (outp : Array String) (sp pa pb dg ua ub pc ou cdp : Nat) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hf : UFacts pc) (hou : 0 < ou) (hou' : ou < 2 ^ 31) :
    Triple (At 0x80004518#64 (z1L v sp pa pb dg ua ub pc ou cdp) M (kF v) outp)
      (At 0x80004448#64 (msL (zAbi v sp pa pb dg ua ub) cdp 0 ou) (writeLog M [(pc, 4, 0#64)]) (kF v) outp) := by
  mf_ctx
  seg_step mfZm 0x80004448#64 ([] : List (List (BitVec 8)))
    [15, 12, 10, 2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [z1L, zL]
    [msL, abiL, zAbi, sKeepL] [] hc

/-- At the `mp_clamp` call (`4450`): `a0 = c`. -/
def clL (u : Abi) (pc : Nat) : GRegs := (10, BitVec.ofNat 64 pc) :: abiL u

theorem gc_step (v : Abi) (outp : Array String) (u : Abi) (sp pc : Nat) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hk : KF sp) (hsp : u.sp = BitVec.ofNat 64 (sp - 2192))
    (hp : bytesT8 M (sp - 2184) = BitVec.ofNat 64 pc) :
    Triple (At 0x8000444c#64 (abiL u) M (kF v) outp) (At 0x80004450#64 (clL u pc) (writeLog M []) (kF v) outp) := by
  mf_ctx
  have h1 : bytesT8 M (sp - 2192 + 8) = BitVec.ofNat 64 pc := by
    rw [show sp - 2192 + 8 = sp - 2184 by omega]; exact hp
  seg_step mfGc 0x80004450#64 [rd8 M (sp - 2192 + 8)] [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [abiL, sKeepL] [clL, abiL, sKeepL] [hsp, h1] hc

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

theorem h_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hf : HFacts M ra s0 v sp) :
    Triple (At 0x80004454#64 [(2, BitVec.ofNat 64 (sp - 2192))] M (kF v) outp)
      (At ra (rL ra s0 v sp) (writeLog M []) (kF v) outp) := by
  mf_ctx
  have hra := hf.ra_al
  seg_step mfH ra [rd8 M (sp - 8), rd8 M (sp - 16), rd8 M (sp - 24), rd8 M (sp - 32), rd8 M (sp - 40),
      rd8 M (sp - 48), rd8 M (sp - 56), rd8 M (sp - 64), rd8 M (sp - 72), rd8 M (sp - 80), rd8 M (sp - 88),
      rd8 M (sp - 96), rd8 M (sp - 104)]
    [2] kFKeys [] [rL]
    [hf.ra_v, hf.s0_v, hf.s1_v, hf.s2_v, hf.s3_v, hf.s4_v, hf.s5_v, hf.s6_v, hf.s7_v, hf.s8_v, hf.s9_v,
     hf.s10_v, hf.s11_v] hc

end Tom.Machine.Fn.MulFast
