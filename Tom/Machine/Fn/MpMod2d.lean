import Tom.Machine.Seg.MpMod2d
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Alu1
import Tom.Machine.Kit.BitW
import Vsa.Sim.TripleCat

/-!
# `mp_mod_2d` on the machine: the segments

`mp_mod_2d(a, b, c)` at `0x800057a4` (68 instructions). The segments, in
program order, with the calls between them (made by the assembly, `jal_at`):

* `b = 0`: `z_step` (save `s1`, `ra`) → `jal mp_zero(c)` at `58ac` → `zr_step`
  (restore, `MP_OKAY`).
* `b > 0`: `p1_step`, `p2_step` (load `a->used`, save `s0`), `p3_step`
  (`28 a->used`, `BitW.mul28W'`). Then `b ≥ 28 a->used`: `c_step` (restore,
  tail-jump to `mp_copy(a, c)` at `07e0`); otherwise `k_step` → `jal mp_copy`
  at `57d8` → `d1_step` → `jal __divdi3(b, 28)` at `57e8` → `d2_step` (`s0 := D`)
  → `jal __moddi3(b, 28)` at `57fc` → `m1_step` (`c->used`), `snez_step`
  (`e = (d != 0)`, `Kit/Alu1.lean`). With `x = D + e`: `x = c->used`:
  `m2t_step`; `x < c->used`: `m2f_step` (spill `d`, `c->dp`) → `jal memset(c->dp
  + x, 0, 4 (c->used - x))` at `5834` → `r_step` (reload). Then `x1_step`
  (`&c->dp[D]`), `x2_step` (`c->dp[D] &= 2^d - 1`, `BitW.mask_and`) → `jal
  mp_clamp(c)` at `5864` → `e_step` (restore, `MP_OKAY`).

The libgcc results arrive as `BitVec.sdiv`/`srem` of `ofNat` values:
`BitW.sdiv_ofNat`, `BitW.srem_ofNat` turn them into `ofNat (b / 28)`, `ofNat (b % 28)`.
`s1` is a local, so the segments keep `Abi.keepR1` and carry `s1`.
-/


namespace Tom.Machine.Fn.MpMod2d

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mmod2d_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpMod2dBase = 0x800057a4 := rfl
   have : mpMod2dCode.length = 68 := rfl))

def entry : BitVec 64 := 0x800057a4#64

/-- The entry: `a0 = a`, `a1 = b`, `a2 = c`. -/
def entryL (ra s0 : BitVec 64) (sp pa b pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 b),
   (12, BitVec.ofNat 64 pc)]

/-- The entry (`s1` carried: the function saves it). -/
def entry1 (ra s0 s1 : BitVec 64) (sp pa b pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 b),
   (12, BitVec.ofNat 64 pc)]

/-- The return (`MP_OKAY`), `s1` carried. -/
def ret1 (ra s0 s1 : BitVec 64) (sp : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, 0#64)]

/-- The stack frame. -/
structure FFacts (sp : Nat) : Prop where
  rs : Ram (sp - 48) 48
  sp_al : sp % 16 = 0
  sp_ge : 48 ≤ sp
  code_off : sp ≤ mpMod2dBase ∨ mpMod2dBase + 272 ≤ sp - 48

/-- The first frame stores (`s1`, `ra`). -/
def frameLog1 (ra s1 : BitVec 64) (sp : Nat) : List WEntry :=
  [(sp - 24, 8, s1), (sp - 8, 8, ra)]

/-- At the `mp_zero(c)` call (`58ac`). -/
def zL (ra s0 : BitVec 64) (sp pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 48)), (8, s0), (9, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pc)]

/-- `b = 0`: save `s1`, `ra`; set up `mp_zero(c)`. -/
theorem z_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pc : Nat) (m : Mem)
    (hc : CodeAt m mpMod2dBase mpMod2dCode) (hs : FFacts sp) :
    Triple (At entry (entry1 ra s0 s1 sp pa 0 pc) m v.keepR1 outp)
      (At 0x800058ac#64 (zL ra s0 sp pc) (writeLog m (frameLog1 ra s1 sp)) v.keepR1 outp) := by
  mmod2d_ctx
  seg_step mod2dZ 0x800058ac#64 ([] : List (List (BitVec 8))) [1, 2, 8, 9, 10, 11, 12] abiKeysR1
    [entry, entry1, frameLog1] [zL] [] hc


/-- The saved `ra` and `s1`. -/
structure RFacts1 (M : Mem) (ra s1 : BitVec 64) (sp : Nat) : Prop where
  rs : Ram (sp - 48) 48
  sp_ge : 48 ≤ sp
  ra_v : bytesT8 M (sp - 8) = ra
  s1_v : bytesT8 M (sp - 24) = s1
  ra_al : ra.toNat % 4 = 0

/-- The whole saved frame: `ra`, `s1` and `s0`. -/
structure RFacts (M : Mem) (ra s0 s1 : BitVec 64) (sp : Nat) : Prop extends RFacts1 M ra s1 sp where
  s0_v : bytesT8 M (sp - 16) = s0

/-- After `mp_zero` (`58b0`): restore `ra`, `s1`, return `MP_OKAY`. -/
theorem zr_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pc : Nat) (M : Mem)
    (hc : CodeAt M mpMod2dBase mpMod2dCode) (hf : RFacts1 M ra s1 sp) :
    Triple (At 0x800058b0#64 [(2, BitVec.ofNat 64 (sp - 48)), (8, s0), (9, BitVec.ofNat 64 pc)] M v.keepR1 outp)
      (At ra (ret1 ra s0 s1 sp) (writeLog M []) v.keepR1 outp) := by
  mmod2d_ctx
  have hra := hf.ra_al
  have h1 : bytesT8 M (sp - 48 + 40) = ra := by rw [show sp - 48 + 40 = sp - 8 by omega]; exact hf.ra_v
  have h2 : bytesT8 M (sp - 48 + 24) = s1 := by rw [show sp - 48 + 24 = sp - 24 by omega]; exact hf.s1_v
  seg_step mod2dZR ra [rd8 M (sp - 48 + 40), rd8 M (sp - 48 + 24)] [2, 8, 9] abiKeysR1 [] [ret1] [h1, h2] hc

/-- The prologue's facts: `a->used` and the frame. -/
structure PFacts (m : Mem) (sp pa u : Nat) : Prop where
  ra_ : Ram pa 24
  u_v : bytesT4 m pa = BitVec.ofNat 32 u
  bits : 28 * u < 2 ^ 31

/-- All three frame stores (`s1`, `ra`, `s0`). -/
def frameLog (ra s0 s1 : BitVec 64) (sp : Nat) : List WEntry :=
  [(sp - 24, 8, s1), (sp - 8, 8, ra), (sp - 16, 8, s0)]

/-- At `57b8` (`b > 0`): `s1 = c`. -/
def p1L (s0 : BitVec 64) (sp pa b pc : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, s0), (9, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 b), (12, BitVec.ofNat 64 pc)]

/-- `b > 0`: save `s1`, `ra`. -/
theorem p1_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc : Nat) (m : Mem)
    (hc : CodeAt m mpMod2dBase mpMod2dCode) (hs : FFacts sp) (hb : 0 < b) (hb' : b < 2 ^ 31) :
    Triple (At entry (entry1 ra s0 s1 sp pa b pc) m v.keepR1 outp)
      (At 0x800057b8#64 (p1L s0 sp pa b pc) (writeLog m (frameLog1 ra s1 sp)) v.keepR1 outp) := by
  mmod2d_ctx
  seg_step mod2dP1 0x800057b8#64 ([] : List (List (BitVec 8))) [1, 2, 8, 9, 10, 11, 12] abiKeysR1
    [entry, entry1, frameLog1] [p1L] [] hc

/-- At the `b ≥ 28 a->used` test (`57d4`): `s0 = b`, `s1 = c`, `a5 = 28 a->used`. -/
def pL (sp pa b pc u : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 pc), (15, BitVec.ofNat 64 (28 * u))]

/-- At `57c0`: `a4 = a->used`. -/
def p2L (sp pa b pc u : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (9, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 b),
   (12, BitVec.ofNat 64 pc), (14, BitVec.ofNat 64 u)]

/-- Load `a->used`, save `s0`. -/
theorem p2_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc u : Nat) (M : Mem)
    (hc : CodeAt M mpMod2dBase mpMod2dCode) (hs : FFacts sp) (hf : PFacts M sp pa u) :
    Triple (At 0x800057b8#64 (p1L s0 sp pa b pc) M v.keepR1 outp)
      (At 0x800057c0#64 (p2L sp pa b pc u) (writeLog M [(sp - 16, 8, s0)]) v.keepR1 outp) := by
  mmod2d_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 u := by
    rw [hf.u_v, signExtend_ofNat32 _ (by omega)]
  seg_step mod2dP2 0x800057c0#64 [rd4 M pa] [2, 8, 9, 10, 11, 12] abiKeysR1 [p1L] [p2L] [h1] hc

/-- `s0 := b`, `a5 := 28 a->used`. -/
theorem p3_step (v : Abi) (outp : Array String) (sp pa b pc u : Nat) (M : Mem)
    (hc : CodeAt M mpMod2dBase mpMod2dCode) (hbits : 28 * u < 2 ^ 31) :
    Triple (At 0x800057c0#64 (p2L sp pa b pc u) M v.keepR1 outp)
      (At 0x800057d4#64 (pL sp pa b pc u) (writeLog M []) v.keepR1 outp) := by
  mmod2d_ctx
  have h28 := BitW.mul28W' u hbits
  seg_step mod2dP3 0x800057d4#64 ([] : List (List (BitVec 8))) [2, 9, 10, 11, 12, 14] abiKeysR1 [p2L] [pL] [h28] hc

/-- At the tail jump to `mp_copy(a, c)`: the caller's registers. -/
def cL (ra s0 s1 : BitVec 64) (sp pa pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pc)]

/-- `b ≥ 28 a->used`: restore the frame, tail-jump to `mp_copy(a, c)`. -/
theorem c_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc u : Nat) (M : Mem)
    (hc : CodeAt M mpMod2dBase mpMod2dCode) (hf : RFacts M ra s0 s1 sp) (hb' : b < 2 ^ 31)
    (hbits : 28 * u < 2 ^ 31) (hge : 28 * u ≤ b) :
    Triple (At 0x800057d4#64 (pL sp pa b pc u) M v.keepR1 outp)
      (At 0x800007e0#64 (cL ra s0 s1 sp pa pc) (writeLog M []) v.keepR1 outp) := by
  mmod2d_ctx
  have h1 : bytesT8 M (sp - 48 + 32) = s0 := by rw [show sp - 48 + 32 = sp - 16 by omega]; exact hf.s0_v
  have h2 : bytesT8 M (sp - 48 + 40) = ra := by rw [show sp - 48 + 40 = sp - 8 by omega]; exact hf.ra_v
  have h3 : bytesT8 M (sp - 48 + 24) = s1 := by rw [show sp - 48 + 24 = sp - 24 by omega]; exact hf.s1_v
  seg_step mod2dC 0x800007e0#64 [rd8 M (sp - 48 + 32), rd8 M (sp - 48 + 40), rd8 M (sp - 48 + 24)]
    [2, 8, 9, 10, 11, 15] abiKeysR1 [pL] [cL] [h1, h2, h3] hc

/-- `b < 28 a->used`: on to the `mp_copy(a, c)` call (`57d8`). -/
theorem k_step (v : Abi) (outp : Array String) (sp pa b pc u : Nat) (M : Mem)
    (hc : CodeAt M mpMod2dBase mpMod2dCode) (hb' : b < 2 ^ 31) (hbits : 28 * u < 2 ^ 31) (hlt : b < 28 * u) :
    Triple (At 0x800057d4#64 (pL sp pa b pc u) M v.keepR1 outp)
      (At 0x800057d8#64 (pL sp pa b pc u) (writeLog M []) v.keepR1 outp) := by
  mmod2d_ctx
  seg_step mod2dK 0x800057d8#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10, 11, 15] abiKeysR1 [pL] [pL] [] hc

/-- After a call: `sp`, `s0`, `s1` and `a0 = r`. -/
def aL (sp s0 pc : Nat) (r : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 s0), (9, BitVec.ofNat 64 pc), (10, r)]

/-- At a libgcc call: `a0 = x`, `a1 = 28`. -/
def gL (sp s0 pc x : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 s0), (9, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 x),
   (11, BitVec.ofNat 64 28)]

/-- `mp_copy` returned `MP_OKAY`: set up `__divdi3(b, 28)` (`57e8`). -/
theorem d1_step (v : Abi) (outp : Array String) (sp b pc : Nat) (M : Mem)
    (hc : CodeAt M mpMod2dBase mpMod2dCode) :
    Triple (At 0x800057dc#64 (aL sp b pc 0#64) M v.keepR1 outp)
      (At 0x800057e8#64 (gL sp b pc b) (writeLog M []) v.keepR1 outp) := by
  mmod2d_ctx
  seg_step mod2dD1 0x800057e8#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10] abiKeysR1 [aL] [gL] [] hc

/-- `D = b / 28` returned: `s0 := D`, set up `__moddi3(b, 28)` (`57fc`). -/
theorem d2_step (v : Abi) (outp : Array String) (sp b pc : Nat) (M : Mem)
    (hc : CodeAt M mpMod2dBase mpMod2dCode) (hb' : b < 2 ^ 31) :
    Triple (At 0x800057ec#64 (aL sp b pc (BitVec.ofNat 64 (b / 28))) M v.keepR1 outp)
      (At 0x800057fc#64 (gL sp (b / 28) pc b) (writeLog M []) v.keepR1 outp) := by
  mmod2d_ctx
  have : b / 28 < 2 ^ 31 := by omega
  seg_step mod2dD2 0x800057fc#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10] abiKeysR1 [aL] [gL] [] hc

/-- At the `snez` (`5808`): `a2 = c->used`, `a3 = d`. -/
def m1L (sp D pc u d : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 D), (9, BitVec.ofNat 64 pc), (12, BitVec.ofNat 64 u),
   (13, BitVec.ofNat 64 d)]

/-- `c` after the copy: its `used` and digit pointer. -/
structure CFacts (M : Mem) (pc dp u : Nat) : Prop where
  rc : Ram pc 24
  u_v : bytesT4 M pc = BitVec.ofNat 32 u
  dp_v : bytesT8 M (pc + 16) = BitVec.ofNat 64 dp
  u_lt : u < 2 ^ 31

/-- `d = b % 28` returned: load `c->used`. -/
theorem m1_step (v : Abi) (outp : Array String) (sp D pc u dp d : Nat) (M : Mem)
    (hc : CodeAt M mpMod2dBase mpMod2dCode) (hf : CFacts M pc dp u) (hd : d < 28) :
    Triple (At 0x80005800#64 (aL sp D pc (BitVec.ofNat 64 d)) M v.keepR1 outp)
      (At 0x80005808#64 (m1L sp D pc u d) (writeLog M []) v.keepR1 outp) := by
  mmod2d_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pc) = BitVec.ofNat 64 u := by
    rw [hf.u_v, signExtend_ofNat32 _ hf.u_lt]
  seg_step mod2dM1 0x80005808#64 [rd4 M pc] [2, 8, 9, 10] abiKeysR1 [aL] [m1L] [h1] hc

/-- After the `snez` (`580c`): `a5 = (d != 0)`. -/
def m2L (sp D pc u d e : Nat) : GRegs :=
  [(15, BitVec.ofNat 64 e), (2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 D), (9, BitVec.ofNat 64 pc),
   (12, BitVec.ofNat 64 u), (13, BitVec.ofNat 64 d)]

/-- The `snez a5, a3` at `5808` (`Kit/Alu1.lean`). -/
theorem snez_step (v : Abi) (outp : Array String) (sp D pc u d : Nat) (M : Mem)
    (hc : CodeAt M mpMod2dBase mpMod2dCode) (hd : d < 28) :
    Triple (At 0x80005808#64 (m1L sp D pc u d) M v.keepR1 outp)
      (At 0x8000580c#64 (m2L sp D pc u d (if d = 0 then 0 else 1)) M v.keepR1 outp) := by
  have h := snez_at (pc := 0x80005808#64) (w := 0x00d037b3#32) (rd := 15) (rs2 := 13)
    (L := m1L sp D pc u d) (keep := v.keepR1) (outp := outp)
    (hc.word (a := (0x80005808#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
    (fun s h1 h2 h3 => decodeW s h1 h2 h3)
    ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩
    (by decide) (Or.inr (by simp [keysG, m1L])) (by decide) (by simp [keysG, m1L])
    (by simp [Abi.keepR1, keysG]) (by simp [Abi.keepR1, keysG])
  have hpc : Sail.BitVec.addInt (0x80005808#64 : BitVec 64) 4 = 0x8000580c#64 := by decide
  rw [hpc, show srcVal 13 (m1L sp D pc u d) = BitVec.ofNat 64 d from by simp [srcVal, lookupG, m1L],
    BitW.ite_ofNat_ne_zero (by omega)] at h
  exact Triple.rmap (fun cf h' => h'.reshape (by simp [m1L, m2L, eraseG]) (fun p hp => by simp [hp])) h

/-- At the mask (`5840`): `a3 = d`, `a4 = c->dp`. -/
def xL (sp D pc d dp : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 D), (9, BitVec.ofNat 64 pc), (13, BitVec.ofNat 64 d),
   (14, BitVec.ofNat 64 dp)]

/-- `x = D + (d != 0) = c->used`: nothing to zero. -/
theorem m2t_step (v : Abi) (outp : Array String) (sp D pc u d e dp : Nat) (M : Mem)
    (hc : CodeAt M mpMod2dBase mpMod2dCode) (hf : CFacts M pc dp u) (he : e ≤ 1) (hx : D + e = u) :
    Triple (At 0x8000580c#64 (m2L sp D pc u d e) M v.keepR1 outp)
      (At 0x80005840#64 (xL sp D pc d dp) (writeLog M []) v.keepR1 outp) := by
  mmod2d_ctx
  seg_step mod2dM2T 0x80005840#64 [rd8 M (pc + 16)] [15, 2, 8, 9, 12, 13] abiKeysR1 [m2L] [xL] [hf.dp_v] hc

/-- At the `memset(c->dp + x, 0, 4 (c->used - x))` call (`5834`). -/
def msL (sp D pc dp x n : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 D), (9, BitVec.ofNat 64 pc),
   (10, BitVec.ofNat 64 (dp + 4 * x)), (11, 0#64), (12, BitVec.ofNat 64 (4 * n))]

/-- The spills around `memset` (`d`, `c->dp`). -/
def spillLog (sp d dp : Nat) : List WEntry :=
  [(sp - 40, 8, BitVec.ofNat 64 d), (sp - 48, 8, BitVec.ofNat 64 dp)]

/-- `x < c->used`: spill `d` and `c->dp`, set up `memset`. -/
theorem m2f_step (v : Abi) (outp : Array String) (sp D pc u d e dp : Nat) (M : Mem)
    (hc : CodeAt M mpMod2dBase mpMod2dCode) (hs : FFacts sp) (hf : CFacts M pc dp u) (he : e ≤ 1)
    (hx : D + e < u) (hdp : dp + 4 * u ≤ 2 ^ 32) :
    Triple (At 0x8000580c#64 (m2L sp D pc u d e) M v.keepR1 outp)
      (At 0x80005834#64 (msL sp D pc dp (D + e) (u - (D + e))) (writeLog M (spillLog sp d dp)) v.keepR1 outp) := by
  mmod2d_ctx
  seg_step mod2dM2F 0x80005834#64 [rd8 M (pc + 16)] [15, 2, 8, 9, 12, 13] abiKeysR1 [m2L, spillLog] [msL]
    [hf.dp_v] hc

/-- The spilled `d` and `c->dp`. -/
structure SFacts (M : Mem) (sp d dp : Nat) : Prop where
  rs : Ram (sp - 48) 48
  sp_ge : 48 ≤ sp
  d_v : bytesT8 M (sp - 40) = BitVec.ofNat 64 d
  dp_v : bytesT8 M (sp - 48) = BitVec.ofNat 64 dp

/-- After `memset`: reload `d` and `c->dp`. -/
theorem r_step (v : Abi) (outp : Array String) (sp D pc d dp : Nat) (M : Mem)
    (hc : CodeAt M mpMod2dBase mpMod2dCode) (hf : SFacts M sp d dp) :
    Triple (At 0x80005838#64 [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 D), (9, BitVec.ofNat 64 pc)]
        M v.keepR1 outp)
      (At 0x80005840#64 (xL sp D pc d dp) (writeLog M []) v.keepR1 outp) := by
  mmod2d_ctx
  have h1 : bytesT8 M (sp - 48 + 8) = BitVec.ofNat 64 d := by
    rw [show sp - 48 + 8 = sp - 40 by omega]; exact hf.d_v
  have h2 : bytesT8 M (sp - 48 + 0) = BitVec.ofNat 64 dp := by
    rw [show sp - 48 + 0 = sp - 48 by omega]; exact hf.dp_v
  seg_step mod2dR 0x80005840#64 [rd8 M (sp - 48 + 8), rd8 M (sp - 48 + 0)] [2, 8, 9] abiKeysR1 [] [xL]
    [h1, h2] hc

/-- At `5848`: `a4 = &c->dp[D]`. -/
def x2L (sp pc d q : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (9, BitVec.ofNat 64 pc), (13, BitVec.ofNat 64 d), (14, BitVec.ofNat 64 q)]

/-- `a4 := c->dp + 4 D`. -/
theorem x1_step (v : Abi) (outp : Array String) (sp D pc d dp : Nat) (M : Mem)
    (hc : CodeAt M mpMod2dBase mpMod2dCode) :
    Triple (At 0x80005840#64 (xL sp D pc d dp) M v.keepR1 outp)
      (At 0x80005848#64 (x2L sp pc d (dp + 4 * D)) (writeLog M []) v.keepR1 outp) := by
  mmod2d_ctx
  seg_step mod2dX1 0x80005848#64 ([] : List (List (BitVec 8))) [2, 8, 9, 13, 14] abiKeysR1 [xL] [x2L] [] hc

/-- Digit `D` of `c` (`y`, at `q = c->dp + 4 D`), and its store window. -/
structure XFacts (M : Mem) (q y : Nat) : Prop where
  ry : Ram q 4
  y_v : bytesT4 M q = BitVec.ofNat 32 y
  y_lt : y < 2 ^ 31
  q_al : q % 4 = 0
  code_off : q + 4 ≤ mpMod2dBase ∨ mpMod2dBase + 272 ≤ q

/-- At the `mp_clamp(c)` call (`5864`). -/
def clL (sp pc : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (9, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pc)]

/-- `c->dp[D] &= 2^d - 1`; set up `mp_clamp(c)`. -/
theorem x2_step (v : Abi) (outp : Array String) (sp pc d q y : Nat) (M : Mem)
    (hc : CodeAt M mpMod2dBase mpMod2dCode) (hf : XFacts M q y) (hd : d < 28) :
    Triple (At 0x80005848#64 (x2L sp pc d q) M v.keepR1 outp)
      (At 0x80005864#64 (clL sp pc) (writeLog M [(q, 4, BitVec.ofNat 64 (y % 2 ^ d))]) v.keepR1 outp) := by
  mmod2d_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M q) = BitVec.ofNat 64 y := by
    rw [hf.y_v, signExtend_ofNat32 _ hf.y_lt]
  have hm := BitW.mask_and y d (by omega)
  seg_step mod2dX2 0x80005864#64 [rd4 M q] [2, 9, 13, 14] abiKeysR1 [x2L] [clL] [h1, hm] hc

/-- After `mp_clamp`: restore the frame, return `MP_OKAY`. -/
theorem e_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pc : Nat) (M : Mem)
    (hc : CodeAt M mpMod2dBase mpMod2dCode) (hf : RFacts M ra s0 s1 sp) :
    Triple (At 0x80005868#64 [(2, BitVec.ofNat 64 (sp - 48)), (9, BitVec.ofNat 64 pc)] M v.keepR1 outp)
      (At ra (ret1 ra s0 s1 sp) (writeLog M []) v.keepR1 outp) := by
  mmod2d_ctx
  have hra := hf.ra_al
  have h1 : bytesT8 M (sp - 48 + 32) = s0 := by rw [show sp - 48 + 32 = sp - 16 by omega]; exact hf.s0_v
  have h2 : bytesT8 M (sp - 48 + 40) = ra := by rw [show sp - 48 + 40 = sp - 8 by omega]; exact hf.ra_v
  have h3 : bytesT8 M (sp - 48 + 24) = s1 := by rw [show sp - 48 + 24 = sp - 24 by omega]; exact hf.s1_v
  seg_step mod2dE ra [rd8 M (sp - 48 + 32), rd8 M (sp - 48 + 40), rd8 M (sp - 48 + 24)] [2, 9] abiKeysR1 []
    [ret1] [h1, h2, h3] hc

end Tom.Machine.Fn.MpMod2d
