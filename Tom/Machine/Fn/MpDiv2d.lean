import Tom.Machine.Seg.MpDiv2d
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.BitW
import Tom.Machine.Kit.BitD
import Vsa.Sim.TripleCat

/-!
# `mp_div_2d` on the machine: the segments

`mp_div_2d(a, b, c, d)` at `0x8000520c` (95 instructions), with `d = NULL`
(`a3 = 0`: every caller in the image but `mp_reduce_2k(_l)` passes `NULL`; those
pass `d = a`, which needs the in-place `mp_mod_2d`). The segments, in program
order, with the calls between them (made by the assembly, `call_std`):

* `b = 0`: `z_step` (save `s1`, `ra`, `s0`, spill `d`) → `jal mp_copy(a, c)` at
  `532c` → `zr_step` (`d = NULL`: restore, return `mp_copy`'s `MP_OKAY`).
* `b > 0`: `p1_step` (save `s1`, `ra`, `s0`), `p2_step` (save `s2`, `s3`, spill
  `d`) → `jal mp_copy(a, c)` at `523c`. Then `b < 28`: `s_step` → `jal
  __moddi3(b, 28)` at `5274`; `b ≥ 28`: `l_step` → `jal __divdi3(b, 28)` at
  `5374` → `r_step` → `jal mp_rshd(c, D)` at `5380` → `r2_step` → `jal __moddi3`
  at `5274`. With `dd = b % 28`: `dd = 0`: `dz_step`; `c->used = 0`: `uz_step`;
  otherwise `i_step` (the masks) into the loop at `52bc`, which runs from the
  top digit down: `lp_step` (back edge) / `lx_step` (last iteration, `x = 0`)
  store `(e >> dd) | (r << (28 - dd))` into digit `x` and carry `e & (2^dd - 1)`
  (`Kit/BitD.lean`). Then `jal mp_clamp(c)` at `52e0` → `e_step` (restore,
  `MP_OKAY`).

`s0` (the error), `s1 = c`, `s2 = b`, `s3 = a` are locals: the segments keep
`keepD` and carry `s1`–`s3`.
-/



namespace Tom.Machine.Fn.MpDiv2d

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mdiv2d_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpDiv2dBase = 0x8000520c := rfl
   have : mpDiv2dCode.length = 95 := rfl))

def entry : BitVec 64 := 0x8000520c#64

/-- `Abi.keepR1` without `s2`, `s3` (locals here). -/
def keepD (v : Abi) : GRegs :=
  [(3, v.gp), (4, v.tp), (20, v.s.s4), (21, v.s.s5), (22, v.s.s6), (23, v.s.s7), (24, v.s.s8),
   (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

abbrev keysD : List Nat := [3, 4, 20, 21, 22, 23, 24, 25, 26, 27]

/-- The entry: `a0 = a`, `a1 = b`, `a2 = c`, `a3 = d = NULL`. -/
def entryL (ra s0 : BitVec 64) (sp pa b pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 b),
   (12, BitVec.ofNat 64 pc), (13, 0#64)]

/-- The entry, `s1`–`s3` carried. -/
def entry1 (ra s0 s1 s2 s3 : BitVec 64) (sp pa b pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 b),
   (12, BitVec.ofNat 64 pc), (13, 0#64), (18, s2), (19, s3)]

/-- The return (`MP_OKAY`), `s1`–`s3` carried. -/
def ret1 (ra s0 s1 s2 s3 : BitVec 64) (sp : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, 0#64), (18, s2), (19, s3)]

/-- The stack frame. -/
structure FFacts (sp : Nat) : Prop where
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  code_off : sp ≤ mpDiv2dBase ∨ mpDiv2dBase + 380 ≤ sp - 64

/-- The first frame stores (`s1`, `ra`, `s0`). -/
def frameLog1 (ra s0 s1 : BitVec 64) (sp : Nat) : List WEntry :=
  [(sp - 24, 8, s1), (sp - 8, 8, ra), (sp - 16, 8, s0)]

/-! ## `b = 0` -/

/-- At the `mp_copy(a, c)` call of `b = 0` (`532c`). -/
def zL (s0 s2 s3 : BitVec 64) (sp pa pc : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, s0), (9, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 pc), (18, s2), (19, s3)]

/-- `b = 0`: save `s1`, `ra`, `s0`, spill `d`; set up `mp_copy(a, c)`. -/
theorem z_step (ra s0 s1 s2 s3 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pc : Nat) (m : Mem)
    (hc : CodeAt m mpDiv2dBase mpDiv2dCode) (hs : FFacts sp) :
    Triple (At entry (entry1 ra s0 s1 s2 s3 sp pa 0 pc) m (keepD v) outp)
      (At 0x8000532c#64 (zL s0 s2 s3 sp pa pc) (writeLog m (frameLog1 ra s0 s1 sp ++ [(sp - 56, 8, 0#64)]))
        (keepD v) outp) := by
  mdiv2d_ctx
  seg_step div2dZ 0x8000532c#64 ([] : List (List (BitVec 8))) [1, 2, 8, 9, 10, 11, 12, 13, 18, 19] keysD
    [entry, entry1, frameLog1] [zL] [] hc

/-- The saved `ra`, `s0`, `s1` and the spilled `d = NULL`. -/
structure RFacts1 (M : Mem) (ra s0 s1 : BitVec 64) (sp : Nat) : Prop where
  rs : Ram (sp - 64) 64
  sp_ge : 64 ≤ sp
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  s1_v : bytesT8 M (sp - 24) = s1
  d_v : bytesT8 M (sp - 56) = 0#64
  ra_al : ra.toNat % 4 = 0

/-- After `mp_copy` (`5330`), `d = NULL`: restore, return `MP_OKAY`. -/
theorem zr_step (ra s0 s1 s2 s3 : BitVec 64) (v : Abi) (outp : Array String) (sp pc : Nat) (M : Mem)
    (hc : CodeAt M mpDiv2dBase mpDiv2dCode) (hf : RFacts1 M ra s0 s1 sp) :
    Triple (At 0x80005330#64 [(2, BitVec.ofNat 64 (sp - 64)), (9, BitVec.ofNat 64 pc), (10, 0#64), (18, s2),
        (19, s3)] M (keepD v) outp)
      (At ra (ret1 ra s0 s1 s2 s3 sp) (writeLog M []) (keepD v) outp) := by
  mdiv2d_ctx
  have hra := hf.ra_al
  have h0 : bytesT8 M (sp - 64 + 8) = 0#64 := by rw [show sp - 64 + 8 = sp - 56 by omega]; exact hf.d_v
  have h1 : bytesT8 M (sp - 64 + 56) = ra := by rw [show sp - 64 + 56 = sp - 8 by omega]; exact hf.ra_v
  have h2 : bytesT8 M (sp - 64 + 48) = s0 := by rw [show sp - 64 + 48 = sp - 16 by omega]; exact hf.s0_v
  have h3 : bytesT8 M (sp - 64 + 40) = s1 := by rw [show sp - 64 + 40 = sp - 24 by omega]; exact hf.s1_v
  seg_step div2dZR ra [rd8 M (sp - 64 + 8), rd8 M (sp - 64 + 56), rd8 M (sp - 64 + 48), rd8 M (sp - 64 + 40)]
    [2, 9, 10, 18, 19] keysD [] [ret1] [h0, h1, h2, h3] hc

/-! ## `b > 0`: the prologue and the copy -/

/-- At `5224` (`b > 0`): `s1 = c`. -/
def p1L (s0 s2 s3 : BitVec 64) (sp pa b pc : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, s0), (9, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 b), (12, BitVec.ofNat 64 pc), (13, 0#64), (18, s2), (19, s3)]

/-- `b > 0`: save `s1`, `ra`, `s0`. -/
theorem p1_step (ra s0 s1 s2 s3 : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc : Nat) (m : Mem)
    (hc : CodeAt m mpDiv2dBase mpDiv2dCode) (hs : FFacts sp) (hb : 0 < b) (hb' : b < 2 ^ 31) :
    Triple (At entry (entry1 ra s0 s1 s2 s3 sp pa b pc) m (keepD v) outp)
      (At 0x80005224#64 (p1L s0 s2 s3 sp pa b pc) (writeLog m (frameLog1 ra s0 s1 sp)) (keepD v) outp) := by
  mdiv2d_ctx
  seg_step div2dP1 0x80005224#64 ([] : List (List (BitVec 8))) [1, 2, 8, 9, 10, 11, 12, 13, 18, 19] keysD
    [entry, entry1, frameLog1] [p1L] [] hc

/-- The second frame stores (`s2`, `s3`, `d`). -/
def frameLog2 (s2 s3 : BitVec 64) (sp : Nat) : List WEntry :=
  [(sp - 32, 8, s2), (sp - 40, 8, s3), (sp - 56, 8, 0#64)]

/-- At the `mp_copy(a, c)` call of `b > 0` (`523c`): `s2 = b`, `s3 = a`. -/
def cpL (s0 : BitVec 64) (sp pa b pc : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, s0), (9, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 pc), (18, BitVec.ofNat 64 b), (19, BitVec.ofNat 64 pa)]

/-- Save `s2`, `s3`, spill `d`; set up `mp_copy(a, c)`. -/
theorem p2_step (s0 s2 s3 : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc : Nat) (M : Mem)
    (hc : CodeAt M mpDiv2dBase mpDiv2dCode) (hs : FFacts sp) :
    Triple (At 0x80005224#64 (p1L s0 s2 s3 sp pa b pc) M (keepD v) outp)
      (At 0x8000523c#64 (cpL s0 sp pa b pc) (writeLog M (frameLog2 s2 s3 sp)) (keepD v) outp) := by
  mdiv2d_ctx
  seg_step div2dP2 0x8000523c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10, 11, 12, 13, 18, 19] keysD
    [p1L, frameLog2] [cpL] [] hc

/-- After a call: `sp`, `s1 = c`, `s2 = b`, `s3 = a` and `a0 = r`. -/
def aL (sp pa b pc : Nat) (r : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (9, BitVec.ofNat 64 pc), (10, r), (18, BitVec.ofNat 64 b),
   (19, BitVec.ofNat 64 pa)]

/-- After a call, `s0 = MP_OKAY`. -/
def kL (sp pa b pc : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, 0#64), (9, BitVec.ofNat 64 pc), (18, BitVec.ofNat 64 b),
   (19, BitVec.ofNat 64 pa)]

/-- After a call, `s0 = MP_OKAY`, `a0 = r`. -/
def a0L (sp pa b pc : Nat) (r : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, 0#64), (9, BitVec.ofNat 64 pc), (10, r), (18, BitVec.ofNat 64 b),
   (19, BitVec.ofNat 64 pa)]

/-- At a libgcc call: `a0 = b`, `a1 = 28`. -/
def gL (sp pa b pc : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, 0#64), (9, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 b),
   (11, BitVec.ofNat 64 28), (18, BitVec.ofNat 64 b), (19, BitVec.ofNat 64 pa)]

/-- The spilled `d = NULL`. -/
structure DFacts (M : Mem) (sp : Nat) : Prop where
  rs : Ram (sp - 64) 64
  sp_ge : 64 ≤ sp
  d_v : bytesT8 M (sp - 56) = 0#64

/-- `mp_copy` returned `MP_OKAY`, `d = NULL`, `b < 28`: set up `__moddi3(b, 28)` (`5274`). -/
theorem s_step (v : Abi) (outp : Array String) (sp pa b pc : Nat) (M : Mem)
    (hc : CodeAt M mpDiv2dBase mpDiv2dCode) (hf : DFacts M sp) (hb : b < 28) :
    Triple (At 0x80005240#64 (aL sp pa b pc 0#64) M (keepD v) outp)
      (At 0x80005274#64 (gL sp pa b pc) (writeLog M []) (keepD v) outp) := by
  mdiv2d_ctx
  have h0 : bytesT8 M (sp - 64 + 8) = 0#64 := by rw [show sp - 64 + 8 = sp - 56 by omega]; exact hf.d_v
  seg_step div2dS 0x80005274#64 [rd8 M (sp - 64 + 8)] [2, 9, 10, 18, 19] keysD [aL] [gL] [h0] hc

/-- `mp_copy` returned `MP_OKAY`, `d = NULL`, `b ≥ 28`: set up `__divdi3(b, 28)` (`5374`). -/
theorem l_step (v : Abi) (outp : Array String) (sp pa b pc : Nat) (M : Mem)
    (hc : CodeAt M mpDiv2dBase mpDiv2dCode) (hf : DFacts M sp) (hb : 28 ≤ b) (hb' : b < 2 ^ 31) :
    Triple (At 0x80005240#64 (aL sp pa b pc 0#64) M (keepD v) outp)
      (At 0x80005374#64 (gL sp pa b pc) (writeLog M []) (keepD v) outp) := by
  mdiv2d_ctx
  have h0 : bytesT8 M (sp - 64 + 8) = 0#64 := by rw [show sp - 64 + 8 = sp - 56 by omega]; exact hf.d_v
  seg_step div2dL 0x80005374#64 [rd8 M (sp - 64 + 8)] [2, 9, 10, 18, 19] keysD [aL] [gL] [h0] hc

/-- At the `mp_rshd(c, D)` call (`5380`). -/
def rsL (sp pa b pc D : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, 0#64), (9, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pc),
   (11, BitVec.ofNat 64 D), (18, BitVec.ofNat 64 b), (19, BitVec.ofNat 64 pa)]

/-- `D = b / 28` returned: set up `mp_rshd(c, D)`. -/
theorem r_step (v : Abi) (outp : Array String) (sp pa b pc : Nat) (M : Mem)
    (hc : CodeAt M mpDiv2dBase mpDiv2dCode) (hb' : b < 2 ^ 31) :
    Triple (At 0x80005378#64 (a0L sp pa b pc (BitVec.ofNat 64 (b / 28))) M (keepD v) outp)
      (At 0x80005380#64 (rsL sp pa b pc (b / 28)) (writeLog M []) (keepD v) outp) := by
  mdiv2d_ctx
  have : b / 28 < 2 ^ 31 := by omega
  seg_step div2dR 0x80005380#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10, 18, 19] keysD [a0L] [rsL] [] hc

/-- After `mp_rshd`: set up `__moddi3(b, 28)` (`5274`). -/
theorem r2_step (v : Abi) (outp : Array String) (sp pa b pc : Nat) (M : Mem)
    (hc : CodeAt M mpDiv2dBase mpDiv2dCode) :
    Triple (At 0x80005384#64 (kL sp pa b pc) M (keepD v) outp)
      (At 0x80005274#64 (gL sp pa b pc) (writeLog M []) (keepD v) outp) := by
  mdiv2d_ctx
  seg_step div2dR2 0x80005274#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 19] keysD [kL] [gL] [] hc

/-! ## After `__moddi3`: the bit loop -/

/-- At the `mp_clamp(c)` call (`52e0`). -/
def clL (sp pa b pc : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, 0#64), (9, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pc),
   (18, BitVec.ofNat 64 b), (19, BitVec.ofNat 64 pa)]

/-- `dd = b % 28 = 0`: no bit loop, set up `mp_clamp(c)`. -/
theorem dz_step (v : Abi) (outp : Array String) (sp pa b pc : Nat) (M : Mem)
    (hc : CodeAt M mpDiv2dBase mpDiv2dCode) :
    Triple (At 0x80005278#64 (a0L sp pa b pc (BitVec.ofNat 64 0)) M (keepD v) outp)
      (At 0x800052e0#64 (clL sp pa b pc) (writeLog M []) (keepD v) outp) := by
  mdiv2d_ctx
  seg_step div2dDZ 0x800052e0#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10, 18, 19] keysD [a0L] [clL] [] hc

/-- `c->used` and `c->dp`. -/
structure UFacts (M : Mem) (pc dp u : Nat) : Prop where
  rc : Ram pc 24
  u_v : bytesT4 M pc = BitVec.ofNat 32 u
  dp_v : bytesT8 M (pc + 16) = BitVec.ofNat 64 dp
  u_lt : u < 2 ^ 31

/-- `dd != 0`, `c->used = 0`: no bit loop, set up `mp_clamp(c)`. -/
theorem uz_step (v : Abi) (outp : Array String) (sp pa b pc dd dp : Nat) (M : Mem)
    (hc : CodeAt M mpDiv2dBase mpDiv2dCode) (hf : UFacts M pc dp 0) (hd : 0 < dd) (hd' : dd < 28) :
    Triple (At 0x80005278#64 (a0L sp pa b pc (BitVec.ofNat 64 dd)) M (keepD v) outp)
      (At 0x800052e0#64 (clL sp pa b pc) (writeLog M []) (keepD v) outp) := by
  mdiv2d_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pc) = BitVec.ofNat 64 0 := by
    rw [hf.u_v, signExtend_ofNat32 _ hf.u_lt]
  seg_step div2dUZ 0x800052e0#64 [rd4 M pc] [2, 8, 9, 10, 18, 19] keysD [a0L] [clL] [h1] hc

/-- The loop's head (`52bc`), digit `x`, carry `r`: `a0 = dd`, `a1 = c->dp - 4`,
`a4 = &c->dp[x]`, `a5 = r`, `a6 = 2^dd - 1`, `a7 = 28 - dd`. -/
def lpL (sp pa b pc dd dp x r : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, 0#64), (9, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 dd),
   (11, BitVec.ofNat 64 (dp - 4)), (14, BitVec.ofNat 64 (dp + 4 * x)), (15, BitVec.ofNat 64 r),
   (16, BitVec.ofNat 64 (2 ^ dd - 1)), (17, BitVec.ofNat 64 (28 - dd)), (18, BitVec.ofNat 64 b),
   (19, BitVec.ofNat 64 pa)]

/-- `c->dp`'s digits in RAM. -/
structure IFacts (M : Mem) (pc dp u : Nat) : Prop extends UFacts M pc dp u where
  rd : Ram dp (4 * u)

/-- `dd != 0`, `c->used > 0`: the masks, enter the loop at the top digit `x = u - 1`, `r = 0`. -/
theorem i_step (v : Abi) (outp : Array String) (sp pa b pc dd dp u : Nat) (M : Mem)
    (hc : CodeAt M mpDiv2dBase mpDiv2dCode) (hf : IFacts M pc dp u) (hu : 0 < u) (hd : 0 < dd) (hd' : dd < 28) :
    Triple (At 0x80005278#64 (a0L sp pa b pc (BitVec.ofNat 64 dd)) M (keepD v) outp)
      (At 0x800052bc#64 (lpL sp pa b pc dd dp (u - 1) 0) (writeLog M []) (keepD v) outp) := by
  mdiv2d_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pc) = BitVec.ofNat 64 u := by
    rw [hf.u_v, signExtend_ofNat32 _ hf.u_lt]
  have hm := BitW.mask_ofNat dd (by omega)
  seg_stepu div2dI 0x800052bc#64 [rd4 M pc, rd8 M (pc + 16)] [2, 8, 9, 10, 18, 19] keysD [a0L] [lpL]
    [h1, hf.dp_v, hm] hc
    using (repeat' apply And.intro) <;> first
      | (simp only [Nat.mod_mod]; exact hm)
      | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega)

/-- One iteration's memory facts: digit `x` of `c` (`e`) and its store window. -/
structure LFacts (M : Mem) (dp x e : Nat) : Prop where
  re : Ram (dp + 4 * x) 4
  rd : Ram dp 4
  e_v : bytesT4 M (dp + 4 * x) = BitVec.ofNat 32 e
  e_lt : e < radix
  dp_al : dp % 4 = 0
  code_off : dp + 4 * x + 4 ≤ mpDiv2dBase ∨ mpDiv2dBase + 380 ≤ dp + 4 * x

/-- The loop's back edge from `x = k + 1`: digit `x := e / 2^dd + r 2^(28 - dd)`, carry `e mod 2^dd`. -/
theorem lp_step (v : Abi) (outp : Array String) (sp pa b pc dd dp k e r : Nat) (M : Mem)
    (hc : CodeAt M mpDiv2dBase mpDiv2dCode) (hf : LFacts M dp (k + 1) e) (hd : 0 < dd) (hd' : dd < 28)
    (hr : r < 2 ^ dd) :
    Triple (At 0x800052bc#64 (lpL sp pa b pc dd dp (k + 1) r) M (keepD v) outp)
      (At 0x800052bc#64 (lpL sp pa b pc dd dp k (e % 2 ^ dd))
        (writeLog M [(dp + 4 * (k + 1), 4, BitVec.ofNat 64 (e / 2 ^ dd + r * 2 ^ (28 - dd)))]) (keepD v) outp) := by
  mdiv2d_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M (dp + 4 * (k + 1))) = BitVec.ofNat 64 e := by
    rw [hf.e_v, signExtend_ofNat32 _ (by simp only [radix, Layout.digitBits] at *; omega)]
  seg_stepu div2dLp 0x800052bc#64 [rd4 M (dp + 4 * (k + 1))] [2, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19]
    keysD [lpL] [] [h1] hc
    using (repeat' apply And.intro) <;> first
      | omega
      | rw [BitD.srl_or_sll e r dd hd' hf.e_lt hr]
      | rw [BitD.and_mask e dd (by omega) (Nat.lt_trans hf.e_lt (by decide))]
      | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega)

/-- The loop's last iteration (`x = 0`): set up `mp_clamp(c)`. -/
theorem lx_step (v : Abi) (outp : Array String) (sp pa b pc dd dp e r : Nat) (M : Mem)
    (hc : CodeAt M mpDiv2dBase mpDiv2dCode) (hf : LFacts M dp 0 e) (hd' : dd < 28)
    (hr : r < 2 ^ dd) :
    Triple (At 0x800052bc#64 (lpL sp pa b pc dd dp 0 r) M (keepD v) outp)
      (At 0x800052e0#64 (clL sp pa b pc)
        (writeLog M [(dp + 4 * 0, 4, BitVec.ofNat 64 (e / 2 ^ dd + r * 2 ^ (28 - dd)))]) (keepD v) outp) := by
  mdiv2d_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M (dp + 4 * 0)) = BitVec.ofNat 64 e := by
    rw [hf.e_v, signExtend_ofNat32 _ (by simp only [radix, Layout.digitBits] at *; omega)]
  seg_stepu div2dLx 0x800052e0#64 [rd4 M (dp + 4 * 0)] [2, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19]
    keysD [lpL] [clL] [h1] hc
    using (repeat' apply And.intro) <;> first
      | omega
      | rw [BitD.srl_or_sll e r dd hd' hf.e_lt hr]
      | rw [BitD.and_mask e dd (by omega) (Nat.lt_trans hf.e_lt (by decide))]
      | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega)

/-- The whole saved frame. -/
structure RFacts (M : Mem) (ra s0 s1 s2 s3 : BitVec 64) (sp : Nat) : Prop where
  rs : Ram (sp - 64) 64
  sp_ge : 64 ≤ sp
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  s1_v : bytesT8 M (sp - 24) = s1
  s2_v : bytesT8 M (sp - 32) = s2
  s3_v : bytesT8 M (sp - 40) = s3
  ra_al : ra.toNat % 4 = 0

/-- After `mp_clamp`: restore the frame, return `MP_OKAY`. -/
theorem e_step (ra s0 s1 s2 s3 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M mpDiv2dBase mpDiv2dCode) (hf : RFacts M ra s0 s1 s2 s3 sp) :
    Triple (At 0x800052e4#64 [(2, BitVec.ofNat 64 (sp - 64)), (8, 0#64)] M (keepD v) outp)
      (At ra (ret1 ra s0 s1 s2 s3 sp) (writeLog M []) (keepD v) outp) := by
  mdiv2d_ctx
  have hra := hf.ra_al
  have h1 : bytesT8 M (sp - 64 + 56) = ra := by rw [show sp - 64 + 56 = sp - 8 by omega]; exact hf.ra_v
  have h2 : bytesT8 M (sp - 64 + 48) = s0 := by rw [show sp - 64 + 48 = sp - 16 by omega]; exact hf.s0_v
  have h3 : bytesT8 M (sp - 64 + 32) = s2 := by rw [show sp - 64 + 32 = sp - 32 by omega]; exact hf.s2_v
  have h4 : bytesT8 M (sp - 64 + 24) = s3 := by rw [show sp - 64 + 24 = sp - 40 by omega]; exact hf.s3_v
  have h5 : bytesT8 M (sp - 64 + 40) = s1 := by rw [show sp - 64 + 40 = sp - 24 by omega]; exact hf.s1_v
  seg_step div2dE ra [rd8 M (sp - 64 + 56), rd8 M (sp - 64 + 48), rd8 M (sp - 64 + 32), rd8 M (sp - 64 + 24),
    rd8 M (sp - 64 + 40)] [2, 8] keysD [] [ret1] [h1, h2, h3, h4, h5] hc

end Tom.Machine.Fn.MpDiv2d
