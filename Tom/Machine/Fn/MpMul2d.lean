import Tom.Machine.Seg.MpMul2d
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.BitW
import Tom.Spec.Div2d
import Vsa.Sim.TripleCat

/-!
# `mp_mul_2d` on the machine: the segments

`mp_mul_2d(a, b, c)` at `0x80001758` (84 instructions). The segments, in
program order, with the calls between them (made by the assembly, `jal_at`):

`p1_step`, `p2_step` (`b ≥ 0`, the frame, `a != c`) → `jal mp_copy(a, c)` at
`177c` → `d_step` → `jal __divdi3(b, 28)` at `178c` → `g_step` (`c->used + D <
c->alloc`: the `mp_grow` branch at `1884` is excluded by the contract, D5). Then
`b < 28`: `s_step` → `jal __moddi3(b, 28)` at `17b4` → `sz_step` (`d = 0`) or
`sn_step`; `b ≥ 28`: `l_step` → `jal mp_lshd(c, D)` at `1864` → `l2_step` →
`jal __moddi3(b, 28)` at `1874` → `lz_step` (`d = 0`) or `ln_step`. With `d != 0`
at `17c0`: `u0_step` (`c->used = 0`) or `i_step` (the masks, `BitW.mask_ofNat`)
into the bit loop at `17f4`: `lp_step` (back edge) / `lx_step` (last iteration)
store `shlLo d e + r` into digit `x` and carry `shlHi d e` (`BitW.shl_or_mask`,
`BitW.srl_and_mask`; `c->used` is reloaded after the store). At `1824`: no last
carry `cz_step`, else `cn1_step` (`c->used += 1`), `cn2_step` (`c->dp[used] :=
r`). Then `k_step` → `jal mp_clamp(c)` at `1840` → `e_step` (restore, `MP_OKAY`).

The libgcc results arrive as `BitVec.sdiv`/`srem` of `ofNat` values:
`BitW.sdiv_ofNat`, `BitW.srem_ofNat`. `s1` is a local (`b`), so the segments keep
`Abi.keepR1` and carry `s1`.
-/


namespace Tom.Machine.Fn.MpMul2d

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mmul2d_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpMul2dBase = 0x80001758 := rfl
   have : mpMul2dCode.length = 84 := rfl))

def entry : BitVec 64 := 0x80001758#64

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
  code_off : sp ≤ mpMul2dBase ∨ mpMul2dBase + 336 ≤ sp - 48

/-- The first frame stores (`s0`, `s1`). -/
def frameLog1 (s0 s1 : BitVec 64) (sp : Nat) : List WEntry :=
  [(sp - 16, 8, s0), (sp - 24, 8, s1)]

/-- At `1768`: the frame allocated. -/
def p1L (ra : BitVec 64) (sp pa b pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 48)), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 b),
   (12, BitVec.ofNat 64 pc)]

/-- `b ≥ 0`: allocate the frame, save `s0`, `s1`. -/
theorem p1_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc : Nat) (m : Mem)
    (hc : CodeAt m mpMul2dBase mpMul2dCode) (hs : FFacts sp) (hb : b < 2 ^ 31) :
    Triple (At entry (entry1 ra s0 s1 sp pa b pc) m v.keepR1 outp)
      (At 0x80001768#64 (p1L ra sp pa b pc) (writeLog m (frameLog1 s0 s1 sp)) v.keepR1 outp) := by
  mmul2d_ctx
  seg_step mul2dP1 0x80001768#64 ([] : List (List (BitVec 8))) [1, 2, 8, 9, 10, 11, 12] abiKeysR1
    [entry, entry1, frameLog1] [p1L] [] hc

/-- At the `mp_copy(a, c)` call (`177c`): `s0 = c`, `s1 = b`. -/
def cpL (sp pa b pc : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (9, BitVec.ofNat 64 b), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 pc)]

/-- Save `ra`; `a != c`: set up `mp_copy(a, c)`. -/
theorem p2_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) (hs : FFacts sp) (hne : pa ≠ pc) (hpa : pa < 2 ^ 64)
    (hpc : pc < 2 ^ 64) :
    Triple (At 0x80001768#64 (p1L ra sp pa b pc) M v.keepR1 outp)
      (At 0x8000177c#64 (cpL sp pa b pc) (writeLog M [(sp - 8, 8, ra)]) v.keepR1 outp) := by
  mmul2d_ctx
  seg_step mul2dP2 0x8000177c#64 ([] : List (List (BitVec 8))) [1, 2, 10, 11, 12] abiKeysR1 [p1L] [cpL] [] hc

/-- After a call: `sp`, `s0 = c`, `s1 = b` and `a0 = r`. -/
def aL (sp pc b : Nat) (r : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (9, BitVec.ofNat 64 b), (10, r)]

/-- At a libgcc call: `a0 = b`, `a1 = 28`. -/
def gL (sp pc b : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (9, BitVec.ofNat 64 b), (10, BitVec.ofNat 64 b),
   (11, BitVec.ofNat 64 28)]

/-- `mp_copy` returned `MP_OKAY`: set up `__divdi3(b, 28)` (`178c`). -/
theorem d_step (v : Abi) (outp : Array String) (sp pc b : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) :
    Triple (At 0x80001780#64 (aL sp pc b 0#64) M v.keepR1 outp)
      (At 0x8000178c#64 (gL sp pc b) (writeLog M []) v.keepR1 outp) := by
  mmul2d_ctx
  seg_step mul2dD 0x8000178c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10] abiKeysR1 [aL] [gL] [] hc

/-- `c->used` and `c->alloc`. -/
structure GFacts (M : Mem) (pc u al : Nat) : Prop where
  rc : Ram pc 24
  u_v : bytesT4 M pc = BitVec.ofNat 32 u
  al_v : bytesT4 M (pc + 4) = BitVec.ofNat 32 al
  u_lt : u < 2 ^ 31
  al_lt : al < 2 ^ 31

/-- At `17a4`: `a3 = D`. -/
def tL (sp pc b D : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (9, BitVec.ofNat 64 b), (13, BitVec.ofNat 64 D)]

/-- `D = b / 28` returned; `c->used + D < c->alloc` (no `mp_grow`, D5). -/
theorem g_step (v : Abi) (outp : Array String) (sp pc b u al : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) (hf : GFacts M pc u al) (hb : b < 2 ^ 31)
    (hroom : u + b / 28 + 1 ≤ al) :
    Triple (At 0x80001790#64 (aL sp pc b (BitVec.ofNat 64 (b / 28))) M v.keepR1 outp)
      (At 0x800017a4#64 (tL sp pc b (b / 28)) (writeLog M []) v.keepR1 outp) := by
  mmul2d_ctx
  have : b / 28 < 2 ^ 31 := by omega
  have h1 : BitVec.signExtend 64 (bytesT4 M pc) = BitVec.ofNat 64 u := by
    rw [hf.u_v, signExtend_ofNat32 _ hf.u_lt]
  have h2 : BitVec.signExtend 64 (bytesT4 M (pc + 4)) = BitVec.ofNat 64 al := by
    rw [hf.al_v, signExtend_ofNat32 _ hf.al_lt]
  seg_step mul2dG 0x800017a4#64 [rd4 M pc, rd4 M (pc + 4)] [2, 8, 9, 10] abiKeysR1 [aL] [tL] [h1, h2] hc

/-- `b < 28`: set up `__moddi3(b, 28)` (`17b4`). -/
theorem s_step (v : Abi) (outp : Array String) (sp pc b D : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) (hb : b < 28) :
    Triple (At 0x800017a4#64 (tL sp pc b D) M v.keepR1 outp)
      (At 0x800017b4#64 (gL sp pc b) (writeLog M []) v.keepR1 outp) := by
  mmul2d_ctx
  seg_step mul2dS 0x800017b4#64 ([] : List (List (BitVec 8))) [2, 8, 9, 13] abiKeysR1 [tL] [gL] [] hc

/-- At the `mp_lshd(c, D)` call (`1864`). -/
def lsL (sp pc b D : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (9, BitVec.ofNat 64 b), (10, BitVec.ofNat 64 pc),
   (11, BitVec.ofNat 64 D)]

/-- `b ≥ 28`: set up `mp_lshd(c, D)`. -/
theorem l_step (v : Abi) (outp : Array String) (sp pc b D : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) (hb : 28 ≤ b) (hb' : b < 2 ^ 31) :
    Triple (At 0x800017a4#64 (tL sp pc b D) M v.keepR1 outp)
      (At 0x80001864#64 (lsL sp pc b D) (writeLog M []) v.keepR1 outp) := by
  mmul2d_ctx
  seg_step mul2dL 0x80001864#64 ([] : List (List (BitVec 8))) [2, 8, 9, 13] abiKeysR1 [tL] [lsL] [] hc

/-- `mp_lshd` returned `MP_OKAY`: set up `__moddi3(b, 28)` (`1874`). -/
theorem l2_step (v : Abi) (outp : Array String) (sp pc b : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) :
    Triple (At 0x80001868#64 (aL sp pc b 0#64) M v.keepR1 outp)
      (At 0x80001874#64 (gL sp pc b) (writeLog M []) v.keepR1 outp) := by
  mmul2d_ctx
  seg_step mul2dL2 0x80001874#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10] abiKeysR1 [aL] [gL] [] hc

/-- At the `mp_clamp(c)` setup (`183c`). -/
def kL (sp pc b : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (9, BitVec.ofNat 64 b)]

/-- At `17c0` (`d != 0`). -/
def nL (sp pc b d : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (9, BitVec.ofNat 64 b), (10, BitVec.ofNat 64 d)]

/-- After `mp_lshd`, `d = 0`: on to `mp_clamp`. -/
theorem lz_step (v : Abi) (outp : Array String) (sp pc b : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) :
    Triple (At 0x80001878#64 (aL sp pc b (BitVec.ofNat 64 0)) M v.keepR1 outp)
      (At 0x8000183c#64 (kL sp pc b) (writeLog M []) v.keepR1 outp) := by
  mmul2d_ctx
  seg_step mul2dLZ 0x8000183c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10] abiKeysR1 [aL] [kL] [] hc

/-- After `mp_lshd`, `d != 0`: to the bit loop's setup. -/
theorem ln_step (v : Abi) (outp : Array String) (sp pc b d : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) (hd : 0 < d) (hd' : d < 28) :
    Triple (At 0x80001878#64 (aL sp pc b (BitVec.ofNat 64 d)) M v.keepR1 outp)
      (At 0x800017c0#64 (nL sp pc b d) (writeLog M []) v.keepR1 outp) := by
  mmul2d_ctx
  seg_step mul2dLN 0x800017c0#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10] abiKeysR1 [aL] [nL] [] hc

/-- `b < 28`, `d = 0`: on to `mp_clamp`. -/
theorem sz_step (v : Abi) (outp : Array String) (sp pc b : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) :
    Triple (At 0x800017b8#64 (aL sp pc b (BitVec.ofNat 64 0)) M v.keepR1 outp)
      (At 0x8000183c#64 (kL sp pc b) (writeLog M []) v.keepR1 outp) := by
  mmul2d_ctx
  seg_step mul2dSZ 0x8000183c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10] abiKeysR1 [aL] [kL] [] hc

/-- `b < 28`, `d != 0`: to the bit loop's setup. -/
theorem sn_step (v : Abi) (outp : Array String) (sp pc b d : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) (hd : 0 < d) (hd' : d < 28) :
    Triple (At 0x800017b8#64 (aL sp pc b (BitVec.ofNat 64 d)) M v.keepR1 outp)
      (At 0x800017c0#64 (nL sp pc b d) (writeLog M []) v.keepR1 outp) := by
  mmul2d_ctx
  seg_step mul2dSN 0x800017c0#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10] abiKeysR1 [aL] [nL] [] hc

/-- `c->used` (after the digit shift) and `c->dp`. -/
structure UFacts (M : Mem) (pc dp u : Nat) : Prop where
  rc : Ram pc 24
  u_v : bytesT4 M pc = BitVec.ofNat 32 u
  dp_v : bytesT8 M (pc + 16) = BitVec.ofNat 64 dp
  u_lt : u < 2 ^ 31

/-- `c->used = 0`: skip the bit loop. -/
theorem u0_step (v : Abi) (outp : Array String) (sp pc b d dp : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) (hf : UFacts M pc dp 0) :
    Triple (At 0x800017c0#64 (nL sp pc b d) M v.keepR1 outp)
      (At 0x8000183c#64 (kL sp pc b) (writeLog M []) v.keepR1 outp) := by
  mmul2d_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pc) = BitVec.ofNat 64 0 := by
    rw [hf.u_v, signExtend_ofNat32 _ hf.u_lt]
  seg_step mul2dU0 0x8000183c#64 [rd4 M pc] [2, 8, 9, 10] abiKeysR1 [nL] [kL] [h1] hc

/-- The bit loop's head (`17f4`), digit `x`, carry `r`: `a0 = d`, `a1 = 2^d - 1`,
`t1 = 28 - d`, `a7 = MP_MASK`, `t3 = c->dp`, `a6 = &c->dp[x]`, `a2 = x`, `a5 = r`. -/
def lpL (sp pc b d dp x r : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (9, BitVec.ofNat 64 b), (10, BitVec.ofNat 64 d),
   (11, BitVec.ofNat 64 (2 ^ d - 1)), (6, BitVec.ofNat 64 (28 - d)), (17, BitVec.ofNat 64 Layout.mpMask),
   (28, BitVec.ofNat 64 dp), (16, BitVec.ofNat 64 (dp + 4 * x)), (12, BitVec.ofNat 64 x), (15, BitVec.ofNat 64 r)]

/-- `c->used > 0`: the masks, enter the bit loop. -/
theorem i_step (v : Abi) (outp : Array String) (sp pc b d dp u : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) (hf : UFacts M pc dp u) (hu : 0 < u) (hd : 0 < d) (hd' : d < 28) :
    Triple (At 0x800017c0#64 (nL sp pc b d) M v.keepR1 outp)
      (At 0x800017f4#64 (lpL sp pc b d dp 0 0) (writeLog M []) v.keepR1 outp) := by
  mmul2d_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pc) = BitVec.ofNat 64 u := by
    rw [hf.u_v, signExtend_ofNat32 _ hf.u_lt]
  have hm := BitW.mask_ofNat d (by omega)
  seg_stepu mul2dI 0x800017f4#64 [rd4 M pc, rd8 M (pc + 16)] [2, 8, 9, 10] abiKeysR1 [nL] [lpL] [h1, hf.dp_v, hm] hc
    using exact ⟨hm, by congr 1; omega, by decide, trivial, by simp⟩


/-- One iteration's memory facts: digit `x` of `c` (`e`), its store window, and
`c->used` (`u`, reloaded after the store). -/
structure LFacts (M : Mem) (pc dp u x e : Nat) : Prop where
  rc : Ram pc 24
  u_v : bytesT4 M pc = BitVec.ofNat 32 u
  u_lt : u < 2 ^ 31
  re : Ram (dp + 4 * x) 4
  e_v : bytesT4 M (dp + 4 * x) = BitVec.ofNat 32 e
  e_lt : e < radix
  dp_al : dp % 4 = 0
  d_c : dp + 4 * x + 4 ≤ pc ∨ pc + 4 ≤ dp + 4 * x
  code_off : dp + 4 * x + 4 ≤ mpMul2dBase ∨ mpMul2dBase + 336 ≤ dp + 4 * x

/-- The loop's back edge (`x + 1 < c->used`): digit `x := shlLo d e + r`, carry `shlHi d e`. -/
theorem lp_step (v : Abi) (outp : Array String) (sp pc b d dp u x e r : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) (hf : LFacts M pc dp u x e) (hd : 0 < d) (hd' : d < 28)
    (hr : r < 2 ^ d) (hx : x + 1 < u) :
    Triple (At 0x800017f4#64 (lpL sp pc b d dp x r) M v.keepR1 outp)
      (At 0x800017f4#64 (lpL sp pc b d dp (x + 1) (shlHi d e))
        (writeLog M [(dp + 4 * x, 4, BitVec.ofNat 64 (shlLo d e + r))]) v.keepR1 outp) := by
  mmul2d_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M (dp + 4 * x)) = BitVec.ofNat 64 e := by
    rw [hf.e_v, signExtend_ofNat32 _ (by simp only [radix, Layout.digitBits] at *; omega)]
  have h2 : BitVec.signExtend 64 (bytesT4 M pc) = BitVec.ofNat 64 u := by
    rw [hf.u_v, signExtend_ofNat32 _ hf.u_lt]
  seg_stepu mul2dLp 0x800017f4#64 [rd4 M (dp + 4 * x), rd4 M pc] [2, 8, 9, 10, 11, 6, 17, 28, 16, 12, 15]
    abiKeysR1 [lpL] [] [h1, h2] hc
    using (repeat' apply And.intro) <;> first
      | exact BitW.srl_and_mask e d (by omega) hf.e_lt
      | exact BitW.shl_or_mask e r d hd' hf.e_lt hr
      | exact True.intro
      | exact congrArg (BitVec.ofNat 64) (by omega)
      | omega

/-- After the bit loop (`1824`): `a3 = c->used`, `a5` the last carry. -/
def xL (sp pc b dp u r : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (9, BitVec.ofNat 64 b), (28, BitVec.ofNat 64 dp),
   (13, BitVec.ofNat 64 u), (15, BitVec.ofNat 64 r)]

/-- The loop's last iteration (`x + 1 = c->used`). -/
theorem lx_step (v : Abi) (outp : Array String) (sp pc b d dp u x e r : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) (hf : LFacts M pc dp u x e) (hd : 0 < d) (hd' : d < 28)
    (hr : r < 2 ^ d) (hx : x + 1 = u) :
    Triple (At 0x800017f4#64 (lpL sp pc b d dp x r) M v.keepR1 outp)
      (At 0x80001824#64 (xL sp pc b dp u (shlHi d e))
        (writeLog M [(dp + 4 * x, 4, BitVec.ofNat 64 (shlLo d e + r))]) v.keepR1 outp) := by
  mmul2d_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M (dp + 4 * x)) = BitVec.ofNat 64 e := by
    rw [hf.e_v, signExtend_ofNat32 _ (by simp only [radix, Layout.digitBits] at *; omega)]
  have h2 : BitVec.signExtend 64 (bytesT4 M pc) = BitVec.ofNat 64 u := by
    rw [hf.u_v, signExtend_ofNat32 _ hf.u_lt]
  seg_stepu mul2dLx 0x80001824#64 [rd4 M (dp + 4 * x), rd4 M pc] [2, 8, 9, 10, 11, 6, 17, 28, 16, 12, 15]
    abiKeysR1 [lpL] [xL] [h1, h2] hc
    using (repeat' apply And.intro) <;> first
      | exact BitW.srl_and_mask e d (by omega) hf.e_lt
      | exact BitW.shl_or_mask e r d hd' hf.e_lt hr
      | exact True.intro
      | exact congrArg (BitVec.ofNat 64) (by omega)
      | omega

/-- No last carry: on to `mp_clamp`. -/
theorem cz_step (v : Abi) (outp : Array String) (sp pc b dp u : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) :
    Triple (At 0x80001824#64 (xL sp pc b dp u 0) M v.keepR1 outp)
      (At 0x8000183c#64 (kL sp pc b) (writeLog M []) v.keepR1 outp) := by
  mmul2d_ctx
  seg_step mul2dCZ 0x8000183c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 28, 13, 15] abiKeysR1 [xL] [kL] [] hc

/-- `c->used`'s slot. -/
structure CUsed (pc : Nat) : Prop where
  rc : Ram pc 24
  pc_al : pc % 8 = 0
  code_off : pc + 24 ≤ mpMul2dBase ∨ mpMul2dBase + 336 ≤ pc

/-- At `1834`: `a3 = 4 c->used` (the old `used`). -/
def c2L (sp pc b dp u r : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (9, BitVec.ofNat 64 b), (28, BitVec.ofNat 64 dp),
   (13, BitVec.ofNat 64 (4 * u)), (15, BitVec.ofNat 64 r)]

/-- A last carry `r != 0`: `c->used := u + 1`. -/
theorem cn1_step (v : Abi) (outp : Array String) (sp pc b dp u r : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) (hs : CUsed pc) (hu : u + 1 < 2 ^ 31) (hr : 0 < r)
    (hr' : r < 2 ^ 64) :
    Triple (At 0x80001824#64 (xL sp pc b dp u r) M v.keepR1 outp)
      (At 0x80001834#64 (c2L sp pc b dp u r) (writeLog M [(pc, 4, BitVec.ofNat 64 (u + 1))]) v.keepR1 outp) := by
  mmul2d_ctx
  seg_stepu mul2dCN1 0x80001834#64 ([] : List (List (BitVec 8))) [2, 8, 9, 28, 13, 15] abiKeysR1 [xL] [c2L] [] hc
    using (repeat' apply And.intro) <;> first
      | exact True.intro
      | exact congrArg (BitVec.ofNat 64) (by omega)
      | omega

/-- The top digit's store window (`c->dp[u]`). -/
structure TFacts (dp u : Nat) : Prop where
  rt : Ram (dp + 4 * u) 4
  dp_al : dp % 4 = 0
  code_off : dp + 4 * u + 4 ≤ mpMul2dBase ∨ mpMul2dBase + 336 ≤ dp + 4 * u

/-- `c->dp[u] := r`. -/
theorem cn2_step (v : Abi) (outp : Array String) (sp pc b dp u r : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) (hs : TFacts dp u) :
    Triple (At 0x80001834#64 (c2L sp pc b dp u r) M v.keepR1 outp)
      (At 0x8000183c#64 (kL sp pc b) (writeLog M [(dp + 4 * u, 4, BitVec.ofNat 64 r)]) v.keepR1 outp) := by
  mmul2d_ctx
  seg_step mul2dCN2 0x8000183c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 28, 13, 15] abiKeysR1 [c2L] [kL] [] hc

/-- At the `mp_clamp(c)` call (`1840`). -/
def clL (sp pc b : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (9, BitVec.ofNat 64 b), (10, BitVec.ofNat 64 pc)]

/-- Set up `mp_clamp(c)`. -/
theorem k_step (v : Abi) (outp : Array String) (sp pc b : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) :
    Triple (At 0x8000183c#64 (kL sp pc b) M v.keepR1 outp)
      (At 0x80001840#64 (clL sp pc b) (writeLog M []) v.keepR1 outp) := by
  mmul2d_ctx
  seg_step mul2dK 0x80001840#64 ([] : List (List (BitVec 8))) [2, 8, 9] abiKeysR1 [kL] [clL] [] hc

/-- The saved frame: `ra`, `s0`, `s1`. -/
structure RFacts (M : Mem) (ra s0 s1 : BitVec 64) (sp : Nat) : Prop where
  rs : Ram (sp - 48) 48
  sp_ge : 48 ≤ sp
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  s1_v : bytesT8 M (sp - 24) = s1
  ra_al : ra.toNat % 4 = 0

/-- After `mp_clamp`: restore the frame, return `MP_OKAY`. -/
theorem e_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pc b : Nat) (M : Mem)
    (hc : CodeAt M mpMul2dBase mpMul2dCode) (hf : RFacts M ra s0 s1 sp) :
    Triple (At 0x80001844#64 (kL sp pc b) M v.keepR1 outp)
      (At ra (ret1 ra s0 s1 sp) (writeLog M []) v.keepR1 outp) := by
  mmul2d_ctx
  have hra := hf.ra_al
  have h1 : bytesT8 M (sp - 48 + 40) = ra := by rw [show sp - 48 + 40 = sp - 8 by omega]; exact hf.ra_v
  have h2 : bytesT8 M (sp - 48 + 32) = s0 := by rw [show sp - 48 + 32 = sp - 16 by omega]; exact hf.s0_v
  have h3 : bytesT8 M (sp - 48 + 24) = s1 := by rw [show sp - 48 + 24 = sp - 24 by omega]; exact hf.s1_v
  seg_step mul2dE ra [rd8 M (sp - 48 + 40), rd8 M (sp - 48 + 32), rd8 M (sp - 48 + 24)] [2, 8, 9] abiKeysR1
    [kL] [ret1] [h1, h2, h3] hc

end Tom.Machine.Fn.MpMul2d
