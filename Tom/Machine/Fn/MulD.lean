import Tom.Machine.Seg.MulD
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.MulCall
import Vsa.Sim.TripleCat

/-!
# `mp_mul_d` on the machine: the segments

`mp_mul_d(a, b, c)` at `0x800019fc` (84 instructions). The prologue saves
`s3`, `s4`, `s6`, `ra` (`mdP1`; the `mp_grow` branch `a->used ≥ c->alloc` is
excluded by the contract, D5), then `s0`, `s2`, `s8` and stores
`c->sign := a->sign` (`mdP2`); with `a->used = 0` it jumps to the final
carry store (`mdP2z`), otherwise it saves `s7`, `s5`, `s1` and enters the
loop (`mdP3`). The loop head `1a74`: load `a->dp[i]` (`mdA`), `jal __muldi3`
(`Kit/MulCall.lean`), add the carry, store the low 28 bits into `c->dp[i]`
and carry the rest (`mdB` back edge, `mdBe` exit). After the loop, restore
`s1`, `s5`, `s7` (`mdC`) and meet the `a->used = 0` path at `1ac4`: store the
carry into `c->dp[a->used]`, `memset` the digits up to `olduse` if any
(`mdJ1`, else `mdJ0`), `c->used := a->used + 1` (`mdD`), `mp_clamp(c)`, the
epilogue (`mdE`).

`s0`–`s8` are locals, so the segments keep only `gp`, `tp`, `s9`–`s11`
(`kMD`) and carry the others in their register lists until saved.
-/


namespace Tom.Machine.Fn.MulD

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "muld_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpMulDBase = 0x800019fc := rfl
   have : mpMulDCode.length = 84 := rfl))

/-- The registers every segment keeps: `gp`, `tp`, `s9`–`s11`. -/
def kMD (v : Abi) : GRegs := [(3, v.gp), (4, v.tp), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

abbrev kMDKeys : List Nat := [3, 4, 25, 26, 27]

/-! ## The prologue -/

/-- The entry: `a0 = a`, `a1 = b`, `a2 = c`, the callee-saved registers. -/
def entL (ra s0 : BitVec 64) (v : Abi) (sp pa b pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, v.s.s1), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 b),
   (12, BitVec.ofNat 64 pc), (18, v.s.s2), (19, v.s.s3), (20, v.s.s4), (21, v.s.s5), (22, v.s.s6),
   (23, v.s.s7), (24, v.s.s8)]

/-- At `1a28`: `a5 = a->used`, `s3 = a`, `s4 = b`, `s6 = c`. -/
def p1L (ra s0 : BitVec 64) (v : Abi) (sp pa b pc ua : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 80)), (8, s0), (9, v.s.s1), (15, BitVec.ofNat 64 ua), (18, v.s.s2),
   (19, BitVec.ofNat 64 pa), (20, BitVec.ofNat 64 b), (21, v.s.s5), (22, BitVec.ofNat 64 pc), (23, v.s.s7),
   (24, v.s.s8)]

/-- The first saves: `s3`, `s4`, `s6`, `ra`. -/
def log1 (ra : BitVec 64) (v : Abi) (sp : Nat) : List WEntry :=
  [(sp - 40, 8, v.s.s3), (sp - 48, 8, v.s.s4), (sp - 64, 8, v.s.s6), (sp - 8, 8, ra)]

/-- The prologue's loads and frame. -/
structure P1Facts (m : Mem) (sp pa pc ua al : Nat) : Prop where
  ra_ : Ram pa 24
  rc : Ram pc 24
  rs : Ram (sp - 80) 80
  sp_al : sp % 16 = 0
  sp_ge : 80 ≤ sp
  ua_v : bytesT4 m pa = BitVec.ofNat 32 ua
  al_v : bytesT4 m (pc + 4) = BitVec.ofNat 32 al
  ua_lt : ua < 2 ^ 31
  al_lt : al < 2 ^ 31
  room : ua < al
  code_off : sp ≤ mpMulDBase ∨ mpMulDBase + 336 ≤ sp - 80

theorem P1Facts.sx {m : Mem} {sp pa pc ua al : Nat} (h : P1Facts m sp pa pc ua al) :
    BitVec.signExtend 64 (bytesT4 m pa) = BitVec.ofNat 64 ua ∧
      BitVec.signExtend 64 (bytesT4 m (pc + 4)) = BitVec.ofNat 64 al :=
  ⟨by rw [h.ua_v, signExtend_ofNat32 _ h.ua_lt], by rw [h.al_v, signExtend_ofNat32 _ h.al_lt]⟩

theorem p1_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ua al : Nat) (m : Mem)
    (hc : CodeAt m mpMulDBase mpMulDCode) (hf : P1Facts m sp pa pc ua al) :
    Triple (At 0x800019fc#64 (entL ra s0 v sp pa b pc) m (kMD v) outp)
      (At 0x80001a28#64 (p1L ra s0 v sp pa b pc ua) (writeLog m (log1 ra v sp)) (kMD v) outp) := by
  muld_ctx
  have ⟨hsa, hsl⟩ := hf.sx
  seg_step mdP1 0x80001a28#64 [rd4 m pa, rd4 m (pc + 4)] [1, 2, 8, 9, 10, 11, 12, 18, 19, 20, 21, 22, 23, 24]
    kMDKeys [entL, log1] [p1L] [hsa, hsl] hc

/-! ## The digit loop -/

/-- The loop head `1a74`, index `i`, carry `u`. -/
def hL (sp pa b pc cdp ou adp i u : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 80)), (8, BitVec.ofNat 64 u), (9, BitVec.ofNat 64 i),
   (18, BitVec.ofNat 64 (cdp + 4 * i)), (19, BitVec.ofNat 64 pa), (20, BitVec.ofNat 64 b),
   (21, 268435455#64), (22, BitVec.ofNat 64 pc), (23, BitVec.ofNat 64 (adp + 4 * i)), (24, BitVec.ofNat 64 ou)]

/-- The live registers across the `__muldi3` call (`s0 = u << 32`). -/
def kL (sp pa b pc cdp ou adp i u : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 80)), (8, BitVec.ofNat 64 (u * 4294967296)), (9, BitVec.ofNat 64 i),
   (18, BitVec.ofNat 64 (cdp + 4 * i)), (19, BitVec.ofNat 64 pa), (20, BitVec.ofNat 64 b),
   (21, 268435455#64), (22, BitVec.ofNat 64 pc), (23, BitVec.ofNat 64 (adp + 4 * i)), (24, BitVec.ofNat 64 ou)]

/-- At the `jal __muldi3` (`1a80`): `a0 = a->dp[i]`, `a1 = b`. -/
def aL (sp pa b pc cdp ou adp i u d : Nat) : GRegs :=
  (10, BitVec.ofNat 64 d) :: (11, BitVec.ofNat 64 b) :: kL sp pa b pc cdp ou adp i u

/-- Back from `__muldi3` (`1a84`): `a0 = a->dp[i] * b`. -/
def bL (sp pa b pc cdp ou adp i u p : Nat) : GRegs :=
  (10, BitVec.ofNat 64 p) :: kL sp pa b pc cdp ou adp i u

/-- A digit read of `a`. -/
structure DRead (M : Mem) (p i x : Nat) : Prop where
  r : Ram (p + 4 * i) 4
  v : bytesT4 M (p + 4 * i) = BitVec.ofNat 32 x
  lt : x < 268435456

theorem zext_ofNat32 (x : Nat) (h : x < 2 ^ 32) :
    zero_extend (m := 64) (BitVec.ofNat 32 x) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  simp [zero_extend, Sail.BitVec.zeroExtend, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega)]

theorem a_step (v : Abi) (outp : Array String) (sp pa b pc cdp ou adp i u d : Nat) (M : Mem)
    (hc : CodeAt M mpMulDBase mpMulDCode) (hd : DRead M adp i d) :
    Triple (At 0x80001a74#64 (hL sp pa b pc cdp ou adp i u) M (kMD v) outp)
      (At 0x80001a80#64 (aL sp pa b pc cdp ou adp i u d) (writeLog M []) (kMD v) outp) := by
  muld_ctx
  have hz : zero_extend (m := 64) (bytesT4 M (adp + 4 * i)) = BitVec.ofNat 64 d := by
    rw [hd.v, zext_ofNat32 _ (by omega)]
  seg_step mdA 0x80001a80#64 [rd4 M (adp + 4 * i)] [2, 8, 9, 18, 19, 20, 21, 22, 23, 24]
    kMDKeys [hL] [aL, kL] [hz] hc

/-- After the digit store (`1a94`): `a0 = p + u`. -/
def b1L (sp pa b pc cdp ou adp i u s : Nat) : GRegs :=
  (10, BitVec.ofNat 64 s) :: hL sp pa b pc cdp ou adp i u

/-- The store of digit `i` into `c`. -/
structure SFacts (cdp i : Nat) : Prop where
  rc : Ram (cdp + 4 * i) 4
  al : cdp % 4 = 0
  code_off : cdp + 4 * i + 4 ≤ mpMulDBase ∨ mpMulDBase + 336 ≤ cdp + 4 * i

/-- `c->dp[i] := (p + u) mod 2^28`. -/
theorem b1_step (v : Abi) (outp : Array String) (sp pa b pc cdp ou adp i u p : Nat) (M : Mem)
    (hc : CodeAt M mpMulDBase mpMulDCode) (hf : SFacts cdp i) (hu : u < 2 ^ 32) :
    Triple (At 0x80001a84#64 (bL sp pa b pc cdp ou adp i u p) M (kMD v) outp)
      (At 0x80001a94#64 (b1L sp pa b pc cdp ou adp i u (p + u))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64 ((p + u) % 268435456))]) (kMD v) outp) := by
  muld_ctx
  seg_step mdB1 0x80001a94#64 ([] : List (List (BitVec 8))) [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24]
    kMDKeys [bL, kL] [b1L, hL] [] hc

/-- The reload of `a->used`. -/
structure UFacts (M : Mem) (pa ua : Nat) : Prop where
  ra_ : Ram pa 4
  ua_v : bytesT4 M pa = BitVec.ofNat 32 ua
  ua_lt : ua < 2 ^ 31

theorem UFacts.sx {M : Mem} {pa ua : Nat} (h : UFacts M pa ua) :
    BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 ua := by
  rw [h.ua_v, signExtend_ofNat32 _ h.ua_lt]

/-- The back edge (`i + 1 < a->used`): carry `s / 2^28`. -/
theorem b_step (v : Abi) (outp : Array String) (sp pa b pc cdp ou adp i u s ua : Nat) (M : Mem)
    (hc : CodeAt M mpMulDBase mpMulDCode) (hf : UFacts M pa ua) (hs : s < 2 ^ 57) (hi : i + 1 < ua) :
    Triple (At 0x80001a94#64 (b1L sp pa b pc cdp ou adp i u s) M (kMD v) outp)
      (At 0x80001a74#64 (hL sp pa b pc cdp ou adp (i + 1) (s / 268435456)) (writeLog M []) (kMD v) outp) := by
  muld_ctx
  have hsx := hf.sx
  seg_step mdB 0x80001a74#64 [rd4 M pa] [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24]
    kMDKeys [b1L, hL] [hL] [hsx] hc

/-- After the loop (`1ab4`): `a4 = i`, the last index. -/
def eL (sp pa b pc cdp ou i u : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 80)), (8, BitVec.ofNat 64 u), (14, BitVec.ofNat 64 i),
   (18, BitVec.ofNat 64 (cdp + 4 * (i + 1))), (19, BitVec.ofNat 64 pa), (20, BitVec.ofNat 64 b),
   (22, BitVec.ofNat 64 pc), (24, BitVec.ofNat 64 ou)]

/-- The last iteration (`i + 1 = a->used`), falling out at `1ab4`. -/
theorem be_step (v : Abi) (outp : Array String) (sp pa b pc cdp ou adp i u s ua : Nat) (M : Mem)
    (hc : CodeAt M mpMulDBase mpMulDCode) (hf : UFacts M pa ua) (hs : s < 2 ^ 57) (hi : i + 1 = ua) :
    Triple (At 0x80001a94#64 (b1L sp pa b pc cdp ou adp i u s) M (kMD v) outp)
      (At 0x80001ab4#64 (eL sp pa b pc cdp ou i (s / 268435456)) (writeLog M []) (kMD v) outp) := by
  muld_ctx
  have hsx := hf.sx
  seg_step mdBe 0x80001ab4#64 [rd4 M pa] [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24]
    kMDKeys [b1L, hL] [eL] [hsx] hc

/-- At `1a4c` (`a->used > 0`): `s2 = c->dp`, `s8 = olduse`. -/
def p2L (ra : BitVec 64) (v : Abi) (sp pa b pc ua cdp ou : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 80)), (9, v.s.s1), (15, BitVec.ofNat 64 ua), (18, BitVec.ofNat 64 cdp),
   (19, BitVec.ofNat 64 pa), (20, BitVec.ofNat 64 b), (21, v.s.s5), (22, BitVec.ofNat 64 pc), (23, v.s.s7),
   (24, BitVec.ofNat 64 ou)]

/-- The second saves: `s0`, `s2`, `s8`. -/
def log2 (s0 : BitVec 64) (v : Abi) (sp : Nat) : List WEntry :=
  [(sp - 16, 8, s0), (sp - 32, 8, v.s.s2), (sp - 80, 8, v.s.s8)]

/-- The stack frame. -/
structure KFacts (sp : Nat) : Prop where
  rs : Ram (sp - 80) 80
  sp_al : sp % 16 = 0
  sp_ge : 80 ≤ sp
  code_off : sp ≤ mpMulDBase ∨ mpMulDBase + 336 ≤ sp - 80

theorem p2_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ua : Nat) (m : Mem)
    (hc : CodeAt m mpMulDBase mpMulDCode) (hf : KFacts sp) :
    Triple (At 0x80001a28#64 (p1L ra s0 v sp pa b pc ua) m (kMD v) outp)
      (At 0x80001a34#64 (p1L ra s0 v sp pa b pc ua) (writeLog m (log2 s0 v sp)) (kMD v) outp) := by
  muld_ctx
  seg_step mdP2 0x80001a34#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 15, 18, 19, 20, 21, 22, 23, 24] kMDKeys [p1L, log2] [p1L] [] hc

/-- `a->sign`, `c->used`, `c->dp` and the sign store. -/
structure P2Facts (m : Mem) (pa pc sa ou cdp : Nat) : Prop where
  ra_ : Ram pa 24
  rc : Ram pc 24
  pc_al : pc % 8 = 0
  sa_v : bytesT4 m (pa + 8) = BitVec.ofNat 32 sa
  ou_v : bytesT4 m pc = BitVec.ofNat 32 ou
  cdp_v : bytesT8 m (pc + 16) = BitVec.ofNat 64 cdp
  sa_lt : sa < 2 ^ 31
  ou_lt : ou < 2 ^ 31
  code_c : pc + 24 ≤ mpMulDBase ∨ mpMulDBase + 336 ≤ pc

theorem P2Facts.sx {m : Mem} {pa pc sa ou cdp : Nat} (h : P2Facts m pa pc sa ou cdp) :
    BitVec.signExtend 64 (bytesT4 m (pa + 8)) = BitVec.ofNat 64 sa ∧
      BitVec.signExtend 64 (bytesT4 m pc) = BitVec.ofNat 64 ou :=
  ⟨by rw [h.sa_v, signExtend_ofNat32 _ h.sa_lt], by rw [h.ou_v, signExtend_ofNat32 _ h.ou_lt]⟩

/-- `c->sign := a->sign`; `a->used > 0`. -/
theorem p2b_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ua sa ou cdp : Nat) (m : Mem)
    (hc : CodeAt m mpMulDBase mpMulDCode) (hf : P2Facts m pa pc sa ou cdp) (hua : 0 < ua)
    (hua' : ua < 2 ^ 31) :
    Triple (At 0x80001a34#64 (p1L ra s0 v sp pa b pc ua) m (kMD v) outp)
      (At 0x80001a4c#64 (p2L ra v sp pa b pc ua cdp ou) (writeLog m [(pc + 8, 4, BitVec.ofNat 64 sa)])
        (kMD v) outp) := by
  muld_ctx
  have ⟨hsa, hou⟩ := hf.sx
  seg_step mdP2b 0x80001a4c#64 [rd4 m (pa + 8), rd4 m pc, rd8 m (pc + 16)]
    [1, 2, 8, 9, 15, 18, 19, 20, 21, 22, 23, 24] kMDKeys [p1L] [p2L] [hsa, hou, hf.cdp_v] hc

/-- The join `1ac4`: carry `u`, `a4 = a->used + 1`, `s2 = c->dp + a->used`, `s1`/`s5`/`s7` restored. -/
def jL (v : Abi) (sp pa b pc cdp ou ua u : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 80)), (8, BitVec.ofNat 64 u), (9, v.s.s1), (14, BitVec.ofNat 64 (ua + 1)),
   (18, BitVec.ofNat 64 (cdp + 4 * ua)), (19, BitVec.ofNat 64 pa), (20, BitVec.ofNat 64 b), (21, v.s.s5),
   (22, BitVec.ofNat 64 pc), (23, v.s.s7), (24, BitVec.ofNat 64 ou)]

/-- `c->sign := a->sign`; `a->used = 0`: straight to the join. -/
theorem p2z_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc sa ou cdp : Nat) (m : Mem)
    (hc : CodeAt m mpMulDBase mpMulDCode) (hf : P2Facts m pa pc sa ou cdp) :
    Triple (At 0x80001a34#64 (p1L ra s0 v sp pa b pc 0) m (kMD v) outp)
      (At 0x80001ac4#64 (jL v sp pa b pc cdp ou 0 0) (writeLog m [(pc + 8, 4, BitVec.ofNat 64 sa)])
        (kMD v) outp) := by
  muld_ctx
  have ⟨hsa, hou⟩ := hf.sx
  seg_step mdP2z 0x80001ac4#64 [rd4 m (pa + 8), rd4 m pc, rd8 m (pc + 16)]
    [1, 2, 8, 9, 15, 18, 19, 20, 21, 22, 23, 24] kMDKeys [p1L] [jL] [hsa, hou, hf.cdp_v] hc

/-- The last saves: `s7`, then `s5`, `s1`. -/
def log3 (v : Abi) (sp : Nat) : List WEntry := [(sp - 72, 8, v.s.s7)]

def log4 (v : Abi) (sp : Nat) : List WEntry := [(sp - 56, 8, v.s.s5), (sp - 24, 8, v.s.s1)]

theorem p3_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ua cdp ou : Nat) (m : Mem)
    (hc : CodeAt m mpMulDBase mpMulDCode) (hf : KFacts sp) :
    Triple (At 0x80001a4c#64 (p2L ra v sp pa b pc ua cdp ou) m (kMD v) outp)
      (At 0x80001a50#64 (p2L ra v sp pa b pc ua cdp ou) (writeLog m (log3 v sp)) (kMD v) outp) := by
  muld_ctx
  seg_step mdP3 0x80001a50#64 ([] : List (List (BitVec 8)))
    [1, 2, 9, 15, 18, 19, 20, 21, 22, 23, 24] kMDKeys [p2L, log3] [p2L] [] hc

/-- `a->dp`. -/
structure P3Facts (m : Mem) (pa adp : Nat) : Prop where
  ra_ : Ram pa 24
  adp_v : bytesT8 m (pa + 16) = BitVec.ofNat 64 adp

theorem p3b_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ua cdp ou adp : Nat) (m : Mem)
    (hc : CodeAt m mpMulDBase mpMulDCode) (hk : KFacts sp) (hf : P3Facts m pa adp) (hb : b < 2 ^ 32) :
    Triple (At 0x80001a50#64 (p2L ra v sp pa b pc ua cdp ou) m (kMD v) outp)
      (At 0x80001a74#64 (hL sp pa b pc cdp ou adp 0 0) (writeLog m (log4 v sp)) (kMD v) outp) := by
  muld_ctx
  seg_step mdP3b 0x80001a74#64 [rd8 m (pa + 16)]
    [1, 2, 9, 15, 18, 19, 20, 21, 22, 23, 24] kMDKeys [p2L, log4] [hL] [hf.adp_v] hc

/-- The restores after the loop. -/
structure CFacts (M : Mem) (v : Abi) (sp : Nat) : Prop where
  rs : Ram (sp - 80) 80
  sp_al : sp % 16 = 0
  sp_ge : 80 ≤ sp
  s1_v : bytesT8 M (sp - 24) = v.s.s1
  s5_v : bytesT8 M (sp - 56) = v.s.s5
  s7_v : bytesT8 M (sp - 72) = v.s.s7

theorem c_step (v : Abi) (outp : Array String) (sp pa b pc cdp ou i u : Nat) (M : Mem)
    (hc : CodeAt M mpMulDBase mpMulDCode) (hf : CFacts M v sp) (hi : i + 2 < 2 ^ 31) :
    Triple (At 0x80001ab4#64 (eL sp pa b pc cdp ou i u) M (kMD v) outp)
      (At 0x80001ac4#64 (jL v sp pa b pc cdp ou (i + 1) u) (writeLog M []) (kMD v) outp) := by
  muld_ctx
  have h1 : bytesT8 M (sp - 80 + 56) = v.s.s1 := by rw [show sp - 80 + 56 = sp - 24 by omega]; exact hf.s1_v
  have h2 : bytesT8 M (sp - 80 + 24) = v.s.s5 := by rw [show sp - 80 + 24 = sp - 56 by omega]; exact hf.s5_v
  have h3 : bytesT8 M (sp - 80 + 8) = v.s.s7 := by rw [show sp - 80 + 8 = sp - 72 by omega]; exact hf.s7_v
  seg_step mdC 0x80001ac4#64 [rd8 M (sp - 80 + 56), rd8 M (sp - 80 + 24), rd8 M (sp - 80 + 8)]
    [2, 8, 14, 18, 19, 20, 22, 24] kMDKeys [eL] [jL] [h1, h2, h3] hc

/-- At `1ae0`: what `mp_clamp`'s set-up needs. -/
def dL (v : Abi) (sp pa b pc cdp ou ua u : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 80)), (8, BitVec.ofNat 64 u), (9, v.s.s1), (18, BitVec.ofNat 64 (cdp + 4 * ua)),
   (19, BitVec.ofNat 64 pa), (20, BitVec.ofNat 64 b), (21, v.s.s5), (22, BitVec.ofNat 64 pc), (23, v.s.s7),
   (24, BitVec.ofNat 64 ou)]

/-- The store of the last carry into `c->dp[a->used]`. -/
structure JFacts (cdp ua ou : Nat) : Prop where
  rc : Ram (cdp + 4 * ua) 4
  al : cdp % 4 = 0
  code_off : cdp + 4 * ua + 4 ≤ mpMulDBase ∨ mpMulDBase + 336 ≤ cdp + 4 * ua
  ua_lt : ua + 1 < 2 ^ 31
  ou_lt : ou < 2 ^ 31

/-- `olduse ≤ a->used + 1`: no `memset`. -/
theorem j0_step (v : Abi) (outp : Array String) (sp pa b pc cdp ou ua u : Nat) (M : Mem)
    (hc : CodeAt M mpMulDBase mpMulDCode) (hf : JFacts cdp ua ou) (hou : ou ≤ ua + 1) :
    Triple (At 0x80001ac4#64 (jL v sp pa b pc cdp ou ua u) M (kMD v) outp)
      (At 0x80001ae0#64 (dL v sp pa b pc cdp ou ua u) (writeLog M [(cdp + 4 * ua, 4, BitVec.ofNat 64 u)])
        (kMD v) outp) := by
  muld_ctx
  seg_step mdJ0 0x80001ae0#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24] kMDKeys [jL] [dL] [] hc

/-- At the `memset` call (`1adc`): `memset(c->dp + a->used + 1, 0, 4 (olduse - a->used - 1))`. -/
def msL (v : Abi) (sp pa b pc cdp ou ua u : Nat) : GRegs :=
  (10, BitVec.ofNat 64 (cdp + 4 * ua + 4)) :: (11, 0#64) :: (12, BitVec.ofNat 64 (4 * (ou - (ua + 1)))) ::
    dL v sp pa b pc cdp ou ua u

/-- `olduse > a->used + 1`: set up the `memset`. -/
theorem j1_step (v : Abi) (outp : Array String) (sp pa b pc cdp ou ua u : Nat) (M : Mem)
    (hc : CodeAt M mpMulDBase mpMulDCode) (hf : JFacts cdp ua ou) (hou : ua + 1 < ou) :
    Triple (At 0x80001ac4#64 (jL v sp pa b pc cdp ou ua u) M (kMD v) outp)
      (At 0x80001adc#64 (msL v sp pa b pc cdp ou ua u) (writeLog M [(cdp + 4 * ua, 4, BitVec.ofNat 64 u)])
        (kMD v) outp) := by
  muld_ctx
  seg_step mdJ1 0x80001adc#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24] kMDKeys [jL] [msL, dL] [] hc

/-- At the `mp_clamp` call (`1af0`): `a0 = c`. -/
def clL (v : Abi) (sp pa b pc cdp ou ua u : Nat) : GRegs :=
  (10, BitVec.ofNat 64 pc) :: dL v sp pa b pc cdp ou ua u

/-- `c->used := a->used + 1`. -/
structure DFacts (M : Mem) (pa pc ua : Nat) : Prop where
  ra_ : Ram pa 4
  rc : Ram pc 4
  pc_al : pc % 8 = 0
  ua_v : bytesT4 M pa = BitVec.ofNat 32 ua
  ua_lt : ua + 1 < 2 ^ 31
  code_c : pc + 4 ≤ mpMulDBase ∨ mpMulDBase + 336 ≤ pc

theorem d_step (v : Abi) (outp : Array String) (sp pa b pc cdp ou ua u : Nat) (M : Mem)
    (hc : CodeAt M mpMulDBase mpMulDCode) (hf : DFacts M pa pc ua) :
    Triple (At 0x80001ae0#64 (dL v sp pa b pc cdp ou ua u) M (kMD v) outp)
      (At 0x80001af0#64 (clL v sp pa b pc cdp ou ua u) (writeLog M [(pc, 4, BitVec.ofNat 64 (ua + 1))])
        (kMD v) outp) := by
  muld_ctx
  have hs : BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 ua := by
    rw [hf.ua_v, signExtend_ofNat32 _ (by omega)]
  seg_step mdD 0x80001af0#64 [rd4 M pa] [2, 8, 9, 18, 19, 20, 21, 22, 23, 24] kMDKeys [dL] [clL] [hs] hc

/-- Back from `mp_clamp` (`1af4`). -/
def fL (v : Abi) (sp : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 80)), (9, v.s.s1), (21, v.s.s5), (23, v.s.s7)]

/-- The return: `a0 = MP_OKAY`, `s0`–`s8` restored. -/
def rL (ra s0 : BitVec 64) (v : Abi) (sp : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, v.s.s1), (10, 0#64), (18, v.s.s2), (19, v.s.s3),
   (20, v.s.s4), (21, v.s.s5), (22, v.s.s6), (23, v.s.s7), (24, v.s.s8)]

/-- The saved frame at the epilogue. -/
structure EFacts (M : Mem) (ra s0 : BitVec 64) (v : Abi) (sp : Nat) : Prop where
  rs : Ram (sp - 80) 80
  sp_al : sp % 16 = 0
  sp_ge : 80 ≤ sp
  ra_al : ra.toNat % 4 = 0
  s0_v : bytesT8 M (sp - 16) = s0
  s2_v : bytesT8 M (sp - 32) = v.s.s2
  s8_v : bytesT8 M (sp - 80) = v.s.s8
  ra_v : bytesT8 M (sp - 8) = ra
  s3_v : bytesT8 M (sp - 40) = v.s.s3
  s4_v : bytesT8 M (sp - 48) = v.s.s4
  s6_v : bytesT8 M (sp - 64) = v.s.s6

theorem e_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M mpMulDBase mpMulDCode) (hf : EFacts M ra s0 v sp) :
    Triple (At 0x80001af4#64 (fL v sp) M (kMD v) outp) (At ra (rL ra s0 v sp) (writeLog M []) (kMD v) outp) := by
  muld_ctx
  have hra := hf.ra_al
  have h1 : bytesT8 M (sp - 80 + 64) = s0 := by rw [show sp - 80 + 64 = sp - 16 by omega]; exact hf.s0_v
  have h2 : bytesT8 M (sp - 80 + 48) = v.s.s2 := by rw [show sp - 80 + 48 = sp - 32 by omega]; exact hf.s2_v
  have h3 : bytesT8 M (sp - 80) = v.s.s8 := hf.s8_v
  have h4 : bytesT8 M (sp - 80 + 72) = ra := by rw [show sp - 80 + 72 = sp - 8 by omega]; exact hf.ra_v
  have h5 : bytesT8 M (sp - 80 + 40) = v.s.s3 := by rw [show sp - 80 + 40 = sp - 40 by omega]; exact hf.s3_v
  have h6 : bytesT8 M (sp - 80 + 32) = v.s.s4 := by rw [show sp - 80 + 32 = sp - 48 by omega]; exact hf.s4_v
  have h7 : bytesT8 M (sp - 80 + 16) = v.s.s6 := by rw [show sp - 80 + 16 = sp - 64 by omega]; exact hf.s6_v
  seg_step mdE ra [rd8 M (sp - 80 + 64), rd8 M (sp - 80 + 48), rd8 M (sp - 80), rd8 M (sp - 80 + 72),
      rd8 M (sp - 80 + 40), rd8 M (sp - 80 + 32), rd8 M (sp - 80 + 16)]
    [2, 9, 21, 23] kMDKeys [fL] [rL] [h1, h2, h3, h4, h5, h6, h7] hc

end Tom.Machine.Fn.MulD
