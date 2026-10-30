import Tom.Machine.Seg.Expt2
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.BitW
import Tom.Machine.Kit.BitD
import Vsa.Sim.TripleCat

/-!
# `mp_2expt` on the machine: the segments

`mp_2expt(a, b)` at `0x800076d4` (42 instructions), `b ≥ 0`. The segments, in
program order, with the calls between them (made by the assembly, `call_std`):
`p_step` (`b ≥ 0`, save `ra`, `s0`–`s2`) → `jal mp_zero(a)` at `76f4` → `g_step`
→ `jal __divdi3(b, 28)` at `7700` → `w_step` (`s2 = D`, spill `D + 1`) → `jal
mp_grow(a, D + 1)` at `7714` (with room: `MP_OKAY`, D5) → `u1_step` (reload,
spill `MP_OKAY`) → `u2_step` (`a->used := D + 1`) → `jal __moddi3(b, 28)` at
`7740` → `e1_step` (`a->dp[D] := 1 << d`) → `e2_step` (restore, `MP_OKAY`).
`s0`–`s2` are locals: the segments keep `keepE` and carry `s1`, `s2`.
-/



namespace Tom.Machine.Fn.Expt2

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "m2expt_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mp2exptBase = 0x800076d4 := rfl
   have : mp2exptCode.length = 42 := rfl))

def entry : BitVec 64 := 0x800076d4#64

/-- `Abi.keepR1` without `s2` (a local here). -/
def keepE (v : Abi) : GRegs :=
  [(3, v.gp), (4, v.tp), (19, v.s.s3), (20, v.s.s4), (21, v.s.s5), (22, v.s.s6), (23, v.s.s7), (24, v.s.s8),
   (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

abbrev keysE : List Nat := [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- The entry: `a0 = a`, `a1 = b`. -/
def entryL (ra s0 : BitVec 64) (sp pa b : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 b)]

/-- The entry, `s1`, `s2` carried. -/
def entry1 (ra s0 s1 s2 : BitVec 64) (sp pa b : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 b),
   (18, s2)]

/-- The return (`MP_OKAY`), `s1`, `s2` carried. -/
def ret1 (ra s0 s1 s2 : BitVec 64) (sp : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, 0#64), (18, s2)]

/-- The stack frame. -/
structure FFacts (sp : Nat) : Prop where
  rs : Ram (sp - 48) 48
  sp_al : sp % 16 = 0
  sp_ge : 48 ≤ sp
  code_off : sp ≤ mp2exptBase ∨ mp2exptBase + 168 ≤ sp - 48

/-- The frame stores (`ra`, `s0`, `s1`, `s2`). -/
def frameLog (ra s0 s1 s2 : BitVec 64) (sp : Nat) : List WEntry :=
  [(sp - 8, 8, ra), (sp - 16, 8, s0), (sp - 24, 8, s1), (sp - 32, 8, s2)]

/-- At the `mp_zero(a)` call (`76f4`): `s0 = b`, `s1 = a`. -/
def zL (s2 : BitVec 64) (sp pa b : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 pa), (10, BitVec.ofNat 64 pa),
   (18, s2)]

/-- `b ≥ 0`: save the frame, set up `mp_zero(a)`. -/
theorem p_step (ra s0 s1 s2 : BitVec 64) (v : Abi) (outp : Array String) (sp pa b : Nat) (m : Mem)
    (hc : CodeAt m mp2exptBase mp2exptCode) (hs : FFacts sp) (hb : b < 2 ^ 31) :
    Triple (At entry (entry1 ra s0 s1 s2 sp pa b) m (keepE v) outp)
      (At 0x800076f4#64 (zL s2 sp pa b) (writeLog m (frameLog ra s0 s1 s2 sp)) (keepE v) outp) := by
  m2expt_ctx
  seg_step e2P 0x800076f4#64 ([] : List (List (BitVec 8))) [1, 2, 8, 9, 10, 11, 18] keysE
    [entry, entry1, frameLog] [zL] [] hc

/-- After `mp_zero`. -/
def kL (s2 : BitVec 64) (sp pa b : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 pa), (18, s2)]

/-- At the `__divdi3(b, 28)` call (`7700`). -/
def gL (s2 : BitVec 64) (sp pa b : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 pa), (10, BitVec.ofNat 64 b),
   (11, BitVec.ofNat 64 28), (18, s2)]

/-- Set up `__divdi3(b, 28)`. -/
theorem g_step (s2 : BitVec 64) (v : Abi) (outp : Array String) (sp pa b : Nat) (M : Mem)
    (hc : CodeAt M mp2exptBase mp2exptCode) :
    Triple (At 0x800076f8#64 (kL s2 sp pa b) M (keepE v) outp)
      (At 0x80007700#64 (gL s2 sp pa b) (writeLog M []) (keepE v) outp) := by
  m2expt_ctx
  seg_step e2G 0x80007700#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18] keysE [kL] [gL] [] hc

/-- After `__divdi3`: `a0 = D`. -/
def dL (s2 : BitVec 64) (sp pa b D : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 pa), (10, BitVec.ofNat 64 D),
   (18, s2)]

/-- At the `mp_grow(a, D + 1)` call (`7714`): `s2 = D`. -/
def grL (sp pa b D : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 pa), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 (D + 1)), (18, BitVec.ofNat 64 D)]

/-- `D = b / 28`: `s2 := D`, spill `D + 1`, set up `mp_grow(a, D + 1)`. -/
theorem w_step (s2 : BitVec 64) (v : Abi) (outp : Array String) (sp pa b D : Nat) (M : Mem)
    (hc : CodeAt M mp2exptBase mp2exptCode) (hs : FFacts sp) (hD : D < 2 ^ 30) :
    Triple (At 0x80007704#64 (dL s2 sp pa b D) M (keepE v) outp)
      (At 0x80007714#64 (grL sp pa b D) (writeLog M [(sp - 48, 8, BitVec.ofNat 64 (D + 1))]) (keepE v) outp) := by
  m2expt_ctx
  seg_step e2W 0x80007714#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10, 18] keysE [dL] [grL] [] hc

/-- After `mp_grow`: `a0 = MP_OKAY`. -/
def oL (sp pa b D : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 pa), (10, 0#64),
   (18, BitVec.ofNat 64 D)]

/-- The spilled `D + 1`, `a->dp`. -/
structure UFacts (M : Mem) (sp pa dp D : Nat) : Prop where
  rs : Ram (sp - 48) 48
  sp_ge : 48 ≤ sp
  sp_al : sp % 16 = 0
  ra_ : Ram pa 24
  d_v : bytesT8 M (sp - 48) = BitVec.ofNat 64 (D + 1)
  dp_v : bytesT8 M (pa + 16) = BitVec.ofNat 64 dp
  code_off : sp ≤ mp2exptBase ∨ mp2exptBase + 168 ≤ sp - 48

/-- At `7730`: `a1 = D + 1`, `a3 = a->dp`, `a5 = 4 D`. -/
def u1L (sp pa b dp D : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 pa), (10, 0#64),
   (11, BitVec.ofNat 64 (D + 1)), (13, BitVec.ofNat 64 dp), (15, BitVec.ofNat 64 (4 * D)), (18, BitVec.ofNat 64 D)]

/-- `MP_OKAY`: reload `D + 1`, `a->dp`; spill `MP_OKAY`. -/
theorem u1_step (v : Abi) (outp : Array String) (sp pa b dp D : Nat) (M : Mem)
    (hc : CodeAt M mp2exptBase mp2exptCode) (hf : UFacts M sp pa dp D) :
    Triple (At 0x80007718#64 (oL sp pa b D) M (keepE v) outp)
      (At 0x80007730#64 (u1L sp pa b dp D) (writeLog M [(sp - 40, 8, 0#64)]) (keepE v) outp) := by
  m2expt_ctx
  have h1 : bytesT8 M (sp - 48 + 0) = BitVec.ofNat 64 (D + 1) := by
    rw [show sp - 48 + 0 = sp - 48 by omega]; exact hf.d_v
  seg_step e2U1 0x80007730#64 [rd8 M (sp - 48 + 0), rd8 M (pa + 16)] [2, 8, 9, 10, 18] keysE [oL] [u1L]
    [h1, hf.dp_v] hc

/-- At the `__moddi3(b, 28)` call (`7740`): `s0 = &a->dp[D]`. -/
def mL (sp pa b q D : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 q), (9, BitVec.ofNat 64 pa), (10, BitVec.ofNat 64 b),
   (11, BitVec.ofNat 64 28), (18, BitVec.ofNat 64 D)]

/-- `a`'s struct slot. -/
structure SFacts (pa : Nat) : Prop where
  ra_ : Ram pa 24
  pa_al : pa % 8 = 0
  code_off : pa + 24 ≤ mp2exptBase ∨ mp2exptBase + 168 ≤ pa

/-- `a->used := D + 1`; set up `__moddi3(b, 28)`. -/
theorem u2_step (v : Abi) (outp : Array String) (sp pa b dp D : Nat) (M : Mem)
    (hc : CodeAt M mp2exptBase mp2exptCode) (hf : SFacts pa) :
    Triple (At 0x80007730#64 (u1L sp pa b dp D) M (keepE v) outp)
      (At 0x80007740#64 (mL sp pa b (dp + 4 * D) D) (writeLog M [(pa, 4, BitVec.ofNat 64 (D + 1))]) (keepE v)
        outp) := by
  m2expt_ctx
  seg_step e2U2 0x80007740#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10, 11, 13, 15, 18] keysE [u1L] [mL] [] hc

/-- After `__moddi3`: `a0 = d`. -/
def eL (sp pa q d D : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 q), (9, BitVec.ofNat 64 pa), (10, BitVec.ofNat 64 d),
   (18, BitVec.ofNat 64 D)]

/-- Digit `D`'s slot. -/
structure DFacts (q : Nat) : Prop where
  rq : Ram q 4
  q_al : q % 4 = 0
  code_off : q + 4 ≤ mp2exptBase ∨ mp2exptBase + 168 ≤ q

/-- At `7750`. -/
def e1L (sp pa D : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (9, BitVec.ofNat 64 pa), (18, BitVec.ofNat 64 D)]

/-- `a->dp[D] := 1 << d`. -/
theorem e1_step (v : Abi) (outp : Array String) (sp pa q d D : Nat) (M : Mem)
    (hc : CodeAt M mp2exptBase mp2exptCode) (hf : DFacts q) (hd : d < 28) :
    Triple (At 0x80007744#64 (eL sp pa q d D) M (keepE v) outp)
      (At 0x80007750#64 (e1L sp pa D) (writeLog M [(q, 4, BitVec.ofNat 64 (2 ^ d))]) (keepE v) outp) := by
  m2expt_ctx
  seg_stepu e2E1 0x80007750#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10, 18] keysE [eL] [e1L] [] hc
    using (repeat' apply And.intro) <;> first
      | omega
      | rw [BitD.sll_one d (by omega)]

/-- The whole saved frame. -/
structure RFacts (M : Mem) (ra s0 s1 s2 : BitVec 64) (sp : Nat) : Prop where
  rs : Ram (sp - 48) 48
  sp_ge : 48 ≤ sp
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  s1_v : bytesT8 M (sp - 24) = s1
  s2_v : bytesT8 M (sp - 32) = s2
  ra_al : ra.toNat % 4 = 0

/-- Restore the frame, return `MP_OKAY`. -/
theorem e2_step (ra s0 s1 s2 : BitVec 64) (v : Abi) (outp : Array String) (sp pa D : Nat) (M : Mem)
    (hc : CodeAt M mp2exptBase mp2exptCode) (hf : RFacts M ra s0 s1 s2 sp) :
    Triple (At 0x80007750#64 (e1L sp pa D) M (keepE v) outp)
      (At ra (ret1 ra s0 s1 s2 sp) (writeLog M []) (keepE v) outp) := by
  m2expt_ctx
  have hra := hf.ra_al
  have h1 : bytesT8 M (sp - 48 + 40) = ra := by rw [show sp - 48 + 40 = sp - 8 by omega]; exact hf.ra_v
  have h2 : bytesT8 M (sp - 48 + 32) = s0 := by rw [show sp - 48 + 32 = sp - 16 by omega]; exact hf.s0_v
  have h3 : bytesT8 M (sp - 48 + 24) = s1 := by rw [show sp - 48 + 24 = sp - 24 by omega]; exact hf.s1_v
  have h4 : bytesT8 M (sp - 48 + 16) = s2 := by rw [show sp - 48 + 16 = sp - 32 by omega]; exact hf.s2_v
  seg_step e2E2 ra [rd8 M (sp - 48 + 40), rd8 M (sp - 48 + 32), rd8 M (sp - 48 + 24), rd8 M (sp - 48 + 16)]
    [2, 9, 18] keysE [e1L] [ret1] [h1, h2, h3, h4] hc

end Tom.Machine.Fn.Expt2
