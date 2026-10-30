import Tom.Machine.Seg.MpAbs
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.AutoEq
import Vsa.Sim.TripleCat

/-!
# `mp_abs` on the machine: the segments

`mp_abs(a, b)` at `0x800005cc` (15 instructions). `a == b`:
`b->sign := MP_ZPOS`, return `MP_OKAY` (`mabsA`). Otherwise save `ra` and
`b` (`mabsP`), call `mp_copy(a, b)` at `05dc`, and on `MP_OKAY` reload `b`,
store `b->sign := MP_ZPOS`, restore `ra` and return `MP_OKAY` (`mabsR`).
-/


namespace Tom.Machine.Fn.MpAbs

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mabs_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpAbsBase = 0x800005cc := rfl
   have : mpAbsCode.length = 15 := rfl))

def entry : BitVec 64 := 0x800005cc#64

/-- The entry: `a0 = a`, `a1 = b`. -/
def entryL (ra s0 : BitVec 64) (sp pa pb : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)]

/-- The return. -/
def retL (ra s0 : BitVec 64) (sp : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)]

/-- `b`'s sign slot. -/
structure BSign (pb : Nat) : Prop where
  rb : Ram pb 24
  pb_al : pb % 8 = 0
  code_off : pb + 24 ≤ mpAbsBase ∨ mpAbsBase + 60 ≤ pb

/-- `a == b`: `sign := 0`, return `MP_OKAY`. -/
theorem a_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp p : Nat) (m : Mem)
    (hc : CodeAt m mpAbsBase mpAbsCode) (hb : BSign p) (hra : ra.toNat % 4 = 0) :
    Triple (At entry (entryL ra s0 sp p p) m v.keepR outp)
      (At ra (retL ra s0 sp) (writeLog m [(p + 8, 4, 0#64)]) v.keepR outp) := by
  mabs_ctx
  seg_step mabsA ra ([] : List (List (BitVec 8))) [1, 2, 8, 10, 11] abiKeysR [entry, entryL] [retL] [] hc

/-- The frame stores. -/
def frameLog (ra : BitVec 64) (sp pb : Nat) : List WEntry := [(sp - 8, 8, ra), (sp - 24, 8, BitVec.ofNat 64 pb)]

/-- The frame. -/
structure FFacts (sp : Nat) : Prop where
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  code_off : sp ≤ mpAbsBase ∨ mpAbsBase + 60 ≤ sp - 32

/-- `a != b`: the frame, to the `mp_copy` call (`05dc`, `a0`/`a1` unchanged). -/
theorem p_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb : Nat) (m : Mem)
    (hc : CodeAt m mpAbsBase mpAbsCode) (hf : FFacts sp) (hne : pa ≠ pb) (ha : pa < 2 ^ 32) (hb : pb < 2 ^ 32) :
    Triple (At entry (entryL ra s0 sp pa pb) m v.keepR outp)
      (At 0x800005dc#64 (entryL ra s0 (sp - 32) pa pb) (writeLog m (frameLog ra sp pb)) v.keepR outp) := by
  mabs_ctx
  seg_step mabsP 0x800005dc#64 ([] : List (List (BitVec 8))) [1, 2, 8, 10, 11] abiKeysR
    [entry, entryL, frameLog] [entryL] [] hc

/-- The saved frame. -/
structure RFacts (M : Mem) (ra : BitVec 64) (sp pb : Nat) : Prop where
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  ra_al : ra.toNat % 4 = 0
  ra_v : bytesT8 M (sp - 8) = ra
  pb_v : bytesT8 M (sp - 24) = BitVec.ofNat 64 pb
  s_b : sp ≤ pb ∨ pb + 24 ≤ sp - 32

/-- `mp_copy` returned `MP_OKAY`: `b->sign := 0`, restore, return `MP_OKAY`. -/
theorem r_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pb : Nat) (M : Mem)
    (hc : CodeAt M mpAbsBase mpAbsCode) (hf : RFacts M ra sp pb) (hb : BSign pb) :
    Triple (At 0x800005e0#64 [(2, BitVec.ofNat 64 (sp - 32)), (8, s0), (10, 0#64)] M v.keepR outp)
      (At ra (retL ra s0 sp) (writeLog M [(pb + 8, 4, 0#64)]) v.keepR outp) := by
  mabs_ctx
  have hra := hf.ra_al
  have h1 : bytesT8 M (sp - 32 + 8) = BitVec.ofNat 64 pb := by
    rw [show sp - 32 + 8 = sp - 24 by omega]; exact hf.pb_v
  have h2 : bytesT8 M (sp - 32 + 24) = ra := by rw [show sp - 32 + 24 = sp - 8 by omega]; exact hf.ra_v
  seg_step_eq mabsR ra [rd8 M (sp - 32 + 8), rd8 M (sp - 32 + 24)] [2, 8, 10] abiKeysR [] [retL] [h1, h2] hc

end Tom.Machine.Fn.MpAbs
