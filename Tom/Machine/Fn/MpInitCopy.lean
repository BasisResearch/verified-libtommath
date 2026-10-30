import Tom.Machine.Seg.MpInit
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Jal

/-!
# `mp_init_copy` on the machine: the segments

`mp_init_copy(a, b)` at `0x8000134c` (31 instructions): save `s0`, `s1`, `ra`
in a 48-byte frame and call `mp_init_size(a, b->used)` at `1368` (`micP`); on
an error return it (`micErr`); otherwise call `mp_copy(b, a)` at `1394`
(`micOK`) and return its result (`micCOK`, `MP_OKAY`: `mp_copy` with room
always succeeds, so its `mp_clear` branch is not taken). `s0`, `s1`, `sp`
travel in the pin list (`Abi.keepR1`).
-/


namespace Tom.Machine.Fn.MpInitCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mic_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpInitCopyBase = 0x8000134c := rfl
   have : mpInitCopyCode.length = 31 := rfl))

def entry : BitVec 64 := 0x8000134c#64

/-- Registers at the entry: `ra`, `sp`, `s0`, `s1`, `a0 = a`, `a1 = b`. -/
def entryL (ra s0 s1 : BitVec 64) (sp pa pb : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)]

/-- At the `mp_init_size(a, b->used)` call (`1368`). -/
def callL (ra : BitVec 64) (sp pa pb u : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pb), (9, BitVec.ofNat 64 pa),
   (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 u)]

/-- The frame stores: `s0`, `s1`, `ra`. -/
def frameLog (ra s0 s1 : BitVec 64) (sp : Nat) : List WEntry :=
  [(sp - 16, 8, s0), (sp - 24, 8, s1), (sp - 8, 8, ra)]

/-- The stack frame. -/
structure SFacts (sp : Nat) : Prop where
  rs : Ram (sp - 48) 48
  sp_al : sp % 16 = 0
  sp_ge : 48 ≤ sp
  code_off : mpInitCopyBase + 124 ≤ sp - 48

/-- The frame; `mp_init_size(a, b->used)`. -/
theorem pro_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb u : Nat) (m : Mem)
    (hc : CodeAt m mpInitCopyBase mpInitCopyCode) (hs : SFacts sp) (hpb : Ram pb 24)
    (hd : pb + 24 ≤ sp - 48 ∨ sp ≤ pb) (hu : BitVec.signExtend 64 (bytesT4 m pb) = BitVec.ofNat 64 u) :
    Triple (At entry (entryL ra s0 s1 sp pa pb) m v.keepR1 outp)
      (At 0x80001368#64 (callL ra sp pa pb u) (writeLog m (frameLog ra s0 s1 sp)) v.keepR1 outp) := by
  mic_ctx
  seg_step micP 0x80001368#64 [rd4 m pb] [1, 2, 8, 9, 10, 11] abiKeysR1 [entry, entryL, frameLog]
    [callL] [hu] hc

/-- Back from a call with `a0 = r`. -/
def backL (sp pa pb : Nat) (r : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pb), (9, BitVec.ofNat 64 pa), (10, r)]

/-- The return. -/
def retL (ra s0 s1 : BitVec 64) (sp : Nat) (r : BitVec 64) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, r)]

/-- `mp_init_size` failed: return its result. -/
theorem err_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb : Nat) (r : BitVec 64)
    (M : Mem) (hc : CodeAt M mpInitCopyBase mpInitCopyCode) (hra : ra.toNat % 4 = 0) (hs : SFacts sp)
    (hr : (r == 0#64) = false) (h40 : bytesT8 M (sp - 48 + 40) = ra) (h32 : bytesT8 M (sp - 48 + 32) = s0)
    (h24 : bytesT8 M (sp - 48 + 24) = s1) :
    Triple (At 0x8000136c#64 (backL sp pa pb r) M v.keepR1 outp)
      (At ra (retL ra s0 s1 sp r) (writeLog M []) v.keepR1 outp) := by
  mic_ctx
  seg_step micErr ra [rd8 M (sp - 48 + 40), rd8 M (sp - 48 + 32), rd8 M (sp - 48 + 24)] [2, 8, 9, 10]
    abiKeysR1 [backL] [retL] [hr, h40, h32, h24] hc

/-- At the `mp_copy(b, a)` call (`1394`). -/
def copyL (sp pa pb : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pb), (9, BitVec.ofNat 64 pa),
   (10, BitVec.ofNat 64 pb), (11, BitVec.ofNat 64 pa)]

/-- `mp_init_size` succeeded: `mp_copy(b, a)`. -/
theorem ok_step (v : Abi) (outp : Array String) (sp pa pb : Nat) (M : Mem)
    (hc : CodeAt M mpInitCopyBase mpInitCopyCode) :
    Triple (At 0x8000136c#64 (backL sp pa pb 0#64) M v.keepR1 outp)
      (At 0x80001394#64 (copyL sp pa pb) (writeLog M []) v.keepR1 outp) := by
  mic_ctx
  seg_step micOK 0x80001394#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10] abiKeysR1 [backL]
    [copyL] [] hc

/-- `mp_copy` returned `MP_OKAY`: return it. -/
theorem cok_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb : Nat)
    (M : Mem) (hc : CodeAt M mpInitCopyBase mpInitCopyCode) (hra : ra.toNat % 4 = 0) (hs : SFacts sp)
    (h40 : bytesT8 M (sp - 48 + 40) = ra) (h32 : bytesT8 M (sp - 48 + 32) = s0)
    (h24 : bytesT8 M (sp - 48 + 24) = s1) :
    Triple (At 0x80001398#64 (backL sp pa pb 0#64) M v.keepR1 outp)
      (At ra (retL ra s0 s1 sp 0#64) (writeLog M []) v.keepR1 outp) := by
  mic_ctx
  seg_step micCOK ra [rd8 M (sp - 48 + 40), rd8 M (sp - 48 + 32), rd8 M (sp - 48 + 24)] [2, 8, 9, 10]
    abiKeysR1 [backL] [retL] [h40, h32, h24] hc

end Tom.Machine.Fn.MpInitCopy
