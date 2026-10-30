import Tom.Machine.Seg.MpClear
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Jal
import Tom.Machine.Kit.MemStore
import Tom.Machine.Kit.Frame
import Tom.Spec.Init

/-!
# `mp_clear` on the machine: the segments

`mp_clear(a)` at `0x80005018` (15 instructions). `a->dp == NULL`: return
(`mclrN`). Otherwise save `a` and `ra` in a 32-byte frame and call
`free(a->dp)` at `5030` (`mclrP`); after it, reload `a` and `ra`, zero
`dp`, `used`/`alloc` (one `sd`) and `sign`, and return (`mclrE`). `s0` is not
touched; it and `sp` travel in the pin list (`Abi.keepR`).
-/


namespace Tom.Machine.Fn.MpClear

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mclr_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpClearBase = 0x80005018 := rfl
   have : mpClearCode.length = 15 := rfl))

def entry : BitVec 64 := 0x80005018#64

/-- Registers at the entry: `ra`, `sp`, `s0`, `a0 = a`. -/
def entryL (ra s0 : BitVec 64) (sp p : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 p)]

/-- Registers at the return. -/
def retL (ra s0 : BitVec 64) (sp : Nat) : GRegs := [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0)]

/-- `a->dp == NULL`: return at once. -/
theorem null_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp p : Nat) (m : Mem)
    (hc : CodeAt m mpClearBase mpClearCode) (hra : ra.toNat % 4 = 0) (hp : Ram p 24)
    (hdp : bytesT8 m (p + 16) = 0#64) :
    Triple (At entry (entryL ra s0 sp p) m v.keepR outp)
      (At ra (retL ra s0 sp) (writeLog m []) v.keepR outp) := by
  mclr_ctx
  seg_step mclrN ra [rd8 m (p + 16)] [1, 2, 8, 10] abiKeysR [entry, entryL] [retL] [hdp] hc

/-- At the `free` call (`5030`): `a0 = dp`. -/
def callL (ra s0 : BitVec 64) (sp dp : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, s0), (10, BitVec.ofNat 64 dp)]

/-- The frame stores: `a` at `sp - 24`, `ra` at `sp - 8`. -/
def proLog (ra : BitVec 64) (sp p : Nat) : List WEntry :=
  [(sp - 24, 8, BitVec.ofNat 64 p), (sp - 8, 8, ra)]

/-- The stack frame. -/
structure SFacts (sp : Nat) : Prop where
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  code_off : sp ≤ mpClearBase ∨ mpClearBase + 60 ≤ sp - 32

/-- `a->dp ≠ NULL`: the frame, `a0 = dp`. -/
theorem pro_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp p dp : Nat) (m : Mem)
    (hc : CodeAt m mpClearBase mpClearCode) (hp : Ram p 24) (hs : SFacts sp)
    (hdp : bytesT8 m (p + 16) = BitVec.ofNat 64 dp) (hz : (BitVec.ofNat 64 dp == 0#64) = false) :
    Triple (At entry (entryL ra s0 sp p) m v.keepR outp)
      (At 0x80005030#64 (callL ra s0 sp dp) (writeLog m (proLog ra sp p)) v.keepR outp) := by
  mclr_ctx
  seg_step mclrP 0x80005030#64 [rd8 m (p + 16)] [1, 2, 8, 10] abiKeysR [entry, entryL, proLog]
    [callL] [hdp, hz] hc

/-- After `free` (`5034`). -/
def backL (s0 : BitVec 64) (sp : Nat) : GRegs := [(2, BitVec.ofNat 64 (sp - 32)), (8, s0)]

/-- `a` and `ra` reloaded (`503c`). -/
def zeroL (ra s0 : BitVec 64) (sp p : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, s0), (15, BitVec.ofNat 64 p)]

/-- Reload `a` and `ra`. -/
theorem back_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp p : Nat) (M : Mem)
    (hc : CodeAt M mpClearBase mpClearCode) (hs : SFacts sp)
    (h8 : bytesT8 M (sp - 32 + 8) = BitVec.ofNat 64 p) (h24 : bytesT8 M (sp - 32 + 24) = ra) :
    Triple (At 0x80005034#64 (backL s0 sp) M v.keepR outp)
      (At 0x8000503c#64 (zeroL ra s0 sp p) (writeLog M []) v.keepR outp) := by
  mclr_ctx
  seg_step mclrE1 0x8000503c#64 [rd8 M (sp - 32 + 8), rd8 M (sp - 32 + 24)] [2, 8] abiKeysR [backL]
    [zeroL] [h8, h24] hc

/-- The struct stores: `dp`, `used`/`alloc`, `sign`. -/
def epiLog (p : Nat) : List WEntry := [(p + 16, 8, 0#64), (p, 8, 0#64), (p + 8, 4, 0#64)]

/-- Zero the struct, return. -/
theorem zero_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp p : Nat) (M : Mem)
    (hc : CodeAt M mpClearBase mpClearCode) (hra : ra.toNat % 4 = 0) (hp : Ram p 24)
    (hpal : p % 8 = 0) (hpc : p + 24 ≤ mpClearBase ∨ mpClearBase + 60 ≤ p) (hs : SFacts sp) :
    Triple (At 0x8000503c#64 (zeroL ra s0 sp p) M v.keepR outp)
      (At ra (retL ra s0 sp) (writeLog M (epiLog p)) v.keepR outp) := by
  mclr_ctx
  have h0 : p % 18446744073709551616 = p := Nat.mod_eq_of_lt (by omega)
  have h8 : (p + 8) % 18446744073709551616 = p + 8 := Nat.mod_eq_of_lt (by omega)
  have h16 : (p + 16) % 18446744073709551616 = p + 16 := Nat.mod_eq_of_lt (by omega)
  seg_step mclrE2 ra ([] : List (List (BitVec 8))) [1, 2, 8, 15] abiKeysR [zeroL, epiLog]
    [retL] [h0, h8, h16] hc

theorem bytesT8_zero {M : Mem} {x : Nat} (h : ∀ k, k < 8 → M[x + k]? = some 0#8) :
    bytesT8 M x = 0#64 := by
  simp only [bytesT8]
  rw [show x = x + 0 from rfl, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
    h 4 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega)]
  rfl

/-- The bytes of a doubleword store of zero. -/
theorem sd_zero_byte (M : Mem) (a k : Nat) (hk : k < 8) : (applyW M (a, 8, 0#64))[a + k]? = some 0#8 := by
  rw [getElem?_applyW_sd_in M a (a + k) 0#64 (by omega) (by omega), Nat.add_sub_cancel_left]
  exact congrArg some (sdFill_zero k hk)

/-- The struct after the three zero stores. -/
theorem cleared_at (M : Mem) (p : Nat) : MpAt (writeLog M (epiLog p)) p 0 MpInt.cleared := by
  have e : writeLog M (epiLog p) =
      writeLog (applyW (applyW M (p + 16, 8, 0#64)) (p, 8, 0#64)) [(p + 8, 4, 0#64)] := rfl
  rw [e]
  refine { used := ?_, alloc := ?_, sign := ?_, dpv := ?_, digits := fun i hi => absurd hi (by simp [MpInt.cleared] at hi) }
  · rw [bytesT4_sw_out _ _ _ _ (by simp [Layout.offUsed])]
    exact bytesT4_zero fun k hk => sd_zero_byte _ _ k (by omega)
  · rw [bytesT4_sw_out _ _ _ _ (by simp [Layout.offAlloc])]
    simp only [Layout.offAlloc]
    exact bytesT4_zero fun k hk => by
      rw [show p + 4 + k = p + (4 + k) by omega]; exact sd_zero_byte _ _ _ (by omega)
  · simp only [Layout.offSign]; exact bytesT4_sw_self _ (p + 8) 0 (by decide)
  · rw [bytesT8_sw_out _ _ _ _ (by simp [Layout.offDp])]
    simp only [Layout.offDp]
    exact bytesT8_zero fun k hk => by
      rw [← writeLog_single, writeLog_out (applyW M (p + 16, 8, 0#64)) [(p, 8, 0#64)] (p + 16 + k)
        (show OutL [(p, 8, 0#64)] (p + 16 + k) from ⟨.inr (by simp only; omega), trivial⟩)]
      exact sd_zero_byte _ _ k hk


end Tom.Machine.Fn.MpClear
