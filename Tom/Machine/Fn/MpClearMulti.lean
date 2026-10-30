import Tom.Machine.Seg.MpClearMulti
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Jal
import Tom.Machine.Kit.Frame

/-!
# `mp_clear_multi` on the machine: the segments

`mp_clear_multi(mp, ...)` at `0x80000698` (21 instructions, varargs ending in
`NULL`): a 96-byte frame saves `s0`, `ra` and spills `a1..a7` to
`[sp - 56, sp)`, right below the caller's stack arguments, so argument `j ≥ 1`
lies at `sp - 64 + 8 j` (`mcmP`); `s0` walks that array. `a0 == NULL`:
return (`mcmZ`). Otherwise the loop at `6cc` calls `mp_clear(a0)` and loads
the next argument (`mcmL`) until it is `NULL` (`mcmE`). `s0`, `sp` travel in
the pin list (`Abi.keepR`).
-/


namespace Tom.Machine.Fn.MpClearMulti

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mcm_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpClearMultiBase = 0x80000698 := rfl
   have : mpClearMultiCode.length = 21 := rfl))

def entry : BitVec 64 := 0x80000698#64

/-- Registers at the entry: `ra`, `sp`, `s0`, `a0..a7 = r 0 .. r 7`. -/
def entryL (ra s0 : BitVec 64) (sp : Nat) (r : Nat → BitVec 64) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, r 0), (11, r 1), (12, r 2), (13, r 3), (14, r 4),
   (15, r 5), (16, r 6), (17, r 7)]

/-- The prologue's first stores: `s0`, `ra`, `a1`, `a2`. -/
def proLog1 (ra s0 : BitVec 64) (sp : Nat) (r : Nat → BitVec 64) : List WEntry :=
  [(sp - 80, 8, s0), (sp - 72, 8, ra), (sp - 56, 8, r 1), (sp - 48, 8, r 2)]

/-- The prologue's last stores: `a3..a7`, the `va_list` pointer. -/
def proLog2 (sp : Nat) (r : Nat → BitVec 64) : List WEntry :=
  [(sp - 40, 8, r 3), (sp - 32, 8, r 4), (sp - 24, 8, r 5), (sp - 16, 8, r 6), (sp - 8, 8, r 7),
   (sp - 88, 8, BitVec.ofNat 64 (sp - 56))]

/-- All the prologue's stores. -/
def proLog (ra s0 : BitVec 64) (sp : Nat) (r : Nat → BitVec 64) : List WEntry :=
  proLog1 ra s0 sp r ++ proLog2 sp r

/-- Half-way through the prologue (`6b0`). -/
def midL (ra : BitVec 64) (sp : Nat) (r : Nat → BitVec 64) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 96)), (8, BitVec.ofNat 64 (sp - 56)), (10, r 0), (13, r 3), (14, r 4),
   (15, r 5), (16, r 6), (17, r 7)]

/-- After the prologue (`6c8`). -/
def topL (ra : BitVec 64) (sp : Nat) (a0 : BitVec 64) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 96)), (8, BitVec.ofNat 64 (sp - 56)), (10, a0)]

/-- The stack frame. -/
structure SFacts (sp : Nat) : Prop where
  rs : Ram (sp - 96) 96
  sp_al : sp % 16 = 0
  sp_ge : 96 ≤ sp
  code_off : mpClearMultiBase + 84 ≤ sp - 96

theorem pro1_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (r : Nat → BitVec 64)
    (m : Mem) (hc : CodeAt m mpClearMultiBase mpClearMultiCode) (hs : SFacts sp) :
    Triple (At entry (entryL ra s0 sp r) m v.keepR outp)
      (At 0x800006b0#64 (midL ra sp r) (writeLog m (proLog1 ra s0 sp r)) v.keepR outp) := by
  mcm_ctx
  seg_step mcmP1 0x800006b0#64 ([] : List (List (BitVec 8))) [1, 2, 8, 10, 11, 12, 13, 14, 15, 16, 17] abiKeysR
    [entry, entryL, proLog1] [midL] [] hc

theorem pro2_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (r : Nat → BitVec 64)
    (M : Mem) (hc : CodeAt M mpClearMultiBase mpClearMultiCode) (hs : SFacts sp) :
    Triple (At 0x800006b0#64 (midL ra sp r) M v.keepR outp)
      (At 0x800006c8#64 (topL ra sp (r 0)) (writeLog M (proLog2 sp r)) v.keepR outp) := by
  mcm_ctx
  seg_step mcmP2 0x800006c8#64 ([] : List (List (BitVec 8))) [1, 2, 8, 10, 13, 14, 15, 16, 17] abiKeysR
    [midL, proLog2] [topL] [] hc

theorem pro_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (r : Nat → BitVec 64)
    (m : Mem) (hc : CodeAt m mpClearMultiBase mpClearMultiCode) (hs : SFacts sp) :
    Triple (At entry (entryL ra s0 sp r) m v.keepR outp)
      (At 0x800006c8#64 (topL ra sp (r 0)) (writeLog m (proLog ra s0 sp r)) v.keepR outp) := by
  have hc1 : CodeAt (writeLog m (proLog1 ra s0 sp r)) mpClearMultiBase mpClearMultiCode :=
    hc.of_eq fun x h1 h2 => writeLog_out _ _ _ (by
      have := hs.code_off; have e : mpClearMultiCode.length = 21 := rfl
      rw [e] at h2
      exact ⟨by simp only; omega, by simp only; omega, by simp only; omega, by simp only; omega, trivial⟩)
  rw [proLog, writeLog_append]
  exact Triple.seq (pro1_step ra s0 v outp sp r m hc hs) (pro2_step ra v outp sp r _ hc1 hs)

/-- The return. -/
def retL (ra s0 : BitVec 64) (sp : Nat) : GRegs := [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)]

/-- `mp == NULL`: return. -/
theorem zero_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M mpClearMultiBase mpClearMultiCode) (hra : ra.toNat % 4 = 0) (hs : SFacts sp)
    (h24 : bytesT8 M (sp - 96 + 24) = ra) (h16 : bytesT8 M (sp - 96 + 16) = s0) :
    Triple (At 0x800006c8#64 (topL ra sp 0#64) M v.keepR outp)
      (At ra (retL ra s0 sp) (writeLog M []) v.keepR outp) := by
  mcm_ctx
  seg_step mcmZ ra [rd8 M (sp - 96 + 24), rd8 M (sp - 96 + 16)] [1, 2, 8, 10] abiKeysR [topL] [retL]
    [h24, h16] hc

/-- The loop head (`6cc`): `s0 = s` (the next argument's slot), `a0 = p`. -/
def loopL (sp s p : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 96)), (8, BitVec.ofNat 64 s), (10, BitVec.ofNat 64 p)]

/-- `mp ≠ NULL`: into the loop. -/
theorem nz_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp p : Nat) (M : Mem)
    (hc : CodeAt M mpClearMultiBase mpClearMultiCode) (hz : (BitVec.ofNat 64 p == 0#64) = false) :
    Triple (At 0x800006c8#64 (topL ra sp (BitVec.ofNat 64 p)) M v.keepR outp)
      (At 0x800006cc#64 (loopL sp (sp - 56) p) (writeLog M []) v.keepR outp) := by
  mcm_ctx
  seg_step mcmNZ 0x800006cc#64 ([] : List (List (BitVec 8))) [1, 2, 8, 10] abiKeysR [topL] [loopL]
    [hz] hc

/-- Back from `mp_clear` (`6d0`). -/
def backL (sp s : Nat) : GRegs := [(2, BitVec.ofNat 64 (sp - 96)), (8, BitVec.ofNat 64 s)]

/-- The next argument `p ≠ NULL`: round again. -/
theorem next_step (v : Abi) (outp : Array String) (sp s p : Nat) (M : Mem)
    (hc : CodeAt M mpClearMultiBase mpClearMultiCode) (hs : Ram s 8) (hs8 : s + 8 < 2 ^ 64)
    (hp : bytesT8 M s = BitVec.ofNat 64 p) (hz : (BitVec.ofNat 64 p == 0#64) = false) (hp64 : p < 2 ^ 64)
    (hp0 : p ≠ 0) :
    Triple (At 0x800006d0#64 (backL sp s) M v.keepR outp)
      (At 0x800006cc#64 (loopL sp (s + 8) p) (writeLog M []) v.keepR outp) := by
  mcm_ctx
  have h8 : (s + 8) % 18446744073709551616 = s + 8 := Nat.mod_eq_of_lt hs8
  seg_step mcmL 0x800006cc#64 [rd8 M s] [2, 8] abiKeysR [backL] [loopL] [hp, hz, h8] hc

/-- The next argument is `NULL`: return. -/
theorem end_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp s : Nat) (M : Mem)
    (hc : CodeAt M mpClearMultiBase mpClearMultiCode) (hra : ra.toNat % 4 = 0) (hs : SFacts sp)
    (hsr : Ram s 8) (hp : bytesT8 M s = 0#64)
    (h24 : bytesT8 M (sp - 96 + 24) = ra) (h16 : bytesT8 M (sp - 96 + 16) = s0) :
    Triple (At 0x800006d0#64 (backL sp s) M v.keepR outp)
      (At ra (retL ra s0 sp) (writeLog M []) v.keepR outp) := by
  mcm_ctx
  seg_step mcmE ra [rd8 M s, rd8 M (sp - 96 + 24), rd8 M (sp - 96 + 16)] [2, 8] abiKeysR [backL] [retL]
    [hp, h24, h16] hc

/-! ## The prologue's frame -/

theorem pro_log (ra s0 : BitVec 64) (sp : Nat) (r : Nat → BitVec 64) : proLog ra s0 sp r =
    [(sp - 80, 8, s0), (sp - 72, 8, ra), (sp - 56, 8, r 1), (sp - 48, 8, r 2), (sp - 40, 8, r 3),
     (sp - 32, 8, r 4), (sp - 24, 8, r 5), (sp - 16, 8, r 6), (sp - 8, 8, r 7),
     (sp - 88, 8, BitVec.ofNat 64 (sp - 56))] := rfl

/-- The spilled argument `j` (`1 ≤ j ≤ 7`) at `sp - 64 + 8 j`. -/
theorem slot_pro (m : Mem) (ra s0 : BitVec 64) (sp : Nat) (r : Nat → BitVec 64) (hs : 96 ≤ sp) :
    ∀ j, 1 ≤ j → j ≤ 7 → bytesT8 (writeLog m (proLog ra s0 sp r)) (sp - 64 + 8 * j) = r j := by
  intro j h1 h7
  rw [pro_log]
  rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show sp - 64 + 8 * 1 = sp - 56 by omega]; exact bytesT8_log _ _ 2 _ _ rfl (by simp [OutLRange]; omega)
  · rw [show sp - 64 + 8 * 2 = sp - 48 by omega]; exact bytesT8_log _ _ 3 _ _ rfl (by simp [OutLRange]; omega)
  · rw [show sp - 64 + 8 * 3 = sp - 40 by omega]; exact bytesT8_log _ _ 4 _ _ rfl (by simp [OutLRange]; omega)
  · rw [show sp - 64 + 8 * 4 = sp - 32 by omega]; exact bytesT8_log _ _ 5 _ _ rfl (by simp [OutLRange]; omega)
  · rw [show sp - 64 + 8 * 5 = sp - 24 by omega]; exact bytesT8_log _ _ 6 _ _ rfl (by simp [OutLRange]; omega)
  · rw [show sp - 64 + 8 * 6 = sp - 16 by omega]; exact bytesT8_log _ _ 7 _ _ rfl (by simp [OutLRange]; omega)
  · rw [show sp - 64 + 8 * 7 = sp - 8 by omega]; exact bytesT8_log _ _ 8 _ _ rfl (by simp [OutLRange]; omega)

theorem pro_ra (m : Mem) (ra s0 : BitVec 64) (sp : Nat) (r : Nat → BitVec 64) (hs : 96 ≤ sp) :
    bytesT8 (writeLog m (proLog ra s0 sp r)) (sp - 96 + 24) = ra := by
  rw [pro_log, show sp - 96 + 24 = sp - 72 by omega]; exact bytesT8_log _ _ 1 _ _ rfl (by simp [OutLRange]; omega)

theorem pro_s0 (m : Mem) (ra s0 : BitVec 64) (sp : Nat) (r : Nat → BitVec 64) (hs : 96 ≤ sp) :
    bytesT8 (writeLog m (proLog ra s0 sp r)) (sp - 96 + 16) = s0 := by
  rw [pro_log, show sp - 96 + 16 = sp - 80 by omega]; exact bytesT8_log _ _ 0 _ _ rfl (by simp [OutLRange]; omega)

/-- The prologue writes `[sp - 88, sp)` only. -/
theorem pro_out (m : Mem) (ra s0 : BitVec 64) (sp : Nat) (r : Nat → BitVec 64) (x : Nat)
    (hx : x < sp - 88 ∨ sp ≤ x) (hs : 96 ≤ sp) : (writeLog m (proLog ra s0 sp r))[x]? = m[x]? := by
  rw [pro_log]
  exact writeLog_out _ _ _ ⟨by simp only; omega, by simp only; omega, by simp only; omega, by simp only; omega,
    by simp only; omega, by simp only; omega, by simp only; omega, by simp only; omega, by simp only; omega,
    by simp only; omega, trivial⟩

end Tom.Machine.Fn.MpClearMulti
