import Tom.Machine.Seg.MpInitMulti
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Jal
import Tom.Machine.Kit.Frame
import Tom.Machine.Kit.Keep

/-!
# `mp_init_multi` on the machine: the segments

`mp_init_multi(mp, ...)` at `0x800013c8` (52 instructions, varargs ending in
`NULL`): a 112-byte frame saves `s1`, `ra`, spills `a1..a7` to `[sp - 56, sp)`
(argument `j ≥ 1` at `sp - 64 + 8 j`) and keeps a `va_list` pointer at
`sp - 112` (`mimP1`, `mimP2`). `mp == NULL`: `MP_OKAY` (`mimZ`). Otherwise
save `s0`, `s2`, `s0 := 0` (the count), `s2 := mp` (`mimS`) and loop at `1428`:
`mp_init(a0)`; on success count, load the next argument through the
`va_list` pointer (`mimN`) or stop at `NULL` (`mimD`, `mimDE`: `MP_OKAY`). On
failure clear the `n` initialised ones, walking the slots from `mp` with
`s1` up to `s0 = sp - 56 + 8 n` (`mimF1`, `mimCa`, `mimCb`, `mimCc`; none:
`mimF0`), and return `MP_MEM` (`mimFE`). `s0`, `s1`, `s2`, `sp` travel in the
pin list (`Abi.keepR2`).
-/


namespace Tom.Machine.Fn.MpInitMulti

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mim_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpInitMultiBase = 0x800013c8 := rfl
   have : mpInitMultiCode.length = 52 := rfl))

def entry : BitVec 64 := 0x800013c8#64

/-- Registers at the entry: `ra`, `sp`, `s0`, `s1`, `s2`, `a0..a7 = r 0 .. r 7`. -/
def entryL (ra s0 s1 s2 : BitVec 64) (sp : Nat) (r : Nat → BitVec 64) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (18, s2), (10, r 0), (11, r 1), (12, r 2), (13, r 3),
   (14, r 4), (15, r 5), (16, r 6), (17, r 7)]

/-- The prologue's first stores: `s1`, `ra`, `a1`, `a2`. -/
def proLog1 (ra s1 : BitVec 64) (sp : Nat) (r : Nat → BitVec 64) : List WEntry :=
  [(sp - 88, 8, s1), (sp - 72, 8, ra), (sp - 56, 8, r 1), (sp - 48, 8, r 2)]

/-- The prologue's last stores: `a3..a7`, the `va_list` pointer. -/
def proLog2 (sp : Nat) (r : Nat → BitVec 64) : List WEntry :=
  [(sp - 40, 8, r 3), (sp - 32, 8, r 4), (sp - 24, 8, r 5), (sp - 16, 8, r 6), (sp - 8, 8, r 7),
   (sp - 112, 8, BitVec.ofNat 64 (sp - 56))]

def proLog (ra s1 : BitVec 64) (sp : Nat) (r : Nat → BitVec 64) : List WEntry :=
  proLog1 ra s1 sp r ++ proLog2 sp r

/-- Half-way through the prologue (`13e0`). -/
def midL (ra s0 s2 : BitVec 64) (sp : Nat) (r : Nat → BitVec 64) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 112)), (8, s0), (9, BitVec.ofNat 64 (sp - 56)), (18, s2), (10, r 0),
   (13, r 3), (14, r 4), (15, r 5), (16, r 6), (17, r 7)]

/-- After the prologue (`13f8`). -/
def topL (ra s0 s2 : BitVec 64) (sp : Nat) (a0 : BitVec 64) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 112)), (8, s0), (9, BitVec.ofNat 64 (sp - 56)), (18, s2), (10, a0)]

/-- The stack frame. -/
structure SFacts (sp : Nat) : Prop where
  rs : Ram (sp - 112) 112
  sp_al : sp % 16 = 0
  sp_ge : 112 ≤ sp
  code_off : mpInitMultiBase + 208 ≤ sp - 112

theorem pro1_step (ra s0 s1 s2 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (r : Nat → BitVec 64)
    (m : Mem) (hc : CodeAt m mpInitMultiBase mpInitMultiCode) (hs : SFacts sp) :
    Triple (At entry (entryL ra s0 s1 s2 sp r) m v.keepR2 outp)
      (At 0x800013e0#64 (midL ra s0 s2 sp r) (writeLog m (proLog1 ra s1 sp r)) v.keepR2 outp) := by
  mim_ctx
  seg_step mimP1 0x800013e0#64 ([] : List (List (BitVec 8))) [1, 2, 8, 9, 18, 10, 11, 12, 13, 14, 15, 16, 17]
    abiKeysR2 [entry, entryL, proLog1] [midL] [] hc

theorem pro2_step (ra s0 s2 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (r : Nat → BitVec 64)
    (M : Mem) (hc : CodeAt M mpInitMultiBase mpInitMultiCode) (hs : SFacts sp) :
    Triple (At 0x800013e0#64 (midL ra s0 s2 sp r) M v.keepR2 outp)
      (At 0x800013f8#64 (topL ra s0 s2 sp (r 0)) (writeLog M (proLog2 sp r)) v.keepR2 outp) := by
  mim_ctx
  seg_step mimP2 0x800013f8#64 ([] : List (List (BitVec 8))) [1, 2, 8, 9, 18, 10, 13, 14, 15, 16, 17]
    abiKeysR2 [midL, proLog2] [topL] [] hc

theorem pro_step (ra s0 s1 s2 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (r : Nat → BitVec 64)
    (m : Mem) (hc : CodeAt m mpInitMultiBase mpInitMultiCode) (hs : SFacts sp) :
    Triple (At entry (entryL ra s0 s1 s2 sp r) m v.keepR2 outp)
      (At 0x800013f8#64 (topL ra s0 s2 sp (r 0)) (writeLog m (proLog ra s1 sp r)) v.keepR2 outp) := by
  have hc1 : CodeAt (writeLog m (proLog1 ra s1 sp r)) mpInitMultiBase mpInitMultiCode :=
    hc.of_eq fun x h1 h2 => writeLog_out _ _ _ (by
      have := hs.code_off; have e : mpInitMultiCode.length = 52 := rfl
      rw [e] at h2
      exact ⟨by simp only; omega, by simp only; omega, by simp only; omega, by simp only; omega, trivial⟩)
  rw [proLog, writeLog_append]
  exact Triple.seq (pro1_step ra s0 s1 s2 v outp sp r m hc hs) (pro2_step ra s0 s2 v outp sp r _ hc1 hs)

/-- A return with `a0 = r`. -/
def retL (ra s0 s1 s2 : BitVec 64) (sp : Nat) (r : BitVec 64) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (18, s2), (10, r)]

/-- `mp == NULL`: `MP_OKAY`. -/
theorem zero_step (ra s0 s1 s2 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M mpInitMultiBase mpInitMultiCode) (hra : ra.toNat % 4 = 0) (hs : SFacts sp)
    (h40 : bytesT8 M (sp - 112 + 40) = ra) (h24 : bytesT8 M (sp - 112 + 24) = s1) :
    Triple (At 0x800013f8#64 (topL ra s0 s2 sp 0#64) M v.keepR2 outp)
      (At ra (retL ra s0 s1 s2 sp 0#64) (writeLog M []) v.keepR2 outp) := by
  mim_ctx
  seg_step mimZ ra [rd8 M (sp - 112 + 40), rd8 M (sp - 112 + 24)] [1, 2, 8, 9, 18, 10] abiKeysR2 [topL] [retL]
    [h40, h24] hc

/-- The loop head (`1428`): count `i`, `s2 = mp`, `a0 = p`. -/
def headL (sp i p0 p : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 112)), (8, BitVec.ofNat 64 i), (9, BitVec.ofNat 64 (sp - 56)), (18, BitVec.ofNat 64 p0),
   (10, BitVec.ofNat 64 p)]

/-- `s0`, `s2` saved. -/
def startLog (s0 s2 : BitVec 64) (sp : Nat) : List WEntry := [(sp - 80, 8, s0), (sp - 96, 8, s2)]

/-- `mp ≠ NULL`: save `s0`, `s2`; into the loop. -/
theorem start_step (ra s0 s2 : BitVec 64) (v : Abi) (outp : Array String) (sp p : Nat) (M : Mem)
    (hc : CodeAt M mpInitMultiBase mpInitMultiCode) (hs : SFacts sp) (hz : (BitVec.ofNat 64 p == 0#64) = false) :
    Triple (At 0x800013f8#64 (topL ra s0 s2 sp (BitVec.ofNat 64 p)) M v.keepR2 outp)
      (At 0x80001428#64 (headL sp 0 p p) (writeLog M (startLog s0 s2 sp)) v.keepR2 outp) := by
  mim_ctx
  seg_step mimS 0x80001428#64 ([] : List (List (BitVec 8))) [1, 2, 8, 9, 18, 10] abiKeysR2 [topL, startLog]
    [headL] [hz] hc

/-- Back from `mp_init` (`142c`) with `a0 = r`. -/
def backL (sp i p0 : Nat) (r : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 112)), (8, BitVec.ofNat 64 i), (9, BitVec.ofNat 64 (sp - 56)), (18, BitVec.ofNat 64 p0),
   (10, r)]

/-- `mp_init` succeeded, the next argument `p ≠ NULL` (through the `va_list` pointer `w`). -/
theorem next_step (v : Abi) (outp : Array String) (sp i p0 w p : Nat) (M : Mem)
    (hc : CodeAt M mpInitMultiBase mpInitMultiCode) (hs : SFacts sp) (hw : Ram w 8) (hw8 : w + 8 < 2 ^ 64)
    (hi : i + 1 < 2 ^ 31)
    (h0 : bytesT8 M (sp - 112) = BitVec.ofNat 64 w) (hp : bytesT8 M w = BitVec.ofNat 64 p)
    (hp64 : p < 2 ^ 64) (hp0 : p ≠ 0) :
    Triple (At 0x8000142c#64 (backL sp i p0 0#64) M v.keepR2 outp)
      (At 0x80001428#64 (headL sp (i + 1) p0 p) (writeLog M [(sp - 112, 8, BitVec.ofNat 64 (w + 8))])
        v.keepR2 outp) := by
  mim_ctx
  have h8 : (w + 8) % 18446744073709551616 = w + 8 := Nat.mod_eq_of_lt hw8
  have h1 : (i + 1) % 4294967296 = i + 1 := Nat.mod_eq_of_lt (by omega)
  seg_step mimN 0x80001428#64 [rd8 M (sp - 112), rd8 M w] [2, 8, 9, 18, 10] abiKeysR2 [backL]
    [headL] [h0, hp, h8, h1] hc

/-- At the epilogue of the success path (`147c`). -/
def doneL (sp i p0 : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 112)), (8, BitVec.ofNat 64 i), (9, BitVec.ofNat 64 (sp - 56)), (18, BitVec.ofNat 64 p0),
   (10, 0#64)]

/-- `mp_init` succeeded, the next argument is `NULL`. -/
theorem done_step (v : Abi) (outp : Array String) (sp i p0 w : Nat) (M : Mem)
    (hc : CodeAt M mpInitMultiBase mpInitMultiCode) (hs : SFacts sp) (hw : Ram w 8) (hw8 : w + 8 < 2 ^ 64)
    (hi : i + 1 < 2 ^ 31)
    (h0 : bytesT8 M (sp - 112) = BitVec.ofNat 64 w) (hp : bytesT8 M w = 0#64) :
    Triple (At 0x8000142c#64 (backL sp i p0 0#64) M v.keepR2 outp)
      (At 0x8000147c#64 (doneL sp (i + 1) p0) (writeLog M [(sp - 112, 8, BitVec.ofNat 64 (w + 8))])
        v.keepR2 outp) := by
  mim_ctx
  have h8 : (w + 8) % 18446744073709551616 = w + 8 := Nat.mod_eq_of_lt hw8
  have h1 : (i + 1) % 4294967296 = i + 1 := Nat.mod_eq_of_lt (by omega)
  seg_step mimD 0x8000147c#64 [rd8 M (sp - 112), rd8 M w] [2, 8, 9, 18, 10] abiKeysR2 [backL]
    [doneL] [h0, hp, h8, h1] hc

/-- The success epilogue: `MP_OKAY`. -/
theorem dend_step (ra s0 s1 s2 : BitVec 64) (v : Abi) (outp : Array String) (sp i p0 : Nat) (M : Mem)
    (hc : CodeAt M mpInitMultiBase mpInitMultiCode) (hra : ra.toNat % 4 = 0) (hs : SFacts sp)
    (h32 : bytesT8 M (sp - 112 + 32) = s0) (h16 : bytesT8 M (sp - 112 + 16) = s2)
    (h40 : bytesT8 M (sp - 112 + 40) = ra) (h24 : bytesT8 M (sp - 112 + 24) = s1) :
    Triple (At 0x8000147c#64 (doneL sp i p0) M v.keepR2 outp)
      (At ra (retL ra s0 s1 s2 sp 0#64) (writeLog M []) v.keepR2 outp) := by
  mim_ctx
  seg_step mimDE ra [rd8 M (sp - 112 + 32), rd8 M (sp - 112 + 16), rd8 M (sp - 112 + 40), rd8 M (sp - 112 + 24)]
    [2, 8, 9, 18, 10] abiKeysR2 [doneL] [retL] [h32, h16, h40, h24] hc

/-- At the failure epilogue (`1460`). -/
def failL (sp : Nat) : GRegs := [(2, BitVec.ofNat 64 (sp - 112))]

/-- `mp_init` failed with nothing initialised. -/
theorem fail0_step (v : Abi) (outp : Array String) (sp p0 : Nat) (M : Mem)
    (hc : CodeAt M mpInitMultiBase mpInitMultiCode) (hs : SFacts sp) :
    Triple (At 0x8000142c#64 (backL sp 0 p0 0xfffffffffffffffe#64) M v.keepR2 outp)
      (At 0x80001460#64 (failL sp) (writeLog M [(sp - 104, 8, BitVec.ofNat 64 (sp - 56))]) v.keepR2 outp) := by
  mim_ctx
  seg_step mimF0 0x80001460#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 10] abiKeysR2 [backL] [failL] [] hc

/-- The failure epilogue: `MP_MEM`. -/
theorem fend_step (ra s0 s1 s2 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M mpInitMultiBase mpInitMultiCode) (hra : ra.toNat % 4 = 0) (hs : SFacts sp)
    (h32 : bytesT8 M (sp - 112 + 32) = s0) (h16 : bytesT8 M (sp - 112 + 16) = s2)
    (h40 : bytesT8 M (sp - 112 + 40) = ra) (h24 : bytesT8 M (sp - 112 + 24) = s1) :
    Triple (At 0x80001460#64 (failL sp) M v.keepR2 outp)
      (At ra (retL ra s0 s1 s2 sp 0xfffffffffffffffe#64) (writeLog M []) v.keepR2 outp) := by
  mim_ctx
  seg_step mimFE ra [rd8 M (sp - 112 + 32), rd8 M (sp - 112 + 40), rd8 M (sp - 112 + 16), rd8 M (sp - 112 + 24)]
    [2] abiKeysR2 [failL] [retL] [h32, h16, h40, h24] hc

/-- The cleanup loop's head (`144c`): bound `b`, slot `s`, `s2 = p`. -/
def clrL (sp b s p : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 112)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 s), (18, BitVec.ofNat 64 p)]

/-- `mp_init` failed after `n > 0`: the bound `sp - 56 + 8 n`, into the cleanup loop. -/
theorem fail1_step (v : Abi) (outp : Array String) (sp n p0 : Nat) (M : Mem)
    (hc : CodeAt M mpInitMultiBase mpInitMultiCode) (hs : SFacts sp) (hn : 0 < n) (hn' : n < 2 ^ 31) :
    Triple (At 0x8000142c#64 (backL sp n p0 0xfffffffffffffffe#64) M v.keepR2 outp)
      (At 0x8000144c#64 (clrL sp (sp - 56 + 8 * n) (sp - 56) p0)
        (writeLog M [(sp - 104, 8, BitVec.ofNat 64 (sp - 56))]) v.keepR2 outp) := by
  mim_ctx
  seg_step mimF1 0x8000144c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 10] abiKeysR2 [backL] [clrL] [] hc

/-- At the `mp_clear(s2)` call (`1450`). -/
def callL (sp b s p : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 112)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 s), (18, BitVec.ofNat 64 p),
   (10, BitVec.ofNat 64 p)]

theorem ca_step (v : Abi) (outp : Array String) (sp b s p : Nat) (M : Mem)
    (hc : CodeAt M mpInitMultiBase mpInitMultiCode) :
    Triple (At 0x8000144c#64 (clrL sp b s p) M v.keepR2 outp)
      (At 0x80001450#64 (callL sp b s p) (writeLog M []) v.keepR2 outp) := by
  mim_ctx
  seg_step mimCa 0x80001450#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18] abiKeysR2 [clrL] [callL] [] hc

/-- Back from `mp_clear` (`1454`). -/
def cbackL (sp b s : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 112)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 s)]

/-- Round again: `s += 8`, `s2 := *s` (the next initialised argument). -/
theorem cb_step (v : Abi) (outp : Array String) (sp b s p : Nat) (M : Mem)
    (hc : CodeAt M mpInitMultiBase mpInitMultiCode) (hsr : Ram s 8) (hs8 : s + 8 < 2 ^ 64) (hb : b < 2 ^ 64)
    (hne : s + 8 ≠ b) (hp : bytesT8 M s = BitVec.ofNat 64 p) :
    Triple (At 0x80001454#64 (cbackL sp b s) M v.keepR2 outp)
      (At 0x8000144c#64 (clrL sp b (s + 8) p) (writeLog M []) v.keepR2 outp) := by
  mim_ctx
  have h8 : (s + 8) % 18446744073709551616 = s + 8 := Nat.mod_eq_of_lt hs8
  have hs' : s + 8 - 8 = s := by omega
  seg_step mimCb 0x8000144c#64 [rd8 M s] [2, 8, 9] abiKeysR2 [cbackL] [clrL] [hp, h8, hs'] hc

/-- Done: `s + 8 = b`. -/
theorem cc_step (v : Abi) (outp : Array String) (sp b s : Nat) (M : Mem)
    (hc : CodeAt M mpInitMultiBase mpInitMultiCode) (hsr : Ram s 8) (hs8 : s + 8 < 2 ^ 64) (he : s + 8 = b) :
    Triple (At 0x80001454#64 (cbackL sp b s) M v.keepR2 outp)
      (At 0x80001460#64 (failL sp) (writeLog M []) v.keepR2 outp) := by
  mim_ctx
  have h8 : (s + 8) % 18446744073709551616 = s + 8 := Nat.mod_eq_of_lt hs8
  have hs' : s + 8 - 8 = s := by omega
  seg_step mimCc 0x80001460#64 [rd8 M s] [2, 8, 9] abiKeysR2 [cbackL] [failL] [h8, hs'] hc

/-! ## The prologue's frame -/

/-- The prologue's and the loop start's stores. -/
def allLog (ra s0 s1 s2 : BitVec 64) (sp : Nat) (r : Nat → BitVec 64) : List WEntry :=
  proLog ra s1 sp r ++ startLog s0 s2 sp

theorem all_log (ra s0 s1 s2 : BitVec 64) (sp : Nat) (r : Nat → BitVec 64) : allLog ra s0 s1 s2 sp r =
    [(sp - 88, 8, s1), (sp - 72, 8, ra), (sp - 56, 8, r 1), (sp - 48, 8, r 2), (sp - 40, 8, r 3),
     (sp - 32, 8, r 4), (sp - 24, 8, r 5), (sp - 16, 8, r 6), (sp - 8, 8, r 7),
     (sp - 112, 8, BitVec.ofNat 64 (sp - 56)), (sp - 80, 8, s0), (sp - 96, 8, s2)] := rfl

theorem pro_log (ra s1 : BitVec 64) (sp : Nat) (r : Nat → BitVec 64) : proLog ra s1 sp r =
    [(sp - 88, 8, s1), (sp - 72, 8, ra), (sp - 56, 8, r 1), (sp - 48, 8, r 2), (sp - 40, 8, r 3),
     (sp - 32, 8, r 4), (sp - 24, 8, r 5), (sp - 16, 8, r 6), (sp - 8, 8, r 7),
     (sp - 112, 8, BitVec.ofNat 64 (sp - 56))] := rfl

section
variable (m : Mem) (ra s0 s1 s2 : BitVec 64) (sp : Nat) (r : Nat → BitVec 64) (hs : 112 ≤ sp)
include hs

theorem slot_all : ∀ j, 1 ≤ j → j ≤ 7 → bytesT8 (writeLog m (allLog ra s0 s1 s2 sp r)) (sp - 64 + 8 * j) = r j := by
  intro j h1 h7
  rw [all_log]
  rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show sp - 64 + 8 * 1 = sp - 56 by omega]; exact bytesT8_log _ _ 2 _ _ rfl (by simp [OutLRange]; omega)
  · rw [show sp - 64 + 8 * 2 = sp - 48 by omega]; exact bytesT8_log _ _ 3 _ _ rfl (by simp [OutLRange]; omega)
  · rw [show sp - 64 + 8 * 3 = sp - 40 by omega]; exact bytesT8_log _ _ 4 _ _ rfl (by simp [OutLRange]; omega)
  · rw [show sp - 64 + 8 * 4 = sp - 32 by omega]; exact bytesT8_log _ _ 5 _ _ rfl (by simp [OutLRange]; omega)
  · rw [show sp - 64 + 8 * 5 = sp - 24 by omega]; exact bytesT8_log _ _ 6 _ _ rfl (by simp [OutLRange]; omega)
  · rw [show sp - 64 + 8 * 6 = sp - 16 by omega]; exact bytesT8_log _ _ 7 _ _ rfl (by simp [OutLRange]; omega)
  · rw [show sp - 64 + 8 * 7 = sp - 8 by omega]; exact bytesT8_log _ _ 8 _ _ rfl (by simp [OutLRange]; omega)

theorem all_va : bytesT8 (writeLog m (allLog ra s0 s1 s2 sp r)) (sp - 112) = BitVec.ofNat 64 (sp - 56 + 8 * 0) := by
  rw [all_log]; exact bytesT8_log _ _ 9 _ _ rfl (by simp [OutLRange]; omega)

theorem all_ra : bytesT8 (writeLog m (allLog ra s0 s1 s2 sp r)) (sp - 112 + 40) = ra := by
  rw [all_log, show sp - 112 + 40 = sp - 72 by omega]; exact bytesT8_log _ _ 1 _ _ rfl (by simp [OutLRange]; omega)

theorem all_s1 : bytesT8 (writeLog m (allLog ra s0 s1 s2 sp r)) (sp - 112 + 24) = s1 := by
  rw [all_log, show sp - 112 + 24 = sp - 88 by omega]; exact bytesT8_log _ _ 0 _ _ rfl (by simp [OutLRange]; omega)

theorem all_s0 : bytesT8 (writeLog m (allLog ra s0 s1 s2 sp r)) (sp - 112 + 32) = s0 := by
  rw [all_log, show sp - 112 + 32 = sp - 80 by omega]; exact bytesT8_log _ _ 10 _ _ rfl (by simp [OutLRange]; omega)

theorem all_s2 : bytesT8 (writeLog m (allLog ra s0 s1 s2 sp r)) (sp - 112 + 16) = s2 := by
  rw [all_log, show sp - 112 + 16 = sp - 96 by omega]; exact bytesT8_log _ _ 11 _ _ rfl (by simp [OutLRange])

theorem all_out (x : Nat) (hx : x < sp - 112 ∨ sp ≤ x) : (writeLog m (allLog ra s0 s1 s2 sp r))[x]? = m[x]? := by
  rw [all_log]
  exact writeLog_out _ _ _ ⟨by simp only; omega, by simp only; omega, by simp only; omega, by simp only; omega,
    by simp only; omega, by simp only; omega, by simp only; omega, by simp only; omega, by simp only; omega,
    by simp only; omega, by simp only; omega, by simp only; omega, trivial⟩

theorem pro_ra : bytesT8 (writeLog m (proLog ra s1 sp r)) (sp - 112 + 40) = ra := by
  rw [pro_log, show sp - 112 + 40 = sp - 72 by omega]; exact bytesT8_log _ _ 1 _ _ rfl (by simp [OutLRange]; omega)

theorem pro_s1 : bytesT8 (writeLog m (proLog ra s1 sp r)) (sp - 112 + 24) = s1 := by
  rw [pro_log, show sp - 112 + 24 = sp - 88 by omega]; exact bytesT8_log _ _ 0 _ _ rfl (by simp [OutLRange]; omega)

theorem pro_out (x : Nat) (hx : x < sp - 112 ∨ sp ≤ x) : (writeLog m (proLog ra s1 sp r))[x]? = m[x]? := by
  rw [pro_log]
  exact writeLog_out _ _ _ ⟨by simp only; omega, by simp only; omega, by simp only; omega, by simp only; omega,
    by simp only; omega, by simp only; omega, by simp only; omega, by simp only; omega, by simp only; omega,
    by simp only; omega, trivial⟩

end

end Tom.Machine.Fn.MpInitMulti
