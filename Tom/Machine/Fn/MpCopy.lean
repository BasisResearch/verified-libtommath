import Tom.Machine.Seg.MpCopy
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Fn.Memset
import Vsa.Sim.TripleCat

/-!
# `mp_copy` on the machine: the segments

`mp_copy(a, b)` at `0x800007e0` (46 instructions). `a == b`: return
`MP_OKAY` (`mcopyA`). Otherwise the frame (`s0 = a`, `s1 = b`, `ra`) and the
`b->alloc < a->used` test (`mcopyP`; the `mp_grow` branch is excluded by the
contract, D5); `a->used ≤ 0` skips the loop (`mcopyE0`), else `mcopyE1`
enters it. The loop head `0818` copies digit `i` and reloads `a->used`
(`mcopyL`, `mcopyLe`). At `0834`: `n := b->used - a->used`; `n ≤ 0` goes to
`0850` (`mcopyM0`), otherwise `memset(b->dp + a->used, 0, 4 n)` at `0848`
(`mcopyM1`, the call, `mcopyU`). `mcopyR` stores `used` and `sign`,
restores the frame and returns `MP_OKAY`.
-/


namespace Tom.Machine.Fn.MpCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mcopy_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpCopyBase = 0x800007e0 := rfl
   have : mpCopyCode.length = 46 := rfl))

def entry : BitVec 64 := 0x800007e0#64

/-- The entry: `a0 = a`, `a1 = b`, the frame registers. -/
def entryL (ra s0 : BitVec 64) (sp pa pb : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)]

/-- The entry (`s1` carried: the function saves it). -/
def entry1 (ra s0 s1 : BitVec 64) (sp pa pb : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)]

/-- `a == b`: return `MP_OKAY`. -/
theorem a_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp p : Nat) (m : Mem)
    (hc : CodeAt m mpCopyBase mpCopyCode) (hra : ra.toNat % 4 = 0) :
    Triple (At entry (entry1 ra s0 s1 sp p p) m v.keepR1 outp)
      (At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, 0#64)] (writeLog m []) v.keepR1 outp) := by
  mcopy_ctx
  seg_step mcopyA ra ([] : List (List (BitVec 8))) [1, 2, 8, 9, 10, 11] abiKeysR1 [entry, entry1] [] [] hc

/-- The frame stores. -/
def frameLog (ra s0 s1 : BitVec 64) (sp : Nat) : List WEntry :=
  [(sp - 24, 8, s1), (sp - 16, 8, s0), (sp - 8, 8, ra)]

/-- At `0808`: `a1 = a->used`, `a5 = b->alloc`. -/
def pL (ra : BitVec 64) (sp pa pb ua bal : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb),
   (11, BitVec.ofNat 64 ua), (15, BitVec.ofNat 64 bal)]

/-- The prologue's facts. -/
structure PFacts (m : Mem) (sp pa pb ua bal : Nat) : Prop where
  ra_ : Ram pa 24
  rb : Ram pb 24
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  ua_v : bytesT4 m pa = BitVec.ofNat 32 ua
  bal_v : bytesT4 m (pb + 4) = BitVec.ofNat 32 bal
  ua_lt : ua < 2 ^ 31
  bal_lt : bal < 2 ^ 31
  ne : pa ≠ pb
  s_a : sp ≤ pa ∨ pa + 24 ≤ sp - 32
  s_b : sp ≤ pb ∨ pb + 24 ≤ sp - 32
  code_off : sp ≤ mpCopyBase ∨ mpCopyBase + 184 ≤ sp - 32

/-- `a != b`, the frame, `b->alloc ≥ a->used` (no `mp_grow`). -/
theorem p_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb ua bal : Nat) (m : Mem)
    (hc : CodeAt m mpCopyBase mpCopyCode) (hf : PFacts m sp pa pb ua bal) (hle : ua ≤ bal) :
    Triple (At entry (entry1 ra s0 s1 sp pa pb) m v.keepR1 outp)
      (At 0x80000808#64 (pL ra sp pa pb ua bal) (writeLog m (frameLog ra s0 s1 sp)) v.keepR1 outp) := by
  mcopy_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 m pa) = BitVec.ofNat 64 ua := by
    rw [hf.ua_v, signExtend_ofNat32 _ hf.ua_lt]
  have h2 : BitVec.signExtend 64 (bytesT4 m (pb + 4)) = BitVec.ofNat 64 bal := by
    rw [hf.bal_v, signExtend_ofNat32 _ hf.bal_lt]
  seg_step mcopyP 0x80000808#64 [rd4 m (pb + 4), rd4 m pa] [1, 2, 8, 9, 10, 11] abiKeysR1
    [entry, entry1, frameLog] [pL] [h1, h2] hc

/-- At the loop head (`0818`), digit `i`. -/
def lL (ra : BitVec 64) (sp pa pb adp bdp ua i : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb),
   (10, BitVec.ofNat 64 (bdp + 4 * i)), (14, BitVec.ofNat 64 (adp + 4 * i)), (15, BitVec.ofNat 64 i),
   (11, BitVec.ofNat 64 ua)]

/-- After the loop (`0834`), `n` digits copied. -/
def jL (ra : BitVec 64) (sp pa pb bdp ua n : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb),
   (10, BitVec.ofNat 64 (bdp + 4 * n)), (15, BitVec.ofNat 64 n), (11, BitVec.ofNat 64 ua)]

/-- The digit pointers. -/
structure DFacts (M : Mem) (pa pb adp bdp : Nat) : Prop where
  ra_ : Ram pa 24
  rb : Ram pb 24
  adp_v : bytesT8 M (pa + 16) = BitVec.ofNat 64 adp
  bdp_v : bytesT8 M (pb + 16) = BitVec.ofNat 64 bdp

/-- `a->used = 0`: skip the loop. -/
theorem e0_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb adp bdp bal : Nat) (M : Mem)
    (hc : CodeAt M mpCopyBase mpCopyCode) (hf : DFacts M pa pb adp bdp) :
    Triple (At 0x80000808#64 (pL ra sp pa pb 0 bal) M v.keepR1 outp)
      (At 0x80000834#64 (jL ra sp pa pb bdp 0 0) (writeLog M []) v.keepR1 outp) := by
  mcopy_ctx
  seg_step mcopyE0 0x80000834#64 [rd8 M (pb + 16)] [1, 2, 8, 9, 11, 15] abiKeysR1 [pL] [jL] [hf.bdp_v] hc

/-- `a->used ≥ 1`: enter the loop. -/
theorem e1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb adp bdp ua bal : Nat) (M : Mem)
    (hc : CodeAt M mpCopyBase mpCopyCode) (hf : DFacts M pa pb adp bdp) (hu : 1 ≤ ua) (hu' : ua < 2 ^ 31) :
    Triple (At 0x80000808#64 (pL ra sp pa pb ua bal) M v.keepR1 outp)
      (At 0x80000818#64 (lL ra sp pa pb adp bdp ua 0) (writeLog M []) v.keepR1 outp) := by
  mcopy_ctx
  seg_step mcopyE1 0x80000818#64 [rd8 M (pb + 16), rd8 M (pa + 16)] [1, 2, 8, 9, 11, 15] abiKeysR1 [pL] [lL]
    [hf.bdp_v, hf.adp_v] hc

/-- One loop iteration's memory facts: digit `i` of `a` (`x`), the store into
digit `i` of `b`, `a->used`. -/
structure LFacts (M : Mem) (pa adp bdp ua i x : Nat) : Prop where
  ra_ : Ram pa 24
  ru : bytesT4 M pa = BitVec.ofNat 32 ua
  ua_lt : ua < 2 ^ 31
  rx : Ram (adp + 4 * i) 4
  xv : bytesT4 M (adp + 4 * i) = BitVec.ofNat 32 x
  x_lt : x < 2 ^ 31
  rd : Ram (bdp + 4 * i) 4
  bdp_al : bdp % 4 = 0
  b_a : bdp + 4 * i + 4 ≤ pa ∨ pa + 4 ≤ bdp + 4 * i
  code_off : bdp + 4 * i + 4 ≤ mpCopyBase ∨ mpCopyBase + 184 ≤ bdp + 4 * i

/-- The loop's back edge (`i + 1 < a->used`). -/
theorem l_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb adp bdp ua i x : Nat) (M : Mem)
    (hc : CodeAt M mpCopyBase mpCopyCode) (hf : LFacts M pa adp bdp ua i x) (hi : i + 1 < ua) :
    Triple (At 0x80000818#64 (lL ra sp pa pb adp bdp ua i) M v.keepR1 outp)
      (At 0x80000818#64 (lL ra sp pa pb adp bdp ua (i + 1))
        (writeLog M [(bdp + 4 * i, 4, BitVec.ofNat 64 x)]) v.keepR1 outp) := by
  mcopy_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 ua := by
    rw [hf.ru, signExtend_ofNat32 _ hf.ua_lt]
  have h2 : BitVec.signExtend 64 (bytesT4 M (adp + 4 * i)) = BitVec.ofNat 64 x := by
    rw [hf.xv, signExtend_ofNat32 _ hf.x_lt]
  seg_step mcopyL 0x80000818#64 [rd4 M (adp + 4 * i), rd4 M pa] [1, 2, 8, 9, 10, 14, 15, 11] abiKeysR1
    [lL] [] [h1, h2] hc

/-- The loop's last iteration (`i + 1 = a->used`). -/
theorem le_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb adp bdp ua i x : Nat) (M : Mem)
    (hc : CodeAt M mpCopyBase mpCopyCode) (hf : LFacts M pa adp bdp ua i x) (hi : i + 1 = ua) :
    Triple (At 0x80000818#64 (lL ra sp pa pb adp bdp ua i) M v.keepR1 outp)
      (At 0x80000834#64 (jL ra sp pa pb bdp ua ua)
        (writeLog M [(bdp + 4 * i, 4, BitVec.ofNat 64 x)]) v.keepR1 outp) := by
  mcopy_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 ua := by
    rw [hf.ru, signExtend_ofNat32 _ hf.ua_lt]
  have h2 : BitVec.signExtend 64 (bytesT4 M (adp + 4 * i)) = BitVec.ofNat 64 x := by
    rw [hf.xv, signExtend_ofNat32 _ hf.x_lt]
  seg_step mcopyLe 0x80000834#64 [rd4 M (adp + 4 * i), rd4 M pa] [1, 2, 8, 9, 10, 14, 15, 11] abiKeysR1
    [lL] [jL] [h1, h2] hc

/-- At `0850`: `a1 = a->used`. -/
def rL (sp pa pb ua : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb), (11, BitVec.ofNat 64 ua)]

/-- At the `memset` call (`0848`). -/
def msL (ra : BitVec 64) (sp pa pb bdp ua ub : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb),
   (10, BitVec.ofNat 64 (bdp + 4 * ua)), (11, 0#64), (12, BitVec.ofNat 64 (4 * (ub - ua)))]

/-- `b->used ≤ a->used`: no `memset`. -/
theorem m0_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb bdp ua ub : Nat) (M : Mem)
    (hc : CodeAt M mpCopyBase mpCopyCode) (hb : Ram pb 24) (hub : bytesT4 M pb = BitVec.ofNat 32 ub)
    (hub' : ub < 2 ^ 31) (hua : ua < 2 ^ 31) (hle : ub ≤ ua) :
    Triple (At 0x80000834#64 (jL ra sp pa pb bdp ua ua) M v.keepR1 outp)
      (At 0x80000850#64 (rL sp pa pb ua) (writeLog M []) v.keepR1 outp) := by
  mcopy_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pb) = BitVec.ofNat 64 ub := by
    rw [hub, signExtend_ofNat32 _ hub']
  seg_step mcopyM0 0x80000850#64 [rd4 M pb] [1, 2, 8, 9, 10, 15, 11] abiKeysR1 [jL] [rL] [h1] hc

/-- `b->used > a->used`: set up `memset(b->dp + a->used, 0, 4 (b->used - a->used))`. -/
theorem m1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb bdp ua ub : Nat) (M : Mem)
    (hc : CodeAt M mpCopyBase mpCopyCode) (hb : Ram pb 24) (hub : bytesT4 M pb = BitVec.ofNat 32 ub)
    (hub' : ub < 2 ^ 31) (hlt : ua < ub) :
    Triple (At 0x80000834#64 (jL ra sp pa pb bdp ua ua) M v.keepR1 outp)
      (At 0x80000848#64 (msL ra sp pa pb bdp ua ub) (writeLog M []) v.keepR1 outp) := by
  mcopy_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pb) = BitVec.ofNat 64 ub := by
    rw [hub, signExtend_ofNat32 _ hub']
  seg_step mcopyM1 0x80000848#64 [rd4 M pb] [1, 2, 8, 9, 10, 15, 11] abiKeysR1 [jL] [msL] [h1] hc

/-- After `memset`: reload `a->used`. -/
theorem u_step (v : Abi) (outp : Array String) (sp pa pb ua : Nat) (M : Mem)
    (hc : CodeAt M mpCopyBase mpCopyCode) (ha : Ram pa 24) (hua : bytesT4 M pa = BitVec.ofNat 32 ua)
    (hua' : ua < 2 ^ 31) :
    Triple (At 0x8000084c#64 [(2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb)]
        M v.keepR1 outp)
      (At 0x80000850#64 (rL sp pa pb ua) (writeLog M []) v.keepR1 outp) := by
  mcopy_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 ua := by
    rw [hua, signExtend_ofNat32 _ hua']
  seg_step mcopyU 0x80000850#64 [rd4 M pa] [2, 8, 9] abiKeysR1 [] [rL] [h1] hc

/-- The epilogue's facts: `a->sign`, the saved registers, `b`'s struct off the frame. -/
structure RFacts (M : Mem) (ra s0 s1 : BitVec 64) (sp pa pb sa : Nat) : Prop where
  ra_ : Ram pa 24
  rb : Ram pb 24
  pb_al : pb % 8 = 0
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  ra_al : ra.toNat % 4 = 0
  sa_v : bytesT4 M (pa + 8) = BitVec.ofNat 32 sa
  sa_lt : sa < 2 ^ 31
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  s1_v : bytesT8 M (sp - 24) = s1
  s_b : sp ≤ pb ∨ pb + 24 ≤ sp - 32
  code_off : pb + 24 ≤ mpCopyBase ∨ mpCopyBase + 184 ≤ pb

/-- `b->used := a->used`, `b->sign := a->sign`, restore, return `MP_OKAY`. -/
theorem r_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb ua sa : Nat) (M : Mem)
    (hc : CodeAt M mpCopyBase mpCopyCode) (hf : RFacts M ra s0 s1 sp pa pb sa) :
    Triple (At 0x80000850#64 (rL sp pa pb ua) M v.keepR1 outp)
      (At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, 0#64)]
        (writeLog M [(pb, 4, BitVec.ofNat 64 ua), (pb + 8, 4, BitVec.ofNat 64 sa)]) v.keepR1 outp) := by
  mcopy_ctx
  have hra := hf.ra_al
  have h0 : BitVec.signExtend 64 (bytesT4 M (pa + 8)) = BitVec.ofNat 64 sa := by
    rw [hf.sa_v, signExtend_ofNat32 _ hf.sa_lt]
  have h1 : bytesT8 M (sp - 32 + 24) = ra := by rw [show sp - 32 + 24 = sp - 8 by omega]; exact hf.ra_v
  have h2 : bytesT8 M (sp - 32 + 16) = s0 := by rw [show sp - 32 + 16 = sp - 16 by omega]; exact hf.s0_v
  have h3 : bytesT8 M (sp - 32 + 8) = s1 := by rw [show sp - 32 + 8 = sp - 24 by omega]; exact hf.s1_v
  seg_step mcopyR ra [rd4 M (pa + 8), rd8 M (sp - 32 + 24), rd8 M (sp - 32 + 16), rd8 M (sp - 32 + 8)]
    [2, 8, 9, 11] abiKeysR1 [rL] [] [h0, h1, h2, h3] hc

end Tom.Machine.Fn.MpCopy
