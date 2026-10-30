import Tom.Machine.Seg.MpAdd
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Jal

/-!
# `mp_add` on the machine: the segments

`mp_add(a, b, c)` at `0x80000608` (36 instructions). Same signs: store
`c->sign := a->sign` and tail-jump to `s_mp_add` (`maddS`). Different signs:
save the frame, call `mp_cmp_mag(a, b)` at `0638` (`maddD`), then on
`MP_LT` store `c->sign := b->sign` and tail-jump to `s_mp_sub(b, a, c)`
(`maddL`), otherwise store `c->sign := a->sign` and tail-jump to
`s_mp_sub(a, b, c)` (`maddG`). `s1` is a local here, so the segments keep
`Abi.keepR1` and carry `s1` in their register lists.
-/


namespace Tom.Machine.Fn.MpAdd

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "madd_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpAddBase = 0x80000608 := rfl
   have : mpAddCode.length = 36 := rfl))

/-- Registers at the entry and at the tail jumps (`s1` carried). -/
def entry1 (ra s0 s1 : BitVec 64) (sp pa pb pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb),
   (12, BitVec.ofNat 64 pc)]

/-- The sign loads. -/
structure SFacts (m : Mem) (pa pb sa sb : Nat) : Prop where
  ra_ : Ram pa 24
  rb : Ram pb 24
  sa_v : bytesT4 m (pa + 8) = BitVec.ofNat 32 sa
  sb_v : bytesT4 m (pb + 8) = BitVec.ofNat 32 sb
  sa_lt : sa < 2 ^ 31
  sb_lt : sb < 2 ^ 31

theorem SFacts.sx {m : Mem} {pa pb sa sb : Nat} (h : SFacts m pa pb sa sb) :
    BitVec.signExtend 64 (bytesT4 m (pa + 8)) = BitVec.ofNat 64 sa ∧
      BitVec.signExtend 64 (bytesT4 m (pb + 8)) = BitVec.ofNat 64 sb :=
  ⟨by rw [h.sa_v, signExtend_ofNat32 _ h.sa_lt], by rw [h.sb_v, signExtend_ofNat32 _ h.sb_lt]⟩

/-- `c`'s sign slot. -/
structure CSign (pc : Nat) : Prop where
  rc : Ram pc 24
  pc_al : pc % 8 = 0
  code_off : pc + 12 ≤ mpAddBase ∨ mpAddBase + 144 ≤ pc + 8

/-- Same signs: `c->sign := a->sign`, tail-jump to `s_mp_add(a, b, c)`. -/
theorem s_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc sa sb : Nat) (m : Mem)
    (hc : CodeAt m mpAddBase mpAddCode) (hf : SFacts m pa pb sa sb) (hs : CSign pc) (he : sa = sb) :
    Triple (At 0x80000608#64 (entry1 ra s0 s1 sp pa pb pc) m v.keepR1 outp)
      (At 0x8000219c#64 (entry1 ra s0 s1 sp pa pb pc) (writeLog m [(pc + 8, 4, BitVec.ofNat 64 sa)])
        v.keepR1 outp) := by
  madd_ctx
  have ⟨hsa, hsb⟩ := hf.sx
  seg_step maddS 0x8000219c#64 [rd4 m (pa + 8), rd4 m (pb + 8)] [1, 2, 8, 9, 10, 11, 12] abiKeysR1
    [entry1] [entry1] [hsa, hsb] hc

/-- Registers at `0628`, half-way through the frame stores. -/
def midL (ra s0 s1 : BitVec 64) (sp pa pb pc sa sb : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, s0), (9, s1), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 pb), (12, BitVec.ofNat 64 pc), (16, BitVec.ofNat 64 sa), (17, BitVec.ofNat 64 sb)]

/-- Registers at the `mp_cmp_mag` call (`0638`): `s0 = a`, `s1 = b`. -/
def callL (ra : BitVec 64) (sp pa pb : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb),
   (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)]

/-- The first frame stores (`s0`, `s1`, the two signs). -/
def frameLog1 (s0 s1 : BitVec 64) (sp sa sb : Nat) : List WEntry :=
  [(sp - 16, 8, s0), (sp - 24, 8, s1), (sp - 40, 8, BitVec.ofNat 64 sb), (sp - 48, 8, BitVec.ofNat 64 sa)]

/-- The last frame stores (`c`, `ra`). -/
def frameLog2 (ra : BitVec 64) (sp pc : Nat) : List WEntry :=
  [(sp - 56, 8, BitVec.ofNat 64 pc), (sp - 8, 8, ra)]

/-- The stack frame. -/
structure FFacts (sp : Nat) : Prop where
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  code_off : sp ≤ mpAddBase ∨ mpAddBase + 144 ≤ sp - 64

/-- Different signs: the first half of the frame. -/
theorem d1_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc sa sb : Nat) (m : Mem)
    (hc : CodeAt m mpAddBase mpAddCode) (hf : SFacts m pa pb sa sb) (hs : FFacts sp) (hne : sa ≠ sb) :
    Triple (At 0x80000608#64 (entry1 ra s0 s1 sp pa pb pc) m v.keepR1 outp)
      (At 0x80000628#64 (midL ra s0 s1 sp pa pb pc sa sb) (writeLog m (frameLog1 s0 s1 sp sa sb))
        v.keepR1 outp) := by
  madd_ctx
  have ⟨hsa, hsb⟩ := hf.sx
  seg_step maddD1 0x80000628#64 [rd4 m (pa + 8), rd4 m (pb + 8)] [1, 2, 8, 9, 10, 11, 12] abiKeysR1
    [entry1, frameLog1] [midL] [hsa, hsb] hc

/-- The rest of the frame; set up `mp_cmp_mag(a, b)`. -/
theorem d2_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc sa sb : Nat) (M : Mem)
    (hc : CodeAt M mpAddBase mpAddCode) (hs : FFacts sp) :
    Triple (At 0x80000628#64 (midL ra s0 s1 sp pa pb pc sa sb) M v.keepR1 outp)
      (At 0x80000638#64 (callL ra sp pa pb) (writeLog M (frameLog2 ra sp pc)) v.keepR1 outp) := by
  madd_ctx
  seg_step maddD2 0x80000638#64 ([] : List (List (BitVec 8))) [1, 2, 8, 9, 10, 11, 12, 16, 17] abiKeysR1
    [midL, frameLog2] [callL] [] hc

/-- After `mp_cmp_mag` returns `r` (`063c`). -/
def retL (sp pa pb : Nat) (r : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb), (10, r)]

/-- At `0650`/`0670`: the saved `c` and signs reloaded. -/
def tailL (sp pa pb pc sa sb : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb),
   (12, BitVec.ofNat 64 pc), (16, BitVec.ofNat 64 sa), (17, BitVec.ofNat 64 sb)]

/-- The saved frame. -/
structure RFacts (M : Mem) (ra s0 s1 : BitVec 64) (sp pc sa sb : Nat) : Prop where
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  s0_v : bytesT8 M (sp - 16) = s0
  s1_v : bytesT8 M (sp - 24) = s1
  sb_v : bytesT8 M (sp - 40) = BitVec.ofNat 64 sb
  sa_v : bytesT8 M (sp - 48) = BitVec.ofNat 64 sa
  pc_v : bytesT8 M (sp - 56) = BitVec.ofNat 64 pc
  ra_v : bytesT8 M (sp - 8) = ra

/-- `r ≠ MP_LT`: reload `c` and the signs. -/
theorem b_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc sa sb : Nat) (r : BitVec 64)
    (M : Mem) (hc : CodeAt M mpAddBase mpAddCode) (hf : RFacts M ra s0 s1 sp pc sa sb)
    (hr : (r == 0xffffffffffffffff#64) = false) :
    Triple (At 0x8000063c#64 (retL sp pa pb r) M v.keepR1 outp)
      (At 0x80000650#64 (tailL sp pa pb pc sa sb) (writeLog M []) v.keepR1 outp) := by
  madd_ctx
  have h1 : bytesT8 M (sp - 64 + 8) = BitVec.ofNat 64 pc := by rw [show sp - 64 + 8 = sp - 56 by omega]; exact hf.pc_v
  have h2 : bytesT8 M (sp - 64 + 16) = BitVec.ofNat 64 sa := by rw [show sp - 64 + 16 = sp - 48 by omega]; exact hf.sa_v
  have h3 : bytesT8 M (sp - 64 + 24) = BitVec.ofNat 64 sb := by rw [show sp - 64 + 24 = sp - 40 by omega]; exact hf.sb_v
  refine Tom.Machine.seg_at' maddB (pc1 := 0x80000650#64) [rd8 M (sp - 64 + 8), rd8 M (sp - 64 + 16),
    rd8 M (sp - 64 + 24)] [2, 8, 9, 10] abiKeysR1 ?_ ?_ ?_ ?_
  · tom_facts hc
    all_goals leaf_auto [retL] [h1, h2, h3, hr]
  · seg_nfo [maddB, retL]
    try (try val_nf [h1, h2, h3, hr]
         exact Tom.Machine.ret_target' _ (by assumption))
  · sub_auto [maddB, retL, tailL] [h1, h2, h3, hr]
  · seg_nfo [maddB, retL]
    try val_nf [h1, h2, h3, hr]
    try regs_close

/-- `r = MP_LT`: reload `c` and the signs. -/
theorem bl_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc sa sb : Nat)
    (M : Mem) (hc : CodeAt M mpAddBase mpAddCode) (hf : RFacts M ra s0 s1 sp pc sa sb) :
    Triple (At 0x8000063c#64 (retL sp pa pb 0xffffffffffffffff#64) M v.keepR1 outp)
      (At 0x80000670#64 (tailL sp pa pb pc sa sb) (writeLog M []) v.keepR1 outp) := by
  madd_ctx
  have h1 : bytesT8 M (sp - 64 + 8) = BitVec.ofNat 64 pc := by rw [show sp - 64 + 8 = sp - 56 by omega]; exact hf.pc_v
  have h2 : bytesT8 M (sp - 64 + 16) = BitVec.ofNat 64 sa := by rw [show sp - 64 + 16 = sp - 48 by omega]; exact hf.sa_v
  have h3 : bytesT8 M (sp - 64 + 24) = BitVec.ofNat 64 sb := by rw [show sp - 64 + 24 = sp - 40 by omega]; exact hf.sb_v
  seg_step maddBL 0x80000670#64 [rd8 M (sp - 64 + 8), rd8 M (sp - 64 + 16), rd8 M (sp - 64 + 24)]
    [2, 8, 9, 10] abiKeysR1 [retL] [tailL] [h1, h2, h3] hc

/-- `|a| ≥ |b|`: `c->sign := a->sign`, restore the frame, tail-jump to `s_mp_sub(a, b, c)`. -/
theorem g_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc sa sb : Nat)
    (M : Mem) (hc : CodeAt M mpAddBase mpAddCode) (hf : RFacts M ra s0 s1 sp pc sa sb) (hs : CSign pc) :
    Triple (At 0x80000650#64 (tailL sp pa pb pc sa sb) M v.keepR1 outp)
      (At 0x80004564#64 (entry1 ra s0 s1 sp pa pb pc) (writeLog M [(pc + 8, 4, BitVec.ofNat 64 sa)])
        v.keepR1 outp) := by
  madd_ctx
  have h4 : bytesT8 M (sp - 64 + 48) = s0 := by rw [show sp - 64 + 48 = sp - 16 by omega]; exact hf.s0_v
  have h5 : bytesT8 M (sp - 64 + 56) = ra := by rw [show sp - 64 + 56 = sp - 8 by omega]; exact hf.ra_v
  have h6 : bytesT8 M (sp - 64 + 40) = s1 := by rw [show sp - 64 + 40 = sp - 24 by omega]; exact hf.s1_v
  seg_step maddG 0x80004564#64 [rd8 M (sp - 64 + 48), rd8 M (sp - 64 + 56), rd8 M (sp - 64 + 40)]
    [2, 8, 9, 12, 16, 17] abiKeysR1 [tailL] [entry1] [h4, h5, h6] hc

/-- `|a| < |b|`: `c->sign := b->sign`, restore the frame, tail-jump to `s_mp_sub(b, a, c)`. -/
theorem l_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc sa sb : Nat)
    (M : Mem) (hc : CodeAt M mpAddBase mpAddCode) (hf : RFacts M ra s0 s1 sp pc sa sb) (hs : CSign pc) :
    Triple (At 0x80000670#64 (tailL sp pa pb pc sa sb) M v.keepR1 outp)
      (At 0x80004564#64 (entry1 ra s0 s1 sp pb pa pc) (writeLog M [(pc + 8, 4, BitVec.ofNat 64 sb)])
        v.keepR1 outp) := by
  madd_ctx
  have h4 : bytesT8 M (sp - 64 + 48) = s0 := by rw [show sp - 64 + 48 = sp - 16 by omega]; exact hf.s0_v
  have h5 : bytesT8 M (sp - 64 + 56) = ra := by rw [show sp - 64 + 56 = sp - 8 by omega]; exact hf.ra_v
  have h6 : bytesT8 M (sp - 64 + 40) = s1 := by rw [show sp - 64 + 40 = sp - 24 by omega]; exact hf.s1_v
  seg_step maddL 0x80004564#64 [rd8 M (sp - 64 + 48), rd8 M (sp - 64 + 56), rd8 M (sp - 64 + 40)]
    [2, 8, 9, 12, 16, 17] abiKeysR1 [tailL] [entry1] [h4, h5, h6] hc

end Tom.Machine.Fn.MpAdd
