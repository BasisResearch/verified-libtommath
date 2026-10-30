import Tom.Machine.Seg.MpSub
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Jal
import Tom.Machine.Kit.Alu1
import Vsa.Sim.TripleCat

/-!
# `mp_sub` on the machine: the segments

`mp_sub(a, b, c)` at `0x80001ef4` (35 instructions). Different signs: store
`c->sign := a->sign` and tail-jump to `s_mp_add` (`msubS`). Same signs: save
the frame, call `mp_cmp_mag(a, b)` at `1f28` (`msubD`), then on `MP_LT`
store `c->sign := (b->sign == 0)` and tail-jump to `s_mp_sub(b, a, c)`
(`msubL`), otherwise store `c->sign := b->sign` and tail-jump to
`s_mp_sub(a, b, c)` (`msubG`). As in `mp_add`, `s1` is a local, so the
segments keep `Abi.keepR1` and carry `s1`.
-/


namespace Tom.Machine.Fn.MpSub

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "msub_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpSubBase = 0x80001ef4 := rfl
   have : mpSubCode.length = 35 := rfl))

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
  code_off : pc + 12 ≤ mpSubBase ∨ mpSubBase + 140 ≤ pc + 8

/-- Different signs: `c->sign := a->sign`, tail-jump to `s_mp_add(a, b, c)`. -/
theorem s_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc sa sb : Nat) (m : Mem)
    (hc : CodeAt m mpSubBase mpSubCode) (hf : SFacts m pa pb sa sb) (hs : CSign pc) (hne : sa ≠ sb) :
    Triple (At 0x80001ef4#64 (entry1 ra s0 s1 sp pa pb pc) m v.keepR1 outp)
      (At 0x8000219c#64 (entry1 ra s0 s1 sp pa pb pc) (writeLog m [(pc + 8, 4, BitVec.ofNat 64 sa)])
        v.keepR1 outp) := by
  msub_ctx
  have ⟨hsa, hsb⟩ := hf.sx
  seg_step msubS 0x8000219c#64 [rd4 m (pa + 8), rd4 m (pb + 8)] [1, 2, 8, 9, 10, 11, 12] abiKeysR1
    [entry1] [entry1] [hsa, hsb] hc

/-- Registers at `1f18`, half-way through the frame stores. -/
def midL (ra s0 s1 : BitVec 64) (sp pa pb pc sa sb : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 48)), (8, s0), (9, s1), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 pb), (12, BitVec.ofNat 64 pc), (16, BitVec.ofNat 64 sa), (17, BitVec.ofNat 64 sb)]

/-- Registers at the `mp_cmp_mag` call (`1f28`): `s0 = a`, `s1 = b`. -/
def callL (ra : BitVec 64) (sp pa pb : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb),
   (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)]

/-- The first frame stores (`s0`, `s1`, `b`'s sign). -/
def frameLog1 (s0 s1 : BitVec 64) (sp sb : Nat) : List WEntry :=
  [(sp - 16, 8, s0), (sp - 24, 8, s1), (sp - 40, 8, BitVec.ofNat 64 sb)]

/-- The last frame stores (`c`, `ra`). -/
def frameLog2 (ra : BitVec 64) (sp pc : Nat) : List WEntry :=
  [(sp - 48, 8, BitVec.ofNat 64 pc), (sp - 8, 8, ra)]

/-- The stack frame. -/
structure FFacts (sp : Nat) : Prop where
  rs : Ram (sp - 48) 48
  sp_al : sp % 16 = 0
  sp_ge : 48 ≤ sp
  code_off : sp ≤ mpSubBase ∨ mpSubBase + 140 ≤ sp - 48

/-- Same signs: the first half of the frame. -/
theorem d1_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc sa sb : Nat) (m : Mem)
    (hc : CodeAt m mpSubBase mpSubCode) (hf : SFacts m pa pb sa sb) (hs : FFacts sp) (he : sa = sb) :
    Triple (At 0x80001ef4#64 (entry1 ra s0 s1 sp pa pb pc) m v.keepR1 outp)
      (At 0x80001f18#64 (midL ra s0 s1 sp pa pb pc sa sb) (writeLog m (frameLog1 s0 s1 sp sb))
        v.keepR1 outp) := by
  msub_ctx
  have ⟨hsa, hsb⟩ := hf.sx
  seg_step msubD1 0x80001f18#64 [rd4 m (pa + 8), rd4 m (pb + 8)] [1, 2, 8, 9, 10, 11, 12] abiKeysR1
    [entry1, frameLog1] [midL] [hsa, hsb] hc

/-- The rest of the frame; set up `mp_cmp_mag(a, b)`. -/
theorem d2_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc sa sb : Nat) (M : Mem)
    (hc : CodeAt M mpSubBase mpSubCode) (hs : FFacts sp) :
    Triple (At 0x80001f18#64 (midL ra s0 s1 sp pa pb pc sa sb) M v.keepR1 outp)
      (At 0x80001f28#64 (callL ra sp pa pb) (writeLog M (frameLog2 ra sp pc)) v.keepR1 outp) := by
  msub_ctx
  seg_step msubD2 0x80001f28#64 ([] : List (List (BitVec 8))) [1, 2, 8, 9, 10, 11, 12, 16, 17] abiKeysR1
    [midL, frameLog2] [callL] [] hc

/-- After `mp_cmp_mag` returns `r` (`1f2c`). -/
def retL (sp pa pb : Nat) (r : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb), (10, r)]

/-- At `1f3c`/`1f5c`: the saved `c` and `b`'s sign reloaded. -/
def tailL (sp pa pb pc sb : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb),
   (12, BitVec.ofNat 64 pc), (17, BitVec.ofNat 64 sb)]

/-- The saved frame. -/
structure RFacts (M : Mem) (ra s0 s1 : BitVec 64) (sp pc sb : Nat) : Prop where
  rs : Ram (sp - 48) 48
  sp_al : sp % 16 = 0
  sp_ge : 48 ≤ sp
  s0_v : bytesT8 M (sp - 16) = s0
  s1_v : bytesT8 M (sp - 24) = s1
  sb_v : bytesT8 M (sp - 40) = BitVec.ofNat 64 sb
  pc_v : bytesT8 M (sp - 48) = BitVec.ofNat 64 pc
  ra_v : bytesT8 M (sp - 8) = ra

/-- `r ≠ MP_LT`: reload `c` and the sign. -/
theorem b_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc sb : Nat) (r : BitVec 64)
    (M : Mem) (hc : CodeAt M mpSubBase mpSubCode) (hf : RFacts M ra s0 s1 sp pc sb)
    (hr : (r == 0xffffffffffffffff#64) = false) :
    Triple (At 0x80001f2c#64 (retL sp pa pb r) M v.keepR1 outp)
      (At 0x80001f3c#64 (tailL sp pa pb pc sb) (writeLog M []) v.keepR1 outp) := by
  msub_ctx
  have h1 := hf.pc_v
  have h3 : bytesT8 M (sp - 48 + 8) = BitVec.ofNat 64 sb := by rw [show sp - 48 + 8 = sp - 40 by omega]; exact hf.sb_v
  refine Tom.Machine.seg_at' msubB (pc1 := 0x80001f3c#64) [rd8 M (sp - 48), rd8 M (sp - 48 + 8)]
    [2, 8, 9, 10] abiKeysR1 ?_ ?_ ?_ ?_
  · tom_facts hc
    all_goals leaf_auto [retL] [h1, h3, hr]
  · seg_nfo [msubB, retL]
    try (try val_nf [h1, h3, hr]
         exact Tom.Machine.ret_target' _ (by assumption))
  · sub_auto [msubB, retL, tailL] [h1, h3, hr]
  · seg_nfo [msubB, retL]
    try val_nf [h1, h3, hr]
    try regs_close

/-- `r = MP_LT`: reload `c` and the sign. -/
theorem bl_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc sb : Nat)
    (M : Mem) (hc : CodeAt M mpSubBase mpSubCode) (hf : RFacts M ra s0 s1 sp pc sb) :
    Triple (At 0x80001f2c#64 (retL sp pa pb 0xffffffffffffffff#64) M v.keepR1 outp)
      (At 0x80001f5c#64 (tailL sp pa pb pc sb) (writeLog M []) v.keepR1 outp) := by
  msub_ctx
  have h1 := hf.pc_v
  have h3 : bytesT8 M (sp - 48 + 8) = BitVec.ofNat 64 sb := by rw [show sp - 48 + 8 = sp - 40 by omega]; exact hf.sb_v
  seg_step msubBL 0x80001f5c#64 [rd8 M (sp - 48), rd8 M (sp - 48 + 8)]
    [2, 8, 9, 10] abiKeysR1 [retL] [tailL] [h1, h3] hc

/-- `|a| ≥ |b|`: `c->sign := b->sign`, restore the frame, tail-jump to `s_mp_sub(a, b, c)`. -/
theorem g_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc sb : Nat)
    (M : Mem) (hc : CodeAt M mpSubBase mpSubCode) (hf : RFacts M ra s0 s1 sp pc sb) (hs : CSign pc) :
    Triple (At 0x80001f3c#64 (tailL sp pa pb pc sb) M v.keepR1 outp)
      (At 0x80004564#64 (entry1 ra s0 s1 sp pa pb pc) (writeLog M [(pc + 8, 4, BitVec.ofNat 64 sb)])
        v.keepR1 outp) := by
  msub_ctx
  have h4 : bytesT8 M (sp - 48 + 32) = s0 := by rw [show sp - 48 + 32 = sp - 16 by omega]; exact hf.s0_v
  have h5 : bytesT8 M (sp - 48 + 40) = ra := by rw [show sp - 48 + 40 = sp - 8 by omega]; exact hf.ra_v
  have h6 : bytesT8 M (sp - 48 + 24) = s1 := by rw [show sp - 48 + 24 = sp - 24 by omega]; exact hf.s1_v
  seg_step msubG 0x80004564#64 [rd8 M (sp - 48 + 32), rd8 M (sp - 48 + 40), rd8 M (sp - 48 + 24)]
    [2, 8, 9, 12, 17] abiKeysR1 [tailL] [entry1] [h4, h5, h6] hc

/-- At the `seqz` (`1f68`): `a1 = a`, `s0`/`ra` restored. -/
def l1L (ra s0 : BitVec 64) (sp pa pb pc sb : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 48)), (8, s0), (9, BitVec.ofNat 64 pb), (11, BitVec.ofNat 64 pa),
   (12, BitVec.ofNat 64 pc), (17, BitVec.ofNat 64 sb)]

/-- After the `seqz` (`1f6c`): `a7` is the new sign `t`. -/
def l2L (ra s0 : BitVec 64) (sp pa pb pc t : Nat) : GRegs :=
  [(17, BitVec.ofNat 64 t), (1, ra), (2, BitVec.ofNat 64 (sp - 48)), (8, s0), (9, BitVec.ofNat 64 pb),
   (11, BitVec.ofNat 64 pa), (12, BitVec.ofNat 64 pc)]

/-- `|a| < |b|`, first half: `a1 := a`, restore `s0` and `ra`. -/
theorem l1_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc sb : Nat)
    (M : Mem) (hc : CodeAt M mpSubBase mpSubCode) (hf : RFacts M ra s0 s1 sp pc sb) :
    Triple (At 0x80001f5c#64 (tailL sp pa pb pc sb) M v.keepR1 outp)
      (At 0x80001f68#64 (l1L ra s0 sp pa pb pc sb) (writeLog M []) v.keepR1 outp) := by
  msub_ctx
  have h4 : bytesT8 M (sp - 48 + 32) = s0 := by rw [show sp - 48 + 32 = sp - 16 by omega]; exact hf.s0_v
  have h5 : bytesT8 M (sp - 48 + 40) = ra := by rw [show sp - 48 + 40 = sp - 8 by omega]; exact hf.ra_v
  seg_step msubL1 0x80001f68#64 [rd8 M (sp - 48 + 32), rd8 M (sp - 48 + 40)]
    [2, 8, 9, 12, 17] abiKeysR1 [tailL] [l1L] [h4, h5] hc

/-- The `seqz a7, a7` at `1f68` (`Kit/Alu1.lean`): the new sign `(b->sign == 0)`. -/
theorem z_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc sb : Nat)
    (M : Mem) (hc : CodeAt M mpSubBase mpSubCode) (hsb : sb < 2) :
    Triple (At 0x80001f68#64 (l1L ra s0 sp pa pb pc sb) M v.keepR1 outp)
      (At 0x80001f6c#64 (l2L ra s0 sp pa pb pc (if sb = 0 then 1 else 0)) M v.keepR1 outp) := by
  have h := seqz_at (pc := 0x80001f68#64) (w := 0x0018b893#32) (rd := 17) (rs1 := 17)
    (L := l1L ra s0 sp pa pb pc sb) (keep := v.keepR1) (outp := outp)
    (hc.word (a := (0x80001f68#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
    (fun s h1 h2 h3 => decodeW s h1 h2 h3)
    ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩
    (by decide) (Or.inr (by simp [keysG, l1L])) (by decide) (by simp [keysG, l1L])
    (by simp [Abi.keepR1, keysG]) (by simp [Abi.keepR1, keysG])
  have hpc : Sail.BitVec.addInt (0x80001f68#64 : BitVec 64) 4 = 0x80001f6c#64 := by decide
  rw [hpc, show srcVal 17 (l1L ra s0 sp pa pb pc sb) = BitVec.ofNat 64 sb from by simp [srcVal, lookupG, l1L],
    ite_ofNat_eq_zero (by omega)] at h
  exact Triple.rmap (fun cf h' => h'.reshape (by simp [l1L, l2L, eraseG]) (fun p hp => by simp [hp])) h

/-- `|a| < |b|`, second half: `c->sign := t`, restore `s1` and the stack, tail-jump to
`s_mp_sub(b, a, c)`. -/
theorem l2_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc sb t : Nat)
    (M : Mem) (hc : CodeAt M mpSubBase mpSubCode) (hf : RFacts M ra s0 s1 sp pc sb) (hs : CSign pc) :
    Triple (At 0x80001f6c#64 (l2L ra s0 sp pa pb pc t) M v.keepR1 outp)
      (At 0x80004564#64 (entry1 ra s0 s1 sp pb pa pc) (writeLog M [(pc + 8, 4, BitVec.ofNat 64 t)])
        v.keepR1 outp) := by
  msub_ctx
  have h6 : bytesT8 M (sp - 48 + 24) = s1 := by rw [show sp - 48 + 24 = sp - 24 by omega]; exact hf.s1_v
  seg_step msubL2 0x80004564#64 [rd8 M (sp - 48 + 24)]
    [17, 1, 2, 8, 9, 11, 12] abiKeysR1 [l2L] [entry1] [h6] hc

end Tom.Machine.Fn.MpSub
