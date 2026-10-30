import Tom.Machine.Seg.SubD
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Arr
import Tom.Machine.Kit.Bits
import Tom.Machine.Kit.Jal
import Tom.Machine.Fn.Memset
import Tom.Machine.Fn.Clamp

/-!
# `mp_sub_d` on the machine: the segments

`mp_sub_d(a, b, c)` at `0x800064a4` (103 instructions). The prologue
(`subdP`) saves `s0`, `ra` and tests `a->used ≥ c->alloc` (the `mp_grow`
branch, excluded by the contract, D5). Then by `a`'s sign and size:

* `a->used = 0` (`subd0a`/`subd0b`) or `a->used = 1`, `a[0] ≤ b`
  (`subd1sa`/`subd1sb`): `c[0] := b - a[0]`, `c->sign := MP_NEG`,
  `c->used := 1`, and the `oldused - 1` test of the zeroing (`…a`: none,
  `…b`: the `memset` call at `6510`);
* `a->used = 1`, `a[0] > b` (`subd1b`) or `a->used ≥ 2` (`subd2b`), at `653c`:
  `c->used := a->used`, `c->sign := MP_ZPOS` (`subdB`), the loop at `6558`
  (`subdL`; the exit `subdLa`/`subdLb` with the zeroing test);
* `MP_NEG` (`subdN`): copy `a` to the stack with `MP_ZPOS`, call `mp_add_d`,
  then `c->sign := MP_NEG` (`subdN2`) and `mp_clamp`, return its result (`subdNR`).

All branches end in `mp_clamp(c)` (`subdD`) and the epilogue (`subdR`).
`s0 = c` is a local (`Abi.keepR` with `s0` carried).
-/


namespace Tom.Machine.Fn.SubD

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "subd_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpSubDBase = 0x800064a4 := rfl
   have : mpSubDCode.length = 103 := rfl))

/-! ## Register lists at the join points -/

/-- At the entry: `a0 = a`, `a1 = b`, `a2 = c`. -/
def entryL (ra s0 : BitVec 64) (sp pa b pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 b),
   (12, BitVec.ofNat 64 pc)]

def frameLog (ra s0 : BitVec 64) (sp : Nat) : List WEntry := [(sp - 16, 8, s0), (sp - 8, 8, ra)]

/-- At `64c8`, after the prologue. -/
def pL (ra : BitVec 64) (sp pa b pc ua : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (16, BitVec.ofNat 64 pa),
   (15, BitVec.ofNat 64 b), (14, BitVec.ofNat 64 ua)]

/-- At `653c`, the big branch. -/
def bL (ra : BitVec 64) (sp pa b pc ua ou adp cdp : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (16, BitVec.ofNat 64 pa),
   (15, BitVec.ofNat 64 b), (17, BitVec.ofNat 64 ua), (12, BitVec.ofNat 64 ou), (13, BitVec.ofNat 64 adp),
   (14, BitVec.ofNat 64 cdp)]

/-- At the loop head `6558`, index `i`, borrow `u`. -/
def lL (ra : BitVec 64) (sp pa pc ou adp cdp i u : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (16, BitVec.ofNat 64 pa),
   (12, BitVec.ofNat 64 ou), (6, 268435455#64), (10, BitVec.ofNat 64 i), (15, BitVec.ofNat 64 u),
   (13, BitVec.ofNat 64 (adp + 4 * i)), (14, BitVec.ofNat 64 (cdp + 4 * i))]

/-- At `6514`, after the zeroing. -/
def jL (ra : BitVec 64) (sp pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc)]

/-- At the `memset` call (`6510`): `memset(c->dp + n, 0, 4 (oldused - n))`. -/
def msL (ra : BitVec 64) (sp pc cdp n ou : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc),
   (10, BitVec.ofNat 64 (cdp + 4 * n)), (11, 0#64), (12, BitVec.ofNat 64 (4 * (ou - n)))]

/-- At `6514` after the `memset` call (`ra` is in the frame). -/
def mL (sp pc : Nat) : GRegs := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc)]

/-- At the `mp_clamp` call (`6518`). -/
def cL (sp pc : Nat) : GRegs := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pc)]

/-- After a call, at `651c`/`6600`. -/
def rL (sp : Nat) : GRegs := [(2, BitVec.ofNat 64 (sp - 64))]

/-! ## Facts the segments read -/

/-- The prologue: `a->used`, `c->alloc`, the stack frame. -/
structure PFacts (m : Mem) (sp pa pc ua al : Nat) : Prop where
  ra_ : Ram pa 24
  rc : Ram pc 24
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  ua_v : bytesT4 m pa = BitVec.ofNat 32 ua
  al_v : bytesT4 m (pc + 4) = BitVec.ofNat 32 al
  ua_lt : ua < 2 ^ 31
  al_lt : al < 2 ^ 31
  room : ua < al
  code_s : sp ≤ mpSubDBase ∨ mpSubDBase + 412 ≤ sp - 64

theorem PFacts.sx {m : Mem} {sp pa pc ua al : Nat} (h : PFacts m sp pa pc ua al) :
    BitVec.signExtend 64 (bytesT4 m pa) = BitVec.ofNat 64 ua ∧
      BitVec.signExtend 64 (bytesT4 m (pc + 4)) = BitVec.ofNat 64 al :=
  ⟨by rw [h.ua_v, signExtend_ofNat32 _ h.ua_lt], by rw [h.al_v, signExtend_ofNat32 _ h.al_lt]⟩

/-- Save `s0`, `ra`; `c` has room (`a->used < c->alloc`, so no `mp_grow`). -/
theorem p_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ua al : Nat) (m : Mem)
    (hc : CodeAt m mpSubDBase mpSubDCode) (hf : PFacts m sp pa pc ua al) :
    Triple (At 0x800064a4#64 (entryL ra s0 sp pa b pc) m v.keepR outp)
      (At 0x800064c8#64 (pL ra sp pa b pc ua) (writeLog m (frameLog ra s0 sp)) v.keepR outp) := by
  subd_ctx
  have ⟨hua, hal⟩ := hf.sx
  seg_step subdP 0x800064c8#64 [rd4 m pa, rd4 m (pc + 4)]
    [1, 2, 8, 10, 11, 12] abiKeysR [entryL, frameLog] [pL] [hua, hal] hc

/-- `a`'s and `c`'s structs at `64c8`. -/
structure HFacts (M : Mem) (pa pc sa ua ou adp cdp : Nat) : Prop where
  ra_ : Ram pa 24
  rc : Ram pc 24
  pc_al : pc % 8 = 0
  sa_v : bytesT4 M (pa + 8) = BitVec.ofNat 32 sa
  ua_v : bytesT4 M pa = BitVec.ofNat 32 ua
  ou_v : bytesT4 M pc = BitVec.ofNat 32 ou
  adp_v : bytesT8 M (pa + 16) = BitVec.ofNat 64 adp
  cdp_v : bytesT8 M (pc + 16) = BitVec.ofNat 64 cdp
  sa_lt : sa < 2 ^ 31
  ua_lt : ua < 2 ^ 31
  ou_lt : ou < 2 ^ 31
  code_c : pc + 24 ≤ mpSubDBase ∨ mpSubDBase + 412 ≤ pc

theorem HFacts.sx {M : Mem} {pa pc sa ua ou adp cdp : Nat} (h : HFacts M pa pc sa ua ou adp cdp) :
    BitVec.signExtend 64 (bytesT4 M (pa + 8)) = BitVec.ofNat 64 sa ∧
      BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 ua ∧
      BitVec.signExtend 64 (bytesT4 M pc) = BitVec.ofNat 64 ou :=
  ⟨by rw [h.sa_v, signExtend_ofNat32 _ h.sa_lt], by rw [h.ua_v, signExtend_ofNat32 _ h.ua_lt],
   by rw [h.ou_v, signExtend_ofNat32 _ h.ou_lt]⟩

/-- The store into `c[0]`. -/
structure DFacts (cdp : Nat) : Prop where
  rd : Ram cdp 4
  d_al : cdp % 4 = 0
  code_d : cdp + 4 ≤ mpSubDBase ∨ mpSubDBase + 412 ≤ cdp

/-- `a[0] = x`. -/
structure XFacts (M : Mem) (adp x : Nat) : Prop where
  rx : Ram adp 4
  x_v : bytesT4 M adp = BitVec.ofNat 32 x
  x_lt : x < 268435456

theorem XFacts.sx {M : Mem} {adp x : Nat} (h : XFacts M adp x) :
    BitVec.signExtend 64 (bytesT4 M adp) = BitVec.ofNat 64 x := by
  rw [h.x_v, signExtend_ofNat32 _ (by have := h.x_lt; omega)]

/-- The small-branch log: `c[0] := d`, `c->sign := MP_NEG`, `c->used := 1`. -/
def smallLog (pc cdp d : Nat) : List WEntry :=
  [(cdp, 4, BitVec.ofNat 64 d), (pc + 8, 4, BitVec.ofNat 64 1), (pc, 4, BitVec.ofNat 64 1)]

/-! ## The small branches -/

/-- At `64f0`: `a->used = 0`, `a0 = c->dp + 1`. -/
def s0L (ra : BitVec 64) (sp b pc ou cdp : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (15, BitVec.ofNat 64 b),
   (12, BitVec.ofNat 64 ou), (14, BitVec.ofNat 64 cdp), (10, BitVec.ofNat 64 (cdp + 4))]

/-- At `6618`: `a->used = 1`, `a1 = a[0] ≤ b`. -/
def s1L (ra : BitVec 64) (sp b pc ou cdp x : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (15, BitVec.ofNat 64 b),
   (12, BitVec.ofNat 64 ou), (14, BitVec.ofNat 64 cdp), (11, BitVec.ofNat 64 x)]

/-- `a ≥ 0`, `a->used = 0`: to `64f0`. -/
theorem s0_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ou adp cdp : Nat) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hf : HFacts M pa pc 0 0 ou adp cdp) (hcd : cdp + 4 ≤ 2 ^ 32) :
    Triple (At 0x800064c8#64 (pL ra sp pa b pc 0) M v.keepR outp)
      (At 0x800064f0#64 (s0L ra sp b pc ou cdp) (writeLog M []) v.keepR outp) := by
  subd_ctx
  have ⟨hsa, hua, hou'⟩ := hf.sx
  seg_step subd0 0x800064f0#64 [rd4 M (pa + 8), rd4 M pa, rd4 M pc, rd8 M (pa + 16), rd8 M (pc + 16)]
    [1, 2, 8, 16, 15, 14] abiKeysR [pL] [s0L] [hsa, hua, hou', hf.adp_v, hf.cdp_v] hc

/-- `a ≥ 0`, `a->used = 1`, `a[0] ≤ b`: to `6618`. -/
theorem s1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ou adp cdp x : Nat) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hf : HFacts M pa pc 0 1 ou adp cdp) (hx : XFacts M adp x)
    (hb : b < 268435456) (hxb : x ≤ b) :
    Triple (At 0x800064c8#64 (pL ra sp pa b pc 1) M v.keepR outp)
      (At 0x80006618#64 (s1L ra sp b pc ou cdp x) (writeLog M []) v.keepR outp) := by
  subd_ctx
  have ⟨hsa, hua, hou'⟩ := hf.sx
  have hxv := hx.sx
  seg_step subd1s 0x80006618#64
    [rd4 M (pa + 8), rd4 M pa, rd4 M pc, rd8 M (pa + 16), rd8 M (pc + 16), rd4 M adp]
    [1, 2, 8, 16, 15, 14] abiKeysR [pL] [s1L] [hsa, hua, hou', hf.adp_v, hf.cdp_v, hxv] hc

/-- `c`'s struct off the code. -/
structure CFacts (pc : Nat) : Prop where
  rc : Ram pc 24
  pc_al : pc % 8 = 0
  code_c : pc + 24 ≤ mpSubDBase ∨ mpSubDBase + 412 ≤ pc

/-- `c[0] := b`, `MP_NEG`, `used := 1`; `oldused ≤ 1`: no `memset`. -/
theorem s0a_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp b pc ou cdp : Nat) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hs : CFacts pc) (hd : DFacts cdp) (hb : b < 2 ^ 31)
    (hou : ou ≤ 1) :
    Triple (At 0x800064f0#64 (s0L ra sp b pc ou cdp) M v.keepR outp)
      (At 0x80006514#64 (jL ra sp pc) (writeLog M (smallLog pc cdp b)) v.keepR outp) := by
  subd_ctx
  seg_step subdS0a 0x80006514#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 15, 12, 14, 10] abiKeysR [s0L, smallLog] [jL] [] hc

/-- `c[0] := b`, `MP_NEG`, `used := 1`; `oldused > 1`: set up the `memset`. -/
theorem s0b_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp b pc ou cdp : Nat) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hs : CFacts pc) (hd : DFacts cdp) (hb : b < 2 ^ 31)
    (hou : 1 < ou) (hou' : ou < 2 ^ 31) (hcd : cdp + 4 * ou ≤ 2 ^ 32) :
    Triple (At 0x800064f0#64 (s0L ra sp b pc ou cdp) M v.keepR outp)
      (At 0x80006510#64 (msL ra sp pc cdp 1 ou) (writeLog M (smallLog pc cdp b)) v.keepR outp) := by
  subd_ctx
  seg_step subdS0b 0x80006510#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 15, 12, 14, 10] abiKeysR [s0L, smallLog] [msL] [] hc

/-- `c[0] := b - a[0]`, `MP_NEG`, `used := 1`; `oldused ≤ 1`: no `memset`. -/
theorem s1a_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp b pc ou cdp x : Nat) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hs : CFacts pc) (hd : DFacts cdp) (hb : b < 268435456)
    (hxb : x ≤ b) (hou : ou ≤ 1) :
    Triple (At 0x80006618#64 (s1L ra sp b pc ou cdp x) M v.keepR outp)
      (At 0x80006514#64 (jL ra sp pc) (writeLog M (smallLog pc cdp (b - x))) v.keepR outp) := by
  subd_ctx
  seg_step subdS1a 0x80006514#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 15, 12, 14, 11] abiKeysR [s1L, smallLog] [jL] [] hc

/-- `c[0] := b - a[0]`, `MP_NEG`, `used := 1`; `oldused > 1`: set up the `memset`. -/
theorem s1b_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp b pc ou cdp x : Nat) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hs : CFacts pc) (hd : DFacts cdp) (hb : b < 268435456)
    (hxb : x ≤ b) (hou : 1 < ou) (hou' : ou < 2 ^ 31) (hcd : cdp + 4 * ou ≤ 2 ^ 32) :
    Triple (At 0x80006618#64 (s1L ra sp b pc ou cdp x) M v.keepR outp)
      (At 0x80006510#64 (msL ra sp pc cdp 1 ou) (writeLog M (smallLog pc cdp (b - x))) v.keepR outp) := by
  subd_ctx
  seg_step subdS1b 0x80006510#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 15, 12, 14, 11] abiKeysR [s1L, smallLog] [msL] [] hc

/-! ## The big branch -/

/-- `a->used = 1`, `a[0] > b`: to `653c`. -/
theorem b1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ou adp cdp x : Nat) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hf : HFacts M pa pc 0 1 ou adp cdp) (hx : XFacts M adp x)
    (hb : b < 268435456) (hxb : b < x) :
    Triple (At 0x800064c8#64 (pL ra sp pa b pc 1) M v.keepR outp)
      (At 0x8000653c#64 (bL ra sp pa b pc 1 ou adp cdp) (writeLog M []) v.keepR outp) := by
  subd_ctx
  have ⟨hsa, hua, hou'⟩ := hf.sx
  have hxv := hx.sx
  seg_step subd1b 0x8000653c#64
    [rd4 M (pa + 8), rd4 M pa, rd4 M pc, rd8 M (pa + 16), rd8 M (pc + 16), rd4 M adp]
    [1, 2, 8, 16, 15, 14] abiKeysR [pL] [bL] [hsa, hua, hou', hf.adp_v, hf.cdp_v, hxv] hc

/-- `a->used ≥ 2`: to `653c`. -/
theorem b2_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ua ou adp cdp : Nat) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hf : HFacts M pa pc 0 ua ou adp cdp) (h2 : 2 ≤ ua) :
    Triple (At 0x800064c8#64 (pL ra sp pa b pc ua) M v.keepR outp)
      (At 0x8000653c#64 (bL ra sp pa b pc ua ou adp cdp) (writeLog M []) v.keepR outp) := by
  subd_ctx
  have ⟨hsa, hua, hou'⟩ := hf.sx
  seg_step subd2b 0x8000653c#64 [rd4 M (pa + 8), rd4 M pa, rd4 M pc, rd8 M (pa + 16), rd8 M (pc + 16)]
    [1, 2, 8, 16, 15, 14] abiKeysR [pL] [bL] [hsa, hua, hou', hf.adp_v, hf.cdp_v] hc

/-- `c`'s struct at `653c`; `a->used`, read after the store into `c->used`. -/
structure BFacts (M : Mem) (pa pc ua : Nat) : Prop where
  ra_ : Ram pa 24
  rc : Ram pc 24
  pc_al : pc % 8 = 0
  ua_v : bytesT4 M pa = BitVec.ofNat 32 ua
  ua_lt : ua < 2 ^ 31
  ac : pa + 4 ≤ pc ∨ pc + 4 ≤ pa
  code_c : pc + 24 ≤ mpSubDBase ∨ mpSubDBase + 412 ≤ pc

/-- `c->used := a->used`, `c->sign := MP_ZPOS`, enter the loop at `i = 0`, borrow `b`. -/
theorem bb_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ua ou adp cdp : Nat) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hf : BFacts M pa pc ua) (h1 : 1 ≤ ua) :
    Triple (At 0x8000653c#64 (bL ra sp pa b pc ua ou adp cdp) M v.keepR outp)
      (At 0x80006558#64 (lL ra sp pa pc ou adp cdp 0 b)
        (writeLog M [(pc, 4, BitVec.ofNat 64 ua), (pc + 8, 4, 0#64)]) v.keepR outp) := by
  subd_ctx
  have hua : BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 ua := by
    rw [hf.ua_v, signExtend_ofNat32 _ hf.ua_lt]
  seg_step subdB 0x80006558#64 [rd4 M pa]
    [1, 2, 8, 16, 15, 17, 12, 13, 14] abiKeysR [bL] [lL] [hua] hc

/-- `c->used := a->used` alone (for `c = a`, where the next load reads this store back). -/
theorem bb1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ua ou adp cdp : Nat) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hs : CFacts pc) :
    Triple (At 0x8000653c#64 (bL ra sp pa b pc ua ou adp cdp) M v.keepR outp)
      (At 0x80006540#64 (bL ra sp pa b pc ua ou adp cdp) (writeLog M [(pc, 4, BitVec.ofNat 64 ua)]) v.keepR outp) := by
  subd_ctx
  seg_step subdB1 0x80006540#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 16, 15, 17, 12, 13, 14] abiKeysR [bL] [bL] [] hc

/-- Reload `a->used`, `c->sign := MP_ZPOS`, enter the loop at `i = 0`, borrow `b`. -/
theorem bb2_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ua ou adp cdp : Nat) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hs : CFacts pc) (hr : Ram pa 24)
    (hu : bytesT4 M pa = BitVec.ofNat 32 ua) (hu' : ua < 2 ^ 31) (h1 : 1 ≤ ua) :
    Triple (At 0x80006540#64 (bL ra sp pa b pc ua ou adp cdp) M v.keepR outp)
      (At 0x80006558#64 (lL ra sp pa pc ou adp cdp 0 b) (writeLog M [(pc + 8, 4, 0#64)]) v.keepR outp) := by
  subd_ctx
  have hua : BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 ua := by
    rw [hu, signExtend_ofNat32 _ hu']
  seg_step subdB2 0x80006558#64 [rd4 M pa]
    [1, 2, 8, 16, 15, 17, 12, 13, 14] abiKeysR [bL] [lL] [hua] hc

/-- One iteration's reads (`a[i] = x`, `a->used` after the store) and store into `c[i]`. -/
structure LFacts (M : Mem) (pa adp cdp ua i x : Nat) : Prop where
  rx : Ram (adp + 4 * i) 4
  x_v : bytesT4 M (adp + 4 * i) = BitVec.ofNat 32 x
  x_lt : x < 268435456
  ra_ : Ram pa 24
  ua_v : bytesT4 M pa = BitVec.ofNat 32 ua
  ua_lt : ua < 2 ^ 31
  rd : Ram (cdp + 4 * i) 4
  d_al : cdp % 4 = 0
  ac : pa + 4 ≤ cdp + 4 * i ∨ cdp + 4 * i + 4 ≤ pa
  code_d : cdp + 4 * i + 4 ≤ mpSubDBase ∨ mpSubDBase + 412 ≤ cdp + 4 * i

theorem LFacts.sx {M : Mem} {pa adp cdp ua i x : Nat} (h : LFacts M pa adp cdp ua i x) :
    BitVec.signExtend 64 (bytesT4 M (adp + 4 * i)) = BitVec.ofNat 64 x ∧
      BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 ua :=
  ⟨by rw [h.x_v, signExtend_ofNat32 _ (by have := h.x_lt; omega)], by rw [h.ua_v, signExtend_ofNat32 _ h.ua_lt]⟩

/-- The loop's back edge: `c[i] := (x - u) mod 2^28`, borrow the sign bit of `x - u`. -/
theorem l_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pc ou adp cdp ua i u x : Nat)
    (M : Mem) (hc : CodeAt M mpSubDBase mpSubDCode) (hf : LFacts M pa adp cdp ua i x) (hu : u < 268435456)
    (hi : i + 1 < ua) :
    Triple (At 0x80006558#64 (lL ra sp pa pc ou adp cdp i u) M v.keepR outp)
      (At 0x80006558#64 (lL ra sp pa pc ou adp cdp (i + 1) ((x + 4294967296 - u) % 4294967296 / 2147483648))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64 ((x + 268435456 - u) % 268435456))]) v.keepR outp) := by
  subd_ctx
  have ⟨hx, hua⟩ := hf.sx
  seg_step subdL 0x80006558#64 [rd4 M (adp + 4 * i), rd4 M pa]
    [1, 2, 8, 16, 12, 6, 10, 15, 13, 14] abiKeysR [lL] [] [hx, hua] hc

/-- The loop's last iteration (`i + 1 = a->used`), `oldused ≤ a->used`: no `memset`. -/
theorem la_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pc ou adp cdp ua i u x : Nat)
    (M : Mem) (hc : CodeAt M mpSubDBase mpSubDCode) (hf : LFacts M pa adp cdp ua i x) (hu : u < 268435456)
    (hi : i + 1 = ua) (hou : ou ≤ ua) (hou' : ou < 2 ^ 31) :
    Triple (At 0x80006558#64 (lL ra sp pa pc ou adp cdp i u) M v.keepR outp)
      (At 0x80006514#64 (jL ra sp pc)
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64 ((x + 268435456 - u) % 268435456))]) v.keepR outp) := by
  subd_ctx
  have ⟨hx, hua⟩ := hf.sx
  seg_step subdLa 0x80006514#64 [rd4 M (adp + 4 * i), rd4 M pa]
    [1, 2, 8, 16, 12, 6, 10, 15, 13, 14] abiKeysR [lL] [jL] [hx, hua] hc

/-- The loop's last iteration, `oldused > a->used`: set up the `memset`. -/
theorem lb_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pc ou adp cdp ua i u x : Nat)
    (M : Mem) (hc : CodeAt M mpSubDBase mpSubDCode) (hf : LFacts M pa adp cdp ua i x) (hu : u < 268435456)
    (hi : i + 1 = ua) (hou : ua < ou) (hou' : ou < 2 ^ 31) (hcd : cdp + 4 * ou ≤ 2 ^ 32) :
    Triple (At 0x80006558#64 (lL ra sp pa pc ou adp cdp i u) M v.keepR outp)
      (At 0x80006510#64 (msL ra sp pc cdp ua ou)
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64 ((x + 268435456 - u) % 268435456))]) v.keepR outp) := by
  subd_ctx
  have ⟨hx, hua⟩ := hf.sx
  seg_step subdLb 0x80006510#64 [rd4 M (adp + 4 * i), rd4 M pa]
    [1, 2, 8, 16, 12, 6, 10, 15, 13, 14] abiKeysR [lL] [msL] [hx, hua] hc

/-! ## The tail -/

/-- `a0 := c` before the `mp_clamp` call (`6514`). -/
theorem d_step (v : Abi) (outp : Array String) (sp pc : Nat) (M : Mem) (hc : CodeAt M mpSubDBase mpSubDCode) :
    Triple (At 0x80006514#64 (mL sp pc) M v.keepR outp)
      (At 0x80006518#64 (cL sp pc) (writeLog M []) v.keepR outp) := by
  subd_ctx
  seg_step subdD 0x80006518#64 ([] : List (List (BitVec 8))) [2, 8] abiKeysR [mL] [cL] [] hc

/-- The saved frame. -/
structure RFacts (M : Mem) (ra s0 : BitVec 64) (sp : Nat) : Prop where
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  ra_al : ra.toNat % 4 = 0

/-- The epilogue (`651c`): restore `ra`, `s0`, `sp`; return `MP_OKAY`. -/
theorem r_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hf : RFacts M ra s0 sp) :
    Triple (At 0x8000651c#64 (rL sp) M v.keepR outp)
      (At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] (writeLog M []) v.keepR outp) := by
  subd_ctx
  have hra := hf.ra_al
  have h1 : bytesT8 M (sp - 64 + 56) = ra := by rw [show sp - 64 + 56 = sp - 8 by omega]; exact hf.ra_v
  have h2 : bytesT8 M (sp - 64 + 48) = s0 := by rw [show sp - 64 + 48 = sp - 16 by omega]; exact hf.s0_v
  seg_step subdR ra [rd8 M (sp - 64 + 56), rd8 M (sp - 64 + 48)] [2] abiKeysR [rL] [] [h1, h2] hc

/-! ## The calls -/

/-- The callee-saved registers `memset`/`mp_clamp` see: this frame's `sp`, `s0 = c`. -/
def calleeAbi (v : Abi) (sp pc : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 64), s0 := BitVec.ofNat 64 pc }

/-- `memset(c->dp + n, 0, 4 (oldused - n))` at `6510`, back at `6514`. -/
theorem memset_call (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp n ou : Nat) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hP : Memset.Pre M (cdp + 4 * n) 0 (4 * (ou - n))) :
    Triple (At 0x80006510#64 (msL ra sp pc cdp n ou) M v.keepR outp)
      (fun c => ∃ M', At 0x80006514#64 (mL sp pc) M' v.keepR outp c ∧
        Memset.Post M (cdp + 4 * n) (4 * (ou - n)) 0#8 M') := by
  refine Triple.seq (jal_at (pc := 0x80006510#64) (w := 0x695020ef#32) (imm := 0x02e94#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc),
        (10, BitVec.ofNat 64 (cdp + 4 * n)), (11, 0#64), (12, BitVec.ofNat 64 (4 * (ou - n)))])
      (hc.word (a := (0x80006510#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [msL]) (by simp [keysG]) (by simp [Abi.keepR, sKeepL, keysG])) ?_
  refine Triple.conseq (Memset.correct_zero 0x80006514#64 (calleeAbi v sp pc) outp M _ _ (by decide) hP)
    (fun c h => ?_) (fun c ⟨M', hat, hpost⟩ => ⟨M', hat.reshape ?_ ?_, hpost⟩)
  · have hpc : (0x80006510#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x02e94#21) = Memset.entry := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [Memset.entryL, Sail.BitVec.addInt]
    · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]
  · simp [mL, Abi.keep, calleeAbi]
  · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]

/-- `mp_clamp(c)` at `6518`, back at `651c`. -/
theorem clamp_call (v : Abi) (outp : Array String) (sp pc cdp : Nat) (cm : MpInt) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hP : Clamp.Pre M pc cdp cm) :
    Triple (At 0x80006518#64 (cL sp pc) M v.keepR outp)
      (fun c => ∃ a' M', At 0x8000651c#64 (rL sp) M' v.keepR outp c ∧ Clamp.Post M pc cdp cm a' M') := by
  refine Triple.seq (jal_at (pc := 0x80006518#64) (w := 0xac1fe0ef#32) (imm := 0x1feac0#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pc)])
      (hc.word (a := (0x80006518#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [cL]) (by simp [keysG]) (by simp [Abi.keepR, sKeepL, keysG])) ?_
  refine Triple.conseq (Clamp.correct 0x8000651c#64 (calleeAbi v sp pc) outp pc cdp cm M (by decide) hP)
    (fun c h => ?_) (fun c ⟨a', M', hat, hpost⟩ => ⟨a', M', hat.reshape ?_ ?_, hpost⟩)
  · have hpc : (0x80006518#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x1feac0#21) = Clamp.entry := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [Sail.BitVec.addInt]
    · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]
  · simp [rL, Abi.keep, calleeAbi]
  · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]

/-! ## `a < 0`: the call of `mp_add_d` on a stack copy -/

/-- At the `mp_add_d(&a_, b, c)` call (`65e8`): `a_` at `sp - 40`. -/
def cpL (ra : BitVec 64) (sp b pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 (sp - 40)),
   (11, BitVec.ofNat 64 b), (12, BitVec.ofNat 64 pc)]

/-- After `mp_add_d` returns `MP_OKAY` (`65ec`). -/
def sdL (sp pc : Nat) : GRegs := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (10, 0#64)]

/-- The stack copy of `a` with `MP_ZPOS`, and the spilled sign. -/
def cpLog (sp : Nat) (w0 w8 w16 : BitVec 64) : List WEntry :=
  [(sp - 32, 8, w8), (sp - 24, 8, w16), (sp - 64, 8, BitVec.ofNat 64 1), (sp - 40, 8, w0), (sp - 32, 4, 0#64)]

/-- The stack copy's reads and stores. -/
structure CpFacts (M : Mem) (sp pa : Nat) : Prop where
  ra_ : Ram pa 24
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  sa_v : bytesT4 M (pa + 8) = BitVec.ofNat 32 1
  s_a : sp ≤ pa ∨ pa + 24 ≤ sp - 64
  code_s : sp ≤ mpSubDBase ∨ mpSubDBase + 412 ≤ sp - 64

/-- `a < 0`: copy `a` to `sp - 40` with `MP_ZPOS`, spill the sign, set up `mp_add_d(&a_, b, c)`. -/
theorem n_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ua : Nat) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hf : CpFacts M sp pa) :
    Triple (At 0x800064c8#64 (pL ra sp pa b pc ua) M v.keepR outp)
      (At 0x800065e8#64 (cpL ra sp b pc)
        (writeLog M (cpLog sp (bytesT8 M pa) (bytesT8 M (pa + 8)) (bytesT8 M (pa + 16)))) v.keepR outp) := by
  subd_ctx
  have hsa : BitVec.signExtend 64 (bytesT4 M (pa + 8)) = BitVec.ofNat 64 1 := by
    rw [hf.sa_v, signExtend_ofNat32 _ (by decide)]
  refine Tom.Machine.seg_at' subdN (pc1 := 0x800065e8#64) [rd4 M (pa + 8), rd8 M (pa + 8), rd8 M (pa + 16), rd8 M pa]
    [1, 2, 8, 16, 15, 14] abiKeysR ?_ ?_ ?_ ?_
  · tom_facts hc
    all_goals leaf_auto [pL, cpLog] [hsa]
  · seg_nfo [subdN, pL, cpLog]
  · sub_auto [subdN, pL, cpLog, cpL] [hsa]
  · seg_nfo [subdN, pL, cpLog]
    try val_nf [hsa]
    repeat' apply And.intro
    all_goals first | rfl | exact True.intro | omega | bv_nat

/-- After `mp_add_d`: spill `MP_OKAY`, `c->sign := MP_NEG` (the spilled sign), `a0 := c`. -/
theorem n2_step (v : Abi) (outp : Array String) (sp pc : Nat) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hs : Ram (sp - 64) 64) (hsp : sp % 16 = 0) (hsp' : 64 ≤ sp)
    (hcs : sp ≤ mpSubDBase ∨ mpSubDBase + 412 ≤ sp - 64) (hr : Ram pc 24) (hal : pc % 8 = 0)
    (hcc : pc + 24 ≤ mpSubDBase ∨ mpSubDBase + 412 ≤ pc) (h1 : bytesT8 M (sp - 64) = BitVec.ofNat 64 1)
    (hps : sp - 64 + 8 ≤ pc + 8 ∨ pc + 12 ≤ sp - 64) :
    Triple (At 0x800065ec#64 (sdL sp pc) M v.keepR outp)
      (At 0x800065fc#64 (cL sp pc) (writeLog M [(sp - 64, 8, 0#64), (pc + 8, 4, BitVec.ofNat 64 1)])
        v.keepR outp) := by
  subd_ctx
  have h1' : bytesT8 M (sp - 64 + 0) = BitVec.ofNat 64 1 := by rw [Nat.add_zero]; exact h1
  seg_step subdN2 0x800065fc#64 [rd8 M (sp - 64 + 0)] [2, 8, 10] abiKeysR [sdL] [cL] [h1'] hc

/-- The negative branch's epilogue (`6600`): reload the spilled `MP_OKAY`, restore, return. -/
theorem nr_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hf : RFacts M ra s0 sp) (he : bytesT8 M (sp - 64) = 0#64) :
    Triple (At 0x80006600#64 (rL sp) M v.keepR outp)
      (At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] (writeLog M []) v.keepR outp) := by
  subd_ctx
  have hra := hf.ra_al
  have h0 : bytesT8 M (sp - 64 + 0) = 0#64 := by rw [Nat.add_zero]; exact he
  have h1 : bytesT8 M (sp - 64 + 56) = ra := by rw [show sp - 64 + 56 = sp - 8 by omega]; exact hf.ra_v
  have h2 : bytesT8 M (sp - 64 + 48) = s0 := by rw [show sp - 64 + 48 = sp - 16 by omega]; exact hf.s0_v
  seg_step subdNR ra [rd8 M (sp - 64 + 0), rd8 M (sp - 64 + 56), rd8 M (sp - 64 + 48)] [2] abiKeysR [rL] []
    [h0, h1, h2] hc

/-- `mp_clamp(c)` at `65fc`, back at `6600`. -/
theorem clamp_call2 (v : Abi) (outp : Array String) (sp pc cdp : Nat) (cm : MpInt) (M : Mem)
    (hc : CodeAt M mpSubDBase mpSubDCode) (hP : Clamp.Pre M pc cdp cm) :
    Triple (At 0x800065fc#64 (cL sp pc) M v.keepR outp)
      (fun c => ∃ a' M', At 0x80006600#64 (rL sp) M' v.keepR outp c ∧ Clamp.Post M pc cdp cm a' M') := by
  refine Triple.seq (jal_at (pc := 0x800065fc#64) (w := 0x9ddfe0ef#32) (imm := 0x1fe9dc#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pc)])
      (hc.word (a := (0x800065fc#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [cL]) (by simp [keysG]) (by simp [Abi.keepR, sKeepL, keysG])) ?_
  refine Triple.conseq (Clamp.correct 0x80006600#64 (calleeAbi v sp pc) outp pc cdp cm M (by decide) hP)
    (fun c h => ?_) (fun c ⟨a', M', hat, hpost⟩ => ⟨a', M', hat.reshape ?_ ?_, hpost⟩)
  · have hpc : (0x800065fc#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x1fe9dc#21) = Clamp.entry := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [Sail.BitVec.addInt]
    · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]
  · simp [rL, Abi.keep, calleeAbi]
  · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]

end Tom.Machine.Fn.SubD
