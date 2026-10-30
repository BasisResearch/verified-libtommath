import Tom.Machine.Seg.AddD
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Arr
import Tom.Machine.Kit.Bits
import Tom.Machine.Kit.Jal
import Tom.Machine.Fn.Memset
import Tom.Machine.Fn.Clamp

/-!
# `mp_add_d` on the machine: the segments

`mp_add_d(a, b, c)` at `0x80004e30` (106 instructions). The prologue
(`adddP`) saves `s0`, `ra` and tests `a->used ≥ c->alloc` (the `mp_grow`
branch, excluded by the contract, D5). Then by `a`'s sign and size:

* `MP_ZPOS`: `a->used = 0` (`addd0z`) or the loop at `4e80` from `mu = b`
  (`adddE`, `adddL`, the exit `adddLe`), meeting at `4eb0`, where the final
  carry is stored and `c->used := a->used + 1` (`adddC`);
* `MP_NEG`, `a->used ≤ 1`, `a[0] < b` (`adddS1`, `adddS2`): `c->used := 1`,
  `c[0] := b - a[0]`;
* `MP_NEG` otherwise (`adddB1`, `adddB2`): copy `a` to the stack with
  `MP_ZPOS` (`adddCp`), call `mp_sub_d`, `c->sign := MP_NEG` (`adddB3`),
  `mp_clamp`, return its result (`adddBR`).

The non-recursive branches meet at `4ec4`: `c->sign := MP_ZPOS`, the
`oldused - ix` test of the zeroing (`adddT0`/`adddT1`, the `memset` call at
`4ed8`), `mp_clamp(c)` (`adddD`), the epilogue (`adddR`). `s0 = c`, `t3 = a`.
-/


namespace Tom.Machine.Fn.AddD

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "addd_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpAddDBase = 0x80004e30 := rfl
   have : mpAddDCode.length = 106 := rfl))

/-! ## Register lists at the join points -/

/-- At the entry: `a0 = a`, `a1 = b`, `a2 = c`. -/
def entryL (ra s0 : BitVec 64) (sp pa b pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 b),
   (12, BitVec.ofNat 64 pc)]

def frameLog (ra s0 : BitVec 64) (sp : Nat) : List WEntry := [(sp - 16, 8, s0), (sp - 8, 8, ra)]

/-- At `4e54`, after the prologue. -/
def pL (ra : BitVec 64) (sp pa b pc ua : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (28, BitVec.ofNat 64 pa),
   (16, BitVec.ofNat 64 b), (15, BitVec.ofNat 64 ua)]

/-- At the loop head `4e80`, index `i`, carry `u`. -/
def lL (ra : BitVec 64) (sp pa pc ou adp cdp i u : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (28, BitVec.ofNat 64 pa),
   (12, BitVec.ofNat 64 ou), (6, 268435455#64), (15, BitVec.ofNat 64 i), (16, BitVec.ofNat 64 u),
   (13, BitVec.ofNat 64 (adp + 4 * i)), (14, BitVec.ofNat 64 (cdp + 4 * i))]

/-- At `4eb0`: the final carry `mu` into digit `u = a->used`. -/
def jL (ra : BitVec 64) (sp pa pc ou cdp u mu : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (28, BitVec.ofNat 64 pa),
   (12, BitVec.ofNat 64 ou), (14, BitVec.ofNat 64 (cdp + 4 * u)), (15, BitVec.ofNat 64 (u + 1)),
   (16, BitVec.ofNat 64 mu)]

/-- At `4ec4`: `n` digits written, `a0 = c->dp + n`. -/
def tL (ra : BitVec 64) (sp pc ou cdp n : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 (cdp + 4 * n)),
   (12, BitVec.ofNat 64 ou), (15, BitVec.ofNat 64 n)]

/-- At `4f18`, the negative small branch: `a5 = a[0]`. -/
def sL (ra : BitVec 64) (sp pa b pc ou adp cdp x : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (28, BitVec.ofNat 64 pa),
   (16, BitVec.ofNat 64 b), (12, BitVec.ofNat 64 ou), (14, BitVec.ofNat 64 cdp), (13, BitVec.ofNat 64 adp),
   (15, BitVec.ofNat 64 x)]

/-- At the `memset` call (`4ed8`). -/
def msL (ra : BitVec 64) (sp pc cdp n ou : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc),
   (10, BitVec.ofNat 64 (cdp + 4 * n)), (11, 0#64), (12, BitVec.ofNat 64 (4 * (ou - n)))]

/-- At `4edc` (after the `memset` call, or instead of it). -/
def mL (sp pc : Nat) : GRegs := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc)]

/-- At an `mp_clamp` call (`4ee0`, `4fb4`). -/
def cL (sp pc : Nat) : GRegs := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pc)]

/-- After a call (`4ee4`, `4fb8`). -/
def rL (sp : Nat) : GRegs := [(2, BitVec.ofNat 64 (sp - 64))]

/-- At `4f78`, the negative big branch. -/
def gL (ra : BitVec 64) (sp pa b pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (28, BitVec.ofNat 64 pa),
   (16, BitVec.ofNat 64 b)]

/-- At the `mp_sub_d(&a_, b, c)` call (`4fa0`): `a_` at `sp - 40`. -/
def cpL (ra : BitVec 64) (sp b pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 (sp - 40)),
   (11, BitVec.ofNat 64 b), (12, BitVec.ofNat 64 pc)]

/-- After `mp_sub_d` returns `MP_OKAY` (`4fa4`). -/
def sdL (sp pc : Nat) : GRegs := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (10, 0#64)]

/-- The stack copy of `a` with `MP_ZPOS`. -/
def cpLog (sp : Nat) (w0 w8 w16 : BitVec 64) : List WEntry :=
  [(sp - 32, 8, w8), (sp - 24, 8, w16), (sp - 40, 8, w0), (sp - 32, 4, 0#64)]

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
  code_s : sp ≤ mpAddDBase ∨ mpAddDBase + 424 ≤ sp - 64

theorem PFacts.sx {m : Mem} {sp pa pc ua al : Nat} (h : PFacts m sp pa pc ua al) :
    BitVec.signExtend 64 (bytesT4 m pa) = BitVec.ofNat 64 ua ∧
      BitVec.signExtend 64 (bytesT4 m (pc + 4)) = BitVec.ofNat 64 al :=
  ⟨by rw [h.ua_v, signExtend_ofNat32 _ h.ua_lt], by rw [h.al_v, signExtend_ofNat32 _ h.al_lt]⟩

/-- Save `s0`, `ra`; `c` has room (`a->used < c->alloc`, so no `mp_grow`). -/
theorem p_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ua al : Nat) (m : Mem)
    (hc : CodeAt m mpAddDBase mpAddDCode) (hf : PFacts m sp pa pc ua al) :
    Triple (At 0x80004e30#64 (entryL ra s0 sp pa b pc) m v.keepR outp)
      (At 0x80004e54#64 (pL ra sp pa b pc ua) (writeLog m (frameLog ra s0 sp)) v.keepR outp) := by
  addd_ctx
  have ⟨hua, hal⟩ := hf.sx
  seg_step adddP 0x80004e54#64 [rd4 m pa, rd4 m (pc + 4)]
    [1, 2, 8, 10, 11, 12] abiKeysR [entryL, frameLog] [pL] [hua, hal] hc

/-- `a`'s and `c`'s structs at `4e54`. -/
structure HFacts (M : Mem) (pa pc sa ua ou adp cdp : Nat) : Prop where
  ra_ : Ram pa 24
  rc : Ram pc 24
  sa_v : bytesT4 M (pa + 8) = BitVec.ofNat 32 sa
  ua_v : bytesT4 M pa = BitVec.ofNat 32 ua
  ou_v : bytesT4 M pc = BitVec.ofNat 32 ou
  adp_v : bytesT8 M (pa + 16) = BitVec.ofNat 64 adp
  cdp_v : bytesT8 M (pc + 16) = BitVec.ofNat 64 cdp
  sa_lt : sa < 2 ^ 31
  ua_lt : ua < 2 ^ 31
  ou_lt : ou < 2 ^ 31

theorem HFacts.sx {M : Mem} {pa pc sa ua ou adp cdp : Nat} (h : HFacts M pa pc sa ua ou adp cdp) :
    BitVec.signExtend 64 (bytesT4 M (pa + 8)) = BitVec.ofNat 64 sa ∧
      BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 ua ∧
      BitVec.signExtend 64 (bytesT4 M pc) = BitVec.ofNat 64 ou :=
  ⟨by rw [h.sa_v, signExtend_ofNat32 _ h.sa_lt], by rw [h.ua_v, signExtend_ofNat32 _ h.ua_lt],
   by rw [h.ou_v, signExtend_ofNat32 _ h.ou_lt]⟩

/-- `a[0] = x`. -/
structure XFacts (M : Mem) (adp x : Nat) : Prop where
  rx : Ram adp 4
  x_v : bytesT4 M adp = BitVec.ofNat 32 x
  x_lt : x < 268435456

theorem XFacts.sx {M : Mem} {adp x : Nat} (h : XFacts M adp x) :
    BitVec.signExtend 64 (bytesT4 M adp) = BitVec.ofNat 64 x := by
  rw [h.x_v, signExtend_ofNat32 _ (by have := h.x_lt; omega)]

/-! ## `a ≥ 0` -/

/-- `a ≥ 0`, `a->used = 0`: to `4eb0` with carry `b`. -/
theorem z_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ou adp cdp : Nat) (M : Mem)
    (hc : CodeAt M mpAddDBase mpAddDCode) (hf : HFacts M pa pc 0 0 ou adp cdp) :
    Triple (At 0x80004e54#64 (pL ra sp pa b pc 0) M v.keepR outp)
      (At 0x80004eb0#64 (jL ra sp pa pc ou cdp 0 b) (writeLog M []) v.keepR outp) := by
  addd_ctx
  have ⟨hsa, hua, hou⟩ := hf.sx
  seg_step addd0z 0x80004eb0#64 [rd4 M (pa + 8), rd4 M pc, rd8 M (pa + 16), rd8 M (pc + 16), rd4 M pa]
    [1, 2, 8, 28, 16, 15] abiKeysR [pL] [jL] [hsa, hua, hou, hf.adp_v, hf.cdp_v] hc

/-- `a ≥ 0`, `a->used ≥ 1`: enter the loop at `i = 0` with carry `b`. -/
theorem e_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ua ou adp cdp : Nat) (M : Mem)
    (hc : CodeAt M mpAddDBase mpAddDCode) (hf : HFacts M pa pc 0 ua ou adp cdp) (h1 : 1 ≤ ua) :
    Triple (At 0x80004e54#64 (pL ra sp pa b pc ua) M v.keepR outp)
      (At 0x80004e80#64 (lL ra sp pa pc ou adp cdp 0 b) (writeLog M []) v.keepR outp) := by
  addd_ctx
  have ⟨hsa, hua, hou⟩ := hf.sx
  seg_step adddE 0x80004e80#64 [rd4 M (pa + 8), rd4 M pc, rd8 M (pa + 16), rd8 M (pc + 16), rd4 M pa]
    [1, 2, 8, 28, 16, 15] abiKeysR [pL] [lL] [hsa, hua, hou, hf.adp_v, hf.cdp_v] hc

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
  code_d : cdp + 4 * i + 4 ≤ mpAddDBase ∨ mpAddDBase + 424 ≤ cdp + 4 * i

theorem LFacts.sx {M : Mem} {pa adp cdp ua i x : Nat} (h : LFacts M pa adp cdp ua i x) :
    BitVec.signExtend 64 (bytesT4 M (adp + 4 * i)) = BitVec.ofNat 64 x ∧
      BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 ua :=
  ⟨by rw [h.x_v, signExtend_ofNat32 _ (by have := h.x_lt; omega)], by rw [h.ua_v, signExtend_ofNat32 _ h.ua_lt]⟩

/-- The loop's back edge: `c[i] := (x + u) mod 2^28`, carry `(x + u) / 2^28`. -/
theorem l_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pc ou adp cdp ua i u x : Nat)
    (M : Mem) (hc : CodeAt M mpAddDBase mpAddDCode) (hf : LFacts M pa adp cdp ua i x) (hu : u < 268435456)
    (hi : i + 1 < ua) :
    Triple (At 0x80004e80#64 (lL ra sp pa pc ou adp cdp i u) M v.keepR outp)
      (At 0x80004e80#64 (lL ra sp pa pc ou adp cdp (i + 1) ((x + u) / 268435456))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64 ((x + u) % 268435456))]) v.keepR outp) := by
  addd_ctx
  have ⟨hx, hua⟩ := hf.sx
  seg_step adddL 0x80004e80#64 [rd4 M (adp + 4 * i), rd4 M pa]
    [1, 2, 8, 28, 12, 6, 15, 16, 13, 14] abiKeysR [lL] [] [hx, hua] hc

/-- The loop's last iteration (`i + 1 = a->used`), to `4eb0`. -/
theorem le_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pc ou adp cdp ua i u x : Nat)
    (M : Mem) (hc : CodeAt M mpAddDBase mpAddDCode) (hf : LFacts M pa adp cdp ua i x) (hu : u < 268435456)
    (hi : i + 1 = ua) :
    Triple (At 0x80004e80#64 (lL ra sp pa pc ou adp cdp i u) M v.keepR outp)
      (At 0x80004eb0#64 (jL ra sp pa pc ou cdp ua ((x + u) / 268435456))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64 ((x + u) % 268435456))]) v.keepR outp) := by
  addd_ctx
  have ⟨hx, hua⟩ := hf.sx
  seg_step adddLe 0x80004eb0#64 [rd4 M (adp + 4 * i), rd4 M pa]
    [1, 2, 8, 28, 12, 6, 15, 16, 13, 14] abiKeysR [lL] [jL] [hx, hua] hc

/-- The carry digit's store and `c->used`'s. -/
structure CFacts (M : Mem) (pa pc cdp ua : Nat) : Prop where
  ra_ : Ram pa 24
  rc : Ram pc 24
  pc_al : pc % 8 = 0
  ua_v : bytesT4 M pa = BitVec.ofNat 32 ua
  ua_lt : ua + 1 < 2 ^ 31
  rd : Ram (cdp + 4 * ua) 4
  d_al : cdp % 4 = 0
  ac : pa + 4 ≤ cdp + 4 * ua ∨ cdp + 4 * ua + 4 ≤ pa
  code_c : pc + 24 ≤ mpAddDBase ∨ mpAddDBase + 424 ≤ pc
  code_d : cdp + 4 * ua + 4 ≤ mpAddDBase ∨ mpAddDBase + 424 ≤ cdp + 4 * ua

/-- `c[a->used] := mu`, `c->used := a->used + 1`, to `4ec4`. -/
theorem c_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pc ou cdp ua mu : Nat)
    (M : Mem) (hc : CodeAt M mpAddDBase mpAddDCode) (hf : CFacts M pa pc cdp ua) (hmu : mu < 2 ^ 32) :
    Triple (At 0x80004eb0#64 (jL ra sp pa pc ou cdp ua mu) M v.keepR outp)
      (At 0x80004ec4#64 (tL ra sp pc ou cdp (ua + 1))
        (writeLog M [(cdp + 4 * ua, 4, BitVec.ofNat 64 mu), (pc, 4, BitVec.ofNat 64 (ua + 1))]) v.keepR outp) := by
  addd_ctx
  have hua : BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 ua := by
    rw [hf.ua_v, signExtend_ofNat32 _ (by have := hf.ua_lt; omega)]
  seg_step adddC 0x80004ec4#64 [rd4 M pa]
    [1, 2, 8, 28, 12, 14, 15, 16] abiKeysR [jL] [tL] [hua] hc

/-! ## `a < 0`, `|a| < b` -/

/-- `a < 0`, `a->used ≤ 1`, `a[0] < b`: to `4f18`. -/
theorem s1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ua ou adp cdp x : Nat) (M : Mem)
    (hc : CodeAt M mpAddDBase mpAddDCode) (hf : HFacts M pa pc 1 ua ou adp cdp) (hx : XFacts M adp x)
    (hu : ua ≤ 1) (hb : b < 268435456) (hxb : x < b) :
    Triple (At 0x80004e54#64 (pL ra sp pa b pc ua) M v.keepR outp)
      (At 0x80004f18#64 (sL ra sp pa b pc ou adp cdp x) (writeLog M []) v.keepR outp) := by
  addd_ctx
  have ⟨hsa, hua, hou⟩ := hf.sx
  have hxv := hx.sx
  seg_step adddS1 0x80004f18#64
    [rd4 M (pa + 8), rd4 M pa, rd8 M (pa + 16), rd4 M adp, rd4 M pc, rd8 M (pc + 16)]
    [1, 2, 8, 28, 16, 15] abiKeysR [pL] [sL] [hsa, hua, hou, hf.adp_v, hf.cdp_v, hxv] hc

/-- The small branch's stores and its reads after them. -/
structure SFacts (M : Mem) (pa pc adp cdp x : Nat) : Prop where
  ra_ : Ram pa 24
  rc : Ram pc 24
  pc_al : pc % 8 = 0
  ua_v : bytesT4 M pa = BitVec.ofNat 32 1
  xf : XFacts M adp x
  rd : Ram cdp 4
  d_al : cdp % 4 = 0
  ac : pa + 4 ≤ pc ∨ pc + 4 ≤ pa
  dc : adp + 4 ≤ pc ∨ pc + 4 ≤ adp
  code_c : pc + 24 ≤ mpAddDBase ∨ mpAddDBase + 424 ≤ pc
  code_d : cdp + 4 ≤ mpAddDBase ∨ mpAddDBase + 424 ≤ cdp

/-- `c->used := 1`, `c[0] := b - a[0]`, to `4ec4` with `n = 1`. -/
theorem s2_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ou adp cdp x : Nat) (M : Mem)
    (hc : CodeAt M mpAddDBase mpAddDCode) (hf : SFacts M pa pc adp cdp x) (hb : b < 268435456) (hxb : x < b) :
    Triple (At 0x80004f18#64 (sL ra sp pa b pc ou adp cdp x) M v.keepR outp)
      (At 0x80004ec4#64 (tL ra sp pc ou cdp 1)
        (writeLog M [(pc, 4, BitVec.ofNat 64 1), (cdp, 4, BitVec.ofNat 64 (b - x))]) v.keepR outp) := by
  addd_ctx
  have hua : BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 1 := by
    rw [hf.ua_v, signExtend_ofNat32 _ (by decide)]
  have hxv := hf.xf.sx
  seg_step adddS2 0x80004ec4#64 [rd4 M pa, rd4 M adp]
    [1, 2, 8, 28, 16, 12, 14, 13, 15] abiKeysR [sL] [tL] [hua, hxv] hc

/-! ## The tail -/

/-- `c->sign := MP_ZPOS`; `oldused ≤ n`: no `memset`. -/
theorem t0_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc ou cdp n : Nat) (M : Mem)
    (hc : CodeAt M mpAddDBase mpAddDCode) (hs : Ram pc 24) (hal : pc % 8 = 0)
    (hcc : pc + 24 ≤ mpAddDBase ∨ mpAddDBase + 424 ≤ pc) (hn : n < 2 ^ 31) (hou : ou ≤ n) :
    Triple (At 0x80004ec4#64 (tL ra sp pc ou cdp n) M v.keepR outp)
      (At 0x80004edc#64 (mL sp pc) (writeLog M [(pc + 8, 4, 0#64)]) v.keepR outp) := by
  addd_ctx
  have := ram_bounds hs
  seg_step adddT0 0x80004edc#64 ([] : List (List (BitVec 8))) [1, 2, 8, 10, 12, 15] abiKeysR [tL] [mL] [] hc

/-- `c->sign := MP_ZPOS`; `oldused > n`: set up `memset(c->dp + n, 0, 4 (oldused - n))`. -/
theorem t1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc ou cdp n : Nat) (M : Mem)
    (hc : CodeAt M mpAddDBase mpAddDCode) (hs : Ram pc 24) (hal : pc % 8 = 0)
    (hcc : pc + 24 ≤ mpAddDBase ∨ mpAddDBase + 424 ≤ pc) (hou : n < ou) (hou' : ou < 2 ^ 31)
    (hcd : cdp + 4 * ou ≤ 2 ^ 32) :
    Triple (At 0x80004ec4#64 (tL ra sp pc ou cdp n) M v.keepR outp)
      (At 0x80004ed8#64 (msL ra sp pc cdp n ou) (writeLog M [(pc + 8, 4, 0#64)]) v.keepR outp) := by
  addd_ctx
  have := ram_bounds hs
  seg_step adddT1 0x80004ed8#64 ([] : List (List (BitVec 8))) [1, 2, 8, 10, 12, 15] abiKeysR [tL] [msL] [] hc

/-- `a0 := c` before the `mp_clamp` call (`4edc`). -/
theorem d_step (v : Abi) (outp : Array String) (sp pc : Nat) (M : Mem) (hc : CodeAt M mpAddDBase mpAddDCode) :
    Triple (At 0x80004edc#64 (mL sp pc) M v.keepR outp)
      (At 0x80004ee0#64 (cL sp pc) (writeLog M []) v.keepR outp) := by
  addd_ctx
  seg_step adddD 0x80004ee0#64 ([] : List (List (BitVec 8))) [2, 8] abiKeysR [mL] [cL] [] hc

/-- The saved frame. -/
structure RFacts (M : Mem) (ra s0 : BitVec 64) (sp : Nat) : Prop where
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  ra_al : ra.toNat % 4 = 0

/-- The epilogue (`4ee4`): restore `ra`, `s0`, `sp`; return `MP_OKAY`. -/
theorem r_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M mpAddDBase mpAddDCode) (hf : RFacts M ra s0 sp) :
    Triple (At 0x80004ee4#64 (rL sp) M v.keepR outp)
      (At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] (writeLog M []) v.keepR outp) := by
  addd_ctx
  have hra := hf.ra_al
  have h1 : bytesT8 M (sp - 64 + 56) = ra := by rw [show sp - 64 + 56 = sp - 8 by omega]; exact hf.ra_v
  have h2 : bytesT8 M (sp - 64 + 48) = s0 := by rw [show sp - 64 + 48 = sp - 16 by omega]; exact hf.s0_v
  seg_step adddR ra [rd8 M (sp - 64 + 56), rd8 M (sp - 64 + 48)] [2] abiKeysR [rL] [] [h1, h2] hc

/-! ## `a < 0`, `|a| ≥ b` -/

/-- `a < 0`, `a->used > 1`: to `4f78`. -/
theorem g1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ua ou adp cdp : Nat) (M : Mem)
    (hc : CodeAt M mpAddDBase mpAddDCode) (hf : HFacts M pa pc 1 ua ou adp cdp) (hu : 1 < ua) :
    Triple (At 0x80004e54#64 (pL ra sp pa b pc ua) M v.keepR outp)
      (At 0x80004f78#64 (gL ra sp pa b pc) (writeLog M []) v.keepR outp) := by
  addd_ctx
  have ⟨hsa, hua, hou⟩ := hf.sx
  seg_step adddB1 0x80004f78#64 [rd4 M (pa + 8), rd4 M pa]
    [1, 2, 8, 28, 16, 15] abiKeysR [pL] [gL] [hsa, hua] hc

/-- `a < 0`, `a->used ≤ 1`, `a[0] ≥ b`: to `4f78`. -/
theorem g2_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc ua ou adp cdp x : Nat) (M : Mem)
    (hc : CodeAt M mpAddDBase mpAddDCode) (hf : HFacts M pa pc 1 ua ou adp cdp) (hx : XFacts M adp x)
    (hu : ua ≤ 1) (hb : b < 268435456) (hxb : b ≤ x) :
    Triple (At 0x80004e54#64 (pL ra sp pa b pc ua) M v.keepR outp)
      (At 0x80004f78#64 (gL ra sp pa b pc) (writeLog M []) v.keepR outp) := by
  addd_ctx
  have ⟨hsa, hua, hou⟩ := hf.sx
  have hxv := hx.sx
  seg_step adddB2 0x80004f78#64 [rd4 M (pa + 8), rd4 M pa, rd8 M (pa + 16), rd4 M adp]
    [1, 2, 8, 28, 16, 15] abiKeysR [pL] [gL] [hsa, hua, hf.adp_v, hxv] hc

/-- The stack copy's reads and stores. -/
structure CpFacts (sp pa : Nat) : Prop where
  ra_ : Ram pa 24
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  s_a : sp ≤ pa ∨ pa + 24 ≤ sp - 64
  code_s : sp ≤ mpAddDBase ∨ mpAddDBase + 424 ≤ sp - 64

/-- Copy `a` to `sp - 40` with `MP_ZPOS`, set up `mp_sub_d(&a_, b, c)`. -/
theorem cp_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa b pc : Nat) (M : Mem)
    (hc : CodeAt M mpAddDBase mpAddDCode) (hf : CpFacts sp pa) :
    Triple (At 0x80004f78#64 (gL ra sp pa b pc) M v.keepR outp)
      (At 0x80004fa0#64 (cpL ra sp b pc)
        (writeLog M (cpLog sp (bytesT8 M pa) (bytesT8 M (pa + 8)) (bytesT8 M (pa + 16)))) v.keepR outp) := by
  addd_ctx
  refine Tom.Machine.seg_at' adddCp (pc1 := 0x80004fa0#64) [rd8 M (pa + 8), rd8 M pa, rd8 M (pa + 16)]
    [1, 2, 8, 28, 16] abiKeysR ?_ ?_ ?_ ?_
  · tom_facts hc
    all_goals leaf_auto [gL, cpLog] []
  · seg_nfo [adddCp, gL, cpLog]
  · sub_auto [adddCp, gL, cpLog, cpL] []
  · seg_nfo [adddCp, gL, cpLog]
    try val_nf []
    repeat' apply And.intro
    all_goals first | rfl | omega | bv_nat

/-- After `mp_sub_d`: spill `MP_OKAY`, `c->sign := MP_NEG`, `a0 := c`. -/
theorem b3_step (v : Abi) (outp : Array String) (sp pc : Nat) (M : Mem)
    (hc : CodeAt M mpAddDBase mpAddDCode) (hs : Ram (sp - 64) 64) (hsp : sp % 16 = 0) (hsp' : 64 ≤ sp)
    (hcs : sp ≤ mpAddDBase ∨ mpAddDBase + 424 ≤ sp - 64) (hr : Ram pc 24) (hal : pc % 8 = 0)
    (hcc : pc + 24 ≤ mpAddDBase ∨ mpAddDBase + 424 ≤ pc) :
    Triple (At 0x80004fa4#64 (sdL sp pc) M v.keepR outp)
      (At 0x80004fb4#64 (cL sp pc) (writeLog M [(sp - 64, 8, 0#64), (pc + 8, 4, BitVec.ofNat 64 1)])
        v.keepR outp) := by
  addd_ctx
  seg_step adddB3 0x80004fb4#64 ([] : List (List (BitVec 8))) [2, 8, 10] abiKeysR [sdL] [cL] [] hc

/-- The big branch's epilogue (`4fb8`): reload the spilled `MP_OKAY`, restore, return. -/
theorem br_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M mpAddDBase mpAddDCode) (hf : RFacts M ra s0 sp) (he : bytesT8 M (sp - 64) = 0#64) :
    Triple (At 0x80004fb8#64 (rL sp) M v.keepR outp)
      (At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] (writeLog M []) v.keepR outp) := by
  addd_ctx
  have hra := hf.ra_al
  have h0 : bytesT8 M (sp - 64 + 0) = 0#64 := by rw [Nat.add_zero]; exact he
  have h1 : bytesT8 M (sp - 64 + 56) = ra := by rw [show sp - 64 + 56 = sp - 8 by omega]; exact hf.ra_v
  have h2 : bytesT8 M (sp - 64 + 48) = s0 := by rw [show sp - 64 + 48 = sp - 16 by omega]; exact hf.s0_v
  seg_step adddBR ra [rd8 M (sp - 64 + 0), rd8 M (sp - 64 + 56), rd8 M (sp - 64 + 48)] [2] abiKeysR [rL] []
    [h0, h1, h2] hc

/-! ## The calls -/

/-- The callee-saved registers the callees see: this frame's `sp`, `s0 = c`. -/
def calleeAbi (v : Abi) (sp pc : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 64), s0 := BitVec.ofNat 64 pc }

/-- `memset(c->dp + n, 0, 4 (oldused - n))` at `4ed8`, back at `4edc`. -/
theorem memset_call (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp n ou : Nat) (M : Mem)
    (hc : CodeAt M mpAddDBase mpAddDCode) (hP : Memset.Pre M (cdp + 4 * n) 0 (4 * (ou - n))) :
    Triple (At 0x80004ed8#64 (msL ra sp pc cdp n ou) M v.keepR outp)
      (fun c => ∃ M', At 0x80004edc#64 (mL sp pc) M' v.keepR outp c ∧
        Memset.Post M (cdp + 4 * n) (4 * (ou - n)) 0#8 M') := by
  refine Triple.seq (jal_at (pc := 0x80004ed8#64) (w := 0x4cc040ef#32) (imm := 0x044cc#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc),
        (10, BitVec.ofNat 64 (cdp + 4 * n)), (11, 0#64), (12, BitVec.ofNat 64 (4 * (ou - n)))])
      (hc.word (a := (0x80004ed8#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [msL]) (by simp [keysG]) (by simp [Abi.keepR, sKeepL, keysG])) ?_
  refine Triple.conseq (Memset.correct_zero 0x80004edc#64 (calleeAbi v sp pc) outp M _ _ (by decide) hP)
    (fun c h => ?_) (fun c ⟨M', hat, hpost⟩ => ⟨M', hat.reshape ?_ ?_, hpost⟩)
  · have hpc : (0x80004ed8#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x044cc#21) = Memset.entry := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [Memset.entryL, Sail.BitVec.addInt]
    · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]
  · simp [mL, Abi.keep, calleeAbi]
  · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]

/-- `mp_clamp(c)` at `4ee0`, back at `4ee4`. -/
theorem clamp_call1 (v : Abi) (outp : Array String) (sp pc cdp : Nat) (cm : MpInt) (M : Mem)
    (hc : CodeAt M mpAddDBase mpAddDCode) (hP : Clamp.Pre M pc cdp cm) :
    Triple (At 0x80004ee0#64 (cL sp pc) M v.keepR outp)
      (fun c => ∃ a' M', At 0x80004ee4#64 (rL sp) M' v.keepR outp c ∧ Clamp.Post M pc cdp cm a' M') := by
  refine Triple.seq (jal_at (pc := 0x80004ee0#64) (w := 0x0f8000ef#32) (imm := 0x000f8#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pc)])
      (hc.word (a := (0x80004ee0#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [cL]) (by simp [keysG]) (by simp [Abi.keepR, sKeepL, keysG])) ?_
  refine Triple.conseq (Clamp.correct 0x80004ee4#64 (calleeAbi v sp pc) outp pc cdp cm M (by decide) hP)
    (fun c h => ?_) (fun c ⟨a', M', hat, hpost⟩ => ⟨a', M', hat.reshape ?_ ?_, hpost⟩)
  · have hpc : (0x80004ee0#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x000f8#21) = Clamp.entry := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [Sail.BitVec.addInt]
    · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]
  · simp [rL, Abi.keep, calleeAbi]
  · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]

/-- `mp_clamp(c)` at `4fb4`, back at `4fb8`. -/
theorem clamp_call2 (v : Abi) (outp : Array String) (sp pc cdp : Nat) (cm : MpInt) (M : Mem)
    (hc : CodeAt M mpAddDBase mpAddDCode) (hP : Clamp.Pre M pc cdp cm) :
    Triple (At 0x80004fb4#64 (cL sp pc) M v.keepR outp)
      (fun c => ∃ a' M', At 0x80004fb8#64 (rL sp) M' v.keepR outp c ∧ Clamp.Post M pc cdp cm a' M') := by
  refine Triple.seq (jal_at (pc := 0x80004fb4#64) (w := 0x024000ef#32) (imm := 0x00024#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pc)])
      (hc.word (a := (0x80004fb4#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [cL]) (by simp [keysG]) (by simp [Abi.keepR, sKeepL, keysG])) ?_
  refine Triple.conseq (Clamp.correct 0x80004fb8#64 (calleeAbi v sp pc) outp pc cdp cm M (by decide) hP)
    (fun c h => ?_) (fun c ⟨a', M', hat, hpost⟩ => ⟨a', M', hat.reshape ?_ ?_, hpost⟩)
  · have hpc : (0x80004fb4#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x00024#21) = Clamp.entry := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [Sail.BitVec.addInt]
    · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]
  · simp [rL, Abi.keep, calleeAbi]
  · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]

end Tom.Machine.Fn.AddD
