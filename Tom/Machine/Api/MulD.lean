import Tom.Machine.Api.Two
import Tom.Machine.Api.Un
import Tom.Machine.Fn.MulD
import Tom.Spec.Mul

/-!
# `mp_mul_d`: the standard contracts

From the entry, `mp_mul_d(a, b, c)` with `a` shaped, its sign a sign, `b` a
digit and `c` with room for `a->used + 1` digits (so `mp_grow` is not called,
D5) returns `MP_OKAY` with `MulDPost a b c c'` (`MulDPost.spec`: `c' = a * b`,
valid), the callee-saved registers restored, and memory changed only in
`Two.ws`: the stack `[sp - 80, sp)` (its own frame; `__muldi3`, `memset` and
`mp_clamp` use none) and `c`. Regions as `Tom/Machine/Api/Two.lean` with
`b := c`.

`StatementInPlace`: `mp_mul_d(a, b, a)` (`mp_reduce_2k`, `mp_div`), over
`Un`'s regions: `a` written, `MulDPost a b a a'`.
-/

namespace Tom.Machine.Api.MulD

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

abbrev lay (sp pa adp pc cdp : Nat) (a c : MpInt) := Two.lay 80 sp pa adp pc cdp a c

/-- What `mp_mul_d(a, b, c)` needs. -/
structure Pre (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt) (ra : BitVec 64) :
    Prop where
  ra_ : MpAt m pa adp a
  rc : MpAt m pc cdp c
  sa : a.Shape
  asign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg
  sc : c.Shape
  hb : b < radix
  ga : MpGeom pa adp a.alloc
  gc : MpGeom pc cdp c.alloc
  room : a.used + 1 ≤ c.alloc
  rs : Ram (sp - 80) 80
  sp_al : sp % 16 = 0
  sp_ge : 80 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pc cdp a c) Two.isW

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  muld : MulDPost a b c c'
  frame : Frm (lay sp pa adp pc cdp a c) Two.ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pc cdp a b c c' M

def entry : BitVec 64 := 0x800019fc#64

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = c`. -/
def entryL (ra s0 : BitVec 64) (sp pa b pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 b),
   (12, BitVec.ofNat 64 pc)]

/-- **`mp_mul_d` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp b : Nat}
    {a c : MpInt} {ra s0 : BitVec 64}, Pre m sp pa adp pc cdp a b c ra →
    Triple (At entry (entryL ra s0 sp pa b pc) m v.keepR outp)
      (Ret m v outp sp pa adp pc cdp a b c ra s0)

/-! ## In place: `mp_mul_d(a, b, a)` -/

abbrev layI (sp pa adp : Nat) (a : MpInt) := Un.lay 80 sp pa adp a

/-- What `mp_mul_d(a, b, a)` needs. -/
structure PreI (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  asign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg
  hb : b < radix
  ga : MpGeom pa adp a.alloc
  room : a.used + 1 ≤ a.alloc
  rs : Ram (sp - 80) 80
  sp_al : sp % 16 = 0
  sp_ge : 80 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (layI sp pa adp a) Un.isW

structure PostI (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  muld : MulDPost a b a a'
  frame : Frm (layI sp pa adp a) Un.ws m M

def RetI (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (b : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostI m sp pa adp a b a' M

/-- **`mp_mul_d(a, b, a)` on the machine.** -/
def StatementInPlace : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp b : Nat}
    {a : MpInt} {ra s0 : BitVec 64}, PreI m sp pa adp a b ra →
    Triple (At entry (entryL ra s0 sp pa b pa) m v.keepR outp)
      (RetI m v outp sp pa adp a b ra s0)

end Tom.Machine.Api.MulD
