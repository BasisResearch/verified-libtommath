import Tom.Machine.Api.Two
import Tom.Machine.Api.Un
import Tom.Machine.Fn.AddD
import Tom.Spec.Digit

/-!
# `mp_add_d`: the standard contract

From the entry, `mp_add_d(a, b, c)` with `a` valid, a digit `b < 2^28`, `c`
shaped and with room for `a->used + 1` digits (so `mp_grow` is not called,
D5), `a` and `c` disjoint (D6), returns `MP_OKAY` with `AddDPost a b c c'`
(so `c'` valid and `c' = a + b`, `AddDPost.spec`), the callee-saved registers
restored, and memory changed only in `Two.ws`: the stack (its own frame of
64 bytes and, for a negative `a`, the frame of `mp_sub_d`, which it calls on
a copy of `a` in its own frame) and `c`. The contract takes the stack depth
`F` as a parameter: `Statement` is for `F = 128`; the non-recursive
branches need `F = 64` (`Fn.AddD.pos_correct`).
-/

namespace Tom.Machine.Api.AddD

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Two

abbrev lay (F sp pa adp pc cdp : Nat) (a c : MpInt) := Two.lay F sp pa adp pc cdp a c

/-- What `mp_add_d(a, b, c)` needs, with a stack of depth `F`. -/
structure Pre (F : Nat) (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt) (ra : BitVec 64) :
    Prop where
  ra_ : MpAt m pa adp a
  rc : MpAt m pc cdp c
  va : a.Valid
  sc : c.Shape
  hb : b < radix
  ga : MpGeom pa adp a.alloc
  gc : MpGeom pc cdp c.alloc
  room : a.used + 1 ≤ c.alloc
  rs : Ram (sp - F) F
  sp_al : sp % 16 = 0
  sp_ge : F ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay F sp pa adp pc cdp a c) isW

/-- What it leaves. -/
structure Post (F : Nat) (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c c' : MpInt) (M : Mem) :
    Prop where
  repr : MpAt M pc cdp c'
  addd : AddDPost a b c c'
  frame : Frm (lay F sp pa adp pc cdp a c) ws m M

/-- The entry registers: `a0 = a`, `a1 = b`, `a2 = c`. -/
def entryL (ra s0 : BitVec 64) (sp pa b pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 b),
   (12, BitVec.ofNat 64 pc)]

def Ret (F : Nat) (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat)
    (c : MpInt) (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post F m sp pa adp pc cdp a b c c' M

def entry : BitVec 64 := 0x80004e30#64

/-- **`mp_add_d` on the machine** (stack depth 128: its frame and `mp_sub_d`'s). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat} {c : MpInt}
    {ra s0 : BitVec 64}, Pre 128 m sp pa adp pc cdp a b c ra →
    Triple (At entry (entryL ra s0 sp pa b pc) m v.keepR outp) (Ret 128 m v outp sp pa adp pc cdp a b c ra s0)

/-! ## In place: `mp_add_d(a, b, a)` -/

/-- The regions of the in-place call (`Api/Un.lean`: `a` written). -/
abbrev layI (F sp pa adp : Nat) (a : MpInt) := Un.lay F sp pa adp a

/-- What `mp_add_d(a, b, a)` needs, with a stack of depth `F`. -/
structure PreI (F : Nat) (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  va : a.Valid
  hb : b < radix
  ga : MpGeom pa adp a.alloc
  room : a.used + 1 ≤ a.alloc
  rs : Ram (sp - F) F
  sp_al : sp % 16 = 0
  sp_ge : F ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (layI F sp pa adp a) Un.isW

/-- What it leaves. -/
structure PostI (F : Nat) (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  addd : AddDPost a b a a'
  frame : Frm (layI F sp pa adp a) Un.ws m M

def RetI (F : Nat) (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (b : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostI F m sp pa adp a b a' M

/-- **`mp_add_d(a, b, a)` on the machine** (stack depth 128). Not proved yet for `a < 0`
(the recursive branch calls the other function with the digits of its `a_` and its
`c` aliased, a layout neither contract covers); `StatementInPlacePos` is. -/
def StatementInPlace : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {b : Nat} {ra s0 : BitVec 64},
    PreI 128 m sp pa adp a b ra →
    Triple (At entry (entryL ra s0 sp pa b pa) m v.keepR outp) (RetI 128 m v outp sp pa adp a b ra s0)

/-- **`mp_add_d(a, b, a)` on the machine for `a ≥ 0`** (any stack depth `F ≥ 64`). -/
def StatementInPlacePos : Prop :=
  ∀ {F : Nat} {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {b : Nat}
    {ra s0 : BitVec 64}, 64 ≤ F → PreI F m sp pa adp a b ra → a.sign = Layout.mpZpos →
    Triple (At entry (entryL ra s0 sp pa b pa) m v.keepR outp) (RetI F m v outp sp pa adp a b ra s0)

end Tom.Machine.Api.AddD
