import Tom.Machine.Api.Two
import Tom.Machine.Api.Un
import Tom.Machine.Fn.Mul2
import Tom.Spec.Shift

/-!
# `mp_mul_2`: the standard contract

From the entry, `mp_mul_2(a, b)` with `a` valid, `b` shaped and with room
for `a->used + 1` digits (so `mp_grow` is not called, D5), `a` and `b`
disjoint (D6), returns `MP_OKAY` with `Mul2Post a b b'` (so `b'` valid and
`b' = 2 a`, `Mul2Post.spec`), the callee-saved registers restored, and
memory changed only in `Two.ws`: the stack `[sp - 32, sp)` (its own frame;
`memset` uses none) and `b`. Regions as `Tom/Machine/Api/Two.lean`.

`StatementInPlace` is the call with `b = a` (same struct, same digits), the
form most libtommath callers use, over `Api/Un.lean`'s regions.
-/

namespace Tom.Machine.Api.Mul2

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Two

abbrev lay (sp pa adp pb bdp : Nat) (a b : MpInt) := Two.lay 32 sp pa adp pb bdp a b

/-- What `mp_mul_2(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  va : a.Valid
  sb : b.Shape
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  room : a.used + 1 ≤ b.alloc
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp a b) isW

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp : Nat) (a b b' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pb bdp b'
  mul2 : Mul2Post a b b'
  frame : Frm (lay sp pa adp pb bdp a b) ws m M

/-- The entry registers: `a0 = a`, `a1 = b`. -/
def entryL (ra s0 : BitVec 64) (sp pa pb : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)]

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ b' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp a b b' M

def entry : BitVec 64 := 0x80005ca0#64

/-- **`mp_mul_2` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat}
    {a b : MpInt} {ra s0 : BitVec 64}, Pre m sp pa adp pb bdp a b ra →
    Triple (At entry (entryL ra s0 sp pa pb) m v.keepR outp)
      (Ret m v outp sp pa adp pb bdp a b ra s0)

/-! ## In place: `mp_mul_2(a, a)` -/

/-- The regions of the in-place call (`Api/Un.lean`: `a` written). -/
abbrev layI (sp pa adp : Nat) (a : MpInt) := Un.lay 32 sp pa adp a

/-- What `mp_mul_2(a, a)` needs. -/
structure PreI (m : Mem) (sp pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  va : a.Valid
  ga : MpGeom pa adp a.alloc
  room : a.used + 1 ≤ a.alloc
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (layI sp pa adp a) Un.isW

/-- What it leaves. -/
structure PostI (m : Mem) (sp pa adp : Nat) (a a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  mul2 : Mul2Post a a a'
  frame : Frm (layI sp pa adp a) Un.ws m M

def RetI (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostI m sp pa adp a a' M

/-- **`mp_mul_2(a, a)` on the machine.** -/
def StatementInPlace : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {ra s0 : BitVec 64},
    PreI m sp pa adp a ra →
    Triple (At entry (entryL ra s0 sp pa pa) m v.keepR outp) (RetI m v outp sp pa adp a ra s0)

end Tom.Machine.Api.Mul2
