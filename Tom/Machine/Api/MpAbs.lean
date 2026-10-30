import Tom.Machine.Api.Two
import Tom.Machine.Api.Un
import Tom.Machine.Fn.MpAbs
import Tom.Spec.Set

/-!
# `mp_abs`: the standard contract

From the entry, `mp_abs(a, b)` with `a`, `b` shaped, `a`'s sign
`MP_ZPOS`/`MP_NEG`, distinct (D6) and `a->used ≤ b->alloc` (D5) returns
`MP_OKAY` with `AbsPost a b b'` (for a valid `a`, `b'` is valid with value
`|a|`), the callee-saved registers restored, memory changed only in
`Two.ws` (stack depth 64: its frame of 32 and `mp_copy`'s).

`AliasStatement`: `mp_abs(a, a)` stores `a->sign := MP_ZPOS` and returns
`MP_OKAY` (regions `Un`'s, no stack).
-/

namespace Tom.Machine.Api.MpAbs

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

abbrev lay (sp pa adp pb bdp : Nat) (a b : MpInt) := Two.lay 64 sp pa adp pb bdp a b

/-- What `mp_abs(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  sa : a.Shape
  sb : b.Shape
  asign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  room : a.used ≤ b.alloc
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp a b) Two.isW

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp : Nat) (a b b' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pb bdp b'
  abs : AbsPost a b b'
  frame : Frm (lay sp pa adp pb bdp a b) Two.ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ b' M, At ra (Fn.MpAbs.retL ra s0 sp) M v.keepR outp cf ∧ Post m sp pa adp pb bdp a b b' M

def entry : BitVec 64 := 0x800005cc#64

/-- **`mp_abs` on the machine** (distinct operands). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    Pre m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.MpAbs.entryL ra s0 sp pa pb) m v.keepR outp) (Ret m v outp sp pa adp pb bdp a b ra s0)

/-- What `mp_abs(a, a)` needs. -/
structure APre (m : Mem) (sp pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (Un.lay 0 sp pa adp a) Un.isW

/-- What it leaves. -/
structure APost (m : Mem) (sp pa adp : Nat) (a a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  abs : AbsPost a a a'
  frame : Frm (Un.lay 0 sp pa adp a) Un.ws m M

/-- **`mp_abs(a, a)` on the machine.** -/
def AliasStatement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {ra s0 : BitVec 64},
    APre m sp pa adp a ra →
    Triple (At entry (Fn.MpAbs.entryL ra s0 sp pa pa) m v.keepR outp)
      (fun cf => ∃ a' M, At ra (Fn.MpAbs.retL ra s0 sp) M v.keepR outp cf ∧ APost m sp pa adp a a' M)

end Tom.Machine.Api.MpAbs
