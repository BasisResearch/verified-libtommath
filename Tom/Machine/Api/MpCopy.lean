import Tom.Machine.Api.Two
import Tom.Machine.Fn.MpCopy
import Tom.Spec.Set

/-!
# `mp_copy`: the standard contract

From the entry, `mp_copy(a, b)` with `a`, `b` shaped, `a`'s sign
`MP_ZPOS`/`MP_NEG`, distinct (the layout
keeps their structs apart, D6) and `a->used ≤ b->alloc` (so no `mp_grow`,
D5) returns `MP_OKAY` with `CopyPost a b b'` (for a valid `a`, `b'` is
valid with `a`'s value), the callee-saved registers restored, and memory
changed only in `Two.ws`: the stack `[sp - 32, sp)` (its frame; the called
`memset` uses none) and `b`. Regions as `Api/Two.lean`.

`AliasStatement`: `mp_copy(a, a)` returns `MP_OKAY` at once, memory untouched.
-/

namespace Tom.Machine.Api.MpCopy

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Two

abbrev lay (sp pa adp pb bdp : Nat) (a b : MpInt) := Two.lay 32 sp pa adp pb bdp a b

/-- What `mp_copy(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  sa : a.Shape
  sb : b.Shape
  asign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  room : a.used ≤ b.alloc
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp a b) isW

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp : Nat) (a b b' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pb bdp b'
  copy : CopyPost a b b'
  frame : Frm (lay sp pa adp pb bdp a b) ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ b' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp a b b' M

def entry : BitVec 64 := 0x800007e0#64

/-- **`mp_copy` on the machine** (distinct operands). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    Pre m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.MpCopy.entryL ra s0 sp pa pb) m v.keepR outp) (Ret m v outp sp pa adp pb bdp a b ra s0)

/-- **`mp_copy(a, a)` on the machine**: `MP_OKAY`, nothing written. -/
def AliasStatement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa : Nat} {ra s0 : BitVec 64},
    ra.toNat % 4 = 0 → Img m →
    Triple (At entry (Fn.MpCopy.entryL ra s0 sp pa pa) m v.keepR outp)
      (At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] m v.keepR outp)

end Tom.Machine.Api.MpCopy
