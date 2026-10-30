import Tom.Machine.Api.Bin
import Tom.Machine.Fn.SSub
import Tom.Spec.Signed

/-!
# `mp_sub`: the standard contract

From the entry, `mp_sub(a, b, c)` with `a`, `b` valid and `c` with room for
`max + 1` digits (so neither `s_mp_add` nor `s_mp_sub` calls `mp_grow`, D5)
returns `MP_OKAY` with `SubPost a b c c'`, the callee-saved registers
restored, and memory changed only in `Bin.ws`: the stack `[sp - 64, sp)`
(its own frame of 48 bytes, and the frame of the tail-called `s_mp_add`)
and `c`. Regions as `Tom/Machine/Api/Bin.lean`.
-/

namespace Tom.Machine.Api.MpSub

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Bin

abbrev lay (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt) := Bin.lay 64 sp pa adp pb bdp pc cdp a b c

/-- What `mp_sub(a, b, c)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  rc : MpAt m pc cdp c
  va : a.Valid
  vb : b.Valid
  sc : c.Shape
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  gc : MpGeom pc cdp c.alloc
  room : max a.used b.used + 1 ≤ c.alloc
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp pc cdp a b c) isW

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp pc cdp : Nat) (a b c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  sub : SubPost a b c c'
  frame : Frm (lay sp pa adp pb bdp pc cdp a b c) ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp pc cdp a b c c' M

def entry : BitVec 64 := 0x80001ef4#64

/-- **`mp_sub` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat}
    {a b c : MpInt} {ra s0 : BitVec 64}, Pre m sp pa adp pb bdp pc cdp a b c ra →
    Triple (At entry (Fn.SSub.entryL ra s0 sp pa pb pc) m v.keepR outp)
      (Ret m v outp sp pa adp pb bdp pc cdp a b c ra s0)

end Tom.Machine.Api.MpSub
