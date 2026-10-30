import Tom.Machine.Api.Two
import Tom.Machine.Fn.MpMod2d
import Tom.Spec.Div2d

/-!
# `mp_mod_2d`: the standard contract

From the entry, `mp_mod_2d(a, b, c)` with `a` valid, `c` shaped, distinct
(the layout keeps their structs and digit arrays apart, D6), the shift count
`0 ≤ b < 2^31` (the C's `int b` when nonnegative; `b = 0` takes the C's
`b <= 0` path, `mp_zero(c)`), `a->used ≤ c->alloc` (so `mp_copy` does not call
`mp_grow`, D5) and `28 a->used < 2^31` (the C's `a->used * MP_DIGIT_BIT` does
not overflow, as `Api.CountBits`), returns `MP_OKAY` with `Mod2dPost a b c c'`
(`Mod2dPost.spec`: `c'` valid, `|c'| = |a| mod 2^b`, the sign of `a`), the
callee-saved registers restored, and memory changed only in `Two.ws`: the stack
`[sp - 80, sp)` (its own frame of 48 bytes and the 32 of the called or
tail-called `mp_copy`; `mp_zero`, `memset`, `mp_clamp` and libgcc use none) and
`c`. Regions as `Api/Two.lean` (`a` read, `c` written).
-/

namespace Tom.Machine.Api.MpMod2d

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Two

abbrev lay (sp pa adp pc cdp : Nat) (a c : MpInt) := Two.lay 80 sp pa adp pc cdp a c

/-- What `mp_mod_2d(a, b, c)` needs. -/
structure Pre (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rc : MpAt m pc cdp c
  va : a.Valid
  sc : c.Shape
  ga : MpGeom pa adp a.alloc
  gc : MpGeom pc cdp c.alloc
  b_lt : b < 2 ^ 31
  bits : Layout.digitBits * a.used < 2 ^ 31
  room : a.used ≤ c.alloc
  rs : Ram (sp - 80) 80
  sp_al : sp % 16 = 0
  sp_ge : 80 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pc cdp a c) isW

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  mod : Mod2dPost a b c c'
  frame : Frm (lay sp pa adp pc cdp a c) ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pc cdp a b c c' M

def entry : BitVec 64 := 0x800057a4#64

/-- **`mp_mod_2d` on the machine** (distinct operands). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat} {c : MpInt}
    {ra s0 : BitVec 64}, Pre m sp pa adp pc cdp a b c ra →
    Triple (At entry (Fn.MpMod2d.entryL ra s0 sp pa b pc) m v.keepR outp)
      (Ret m v outp sp pa adp pc cdp a b c ra s0)

end Tom.Machine.Api.MpMod2d
