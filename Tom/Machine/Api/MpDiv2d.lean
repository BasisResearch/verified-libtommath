import Tom.Machine.Api.Two
import Tom.Machine.Api.Un
import Tom.Machine.Fn.MpDiv2d
import Tom.Spec.Div2d

/-!
# `mp_div_2d(a, b, c, NULL)`: the standard contracts

From the entry, `mp_div_2d(a, b, c, d)` with `d = NULL` (`a3 = 0`), `a` valid,
the shift count `0 ≤ b < 2^31` (the C's `int b` when nonnegative; `b = 0` takes
the C's `b <= 0` path, `mp_copy(a, c)` only) and `a->used ≤ c->alloc` (so
`mp_copy` does not call `mp_grow`, D5) returns `MP_OKAY` with
`Div2dPost a b c c'` (`Div2dPost.spec`: `c'` valid, `|c'| = |a| / 2^b`, the sign
of `a`), the callee-saved registers restored, and memory changed only in the
stack `[sp - 96, sp)` (its own frame of 64 bytes and the 32 of the called
`mp_copy` or `mp_rshd`; `mp_clamp` and libgcc use none) and `c`.

* `Statement`: `a`, `c` distinct (D6), `c` shaped; regions as `Api/Two.lean`
  (`a` read, `c` written).
* `StatementInPlace`: `mp_div_2d(a, b, a, NULL)` (`mp_div`'s `mp_div_2d(&x, norm,
  &x, NULL)`, `mp_gcd`'s): `Div2dPost a b a a'`; regions as `Api/Un.lean`.

`d != NULL` is not covered: the only callers that pass it (`mp_reduce_2k`,
`mp_reduce_2k_l`) pass `d = a`, whose `mp_mod_2d(a, b, a)` is in place.
-/

namespace Tom.Machine.Api.MpDiv2d

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

def entry : BitVec 64 := 0x8000520c#64

abbrev lay (sp pa adp pc cdp : Nat) (a c : MpInt) := Two.lay 96 sp pa adp pc cdp a c

/-- What `mp_div_2d(a, b, c, NULL)` needs (distinct operands). -/
structure Pre (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rc : MpAt m pc cdp c
  va : a.Valid
  sc : c.Shape
  ga : MpGeom pa adp a.alloc
  gc : MpGeom pc cdp c.alloc
  b_lt : b < 2 ^ 31
  room : a.used ≤ c.alloc
  rs : Ram (sp - 96) 96
  sp_al : sp % 16 = 0
  sp_ge : 96 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pc cdp a c) Two.isW

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  div : Div2dPost a b c c'
  frame : Frm (lay sp pa adp pc cdp a c) Two.ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pc cdp a b c c' M

/-- **`mp_div_2d(a, b, c, NULL)` on the machine** (distinct operands). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat} {c : MpInt}
    {ra s0 : BitVec 64}, Pre m sp pa adp pc cdp a b c ra →
    Triple (At entry (Fn.MpDiv2d.entryL ra s0 sp pa b pc) m v.keepR outp)
      (Ret m v outp sp pa adp pc cdp a b c ra s0)

abbrev layI (sp pa adp : Nat) (a : MpInt) := Un.lay 96 sp pa adp a

/-- What `mp_div_2d(a, b, a, NULL)` needs. -/
structure PreI (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  va : a.Valid
  ga : MpGeom pa adp a.alloc
  b_lt : b < 2 ^ 31
  rs : Ram (sp - 96) 96
  sp_al : sp % 16 = 0
  sp_ge : 96 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (layI sp pa adp a) Un.isW

/-- What it leaves. -/
structure PostI (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  div : Div2dPost a b a a'
  frame : Frm (layI sp pa adp a) Un.ws m M

def RetI (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (b : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostI m sp pa adp a b a' M

/-- **`mp_div_2d(a, b, a, NULL)` on the machine** (in place). -/
def StatementInPlace : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {b : Nat} {ra s0 : BitVec 64},
    PreI m sp pa adp a b ra →
    Triple (At entry (Fn.MpDiv2d.entryL ra s0 sp pa b pa) m v.keepR outp) (RetI m v outp sp pa adp a b ra s0)

end Tom.Machine.Api.MpDiv2d
