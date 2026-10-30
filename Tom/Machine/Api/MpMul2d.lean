import Tom.Machine.Api.Two
import Tom.Machine.Fn.MpMul2d
import Tom.Spec.Div2d

/-!
# `mp_mul_2d`: the standard contract

From the entry, `mp_mul_2d(a, b, c)` with `a` valid, `c` shaped, distinct
(the layout keeps their structs and digit arrays apart, D6; the C skips
`mp_copy` only when `a == c`, a case this contract does not cover), the shift
count `0 ≤ b < 2^31` (the C's `int b` when nonnegative) and
`a->used + b / 28 + 1 ≤ c->alloc` (so neither `mp_copy` nor `mp_mul_2d` itself
calls `mp_grow`, and `mp_lshd` has room, D5), returns `MP_OKAY` with
`Mul2dPost a b c c'` (`Mul2dPost.spec`: `c'` valid, `c' = a * 2^b`), the
callee-saved registers restored, and memory changed only in `Two.ws`: the stack
`[sp - 80, sp)` (its own frame of 48 bytes and the 32 of `mp_copy` or
`mp_lshd`; `mp_clamp` and libgcc use none) and `c`. Regions as
`Api/Two.lean` (`a` read, `c` written).
-/

namespace Tom.Machine.Api.MpMul2d

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Two

abbrev lay (sp pa adp pc cdp : Nat) (a c : MpInt) := Two.lay 80 sp pa adp pc cdp a c

/-- What `mp_mul_2d(a, b, c)` needs. -/
structure Pre (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rc : MpAt m pc cdp c
  va : a.Valid
  sc : c.Shape
  ga : MpGeom pa adp a.alloc
  gc : MpGeom pc cdp c.alloc
  b_lt : b < 2 ^ 31
  room : a.used + b / Layout.digitBits + 1 ≤ c.alloc
  rs : Ram (sp - 80) 80
  sp_al : sp % 16 = 0
  sp_ge : 80 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pc cdp a c) isW

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  mul : Mul2dPost a b c c'
  frame : Frm (lay sp pa adp pc cdp a c) ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pc cdp a b c c' M

def entry : BitVec 64 := 0x80001758#64

/-- **`mp_mul_2d` on the machine** (distinct operands). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat} {c : MpInt}
    {ra s0 : BitVec 64}, Pre m sp pa adp pc cdp a b c ra →
    Triple (At entry (Fn.MpMul2d.entryL ra s0 sp pa b pc) m v.keepR outp)
      (Ret m v outp sp pa adp pc cdp a b c ra s0)

end Tom.Machine.Api.MpMul2d
