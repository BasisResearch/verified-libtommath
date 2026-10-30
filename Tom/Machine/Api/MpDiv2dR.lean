import Tom.Machine.Api.Two
import Tom.Spec.Div2d

/-!
# `mp_div_2d(a, b, c, d)` with `d != NULL`: the standard contract (`d = a`)

`Api/MpDiv2d.lean` is the `d = NULL` case. Every caller in the image that passes a
remainder (`mp_reduce_2k`, `mp_reduce_2k_l`: `mp_div_2d(a, p, &q, a)`) passes `d = a`, so
this is the contract of `mp_div_2d(a, b, c, a)`: `mp_copy(a, c)`, then `mp_mod_2d(a, b, a)`
(in place, `Api/MpMod2dI.lean`), then `c`'s shift (`mp_rshd`, the bit loop, `mp_clamp`). From
the entry, with `a` valid, `c` shaped, distinct (D6), `0 < b < 2^31`, `28 a->used < 2^31` and
`a->used ≤ c->alloc` (D5), it returns `MP_OKAY` with `Div2dPost a b c c'` in `c`
(`Div2dPost.spec`: `|c'| = |a| / 2^b`) and `Mod2dPost a b a a'` in `a` (`Mod2dPost.spec`:
`|a'| = |a| mod 2^b`), both with `a`'s sign and their `alloc`/`dp` kept, the callee-saved
registers restored, and memory changed only in the stack `[sp - 112, sp)` (the 64-byte frame and
the 48 of `mp_mod_2d`; `mp_copy`, `mp_rshd` use 32, `mp_clamp` and libgcc none), `a` and `c`.
Regions as `Api/Two.lean` with both operands written (`isW2`).
-/

namespace Tom.Machine.Api.MpDiv2dR

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

def entry : BitVec 64 := 0x8000520c#64

/-- The stack depth: the 64-byte frame and `mp_mod_2d`'s 48. -/
abbrev F : Nat := 112

abbrev lay (sp pa adp pc cdp : Nat) (a c : MpInt) := Two.lay 112 sp pa adp pc cdp a c

/-- The entry: `a0 = a`, `a1 = b`, `a2 = c`, `a3 = d = a`. -/
def entryL (ra s0 : BitVec 64) (sp pa b pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 b),
   (12, BitVec.ofNat 64 pc), (13, BitVec.ofNat 64 pa)]

/-- What `mp_div_2d(a, b, c, a)` needs. -/
structure Pre (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rc : MpAt m pc cdp c
  va : a.Valid
  sc : c.Shape
  ga : MpGeom pa adp a.alloc
  gc : MpGeom pc cdp c.alloc
  /-- `b > 0`: the shifting path. Both callers pass `p = mp_count_bits(n)` of a nonzero
  modulus; `b ≤ 0` (`mp_copy(a, c)`, `mp_zero(d)`) is not covered. -/
  b_pos : 0 < b
  /-- The C's `int b`. -/
  b_lt : b < 2 ^ 31
  /-- `mp_mod_2d`'s `a->used * MP_DIGIT_BIT` does not overflow (`Api.MpMod2dI`). -/
  bits : Layout.digitBits * a.used < 2 ^ 31
  /-- D5: `mp_copy(a, c)` does not call `mp_grow`. -/
  room : a.used ≤ c.alloc
  rs : Ram (sp - 112) 112
  sp_al : sp % 16 = 0
  sp_ge : 112 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pc cdp a c) Two.isW2

/-- What it leaves: the quotient in `c`, the remainder in `a`. -/
structure Post (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c a' c' : MpInt) (M : Mem) : Prop where
  reprA : MpAt M pa adp a'
  reprC : MpAt M pc cdp c'
  div : Div2dPost a b c c'
  mod : Mod2dPost a b a a'
  frame : Frm (lay sp pa adp pc cdp a c) Two.ws2 m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pc cdp a b c a' c' M

/-- **`mp_div_2d(a, b, c, a)` on the machine** (`d = a`, distinct from `c`). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat} {c : MpInt}
    {ra s0 : BitVec 64}, Pre m sp pa adp pc cdp a b c ra →
    Triple (At entry (entryL ra s0 sp pa b pc) m v.keepR outp) (Ret m v outp sp pa adp pc cdp a b c ra s0)

end Tom.Machine.Api.MpDiv2dR
