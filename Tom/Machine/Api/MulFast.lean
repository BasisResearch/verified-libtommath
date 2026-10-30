import Tom.Machine.Api.Bin
import Tom.Machine.Api.Two
import Tom.Machine.Fn.MulFast
import Tom.Spec.Mul

/-!
# `s_mp_mul_digs_fast`: the standard contracts

From the entry, `s_mp_mul_digs_fast(a, b, c, digs)` under the C's conditions
(`digs < MP_WARRAY = 512`, `min(a->used, b->used) ≤ MP_MAXFAST = 256`, so no
column overflows 64 bits) with `c->alloc ≥ digs` (no `mp_grow`, D5) returns
`MP_OKAY` with `MulFastPost a b c c' digs` (`MulFastPost.spec`: `|c'| = |a| |b|
mod radix^min(digs, a->used + b->used)`, valid), the callee-saved registers
restored, and memory changed only in the stack `[sp - 2192, sp)` (its frame,
with `W[MP_WARRAY]`; `__muldi3`, `memcpy`, `memset`, `mp_clamp` use none) and
`c`. `a->used + b->used < 2^30` keeps the C's `int` sums small.

Three placements: distinct operands (`Statement`, regions `Api/Bin.lean`), and
`c = a` or `c = b` (`StatementInPlaceA`/`StatementInPlaceB`, regions
`Api/Two.lean` with the destination written: `mp_mul(&q, mu, &q)`,
`mp_sqr`'s aliased routes); the comba loop reads both operands into `W`
before it writes `c`.
-/

namespace Tom.Machine.Api.MulFast

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

def entry : BitVec 64 := 0x800042f0#64

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = c`, `a3 = digs`. -/
def entryL (ra s0 : BitVec 64) (sp pa pb pc dg : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb),
   (12, BitVec.ofNat 64 pc), (13, BitVec.ofNat 64 dg)]

/-- The C's conditions on the operands. -/
structure Cond (a b : MpInt) (dg : Nat) : Prop where
  dg_w : dg < 512
  maxf : min a.used b.used ≤ 256
  uab : a.used + b.used < 2 ^ 30

abbrev lay (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt) := Bin.lay 2192 sp pa adp pb bdp pc cdp a b c

/-- What `s_mp_mul_digs_fast(a, b, c, digs)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp pc cdp dg : Nat) (a b c : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  rc : MpAt m pc cdp c
  sa : a.ShapeU
  sb : b.ShapeU
  sc : c.Shape
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  gc : MpGeom pc cdp c.alloc
  cond : Cond a b dg
  room : dg ≤ c.alloc
  rs : Ram (sp - 2192) 2192
  sp_al : sp % 16 = 0
  sp_ge : 2192 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp pc cdp a b c) Bin.isW

structure Post (m : Mem) (sp pa adp pb bdp pc cdp dg : Nat) (a b c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  fast : MulFastPost a b c c' dg
  frame : Frm (lay sp pa adp pb bdp pc cdp a b c) Bin.ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp pc cdp dg : Nat) (a b c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp pc cdp dg a b c c' M

/-- **`s_mp_mul_digs_fast` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp dg : Nat}
    {a b c : MpInt} {ra s0 : BitVec 64}, Pre m sp pa adp pb bdp pc cdp dg a b c ra →
    Triple (At entry (entryL ra s0 sp pa pb pc dg) m v.keepR outp)
      (Ret m v outp sp pa adp pb bdp pc cdp dg a b c ra s0)

/-! ## In place -/

/-- Two operands, `x` read, `y` the destination (`Two`'s regions, `y` written). -/
structure PreI (m : Mem) (sp px xdp py ydp dg : Nat) (x y : MpInt) (ra : BitVec 64) : Prop where
  rx : MpAt m px xdp x
  ry : MpAt m py ydp y
  sx : x.Shape
  sy : y.Shape
  gx : MpGeom px xdp x.alloc
  gy : MpGeom py ydp y.alloc
  room : dg ≤ y.alloc
  rs : Ram (sp - 2192) 2192
  sp_al : sp % 16 = 0
  sp_ge : 2192 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (Two.lay 2192 sp px xdp py ydp x y) Two.isW

structure PostI (m : Mem) (sp px xdp py ydp : Nat) (x y y' : MpInt) (M : Mem) (P : Prop) : Prop where
  repr : MpAt M py ydp y'
  fast : P
  frame : Frm (Two.lay 2192 sp px xdp py ydp x y) Two.ws m M

/-- **`s_mp_mul_digs_fast(a, b, a, digs)`**: `c = a`. -/
def StatementInPlaceA : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp dg : Nat}
    {a b : MpInt} {ra s0 : BitVec 64}, PreI m sp pb bdp pa adp dg b a ra → Cond a b dg →
    Triple (At entry (entryL ra s0 sp pa pb pa dg) m v.keepR outp)
      (fun cf => ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
        PostI m sp pb bdp pa adp b a a' M (MulFastPost a b a a' dg))

/-- **`s_mp_mul_digs_fast(a, b, b, digs)`**: `c = b`. -/
def StatementInPlaceB : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp dg : Nat}
    {a b : MpInt} {ra s0 : BitVec 64}, PreI m sp pa adp pb bdp dg a b ra → Cond a b dg →
    Triple (At entry (entryL ra s0 sp pa pb pb dg) m v.keepR outp)
      (fun cf => ∃ b' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
        PostI m sp pa adp pb bdp a b b' M (MulFastPost a b b b' dg))

end Tom.Machine.Api.MulFast
