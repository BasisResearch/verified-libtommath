import Tom.Machine.Api.Two
import Tom.Machine.Api.Un
import Tom.Machine.Fn.SqrFast
import Tom.Spec.Mul

/-!
# `s_mp_sqr_fast`: the standard contracts

From the entry, `s_mp_sqr_fast(a, b)` under the C's condition
(`2 a->used + 1 < MP_WARRAY = 512`, which `mp_sqr` checks; it keeps every column
within 64 bits) with `b->alloc ≥ 2 a->used` (no `mp_grow`, D5) returns `MP_OKAY`
with `SqrFastPost a b b'` (`SqrFastPost.spec`: `|b'| = |a|²`, valid), the
callee-saved registers restored, and memory changed only in the stack
`[sp - 2208, sp)` (its frame, with `W[MP_WARRAY]`; `__muldi3`, `memset`,
`mp_clamp` use none) and `b`. Regions `Api/Two.lean` (`a` read, `b` written);
`StatementInPlace`: `s_mp_sqr_fast(a, a)` (`mp_sqr(&g, &g)`), regions
`Api/Un.lean` (`a` written): the column loop reads `a` into `W` before `a` is
written.
-/

namespace Tom.Machine.Api.SqrFast

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

def entry : BitVec 64 := 0x80007010#64

def entryL (ra s0 : BitVec 64) (sp pa pb : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)]

abbrev lay (sp pa adp pb bdp : Nat) (a b : MpInt) := Two.lay 2208 sp pa adp pb bdp a b

structure Pre (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  sa : a.Shape
  sb : b.Shape
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  warr : 2 * a.used + 1 < 512
  room : 2 * a.used ≤ b.alloc
  rs : Ram (sp - 2208) 2208
  sp_al : sp % 16 = 0
  sp_ge : 2208 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp a b) Two.isW

structure Post (m : Mem) (sp pa adp pb bdp : Nat) (a b b' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pb bdp b'
  sqr : SqrFastPost a b b'
  frame : Frm (lay sp pa adp pb bdp a b) Two.ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra s0 : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ b' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp a b b' M

/-- **`s_mp_sqr_fast` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    Pre m sp pa adp pb bdp a b ra →
    Triple (At entry (entryL ra s0 sp pa pb) m v.keepR outp) (Ret m v outp sp pa adp pb bdp a b ra s0)

/-! ## In place: `s_mp_sqr_fast(a, a)` -/

abbrev layI (sp pa adp : Nat) (a : MpInt) := Un.lay 2208 sp pa adp a

structure PreI (m : Mem) (sp pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  warr : 2 * a.used + 1 < 512
  room : 2 * a.used ≤ a.alloc
  rs : Ram (sp - 2208) 2208
  sp_al : sp % 16 = 0
  sp_ge : 2208 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (layI sp pa adp a) Un.isW

structure PostI (m : Mem) (sp pa adp : Nat) (a a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  sqr : SqrFastPost a a a'
  frame : Frm (layI sp pa adp a) Un.ws m M

/-- **`s_mp_sqr_fast(a, a)` on the machine.** -/
def StatementInPlace : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {ra s0 : BitVec 64},
    PreI m sp pa adp a ra →
    Triple (At entry (entryL ra s0 sp pa pa) m v.keepR outp)
      (fun cf => ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
        PostI m sp pa adp a a' M)

end Tom.Machine.Api.SqrFast
