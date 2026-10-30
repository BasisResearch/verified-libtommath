import Tom.Machine.Api.Two
import Tom.Spec.Reduce

/-!
# `s_mp_mul_high_digs_fast`: the standard contract, in place (`c = a`)

`mp_reduce` calls `s_mp_mul_high_digs(&q, mu, &q, um)`, which hands the work to
`s_mp_mul_high_digs_fast(a, b, a, digs)` when the columns fit: the in-place
placement `c = a`. From the entry, under the C's conditions on the operands
(`Cond`: `digs ≤ a->used + b->used ≤ MP_WARRAY = 512`, so `W[ix]` stays in the
array; `min(a->used, b->used) ≤ MP_MAXFAST = 256`, so no column overflows
`mp_word`; `b->used ≥ 1`) with `a->alloc ≥ a->used + b->used` (no `mp_grow`,
D5), it returns `MP_OKAY` with `MulHighFastPost a b a a' digs`
(`MulHighFastPost.spec`: `a'` valid, `|a'| = |a| mod radix^digs + high
product`), the callee-saved registers restored, and memory changed only in
`Two.ws`: the stack `[sp - 2192, sp)` (its frame, with `W[MP_WARRAY]`;
`__muldi3`, `memcpy`, `mp_clamp` use none) and `a`. Regions as `Api/Two.lean`
with `b` read (Two's `a`) and `a` written (Two's `b`); the comba loop reads
both operands into `W` before `memcpy` writes `a`.
-/

namespace Tom.Machine.Api.MulHighFast

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Reduce

def entry : BitVec 64 := 0x80006be4#64

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = c`, `a3 = digs`. -/
def entryL (ra s0 : BitVec 64) (sp pa pb pc dg : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb),
   (12, BitVec.ofNat 64 pc), (13, BitVec.ofNat 64 dg)]

/-- The C's conditions on the operands. -/
structure Cond (a b : MpInt) (dg : Nat) : Prop where
  dg_le : dg ≤ a.used + b.used
  pa_w : a.used + b.used ≤ 512
  maxf : min a.used b.used ≤ 256
  ub_pos : 1 ≤ b.used

/-- `b` read (Two's `a`), `a` written (Two's `b`). -/
abbrev lay (sp pa adp pb bdp : Nat) (a b : MpInt) := Two.lay 2192 sp pb bdp pa adp b a

/-- What `s_mp_mul_high_digs_fast(a, b, a, digs)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp dg : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  sa : a.Shape
  sb : b.Shape
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  cond : Cond a b dg
  room : a.used + b.used ≤ a.alloc
  rs : Ram (sp - 2192) 2192
  sp_al : sp % 16 = 0
  sp_ge : 2192 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp a b) Two.isW

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp dg : Nat) (a b a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  fast : MulHighFastPost a b a a' dg
  frame : Frm (lay sp pa adp pb bdp a b) Two.ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp dg : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp dg a b a' M

/-- **`s_mp_mul_high_digs_fast(a, b, a, digs)` on the machine** (`c = a`). -/
def StatementInPlace : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp dg : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    Pre m sp pa adp pb bdp dg a b ra →
    Triple (At entry (entryL ra s0 sp pa pb pa dg) m v.keepR outp) (Ret m v outp sp pa adp pb bdp dg a b ra s0)

end Tom.Machine.Api.MulHighFast
