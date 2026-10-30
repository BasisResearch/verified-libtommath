import Tom.Machine.Api.BinA
import Tom.Machine.Fn.MontNorm
import Tom.Spec.Mont

/-!
# `mp_montgomery_calc_normalization`: the standard contract

From the entry, `mp_montgomery_calc_normalization(a, b)` with `a` shaped, `b` valid,
odd and `> 1` (a Montgomery modulus), distinct (D6), `28 b->used < 2^31` (the C's
`int` arithmetic of `mp_count_bits` and the exponent) and `b->used + 1 ≤ a->alloc`
(so neither `mp_2expt`'s `mp_grow` nor `mp_mul_2`'s reallocates, D5) returns
`MP_OKAY` with `NormPost b a'` (`NormPost.spec`: `a' = radix^b->used mod b`), the
callee-saved registers restored, and memory changed only in the stack
`[sp - 112, sp)` (its own frame of 64 bytes and the 48 of the deepest callee,
`mp_2expt` or `s_mp_sub`) and `a`. Regions as `Api/BinA.lean` (`isWA`: `a` written,
`b` read).
-/

namespace Tom.Machine.Api.MontNorm

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.BinA

def entry : BitVec 64 := 0x800058b4#64

abbrev lay (sp pa adp pb bdp : Nat) (a b : MpInt) := BinA.lay 112 sp pa adp pb bdp a b

/-- What `mp_montgomery_calc_normalization(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  sa : a.Shape
  vb : b.Valid
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  odd : b.mag % 2 = 1
  gt1 : 1 < b.mag
  bits : Layout.digitBits * b.used < 2 ^ 31
  room : b.used + 1 ≤ a.alloc
  rs : Ram (sp - 112) 112
  sp_al : sp % 16 = 0
  sp_ge : 112 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp a b) isWA

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp : Nat) (a b a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  norm : Mont.NormPost b a'
  alloc : a'.alloc = a.alloc
  frame : Frm (lay sp pa adp pb bdp a b) wsA m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra s0 : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp a b a' M

/-- **`mp_montgomery_calc_normalization` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    Pre m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.MontNorm.entryL ra s0 sp pa pb) m v.keepR outp) (Ret m v outp sp pa adp pb bdp a b ra s0)

end Tom.Machine.Api.MontNorm
