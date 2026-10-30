import Tom.Machine.Api.Un
import Tom.Machine.Fn.Expt2
import Tom.Spec.Expt2

/-!
# `mp_2expt`: the standard contract

From the entry, `mp_2expt(a, b)` with `a` shaped, `0 ≤ b < 2^31` (the C's `int b`
when nonnegative) and `b / 28 + 1 ≤ a->alloc` (so `mp_grow` does not reallocate, D5)
returns `MP_OKAY` with `Expt2Post a b a'` (`Expt2Post.spec`: `a'` valid, `a' = 2^b`),
the callee-saved registers restored, and memory changed only in `Un.ws`: the stack
`[sp - 48, sp)` (its own frame; `mp_zero`, `mp_grow` with room and libgcc use none)
and `a`. Regions as `Api/Un.lean`.
-/

namespace Tom.Machine.Api.Expt2

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Un

def entry : BitVec 64 := 0x800076d4#64

abbrev lay (sp pa adp : Nat) (a : MpInt) := Un.lay 48 sp pa adp a

/-- What `mp_2expt(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  b_lt : b < 2 ^ 31
  room : b / Layout.digitBits + 1 ≤ a.alloc
  rs : Ram (sp - 48) 48
  sp_al : sp % 16 = 0
  sp_ge : 48 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp a) isW

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  expt : Expt2Post a b a'
  frame : Frm (lay sp pa adp a) ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra s0 : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp a b a' M

/-- **`mp_2expt` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {b : Nat} {ra s0 : BitVec 64},
    Pre m sp pa adp a b ra →
    Triple (At entry (Fn.Expt2.entryL ra s0 sp pa b) m v.keepR outp) (Ret m v outp sp pa adp a b ra s0)

end Tom.Machine.Api.Expt2
