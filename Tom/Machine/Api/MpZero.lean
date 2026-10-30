import Tom.Machine.Api.Un
import Tom.Machine.Fn.MpZero
import Tom.Spec.Set

/-!
# `mp_zero`: the standard contract

From the entry, `mp_zero(a)` with `a` shaped returns to `ra` with
`ZeroPost a a'` (so `a'` is a valid zero), the callee-saved registers kept,
and memory changed only in `a` (`Un.ws`; it uses no stack: depth 0, the
tail-called `memset` uses none either). Regions as `Api/Un.lean`.
-/

namespace Tom.Machine.Api.MpZero

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Un

abbrev lay (sp pa adp : Nat) (a : MpInt) := Un.lay 0 sp pa adp a

/-- What `mp_zero(a)` needs. -/
structure Pre (m : Mem) (sp pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp a) isW

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp : Nat) (a a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  zero : ZeroPost a a'
  frame : Frm (lay sp pa adp a) ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra)] M v.keep outp cf ∧ Post m sp pa adp a a' M

def entry : BitVec 64 := 0x80002178#64

/-- **`mp_zero` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {ra : BitVec 64},
    Pre m sp pa adp a ra →
    Triple (At entry (Fn.MpZero.entryL ra pa) m v.keep outp) (Ret m v outp sp pa adp a ra)

end Tom.Machine.Api.MpZero
