import Tom.Machine.Api.Un
import Tom.Machine.Fn.MpSet
import Tom.Spec.Set

/-!
# `mp_set`: the standard contract

From the entry, `mp_set(a, b)` with `a` shaped and `a->alloc ≥ 1` (the C
stores `dp[0]` unconditionally) returns to `ra` with `SetPost a (b mod 2^28) a'`
(so `a'` is valid with value `b & MP_MASK`), the callee-saved registers kept,
and memory changed only in `a` (`Un.ws`, stack depth 0). `b` is any 64-bit
register value `bn` (the C's `mp_digit` is masked by the code itself).
-/

namespace Tom.Machine.Api.MpSet

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Un

abbrev lay (sp pa adp : Nat) (a : MpInt) := Un.lay 0 sp pa adp a

/-- What `mp_set(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  room : 1 ≤ a.alloc
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp a) isW

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp : Nat) (a : MpInt) (bn : Nat) (a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  set : SetPost a (bn % radix) a'
  frame : Frm (lay sp pa adp a) ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (bn : Nat) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra)] M v.keep outp cf ∧ Post m sp pa adp a bn a' M

def entry : BitVec 64 := 0x80001eb0#64

/-- **`mp_set` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {bn : Nat} {ra : BitVec 64},
    Pre m sp pa adp a ra →
    Triple (At entry (Fn.MpSet.entryL ra pa bn) m v.keep outp) (Ret m v outp sp pa adp a bn ra)

end Tom.Machine.Api.MpSet
