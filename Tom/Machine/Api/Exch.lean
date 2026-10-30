import Tom.Machine.Api.Two
import Tom.Machine.Fn.Exch

/-!
# `mp_exch`: the standard contract

From the entry, `mp_exch(a, b)` returns to `ra` with the two structs swapped:
the struct at `a` holds `b` (its digit pointer `bdp`) and the struct at `b`
holds `a`, the digit arrays untouched, the callee-saved registers kept, and
memory changed only in the two structs. Regions are `Api/Two.lean`'s with
both operands written (`isW2`) and stack depth `0` (no frame); the frame is
`[aS, bS]`, inside `Two.ws2`.

Beyond `Shape`: nothing about the values (the C copies bytes); the sign
below `2^31`, as the code moves it by `lw`/`sw`.
-/

namespace Tom.Machine.Api.Exch

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Two

abbrev lay (sp pa adp pb bdp : Nat) (a b : MpInt) := Two.lay 0 sp pa adp pb bdp a b

/-- What `mp_exch(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  sgn : a.sign < 2 ^ 31
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp a b) isW2

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (M : Mem) : Prop where
  ra_ : MpAt M pa bdp b
  rb : MpAt M pb adp a
  frame : Frm (lay sp pa adp pb bdp a b) [R.aS, R.bS] m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ M, At ra [(1, ra)] M v.keep outp cf ∧ Post m sp pa adp pb bdp a b M

def entry : BitVec 64 := 0x80000e60#64

/-- **`mp_exch` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra : BitVec 64},
    Pre m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.Exch.entryL ra pa pb) m v.keep outp) (Ret m v outp sp pa adp pb bdp a b ra)

end Tom.Machine.Api.Exch
