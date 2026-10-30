import Tom.Machine.Img
import Tom.Machine.Fn.DrSetup
import Tom.Spec.ModShape

/-!
# `mp_dr_setup`: the standard contract

From the entry, `mp_dr_setup(a, d)` stores `drSetupDigit a = 2^28 - dp[0]` at
`d` and returns to `ra`, the callee-saved registers kept and memory changed
only in the digit at `d`. Its regions: the digit `*d` (written), `a`'s
struct and digit array, the code; no frame, so no stack region.

Beyond `Shape`: `1 ≤ alloc` (`dp[0]` is read; every `mp_int` has it).
-/

namespace Tom.Machine.Api.DrSetup

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

inductive R | dW | aS | aD | code
  deriving DecidableEq

def isW : R → Bool
  | .dW => true
  | _ => false

def lay (pd pa adp : Nat) (a : MpInt) : R → Iv
  | .dW => ⟨pd, 4⟩
  | .aS => ⟨pa, 24⟩
  | .aD => ⟨adp, 4 * a.alloc⟩
  | .code => textIv

/-- What `mp_dr_setup(a, d)` needs. -/
structure Pre (m : Mem) (pa adp pd : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  alloc_pos : 1 ≤ a.alloc
  rd : Ram pd 4
  pd_al : pd % 4 = 0
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay pd pa adp a) isW

/-- What it leaves. -/
structure Post (m : Mem) (pa adp pd : Nat) (a : MpInt) (M : Mem) : Prop where
  res : bytesT4 M pd = BitVec.ofNat 32 (drSetupDigit a)
  frame : Frm (lay pd pa adp a) [R.dW] m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (pa adp pd : Nat) (a : MpInt) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ M, At ra [(1, ra)] M v.keep outp cf ∧ Post m pa adp pd a M

def entry : BitVec 64 := 0x8000578c#64

/-- **`mp_dr_setup` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {pa adp pd : Nat} {a : MpInt} {ra : BitVec 64},
    Pre m pa adp pd a ra →
    Triple (At entry (Fn.DrSetup.entryL ra pa pd) m v.keep outp) (Ret m v outp pa adp pd a ra)

end Tom.Machine.Api.DrSetup
