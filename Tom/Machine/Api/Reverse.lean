import Tom.Machine.Img
import Tom.Machine.Fn.Reverse
import Tom.Spec.ByteRev

/-!
# `s_mp_reverse`: the standard contract

From the entry, `s_mp_reverse(s, len)` with `s[0 .. len)` holding the bytes
`l` (`len = |l| ≥ 1`) returns to `ra` with the array holding `l.reverse`,
the callee-saved registers kept and memory changed only in the array. Its
regions: the array (written) and the code; no frame, so no stack region.

Beyond the C: `len ≥ 1` (for `len = 0` the C's `len - 1u` wraps and the
loop runs off the array).
-/

namespace Tom.Machine.Api.Reverse

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

inductive R | arr | code
  deriving DecidableEq

def isW : R → Bool
  | .arr => true
  | _ => false

def lay (s n : Nat) : R → Iv
  | .arr => ⟨s, n⟩
  | .code => textIv

/-- The bytes `l` at `s`, as total reads. -/
def BytesAt (M : Mem) (s : Nat) (l : List (BitVec 8)) : Prop :=
  ∀ i, i < l.length → (M[s + i]?).getD 0 = l.getD i 0

structure Pre (m : Mem) (s : Nat) (l : List (BitVec 8)) (ra : BitVec 64) : Prop where
  bytes : BytesAt m s l
  n_pos : 1 ≤ l.length
  rs : Ram s l.length
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay s l.length) isW

structure Post (m : Mem) (s : Nat) (l : List (BitVec 8)) (M : Mem) : Prop where
  bytes : BytesAt M s l.reverse
  frame : Frm (lay s l.length) [R.arr] m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (s : Nat) (l : List (BitVec 8)) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ M, At ra [(1, ra)] M v.keep outp cf ∧ Post m s l M

def entry : BitVec 64 := 0x80004528#64

/-- **`s_mp_reverse` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {s : Nat} {l : List (BitVec 8)} {ra : BitVec 64},
    Pre m s l ra →
    Triple (At entry (Fn.Reverse.entryL ra s l.length) m v.keep outp) (Ret m v outp s l ra)

end Tom.Machine.Api.Reverse
