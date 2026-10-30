import Tom.Machine.Img
import Tom.Machine.Repr

/-!
# Standard contracts: the regions of a one-operand function `f(a, …)`

As `Api/Bin.lean`: the stack `[sp - F, sp)`, `a`'s struct and digit array,
the code. `isW` (writes `a`: `mp_zero`, `mp_set`, `mp_lshd`, …) or `isR`
(reads `a` only: `mp_count_bits`, `mp_cmp_d`, …); the stack is written in
both.
-/

namespace Tom.Machine.Api.Un

open Tom.Machine Tom.Machine.Code

inductive R | stk | aS | aD | code
  deriving DecidableEq

/-- `a` written. -/
def isW : R → Bool
  | .stk | .aS | .aD => true
  | _ => false

/-- `a` read only. -/
def isR : R → Bool
  | .stk => true
  | _ => false

def lay (F sp pa adp : Nat) (a : MpInt) : R → Iv
  | .stk => ⟨sp - F, F⟩
  | .aS => ⟨pa, 24⟩
  | .aD => ⟨adp, 4 * a.alloc⟩
  | .code => textIv

/-- The written names under `isW` and `isR`. -/
def ws : List R := [.stk, .aS, .aD]
def wsR : List R := [.stk]

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .code] := by cases r <;> simp

end Tom.Machine.Api.Un
