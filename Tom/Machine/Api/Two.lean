import Tom.Machine.Img
import Tom.Machine.Repr

/-!
# Standard contracts: the regions of a two-operand function `f(a, …, b)`

As `Api/Bin.lean`: the stack `[sp - F, sp)`, the structs and digit arrays
of `a` and `b`, the code. `isW`: `a` read, `b` written (`mp_copy(a, b)`,
`mp_mul_2(a, b)`, `mp_add_d(a, d, b)`, …); `isW2`: both written
(`mp_exch`); `isR`: both read (`mp_cmp`).
-/

namespace Tom.Machine.Api.Two

open Tom.Machine Tom.Machine.Code

inductive R | stk | aS | aD | bS | bD | code
  deriving DecidableEq

def isW : R → Bool
  | .stk | .bS | .bD => true
  | _ => false

def isW2 : R → Bool
  | .code => false
  | _ => true

def isR : R → Bool
  | .stk => true
  | _ => false

def lay (F sp pa adp pb bdp : Nat) (a b : MpInt) : R → Iv
  | .stk => ⟨sp - F, F⟩
  | .aS => ⟨pa, 24⟩
  | .aD => ⟨adp, 4 * a.alloc⟩
  | .bS => ⟨pb, 24⟩
  | .bD => ⟨bdp, 4 * b.alloc⟩
  | .code => textIv

def ws : List R := [.stk, .bS, .bD]
def ws2 : List R := [.stk, .aS, .aD, .bS, .bD]
def wsR : List R := [.stk]

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .code] := by cases r <;> simp

end Tom.Machine.Api.Two
