import Tom.Machine.Img
import Tom.Machine.Repr

/-!
# Standard contracts: the regions of a binary operation `op(a, b, c)`

Every function contract from here on (`Tom/Machine/Api/*.lean`) states its
memory over named regions (`Tom/Machine/Kit/Frame.lean`): a closed region
type, `isW` (written), a placement `lay`, the layout as `Sound (lay …) isW`
(a `Pre` field), and the frame as `Frm (lay …) W m M` (a `Post` field). A
caller builds a callee's `Sound` by renaming (`Sound.pull`, closed) and
reads a callee's frame in its own names (`Frm.push`). All code is one
read-only region, the text section (`Img`, `Img.reads`).

`Bin.R`: the stack (`[sp - F, sp)`, the function's and all its callees'
frames), the three structs and digit arrays, the code. Written: the stack
and `c`.
-/

namespace Tom.Machine.Api.Bin

open Tom.Machine Tom.Machine.Code

inductive R | stk | cS | cD | aS | aD | bS | bD | code
  deriving DecidableEq

def isW : R → Bool
  | .stk | .cS | .cD => true
  | _ => false

/-- The placement, for a stack depth `F`. -/
def lay (F sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt) : R → Iv
  | .stk => ⟨sp - F, F⟩
  | .cS => ⟨pc, 24⟩
  | .cD => ⟨cdp, 4 * c.alloc⟩
  | .aS => ⟨pa, 24⟩
  | .aD => ⟨adp, 4 * a.alloc⟩
  | .bS => ⟨pb, 24⟩
  | .bD => ⟨bdp, 4 * b.alloc⟩
  | .code => textIv

/-- The written names. -/
def ws : List R := [.stk, .cS, .cD]

theorem all (r : R) : r ∈ [R.stk, .cS, .cD, .aS, .aD, .bS, .bD, .code] := by cases r <;> simp

/-- `a` and `b` exchanged (a renaming onto itself). -/
def swap : R → R
  | .aS => .bS | .aD => .bD | .bS => .aS | .bD => .aD | r => r

theorem sound_swap {F sp pa adp pb bdp pc cdp : Nat} {a b c : MpInt}
    (hS : Sound (lay F sp pa adp pb bdp pc cdp a b c) isW) : Sound (lay F sp pb bdp pa adp pc cdp b a c) isW :=
  hS.pull swap _ all (fun r => by cases r <;> exact Iv.sub_self _)

/-- A function's code lies in the text section. -/
theorem sub_text {b k : Nat} (h1 : textBase ≤ b := by decide) (h2 : b + k ≤ textBase + textLen := by decide) :
    Iv.Sub ⟨b, k⟩ textIv := ⟨h1, h2⟩

end Tom.Machine.Api.Bin
