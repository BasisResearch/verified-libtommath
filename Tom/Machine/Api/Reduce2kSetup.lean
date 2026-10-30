import Tom.Machine.Api.StdHeapFn
import Tom.Machine.Fn.Reduce2kSetupG
import Tom.Spec.Reduce
import Tom.Spec.Bits
import Tom.Spec.Init

/-!
# `mp_reduce_2k_setup(a, &d)`: the contract (over `Kit/MeetHeap.lean`)

`mp_init(&tmp)` (struct in the frame at `sp - 56`, `MP_PREC = 32` digits), `p = mp_count_bits(a)`,
`mp_2expt(&tmp, p)`, `s_mp_sub(&tmp, a, &tmp)`, `*d = tmp.dp[0]`, `mp_clear(&tmp)`: `d` receives
the low digit of `2^p - |a|` (`Setup2kPost`, `Spec/Reduce.lean`; the true `d` of a `2^p - d`
modulus only when that is one digit, `Setup2kPost.spec`). On `MP_MEM` from `mp_init` nothing is
changed (`d` keeps its digit); `mp_2expt` and `s_mp_sub` cannot fail under the residue. The heap
has the same blocks after (`tmp`'s freed). Memory changes only in the stack `[sp - 640, sp)` (the
80-byte frame and `mp_init`'s 560; `mp_clear` needs 544, `mp_2expt` and `s_mp_sub` 48,
`mp_count_bits` none), `d` and the allocator's footprint.

`d` (`mp_digit *`) is a one-digit cell (`Cell`, a digit array of length one, `Kind.mpD`).
-/

namespace Tom.Machine.Api.Reduce2kSetup

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Reduce Tom.Mont

def entry : BitVec 64 := 0x80006088#64

inductive R | stk | aS | aD | dD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .dD, .code] := by cases r <;> simp

/-- The stack depth: the 80-byte frame and `mp_init`'s. -/
abbrev F : Nat := 80 + MpInit.Finit

/-- One `mp_digit` in memory, as a digit array of length one. -/
structure Cell where
  v : Nat

def Cell.alloc (_ : Cell) : Nat := 1

def Cell.digit (c : Cell) : Nat → Nat := fun _ => c.v

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pd : Nat
  a : MpInt
  /-- `*d` before. -/
  d : Cell
  H : List (Nat × Nat)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .dD => ⟨p.pd, 4 * p.d.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .dD => .mpD p.pd p.d.alloc p.d.digit
  | .code => .code

/-- After: `none` on `MP_MEM`, `some x` with `*d = x`. -/
def out (p : P) : Option Nat → R → Kind
  | some x, .dD => .mpD p.pd 1 (fun _ => x)
  | _, r => kind p r

def isW : R → Bool
  | .stk | .dD => true
  | _ => false

def ws : List R := [.stk, .dD]

def hin (p : P) : List (Nat × Nat) := p.H

/-- The arguments: `a0 = a`, `a1 = d` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pd)]

def rets (_ : P) (x : Option Nat) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpInit.memBV | some _ => 0#64)]

/-- What `mp_reduce_2k_setup(a, &d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_count_bits` and `s_mp_sub` read `a` (`mp_reduce_2k`'s callers pass a valid modulus). -/
  va : p.a.Valid
  /-- `mp_count_bits`'s `int` result (`Std.cntBits`). -/
  bits : Layout.digitBits * p.a.used < 2 ^ 31
  /-- D5: `mp_2expt(&tmp, p)` stays in `tmp`'s `MP_PREC` digits (its `mp_grow` does not
  reallocate): `|a| < 2^896`. -/
  room : countBits p.a / Layout.digitBits + 1 ≤ defPrec
  /-- A nonempty digit array (`HContract.pos`: an empty region inside the arena is not off it). -/
  apos : 0 < p.a.alloc

def Q (p : P) : Option Nat → Prop
  | none => True
  | some x => Setup2kPost p.a x

/-- **`mp_reduce_2k_setup(a, &d)` on the machine.** The site is `d`'s cell, kept in place. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .dD (out p x) (lay p .dD) (hin p) (hin p) m M)

end Tom.Machine.Api.Reduce2kSetup
