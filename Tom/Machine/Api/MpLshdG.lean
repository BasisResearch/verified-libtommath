import Tom.Machine.Api.Std_grow6G
import Tom.Spec.Grow6Step

/-!
# `mp_lshd(a, k)` with growth: the allocating contract

`Api/MpLshd.lean` assumes room (`a->used + k ≤ a->alloc`, D5). Here `a` is shaped and live
(its digits the front block of the heap's blocks, `0 < a->alloc`), `0 ≤ k < 2^31` with
`a->used + k < 2^31` (`mp_grow`'s `int size`), and nothing about room: with `0 < k`, `0 < used`
and `alloc < used + k` the code calls `mp_grow(a, used + k)` (`realloc`) first. As an allocating
contract (the shape of `Api/SMpSqr.lean`) the site is `a`'s own digit array:
* `none`: `mp_grow` returned `MP_MEM` (only when it had to grow); `a` and the heap unchanged
  (`Place.keep`);
* `some (q, a')`: `MP_OKAY`, `a'` at `q` with `LshdPost (lshdIn a k) k a'` (`lshdIn`: `a` grown
  to `used + k` when it had to, else `a`; `LshdShift.spec`: valid, `|a'| = |a| radix^k`); `q` is
  `a`'s old block (kept) or a fresh one (`Place.regrow`, the old block freed by `realloc`).
Memory changes only in the stack `[sp - 576, sp)` (the 32-byte frame and `mp_grow`'s 544;
`memset` uses none), `a` and the allocator's footprint. Regions as `Api/Un.lean`'s.
-/

namespace Tom.Machine.Api.MpLshdG

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x800015b8#64

/-- The stack depth: the 32-byte frame and `mp_grow`'s. -/
abbrev F : Nat := 32 + MpGrow.F

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt
  k : Nat
  H : List (Nat × Nat)

inductive R | stk | aS | aD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .code] := by cases r <;> simp

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .code => .code

/-- After: `none` on `MP_MEM`, `some (q, a')` with `a'`'s digits at `q`. -/
def out (p : P) : Option (Nat × MpInt) → R → Kind
  | some (q, a'), .aS => .mpS p.pa q a'
  | some (q, a'), .aD => .mpD q a'.alloc a'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .aS | .aD => true
  | _ => false

def ws : List R := [.stk, .aS, .aD]

def site' (p : P) : Option (Nat × MpInt) → Iv
  | none => lay p .aD
  | some (q, a') => ⟨q, 4 * a'.alloc⟩

/-- `a`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.adp p.a :: p.H

def hout (p : P) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => hin p
  | some (q, a') => (q, 4 * a'.alloc) :: p.H

/-- The arguments: `a0 = a`, `a1 = k` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.k)]

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpGrow.memBV | some _ => 0#64)]

/-- What `mp_lshd(a, k)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The shift reads `a`'s digits below `used` and `alloc` (`mp_grow` keeps them). -/
  sa : p.a.Shape
  /-- The C's `int b`, nonnegative. -/
  k_lt : p.k < 2 ^ 31
  /-- `mp_grow(a, a->used + b)`'s `int size` (`addw` at `15d8`). -/
  size_lt : p.a.used + p.k < 2 ^ 31
  /-- `a`'s digits are `realloc`'s block: live and nonempty. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.a.alloc < p.a.used + p.k
  | some (_, a') => LshdPost (lshdIn p.a p.k) p.k a'

/-- **`mp_lshd(a, k)` on the machine, growing `a`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpLshdG
