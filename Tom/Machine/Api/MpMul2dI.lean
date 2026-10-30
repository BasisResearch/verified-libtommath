import Tom.Machine.Api.Std_grow6G
import Tom.Spec.Grow6Step

/-!
# `mp_mul_2d(a, b, a)`: the in-place allocating contract

`Api/MpMul2d.lean` covers distinct operands with room. Here `c = a` (the C skips `mp_copy`;
`mp_div`'s `mp_mul_2d(&x, norm, &x)`, `mp_mul_2d(&y, norm, &y)`), `a` shaped and live (its digits
the front block of the heap's blocks, `0 < a->alloc`), `0 ≤ b < 2^31` with
`a->used + b / 28 + 1 < 2^31` (`mp_grow`'s `int size`), and nothing about room: when
`a->alloc < a->used + b / 28 + 1` the code calls `mp_grow` (`realloc`) first, then `mp_lshd`
(with room) and the bit loop. As an allocating contract the site is `a`'s own digit array:
* `none`: `mp_grow` returned `MP_MEM` (only when it had to grow); `a` and the heap unchanged
  (`Place.keep`);
* `some (q, a')`: `MP_OKAY`, `a'` at `q` with `Mul2dPost a b (mul2dIn a b) a'` (`mul2dIn`: `a`
  grown to `used + b / 28 + 1` when it had to, else `a`; `Mul2dPost.spec`: for a valid `a`,
  `a'` valid, `a' = a * 2^b`); `q` is `a`'s old block (kept) or a fresh one (`Place.regrow`).
Memory changes only in the stack `[sp - 592, sp)` (the 48-byte frame and `mp_grow`'s 544;
`mp_lshd` needs 32, `mp_clamp` and libgcc none), `a` and the allocator's footprint.
-/

namespace Tom.Machine.Api.MpMul2dI

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x80001758#64

/-- The stack depth: the 48-byte frame and `mp_grow`'s. -/
abbrev F : Nat := 48 + MpGrow.F

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt
  b : Nat
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

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = a` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.b),
   (12, BitVec.ofNat 64 p.pa)]

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpGrow.memBV | some _ => 0#64)]

/-- What `mp_mul_2d(a, b, a)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The shift reads `a`'s digits below `used` and `alloc` (`mp_grow` keeps them). -/
  sa : p.a.Shape
  /-- The C's `int b`, nonnegative (`bltz` at `1758`: `MP_VAL` is not covered). -/
  b_lt : p.b < 2 ^ 31
  /-- `mp_grow(a, a->used + b / 28 + 1)`'s `int size` (`addw`/`addiw` at `179c`, `1884`). -/
  size_lt : p.a.used + p.b / 28 + 1 < 2 ^ 31
  /-- `a`'s digits are `realloc`'s block: live and nonempty. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.a.alloc < p.a.used + p.b / 28 + 1
  | some (_, a') => Mul2dPost p.a p.b (mul2dIn p.a p.b) a'

/-- **`mp_mul_2d(a, b, a)` on the machine, growing `a`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpMul2dI
