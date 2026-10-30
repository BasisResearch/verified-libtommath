import Tom.Machine.Api.Std_grow6G
import Tom.Spec.Grow6Step

/-!
# `mp_mul_d(a, b, c)` with growth: the allocating contract

`Api/MulD.lean` (and `Std_r6f.mulDC`) assume room (`a->used + 1 ≤ c->alloc`, D5). Here `a` is
shaped with a sign, `c` shaped and live (its digits the front block of the heap's blocks,
`0 < c->alloc`), distinct from `a` (D6; `mp_mul_d(a, b, a)` is `Std.mulDA`), `b` a digit,
`a->used + 1 < 2^31` (`mp_grow`'s `int size`), and nothing about room: when
`c->alloc < a->used + 1` the code calls `mp_grow(c, a->used + 1)` (`realloc`) first. As an
allocating contract the site is `c`'s own digit array:
* `none`: `mp_grow` returned `MP_MEM` (only when it had to grow); `c` and the heap unchanged
  (`Place.keep`);
* `some (q, c')`: `MP_OKAY`, `c'` at `q` with `MulDPost a b (mulDIn a c) c'` (`mulDIn`: `c` grown
  to `a->used + 1` when it had to, else `c`; `MulDPost.spec`: for a valid `a`, `c'` valid,
  `c' = a * b`); `q` is `c`'s old block (kept) or a fresh one (`Place.regrow`).
Memory changes only in the stack `[sp - 624, sp)` (the 80-byte frame and `mp_grow`'s 544;
`memset`, `mp_clamp` and `__muldi3` use none), `c` and the allocator's footprint.
-/

namespace Tom.Machine.Api.MulDG

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x800019fc#64

/-- The stack depth: the 80-byte frame and `mp_grow`'s. -/
abbrev F : Nat := 80 + MpGrow.F

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pc : Nat
  cdp : Nat
  a : MpInt
  b : Nat
  c : MpInt
  H : List (Nat × Nat)

inductive R | stk | aS | aD | cS | cD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .cS, .cD, .code] := by cases r <;> simp

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .cS => ⟨p.pc, 24⟩
  | .cD => ⟨p.cdp, 4 * p.c.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .cS => .mpS p.pc p.cdp p.c
  | .cD => .mpD p.cdp p.c.alloc p.c.digit
  | .code => .code

/-- After: `none` on `MP_MEM`, `some (q, c')` with `c'`'s digits at `q`. -/
def out (p : P) : Option (Nat × MpInt) → R → Kind
  | some (q, c'), .cS => .mpS p.pc q c'
  | some (q, c'), .cD => .mpD q c'.alloc c'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .cS | .cD => true
  | _ => false

def ws : List R := [.stk, .cS, .cD]

def site' (p : P) : Option (Nat × MpInt) → Iv
  | none => lay p .cD
  | some (q, c') => ⟨q, 4 * c'.alloc⟩

/-- `c`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.cdp p.c :: p.H

def hout (p : P) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => hin p
  | some (q, c') => (q, 4 * c'.alloc) :: p.H

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.b),
   (12, BitVec.ofNat 64 p.pc)]

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpGrow.memBV | some _ => 0#64)]

/-- What `mp_mul_d(a, b, c)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The row reads `a`'s digits below `used`. -/
  sa : p.a.Shape
  /-- `a`'s digit array is nonempty (an initialised `mp_int`; the region is then off the arena by
  its own bytes). -/
  apos : 0 < p.a.alloc
  /-- `c->sign = a->sign` is stored as a word (`sw` at `1a40`). -/
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  /-- `c`'s old digits above the result are zeroed only up to its old `used`. -/
  sc : p.c.Shape
  /-- `b` is an `mp_digit` (the products stay below `2^56`). -/
  hb : p.b < radix
  /-- `mp_grow(c, a->used + 1)`'s `int size` (`addiw` at `1b1c`). -/
  size_lt : p.a.used + 1 < 2 ^ 31
  /-- `c`'s digits are `realloc`'s block: live and nonempty. -/
  cpos : 0 < p.c.alloc
  coff : OffHeap p.pc 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.c.alloc < p.a.used + 1
  | some (_, c') => MulDPost p.a p.b (mulDIn p.a p.c) c'

/-- **`mp_mul_d(a, b, c)` on the machine, growing `c`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MulDG
