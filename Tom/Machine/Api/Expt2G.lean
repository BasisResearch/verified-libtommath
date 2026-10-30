import Tom.Machine.Api.Std_grow6G
import Tom.Spec.Expt2G

/-!
# `mp_2expt(a, b)` growing `a`: the allocating contract

`Api/Expt2.lean` asks for room (`b / 28 + 1 ≤ a->alloc`, D5). Here nothing about room: `mp_zero(a)`,
then `mp_grow(a, b / 28 + 1)` reallocates `a`'s digits when it must (`Std.mpGrowF`), then
`a->used := b / 28 + 1`, `a->dp[b / 28] := 1 << (b % 28)`. The site is `a`'s digit array:
* `none`: `mp_grow` returned `MP_MEM` (only when it had to grow); `a` is the zero of its old
  allocation (`mp_zero` ran), at its block (`Place.keep`);
* `some (q, a')`: `MP_OKAY`, `a'` at `q` with `Expt2Post (expt2In a b) b a'` (`Expt2Post.specG`:
  `a'` valid, `2^b`); `q` is `a`'s old block or a fresh one (`Place.regrow`), stated in `Q` (`Ok.place`).
`0 ≤ b < 2^31` (the C's `int b`; `MP_VAL` for `b < 0` is not covered). Memory changes only in the
stack `[sp - 592, sp)` (the 48-byte frame and `mp_grow`'s 544; `mp_zero` and libgcc use none), `a`
and the allocator's footprint.
-/

namespace Tom.Machine.Api.Expt2G

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x800076d4#64

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

/-- After: `none` on `MP_MEM` (`a` zeroed in place), `some (q, a')` with `a'`'s digits at `q`. -/
def out (p : P) : Option (Nat × MpInt) → R → Kind
  | none, .aS => .mpS p.pa p.adp (MpInt.zeroN p.a.alloc)
  | none, .aD => .mpD p.adp p.a.alloc (MpInt.zeroN p.a.alloc).digit
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

/-- The arguments: `a0 = a`, `a1 = b` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.b)]

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpGrow.memBV | some _ => 0#64)]

/-- What `mp_2expt(a, b)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_zero` and `mp_grow` take a shaped `a`. -/
  sa : p.a.Shape
  /-- The C's `int b`, nonnegative (`bltz` at `76d4`: `MP_VAL` is not covered). -/
  b_lt : p.b < 2 ^ 31
  /-- `a`'s digits are `realloc`'s block: live and nonempty. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

/-- `MP_OKAY`: the value, and where `a`'s digits went (kept or re-placed: a caller that re-places its
own region by this call needs it, `HContract.after` consumes the callee's `HPost.place`). -/
structure Ok (p : P) (q : Nat) (a' : MpInt) : Prop where
  post : Expt2Post (expt2In p.a p.b) p.b a'
  place : Place (hin p) (lay p .aD) ⟨q, 4 * a'.alloc⟩

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.a.alloc < p.b / Layout.digitBits + 1
  | some (q, a') => Ok p q a'

/-- **`mp_2expt(a, b)` on the machine, growing `a`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.Expt2G
