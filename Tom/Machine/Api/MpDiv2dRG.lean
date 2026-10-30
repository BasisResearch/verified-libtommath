import Tom.Machine.Api.MpCopyG
import Tom.Spec.Div2d

/-!
# `mp_div_2d(a, b, c, a)` growing `c`: the allocating contract

`Api/MpDiv2dR.lean` asks for room in `c` (`a->used ≤ c->alloc`, D5: its `mp_copy(a, c)` does not
grow). Here `mp_copy(a, c)` grows `c` (`Api/MpCopyG.lean`), then `mp_mod_2d(a, b, a)` (in place),
`mp_rshd(c, b / 28)`, the bit loop and `mp_clamp(c)` run as there, over the grown `copyIn a c`. The
site is `c`'s digit array; `a` is written in place:
* `none`: `mp_copy`'s `mp_grow` returned `MP_MEM`; `a`, `c` and the heap unchanged;
* `some (q, a', c')`: `MP_OKAY`, `Mod2dPost a b a a'` (`|a'| = |a| mod 2^b`, `a`'s block and length),
  `Div2dPost a b (copyIn a c) c'` (`|c'| = |a| / 2^b`), `c'` at `q`.
`0 < b < 2^31` (both callers pass a modulus' bit count). Memory changes only in the stack
`[sp - 640, sp)` (the 64-byte frame and `mp_copy`'s 576), `a`, `c` and the allocator's footprint.
-/

namespace Tom.Machine.Api.MpDiv2dRG

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x8000520c#64

/-- The stack depth: the 64-byte frame and the growing `mp_copy`'s. -/
abbrev F : Nat := 64 + MpCopyG.F

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

/-- `MP_MEM` (`none`), or `MP_OKAY` with `a'` in place and `c'`'s digits at `q`. -/
abbrev X := Option (Nat × MpInt × MpInt)

def out (p : P) : X → R → Kind
  | some (_, a', _), .aS => .mpS p.pa p.adp a'
  | some (_, a', _), .aD => .mpD p.adp p.a.alloc a'.digit
  | some (q, _, c'), .cS => .mpS p.pc q c'
  | some (q, _, c'), .cD => .mpD q c'.alloc c'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .aS | .aD | .cS | .cD => true
  | _ => false

def ws : List R := [.stk, .aS, .aD, .cS, .cD]

def site' (p : P) : X → Iv
  | none => lay p .cD
  | some (q, _, c') => ⟨q, 4 * c'.alloc⟩

/-- `c`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.cdp p.c :: p.H

def hout (p : P) : X → List (Nat × Nat)
  | none => hin p
  | some (q, _, c') => (q, 4 * c'.alloc) :: p.H

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = c`, `a3 = d = a` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.b),
   (12, BitVec.ofNat 64 p.pc), (13, BitVec.ofNat 64 p.pa)]

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpGrow.memBV | some _ => 0#64)]

/-- What `mp_div_2d(a, b, c, a)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  sc : p.c.Shape
  /-- `b > 0`: the shifting path. -/
  b_pos : 0 < p.b
  /-- The C's `int b`. -/
  b_lt : p.b < 2 ^ 31
  /-- `mp_mod_2d`'s `a->used * MP_DIGIT_BIT` does not overflow. -/
  bits : Layout.digitBits * p.a.used < 2 ^ 31
  /-- `a`, `c` distinct, nonempty digit arrays (`c`'s: `realloc`'s block). -/
  ne : p.pa ≠ p.pc
  apos : 0 < p.a.alloc
  cpos : 0 < p.c.alloc
  coff : OffHeap p.pc 24

/-- `MP_OKAY`: the remainder in `a`, the quotient in `c`. -/
structure Ok (p : P) (a' c' : MpInt) : Prop where
  mod : Mod2dPost p.a p.b p.a a'
  div : Div2dPost p.a p.b (copyIn p.a p.c) c'

def Q (p : P) : X → Prop
  | none => p.c.alloc < p.a.used
  | some (_, a', c') => Ok p a' c'

/-- **`mp_div_2d(a, b, c, a)` on the machine, growing `c`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpDiv2dRG
