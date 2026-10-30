import Tom.Machine.Api.MpLshdG

/-!
# `mp_mul_d(a, b, a)` in place, growing `a`: the allocating contract

`Std.mulDA` (`Api/StdR5.lean`) assumes room (`a->used + 1 ≤ a->alloc`, D5) and `Api/MulDG.lean` grows
a destination distinct from the source (D6). Here the destination is the source (`mp_reduce_2k`'s
`mp_mul_d(&q, d, &q)`): when `a->alloc < a->used + 1` the code calls `mp_grow(a, a->used + 1)` first and
reads `a->dp` after it, so the row runs over the grown block. As an allocating contract the site is
`a`'s digit array (regions `Api/MpLshdG.lean`'s):
* `none`: `mp_grow` returned `MP_MEM` (only when it had to grow); `a` and the heap unchanged;
* `some (q, a')`: `MP_OKAY`, `a'` at `q` with `MulDPost a b (mulDIn a a) a'` (`MulDPost.spec`: for a
  valid `a`, `a'` valid, `a' = a b`).
Memory changes only in the stack `[sp - 624, sp)` (the 80-byte frame and `mp_grow`'s 544), `a` and the
allocator's footprint.
-/

namespace Tom.Machine.Api.MulDGA

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpLshdG (R)

def entry : BitVec 64 := 0x800019fc#64

/-- The stack depth: the 80-byte frame and `mp_grow`'s. -/
abbrev F : Nat := 80 + MpGrow.F

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt
  b : Nat
  H : List (Nat × Nat)

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

/-- What `mp_mul_d(a, b, a)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  sa : p.a.Shape
  apos : 0 < p.a.alloc
  /-- `c->sign = a->sign` is stored as a word. -/
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  /-- `b` is an `mp_digit`. -/
  hb : p.b < radix
  /-- `mp_grow(a, a->used + 1)`'s `int size`. -/
  size_lt : p.a.used + 1 < 2 ^ 31
  aoff : OffHeap p.pa 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.a.alloc < p.a.used + 1
  | some (_, a') => MulDPost p.a p.b (mulDIn p.a p.a) a'

/-- **`mp_mul_d(a, b, a)` on the machine, growing `a`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MulDGA
