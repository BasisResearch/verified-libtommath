import Tom.Machine.Api.Std_grow6G
import Tom.Spec.SAddGStep

/-!
# `s_mp_add(a, b, a)` with growth: the allocating contract

The room contracts (`Api/SAdd.lean`, `Api/SAddAlias.lean`) assume `max(used) + 1 ≤ c->alloc` (D5). Here the destination `a` is grown by `mp_grow(c, max + 1)` (`realloc`) when short; the operands are shaped, the destination live (its digits the front block of the heap's blocks). Results: `none`, `MP_MEM` (only when it had to grow; nothing changed, `Place.keep`); `some (q, a')` with `SAddPost a b (sAddIn a b a) a'` (`SAddPost.spec`: `|a'| = |a| + |b|`), `q` the old block (kept) or a fresh one (`Place.regrow`). Memory changes only in the stack `[sp - 608, sp)` (the 64-byte frame and `mp_grow`'s 544), `a` and the allocator's footprint.
-/

namespace Tom.Machine.Api.SAddGA

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x8000219c#64

/-- The stack depth: the 64-byte frame and `mp_grow`'s. -/
abbrev F : Nat := 64 + MpGrow.F

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt
  H : List (Nat × Nat)

inductive R | stk | aS | aD | bS | bD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .code] := by cases r <;> simp

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .bS => .mpS p.pb p.bdp p.b
  | .bD => .mpD p.bdp p.b.alloc p.b.digit
  | .code => .code

/-- After: `none` on `MP_MEM`, `some (q, a')` with `a'`'s digits at `q`. -/
def out (p : P) : Option (Nat × MpInt) → R → Kind
  | some (q, x), .aS => .mpS p.pa q x
  | some (q, x), .aD => .mpD q x.alloc x.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .aS | .aD => true
  | _ => false

def ws : List R := [.stk, .aS, .aD]

def site' (p : P) : Option (Nat × MpInt) → Iv
  | none => lay p .aD
  | some (q, x) => ⟨q, 4 * x.alloc⟩

/-- `a`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.adp p.a :: p.H

def hout (p : P) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => hin p
  | some (q, x) => (q, 4 * x.alloc) :: p.H

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
   (12, BitVec.ofNat 64 p.pa)]

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpGrow.memBV | some _ => 0#64)]

/-- What `s_mp_add(a, b, a)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The loops read the operands' digits below `used`. -/
  sa : p.a.Shape
  sb : p.b.Shape
  /-- `mp_grow`'s `int size` (`max(used) + 1`). -/
  size_lt : max p.a.used p.b.used + 1 < 2 ^ 31
  /-- The operands' digit arrays are nonempty (initialised `mp_int`s). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- `a`'s struct is off the arena (`mp_grow` reads and writes it). -/
  coff : OffHeap p.pa 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.a.alloc < max p.a.used p.b.used + 1
  | some (_, x) => SAddPost p.a p.b (sAddIn p.a p.b p.a) x

/-- **`s_mp_add(a, b, a)` on the machine, growing `a`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.SAddGA
