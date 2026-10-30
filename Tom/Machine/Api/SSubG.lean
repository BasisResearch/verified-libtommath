import Tom.Machine.Api.Std_grow6G
import Tom.Spec.SSubGStep

/-!
# `s_mp_sub(a, b, c)` with growth: the allocating contract

The room contracts (`Api/SSub.lean`, `Api/SSubAlias.lean`) assume `a->used ≤ c->alloc` (D5). Here the destination `c` is grown by `mp_grow(c, a->used)` (`realloc`) when short; `b->used ≤ a->used` (the C's precondition, `mp_sub`/`mp_add` order the operands by `mp_cmp_mag`), the operands shaped, the destination live. Results: `none`, `MP_MEM` (only when it had to grow; nothing changed, `Place.keep`); `some (q, c')` with `SSubPost a b (sSubIn a c) c'` (`SSubPost.spec`: `|c'| = |a| - |b|`), `q` the old block (kept) or a fresh one (`Place.regrow`). Memory changes only in the stack `[sp - 592, sp)` (the 48-byte frame and `mp_grow`'s 544), `c` and the allocator's footprint.
-/

namespace Tom.Machine.Api.SSubG

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x80004564#64

/-- The stack depth: the 48-byte frame and `mp_grow`'s. -/
abbrev F : Nat := 48 + MpGrow.F

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  pc : Nat
  cdp : Nat
  a : MpInt
  b : MpInt
  c : MpInt
  H : List (Nat × Nat)

inductive R | stk | aS | aD | bS | bD | cS | cD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .cS, .cD, .code] := by cases r <;> simp

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .cS => ⟨p.pc, 24⟩
  | .cD => ⟨p.cdp, 4 * p.c.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .bS => .mpS p.pb p.bdp p.b
  | .bD => .mpD p.bdp p.b.alloc p.b.digit
  | .cS => .mpS p.pc p.cdp p.c
  | .cD => .mpD p.cdp p.c.alloc p.c.digit
  | .code => .code

/-- After: `none` on `MP_MEM`, `some (q, c')` with `c'`'s digits at `q`. -/
def out (p : P) : Option (Nat × MpInt) → R → Kind
  | some (q, x), .cS => .mpS p.pc q x
  | some (q, x), .cD => .mpD q x.alloc x.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .cS | .cD => true
  | _ => false

def ws : List R := [.stk, .cS, .cD]

def site' (p : P) : Option (Nat × MpInt) → Iv
  | none => lay p .cD
  | some (q, x) => ⟨q, 4 * x.alloc⟩

/-- `c`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.cdp p.c :: p.H

def hout (p : P) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => hin p
  | some (q, x) => (q, 4 * x.alloc) :: p.H

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
   (12, BitVec.ofNat 64 p.pc)]

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpGrow.memBV | some _ => 0#64)]

/-- What `s_mp_sub(a, b, c)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The loops read the operands' digits below `used`. -/
  sa : p.a.Shape
  sb : p.b.Shape
  /-- `c`'s old digits above the result are zeroed only up to its old `used`. -/
  sc : p.c.Shape
  /-- `mp_grow`'s `int size` (`a->used`). -/
  size_lt : p.a.used < 2 ^ 31
  /-- The operands' digit arrays are nonempty (initialised `mp_int`s). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  cpos : 0 < p.c.alloc
  /-- `c`'s struct is off the arena (`mp_grow` reads and writes it). -/
  coff : OffHeap p.pc 24
  /-- The C's order: the subtrahend no longer than the minuend. -/
  ge : p.b.used ≤ p.a.used

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.c.alloc < p.a.used
  | some (_, x) => SSubPost p.a p.b (sSubIn p.a p.c) x

/-- **`s_mp_sub(a, b, c)` on the machine, growing `c`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.SSubG
