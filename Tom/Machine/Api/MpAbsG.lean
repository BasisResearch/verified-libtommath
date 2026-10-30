import Tom.Machine.Api.MpCopyG

/-!
# `mp_abs(a, b)` growing `b`: the allocating contract

`Api/MpAbs.lean` asks for room (`a->used ≤ b->alloc`, D5: its `mp_copy(a, b)` does not grow). Here
`mp_copy(a, b)` grows `b` (`Api/MpCopyG.lean`), then `b->sign := MP_ZPOS`. `a`, `b` distinct
(`a == b` only stores the sign). The site is `b`'s digit array:
* `none`: `mp_copy`'s `mp_grow` returned `MP_MEM` (returned); `b` and the heap unchanged;
* `some (q, b')`: `MP_OKAY`, `AbsPost a (copyIn a b) b'` (`b'` valid with value `|a|`), `b'` at `q`.
Memory changes only in the stack `[sp - 608, sp)` (the 32-byte frame and `mp_copy`'s 576), `b` and
the allocator's footprint.
-/

namespace Tom.Machine.Api.MpAbsG

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x800005cc#64

/-- The stack depth: the 32-byte frame and the growing `mp_copy`'s. -/
abbrev F : Nat := 32 + MpCopyG.F

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

def out (p : P) : Option (Nat × MpInt) → R → Kind
  | some (q, b'), .bS => .mpS p.pb q b'
  | some (q, b'), .bD => .mpD q b'.alloc b'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .bS | .bD => true
  | _ => false

def ws : List R := [.stk, .bS, .bD]

def site' (p : P) : Option (Nat × MpInt) → Iv
  | none => lay p .bD
  | some (q, b') => ⟨q, 4 * b'.alloc⟩

/-- `b`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.bdp p.b :: p.H

def hout (p : P) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => hin p
  | some (q, b') => (q, 4 * b'.alloc) :: p.H

/-- The arguments: `a0 = a`, `a1 = b` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpGrow.memBV | some _ => 0#64)]

/-- What `mp_abs(a, b)` needs: `mp_copy(a, b)`'s (`MpCopyG.Res`) on the deeper stack. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  sa : p.a.Shape
  sb : p.b.Shape
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  apos : 0 < p.a.alloc
  ne : p.pa ≠ p.pb
  bpos : 0 < p.b.alloc
  boff : OffHeap p.pb 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.b.alloc < p.a.used
  | some (_, b') => AbsPost p.a (copyIn p.a p.b) b'

/-- **`mp_abs(a, b)` on the machine, growing `b`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .bD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpAbsG
