import Tom.Machine.Api.Std_grow6G
import Tom.Spec.AddGStep

/-!
# `mp_add(a, b, b)` with growth: the allocating contract

The room contracts (`Api/MpAdd.lean`, `Api/MpAddAlias.lean`) assume `max(used) + 1 ≤ c->alloc` (D5). Here `b` gets the branch's sign (`addSign`, stored before the tail call) and the tail callee (`s_mp_add` for equal signs, `s_mp_sub(b, a, c)` for `|a| < |b|`, else `s_mp_sub(a, b, c)`, the growing contracts of `Api/SAddG*.lean`, `Api/SSubG*.lean`) grows it when short. Results: `none`, `MP_MEM` (only when it had to grow; `b` changed only in its sign); `some (q, b')` with `AddG a b …`: in each branch the callee's post (`AddPost.spec`'s branches with the grown destination). Memory changes only in the stack `[sp - 608, sp)` (the 64-byte frame of the unequal-sign branch, then the callees' 608 / 592), `b` and the allocator's footprint.
-/

namespace Tom.Machine.Api.MpAddGB

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x80000608#64

/-- The stack depth: the tail callees' (`s_mp_add`'s 64-byte frame and `mp_grow`'s; the own 64-byte frame is popped before the tail calls). -/
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

/-- After: `none` on `MP_MEM`, `some (q, b')` with `b'`'s digits at `q`. -/
def out (p : P) : Option (Nat × MpInt) → R → Kind
  | some (q, x), .bS => .mpS p.pb q x
  | some (q, x), .bD => .mpD q x.alloc x.digit
  | none, .bS => .mpS p.pb p.bdp (p.b.withSign (addSign p.a p.b))
  | _, r => kind p r

def isW : R → Bool
  | .stk | .bS | .bD => true
  | _ => false

def ws : List R := [.stk, .bS, .bD]

def site' (p : P) : Option (Nat × MpInt) → Iv
  | none => lay p .bD
  | some (q, x) => ⟨q, 4 * x.alloc⟩

/-- `b`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.bdp p.b :: p.H

def hout (p : P) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => hin p
  | some (q, x) => (q, 4 * x.alloc) :: p.H

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
   (12, BitVec.ofNat 64 p.pb)]

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpGrow.memBV | some _ => 0#64)]

/-- What `mp_add(a, b, b)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_cmp_mag` compares the operands' magnitudes (valid operands). -/
  va : p.a.Valid
  vb : p.b.Valid
  /-- `mp_grow`'s `int size` (`max(used) + 1`). -/
  size_lt : max p.a.used p.b.used + 1 < 2 ^ 31
  /-- The operands' digit arrays are nonempty (initialised `mp_int`s). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- `b`'s struct is off the arena (`mp_grow` reads and writes it). -/
  coff : OffHeap p.pb 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.b.alloc < addSize p.a p.b
  | some (_, x) => AddG p.a p.b (SAddPost p.a (p.b.withSign p.a.sign) (sAddIn p.a (p.b.withSign p.a.sign) (p.b.withSign p.a.sign)) x) (SSubPost (p.b.withSign p.b.sign) p.a (sSubIn (p.b.withSign p.b.sign) (p.b.withSign p.b.sign)) x) (SSubPost p.a (p.b.withSign p.a.sign) (sSubIn p.a (p.b.withSign p.a.sign)) x)

/-- **`mp_add(a, b, b)` on the machine, growing `b`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .bD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpAddGB
