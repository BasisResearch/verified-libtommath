import Tom.Machine.Api.MpDivQ
import Tom.Spec.MpReduceSetupStep

/-!
# `mp_reduce_setup(a, b)`: the allocating contract

`vendor/libtommath/bn_mp_reduce_setup.c` at `0x800063a8` (frame 32): `mp_2expt(a, b->used * 2 *
MP_DIGIT_BIT)` (`Api/StdNorm.lean` `mp2expt`, with room: it returns `MP_OKAY`), then the tail call
`mp_div(a, b, a, NULL)` (`Api/MpDivQ.lean`) on the whole stack. One site is re-placed, `a`'s digits:

* `ok q a'`: `MP_OKAY`, `a'` at `q` with `ReduceSetupPost b a'` (`a' = ⌊radix^(2 b->used) / b⌋`);
* `mem a'`: `mp_div` failed to allocate; `a`'s digits (block and length) as before, `a'` its value
  (`2^(56 b->used)`, nothing stated).

Stated for `b > 0` (`ReduceSetupPost`; for `b < 0` the C leaves `-mu`). `a`, `b` distinct (D6).
-/

namespace Tom.Machine.Api.MpReduceSetup

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x800063a8#64

/-- The stack depth: `mp_div`'s, on the whole stack (`mp_2expt` needs 32 + 48). -/
abbrev F : Nat := MpDivQ.F

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

/-- `MP_MEM` (`a`'s value then), or `MP_OKAY` with `a'`'s digits at `q`. -/
inductive Out
  | mem (a' : MpInt)
  | ok (q : Nat) (a' : MpInt)

def out (p : P) : Out → R → Kind
  | .mem a', .aS => .mpS p.pa p.adp a'
  | .mem a', .aD => .mpD p.adp p.a.alloc a'.digit
  | .ok q a', .aS => .mpS p.pa q a'
  | .ok q a', .aD => .mpD q a'.alloc a'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .aS | .aD => true
  | _ => false

def ws : List R := [.stk, .aS, .aD]

def site' (p : P) : Out → Iv
  | .ok q a' => ⟨q, 4 * a'.alloc⟩
  | .mem _ => lay p .aD

/-- `a`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.adp p.a :: p.H

def hout (p : P) : Out → List (Nat × Nat)
  | .ok q a' => (q, 4 * a'.alloc) :: p.H
  | .mem _ => hin p

/-- The arguments: `a0 = a`, `a1 = b`. -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]

def rets (_ : P) (x : Out) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | .mem _ => MpInit.memBV | .ok _ _ => 0#64)]

/-- What `mp_reduce_setup(a, b)` needs (`MpReduceSetupStep.Env` and the machine's facts). -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_2expt` writes `a` in place (D5: `room`). -/
  sa : p.a.Shape
  room : p.b.used * 2 * Layout.digitBits / Layout.digitBits + 1 ≤ p.a.alloc
  /-- The modulus: valid, positive (`ReduceSetupPost` is stated for `b > 0`; `mp_div`'s `b ≠ 0`). -/
  vb : p.b.Valid
  b0 : 0 < p.b.used
  bz : p.b.sign = Layout.mpZpos
  /-- `mp_2expt`'s `int b` (`slliw`/`subw`/`slliw` at `63b8`: `56 b->used`). -/
  k_lt : p.b.used * 2 * Layout.digitBits < 2 ^ 31
  /-- `a`'s digits are `mp_div`'s old block of `c = a`, freed after the exchange: nonempty. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  /-- `mp_div`'s `mp_init_copy(&y, b)` copies from a live block. -/
  bblk : digBlk p.bdp p.b ∈ p.H

/-- What `a` holds. -/
def Q (p : P) : Out → Prop
  | .mem _ => True
  | .ok _ a' => Reduce.ReduceSetupPost p.b a'

/-- **`mp_reduce_setup(a, b)` on the machine**, as an allocating contract (site: `a`'s digits). -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpReduceSetup
