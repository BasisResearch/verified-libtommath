import Tom.Machine.Api.MpSqr

/-!
# `mp_sqr(a, a)`: the in-place contract

`Api/MpSqr.lean` with `b = a` (karatsuba's `mp_sqr(&t1, &t1)`, toom's `mp_sqr(&a0, &a0)`,
`mp_sqr(b, b)`, `mp_sqr(&a2, &a2)`). Every algorithm reads `a` before it writes the
destination: `s_mp_sqr_fast` reads the columns into its `W` array first
(`SqrFast.StatementInPlace`), karatsuba and toom copy `a`'s digits into their halves first.
Regions `stk aS aD ks ts km tm code`, written `stk aS aD`; the site is `a`'s digit array.
-/

namespace Tom.Machine.Api.MpSqrA

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpSqr (entry ksAddr tsAddr kmAddr tmAddr ksV tsV kmV tmV Fs X)

inductive R | stk | aS | aD | ks | ts | km | tm | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .ks, .ts, .km, .tm, .code] := by cases r <;> simp

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt
  H : List (Nat × Nat)

def F (p : P) : Nat := Fs p.a.used

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - (2224 + 8 * p.a.used), 2224 + 8 * p.a.used⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .ks => ⟨ksAddr, 4⟩
  | .ts => ⟨tsAddr, 4⟩
  | .km => ⟨kmAddr, 4⟩
  | .tm => ⟨tmAddr, 4⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .ks => .mpD ksAddr 1 ksV
  | .ts => .mpD tsAddr 1 tsV
  | .km => .mpD kmAddr 1 kmV
  | .tm => .mpD tmAddr 1 tmV
  | .code => .code

def out (p : P) : X → R → Kind
  | (_, q, a'), .aS => .mpS p.pa q a'
  | (_, q, a'), .aD => .mpD q a'.alloc a'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .aS | .aD => true
  | _ => false

def ws : List R := [.stk, .aS, .aD]

def site' (_ : P) : X → Iv
  | (_, q, a') => ⟨q, 4 * a'.alloc⟩

def hin (p : P) : List (Nat × Nat) := digBlk p.adp p.a :: p.H

def hout (p : P) : X → List (Nat × Nat)
  | (_, q, a') => (q, 4 * a'.alloc) :: p.H

/-- The arguments: `a0 = a1 = a`. -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pa)]

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpInit.memBV)]

/-- `Api.MpSqr.Res` with `b = a` (`a` valid, hence shaped with a sign). -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp (F p)
  va : p.a.Valid
  /-- The C's `int` arithmetic on `a->used`. -/
  au : p.a.used < 2 ^ 29
  /-- D5 for the comba path: `s_mp_sqr_fast` would `mp_grow` `a` otherwise. -/
  room : p.a.used < 120 → 2 * p.a.used ≤ p.a.alloc
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  sign : x.2.2.sign = Layout.mpZpos
  pos : 0 < x.2.2.alloc
  post : x.1 = true → SqrPost p.a x.2.2
  place : Place (hin p) (lay p .aD) (site' p x)
  grow : p.a.alloc ≤ x.2.2.alloc

def Q (p : P) (x : X) : Prop := Out p x

def SpecR (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

def Spec (p : P) : Prop := SpecR Res p

/-- **`mp_sqr(a, a)` on the machine.** -/
def Statement : Prop := ∀ p : P, Spec p

end Tom.Machine.Api.MpSqrA
