import Tom.Machine.Api.MpMul

/-!
# `mp_mul(a, b, a)`: the in-place contract

`Api/MpMul.lean` with `c = a` (karatsuba's `mp_mul(&t1, &x0, &t1)`, toom's
`mp_mul(&S1, &S2, &S1)`, `mp_mul(&a1, &b1, &a1)`, `mp_mul(&a0, &b0, &a0)`). The code reads
`a->sign`, `b->sign` before the call and every algorithm reads `a` before it writes the
destination (karatsuba copies `a`'s digits into `x0`, `x1` first; `s_mp_mul_digs` builds
the product in a temporary; `s_mp_mul_digs_fast` in its `W` array), so `c = a` is
`mp_mul`'s case too. Regions `stk aS aD bS bD kc tc code`, written `stk aS aD`; the site
is `a`'s digit array. `b` stays distinct (D6).
-/

namespace Tom.Machine.Api.MpMulA

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpMul (entry kcAddr tcAddr μ Fm kcV tcV X)

inductive R | stk | aS | aD | bS | bD | kc | tc | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .kc, .tc, .code] := by cases r <;> simp

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt
  H : List (Nat × Nat)

def F (p : P) : Nat := Fm (μ p.a p.b)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - (2768 + 8 * (p.a.used + p.b.used)), 2768 + 8 * (p.a.used + p.b.used)⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .kc => ⟨kcAddr, 4⟩
  | .tc => ⟨tcAddr, 4⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .bS => .mpS p.pb p.bdp p.b
  | .bD => .mpD p.bdp p.b.alloc p.b.digit
  | .kc => .mpD kcAddr 1 kcV
  | .tc => .mpD tcAddr 1 tcV
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

/-- The arguments: `a0 = a2 = a`, `a1 = b`. -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
   (12, BitVec.ofNat 64 p.pa)]

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpInit.memBV)]

/-- `Api.MpMul.Res` with `c = a` (`a` valid, hence shaped with a sign). -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp (F p)
  va : p.a.Valid
  vb : p.b.Valid
  uab : μ p.a p.b < 2 ^ 30
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

structure Out (p : P) (ok : Bool) (a' : MpInt) : Prop where
  shape : a'.Shape
  sign : a'.sign = Layout.mpZpos ∨ a'.sign = Layout.mpNeg
  pos : 0 < a'.alloc
  post : ok = true → MulPost p.a p.b a'

def Q (p : P) : X → Prop
  | (ok, _, a') => Out p ok a'

def SpecR (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

def Spec (p : P) : Prop := SpecR Res p

/-- **`mp_mul(a, b, a)` on the machine.** -/
def Statement : Prop := ∀ p : P, Spec p

end Tom.Machine.Api.MpMulA
