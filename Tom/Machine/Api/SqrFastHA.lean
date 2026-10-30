import Tom.Machine.Api.SqrFastH

/-!
# `s_mp_sqr_fast(a, a)` with growth: the allocating contract

`Api/SqrFastH.lean` with `b = a` (`mp_sqr(a, a)` below the cut-off): regions `Api/Un.lean`'s, the
site `a`'s digits. The column loop reads `a` (at its new block after `mp_grow`) into `W` before the
copy writes it.
-/

namespace Tom.Machine.Api.SqrFastHA

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.Un (R isW ws)
open Tom.Machine.Api.MpSqr (X)

def entry : BitVec 64 := 0x80007010#64

def F : Nat := 2752

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt
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

def out (p : P) : X → R → Kind
  | (_, q, a'), .aS => .mpS p.pa q a'
  | (_, q, a'), .aD => .mpD q a'.alloc a'.digit
  | _, r => kind p r

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

/-- What `s_mp_sqr_fast(a, a)` needs (in place: the column loop reads `a` into `W` before the
copy writes it; a grown `a` is read at its new block). -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 2752
  sa : p.a.Shape
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  warr : 2 * p.a.used + 1 < 512
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

def Q (p : P) (x : X) : Prop := SqrAlg.Out p.a p.a.alloc (hin p) (lay p .aD) x

/-- **`s_mp_sqr_fast(a, a)` on the machine, growing `a`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.SqrFastHA
