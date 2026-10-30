import Tom.Machine.Api.MpAddGA
import Tom.Machine.Api.MpAddGB
import Tom.Machine.Api.MpSqr

/-!
# `mp_add(a, b, a)` and `mp_add(a, b, b)` with growth, read as values

On `MP_MEM` the destination at its old block, its sign set by the code
before the failing tail call), and `Out`: shaped, live, placed, grown only; on `MP_OKAY`
valid with value `a + b`. Proved in
`Fn/GrowT7.lean`.
-/

namespace Tom.Machine.Api.MpAddHA

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpAddGA (P R entry lay kind isW ws hin args Res)
open Tom.Machine.Api.MpSqr (X)

def out (p : P) : X → R → Kind
  | (_, q, x), .aS => .mpS p.pa q x
  | (_, q, x), .aD => .mpD q x.alloc x.digit
  | _, r => kind p r

def site' (_ : P) : X → Iv
  | (_, q, x) => ⟨q, 4 * x.alloc⟩

def hout (p : P) : X → List (Nat × Nat)
  | (_, q, x) => (q, 4 * x.alloc) :: p.H

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpGrow.memBV)]

/-- What `a` holds after: shaped, live, placed, grown only; on `MP_OKAY` the sum. -/
structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) (lay p .aD) (site' p x)
  grow : p.a.alloc ≤ x.2.2.alloc
  valid : x.1 = true → x.2.2.Valid
  val : x.1 = true → x.2.2.val = p.a.val + p.b.val

def Q (p : P) (x : X) : Prop := Out p x

/-- **`mp_add(a, b, a)` with growth**, read as values. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpAddHA

namespace Tom.Machine.Api.MpAddHB

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpAddGB (P R entry lay kind isW ws hin args Res)
open Tom.Machine.Api.MpSqr (X)

def out (p : P) : X → R → Kind
  | (_, q, x), .bS => .mpS p.pb q x
  | (_, q, x), .bD => .mpD q x.alloc x.digit
  | _, r => kind p r

def site' (_ : P) : X → Iv
  | (_, q, x) => ⟨q, 4 * x.alloc⟩

def hout (p : P) : X → List (Nat × Nat)
  | (_, q, x) => (q, 4 * x.alloc) :: p.H

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpGrow.memBV)]

/-- What `b` holds after: shaped, live, placed, grown only; on `MP_OKAY` the sum. -/
structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) (lay p .bD) (site' p x)
  grow : p.b.alloc ≤ x.2.2.alloc
  valid : x.1 = true → x.2.2.Valid
  val : x.1 = true → x.2.2.val = p.a.val + p.b.val

def Q (p : P) (x : X) : Prop := Out p x

/-- **`mp_add(a, b, b)` with growth**, read as values. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .bD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpAddHB
