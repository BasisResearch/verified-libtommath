import Tom.Machine.Api.MpAddGB
import Tom.Machine.Api.MpAddHA
import Tom.Machine.Api.MpSubH
import Tom.Spec.SubGBStep

/-!
# `mp_sub(a, b, b)` with growth: the allocating contract and its value form

The regions, residue, stack and heap are `mp_add(a, b, b)`'s
(`Api/MpAddGB.lean`, reused). `MpSubHB` is the same call read as values (`Api/MpSubH.lean`'s
`MpSubHA` with `b`): result `(ok, q, x)`, on `MP_OKAY` `x` valid with value `a − b`.
-/

namespace Tom.Machine.Api.MpSubGB

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpAddGB (P R lay kind isW ws args Res)

def entry : BitVec 64 := 0x80001ef4#64

abbrev F : Nat := 64 + MpGrow.F

/-- After: `none` on `MP_MEM` (`b` with the branch's sign), `some (q, x)` with `x`'s digits at `q`. -/
def out (p : P) : Option (Nat × MpInt) → R → Kind
  | some (q, x), .bS => .mpS p.pb q x
  | some (q, x), .bD => .mpD q x.alloc x.digit
  | none, .bS => .mpS p.pb p.bdp (p.b.withSign (subSign p.a p.b))
  | _, r => kind p r

def site' (p : P) : Option (Nat × MpInt) → Iv
  | none => lay p .bD
  | some (q, x) => ⟨q, 4 * x.alloc⟩

/-- `b`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.bdp p.b :: p.H

def hout (p : P) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => hin p
  | some (q, x) => (q, 4 * x.alloc) :: p.H

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpGrow.memBV | some _ => 0#64)]

/-- The tail callee's post by branch: `s_mp_add(a, b, b)`, `s_mp_sub(b, a, b)`, `s_mp_sub(a, b, b)`,
each over `b` with the sign `mp_sub` stored. -/
def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.b.alloc < subSize p.a p.b
  | some (_, x) => SubG p.a p.b
      (SAddPost p.a (p.b.withSign p.a.sign) (sAddIn p.a (p.b.withSign p.a.sign) (p.b.withSign p.a.sign)) x)
      (SSubPost (p.b.withSign (if p.b.sign = 0 then 1 else 0)) p.a
        (sSubIn (p.b.withSign (if p.b.sign = 0 then 1 else 0)) (p.b.withSign (if p.b.sign = 0 then 1 else 0))) x)
      (SSubPost p.a (p.b.withSign p.b.sign) (sSubIn p.a (p.b.withSign p.b.sign)) x)

/-- **`mp_sub(a, b, b)` on the machine, growing `b`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .bD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpSubGB

namespace Tom.Machine.Api.MpSubHB

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpAddGB (P R lay kind isW ws hin args Res)
open Tom.Machine.Api.MpAddHB (out site' hout rets)

def entry : BitVec 64 := 0x80001ef4#64

/-- What `b` holds after: shaped, live, placed, grown only; on `MP_OKAY` the difference. -/
structure Out (p : P) (x : MpSqr.X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) (lay p .bD) (site' p x)
  grow : p.b.alloc ≤ x.2.2.alloc
  valid : x.1 = true → x.2.2.Valid
  val : x.1 = true → x.2.2.val = p.a.val - p.b.val

def Q (p : P) (x : MpSqr.X) : Prop := Out p x

/-- **`mp_sub(a, b, b)` with growth**, read as values. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .bD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpSubHB
