import Tom.Machine.Api.MpAddG
import Tom.Machine.Api.MpAddGA
import Tom.Spec.SubGStep

/-!
# `mp_sub(a, b, c)` and `mp_sub(a, b, a)` with growth: the allocating contracts

`bn_mp_sub.c` at `0x80001ef4`: unequal signs: `c->sign = a->sign`, tail call `s_mp_add(a, b, c)`;
equal signs: a 48-byte frame around `mp_cmp_mag(a, b)`, popped before the tail call
`s_mp_sub(a, b, c)` (`|a| ≥ |b|`, `c->sign = b->sign`) or `s_mp_sub(b, a, c)` (`c->sign` the
flip of `b->sign` by `seqz` at `1f68`). The regions,
residue, stack (608: `s_mp_add`'s 64-byte frame with `mp_grow`'s 544) and heap are `mp_add`'s
exactly (`Api/MpAddG.lean`, `Api/MpAddGA.lean`, reused): the sign before the call is `subSign`,
the posts by branch are `SubG` (`Tom/Spec/SubGStep.lean`). Results: `none` (`MP_MEM`, only when
it had to grow; the destination changed only in its sign), `some (q, x)` with `x`'s digits at `q`.
-/

namespace Tom.Machine.Api.MpSubG

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpAddG (P R lay kind isW ws args Res)

def entry : BitVec 64 := 0x80001ef4#64

/-- The stack depth: the tail callees' (`s_mp_add`'s 64-byte frame and `mp_grow`'s; the own 48-byte frame is popped before the tail calls). -/
abbrev F : Nat := 64 + MpGrow.F

/-- After: `none` on `MP_MEM` (`c` with the branch's sign), `some (q, x)` with `x`'s digits at `q`. -/
def out (p : P) : Option (Nat × MpInt) → R → Kind
  | some (q, x), .cS => .mpS p.pc q x
  | some (q, x), .cD => .mpD q x.alloc x.digit
  | none, .cS => .mpS p.pc p.cdp (p.c.withSign (subSign p.a p.b))
  | _, r => kind p r

def site' (p : P) : Option (Nat × MpInt) → Iv
  | none => lay p .cD
  | some (q, x) => ⟨q, 4 * x.alloc⟩

/-- `c`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.cdp p.c :: p.H

def hout (p : P) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => hin p
  | some (q, x) => (q, 4 * x.alloc) :: p.H

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpGrow.memBV | some _ => 0#64)]

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.c.alloc < subSize p.a p.b
  | some (_, x) => SubG p.a p.b (SAddPost p.a p.b (sAddIn p.a p.b (p.c.withSign p.a.sign)) x)
      (SSubPost p.b p.a (sSubIn p.b (p.c.withSign (if p.b.sign = 0 then 1 else 0))) x)
      (SSubPost p.a p.b (sSubIn p.a (p.c.withSign p.b.sign)) x)

/-- **`mp_sub(a, b, c)` on the machine, growing `c`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpSubG

namespace Tom.Machine.Api.MpSubGA

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpAddGA (P R lay kind isW ws args Res)

def entry : BitVec 64 := 0x80001ef4#64

abbrev F : Nat := 64 + MpGrow.F

/-- After: `none` on `MP_MEM` (`a` with the branch's sign), `some (q, x)` with `x`'s digits at `q`. -/
def out (p : P) : Option (Nat × MpInt) → R → Kind
  | some (q, x), .aS => .mpS p.pa q x
  | some (q, x), .aD => .mpD q x.alloc x.digit
  | none, .aS => .mpS p.pa p.adp (p.a.withSign (subSign p.a p.b))
  | _, r => kind p r

def site' (p : P) : Option (Nat × MpInt) → Iv
  | none => lay p .aD
  | some (q, x) => ⟨q, 4 * x.alloc⟩

/-- `a`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.adp p.a :: p.H

def hout (p : P) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => hin p
  | some (q, x) => (q, 4 * x.alloc) :: p.H

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpGrow.memBV | some _ => 0#64)]

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.a.alloc < subSize p.a p.b
  | some (_, x) => SubG p.a p.b
      (SAddPost (p.a.withSign p.a.sign) p.b (sAddIn (p.a.withSign p.a.sign) p.b (p.a.withSign p.a.sign)) x)
      (SSubPost p.b (p.a.withSign (if p.b.sign = 0 then 1 else 0))
        (sSubIn p.b (p.a.withSign (if p.b.sign = 0 then 1 else 0))) x)
      (SSubPost (p.a.withSign p.b.sign) p.b (sSubIn (p.a.withSign p.b.sign) (p.a.withSign p.b.sign)) x)

/-- **`mp_sub(a, b, a)` on the machine, growing `a`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpSubGA
