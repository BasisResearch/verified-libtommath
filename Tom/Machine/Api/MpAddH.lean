import Tom.Machine.Api.MpAdd
import Tom.Machine.Api.MpSqr

/-!
# `mp_add(a, b, c)` with growth, `c` distinct: the allocating contract (a named premise)

`Api/MpAdd.lean` (`Api.MpAdd.correct`) assumes `max(a->used, b->used) + 1 ≤ c->alloc` (D5:
no `mp_grow`). `s_mp_karatsuba_sqr`'s last `mp_add(&t1, &x1x1, b)` writes `mp_sqr`'s
destination, which may be too small (karatsuba below karatsuba: `x0x0` has exactly `2B`
digits): `s_mp_add`/`s_mp_sub`'s `mp_grow(c, …)` may re-place `c`'s digits or fail
(`MP_MEM`). This file states that contract; it is **not proved** (the growing paths of
`s_mp_add`/`s_mp_sub` over `Api/StdHeapFn.lean`'s `mpGrowH`): a named premise of
karatsuba's proof, reported to the parent.

Regions `Api/Bin.lean`'s, the site `c`'s digits; result `(ok, q, c')` as `Api/MpSqr.lean`'s.
Stack: 608 bytes (`mp_add`'s 64, with the tail-called `s_mp_add`, and `mp_grow`'s 544).
-/

namespace Tom.Machine.Api.MpAddH

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.Bin (R isW ws)
open Tom.Machine.Api.MpSqr (X)

def entry : BitVec 64 := 0x80000608#64

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

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - 608, 608⟩
  | .cS => ⟨p.pc, 24⟩
  | .cD => ⟨p.cdp, 4 * p.c.alloc⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .cS => .mpS p.pc p.cdp p.c
  | .cD => .mpD p.cdp p.c.alloc p.c.digit
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .bS => .mpS p.pb p.bdp p.b
  | .bD => .mpD p.bdp p.b.alloc p.b.digit
  | .code => .code

def out (p : P) : X → R → Kind
  | (_, q, c'), .cS => .mpS p.pc q c'
  | (_, q, c'), .cD => .mpD q c'.alloc c'.digit
  | _, r => kind p r

def site' (_ : P) : X → Iv
  | (_, q, c') => ⟨q, 4 * c'.alloc⟩

def hin (p : P) : List (Nat × Nat) := digBlk p.cdp p.c :: p.H

def hout (p : P) : X → List (Nat × Nat)
  | (_, q, c') => (q, 4 * c'.alloc) :: p.H

def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
   (12, BitVec.ofNat 64 p.pc)]

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpInit.memBV)]

structure Res (p : P) : Prop where
  stk : StkRes p.sp 608
  va : p.a.Valid
  vb : p.b.Valid
  sc : p.c.Shape
  /-- `max + 1` is an `int` (`mp_grow`'s size). -/
  ab : max p.a.used p.b.used < 2 ^ 30
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  cpos : 0 < p.c.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24

/-- What `c` holds after: shaped, live, grown only; on `MP_OKAY` the sum. -/
structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) (lay p .cD) (site' p x)
  grow : p.c.alloc ≤ x.2.2.alloc
  valid : x.1 = true → x.2.2.Valid
  val : x.1 = true → x.2.2.val = p.a.val + p.b.val

def Q (p : P) (x : X) : Prop := Out p x

/-- **`mp_add(a, b, c)` with growth** (named premise, not proved). -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpAddH
