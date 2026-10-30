import Tom.Machine.Api.MpLshd
import Tom.Machine.Api.MpSqr

/-!
# `mp_lshd(a, k)` with growth: the allocating contract (a named premise)

`Api/MpLshd.lean` (`Fn.MpLshd.correct`) assumes `a->used + k ≤ a->alloc` (D5).
`s_mp_karatsuba_sqr`'s `mp_lshd(&x1x1, 2B)` shifts `x1x1` (allocated with `2 (a->used - B)`
digits) by `2B` digits: `mp_grow(a, a->used + k)` re-places its digits (or fails, `MP_MEM`).
This file states that contract; it is **not proved** (the growing path over
`Api/StdHeapFn.lean`'s `mpGrowH`): a named premise of karatsuba's proof, reported to the parent.

Regions `Api/Un.lean`'s, the site `a`'s digits; result `(ok, q, a')`. Stack: 576 bytes
(`mp_lshd`'s frame and `mp_grow`'s 544).
-/

namespace Tom.Machine.Api.MpLshdH

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.Un (R isW ws)
open Tom.Machine.Api.MpSqr (X)

def entry : BitVec 64 := 0x800015b8#64

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt
  k : Nat
  H : List (Nat × Nat)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - 576, 576⟩
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

def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.k)]

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpInit.memBV)]

structure Res (p : P) : Prop where
  stk : StkRes p.sp 576
  va : p.a.Valid
  /-- `a->used + k` is an `int` (`mp_grow`'s size). -/
  uk : p.a.used + p.k < 2 ^ 30
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

/-- What `a` holds after: shaped, live, grown only; on `MP_OKAY` shifted by `k` digits. -/
structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) (lay p .aD) (site' p x)
  grow : p.a.alloc ≤ x.2.2.alloc
  valid : x.1 = true → x.2.2.Valid
  mag : x.1 = true → x.2.2.mag = p.a.mag * radix ^ p.k
  sign : x.1 = true → x.2.2.sign = p.a.sign

def Q (p : P) (x : X) : Prop := Out p x

/-- **`mp_lshd(a, k)` with growth** (named premise, not proved). -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpLshdH
