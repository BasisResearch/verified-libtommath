import Tom.Machine.Api.MpLshdH

/-!
# `mp_mul_2(a, a)` with growth: the allocating contract

`bn_mp_mul_2.c` at `0x80005ca0` (frame 32): `if (b->alloc < a->used + 1) mp_grow(b, a->used + 1)`
(`bge a1, a5` at `5cc0`, the call at `5d80`), then the doubling loop, the carry digit, the zeroed
tail (`memset`) and `b->sign = a->sign`. In place (`b = a`) it reads each digit before writing
it. `Api/Mul2.lean` (`Fn.Mul2.InPlace.correct_inplace`, `Std.mul2I`) assumes the room (D5). Here
the growing path: result `(ok, q, a')` as `Api/MpLshdH.lean`'s, regions `Api/Un.lean`'s, the site
`a`'s digits, stack 576 (the 32-byte frame and `mp_grow`'s 544). Used by `s_mp_toom_sqr`'s
`mp_mul_2(&a1, &a1)` (`a1 = a1·a2` from `mp_mul`, whose room is not known). Proved by
`Fn.Mul2HG5.correct` (`Fn/Mul2HMainG.lean`).
-/

namespace Tom.Machine.Api.Mul2H

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.Un (R isW ws)
open Tom.Machine.Api.MpSqr (X)

def entry : BitVec 64 := 0x80005ca0#64

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt
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

/-- The arguments: `a0 = a1 = a` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pa)]

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpInit.memBV)]

structure Res (p : P) : Prop where
  stk : StkRes p.sp 576
  va : p.a.Valid
  /-- `a->used + 1` is an `int` (`mp_grow`'s size). -/
  ua : p.a.used + 1 < 2 ^ 30
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

/-- What `a` holds after: shaped, live, placed, grown only; on `MP_OKAY` doubled. -/
structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) (lay p .aD) (site' p x)
  grow : p.a.alloc ≤ x.2.2.alloc
  valid : x.1 = true → x.2.2.Valid
  val : x.1 = true → x.2.2.val = 2 * p.a.val

def Q (p : P) (x : X) : Prop := Out p x

/-- **`mp_mul_2(a, a)` with growth** (proved: `Fn.Mul2HG5.correct`). -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.Mul2H
