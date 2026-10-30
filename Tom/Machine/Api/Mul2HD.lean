import Tom.Machine.Api.Mul2H
import Tom.Machine.Api.Two

/-!
# `mp_mul_2(a, b)` with growth, `b` distinct: the allocating contract

`bn_mp_mul_2.c` at `0x80005ca0` (frame 32) as `Api/Mul2H.lean` states it in place, with the
destination `b` distinct (`s_mp_toom_mul`'s `mp_mul_2(&b1, &T1)`: `T1` is not known to have
room for `2 b1`): `if (b->alloc < a->used + 1) mp_grow(b, a->used + 1)`, the doubling loop
reading `a`'s digits into `b`'s, the carry digit, `memset` of `b`'s old digits above, then
`b->sign = a->sign`. Regions `Api/Two.lean`'s (`b` written), the site `b`'s digits, stack 576
(the frame and `mp_grow`'s 544; `memset` runs in the frame's shadow). Result `(ok, q, b')`; on
`MP_OKAY` `b'` valid with value `2 a`. Proved by `Fn.Mul2HDG5.correct` (`mul2hd.asm.json`).
-/

namespace Tom.Machine.Api.Mul2HD

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.Two (R isW ws)
open Tom.Machine.Api.MpSqr (X)

def entry : BitVec 64 := 0x80005ca0#64

abbrev F : Nat := 576

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt
  H : List (Nat × Nat)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - 576, 576⟩
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

def out (p : P) : X → R → Kind
  | (_, q, b'), .bS => .mpS p.pb q b'
  | (_, q, b'), .bD => .mpD q b'.alloc b'.digit
  | _, r => kind p r

def site' (_ : P) : X → Iv
  | (_, q, b') => ⟨q, 4 * b'.alloc⟩

/-- `b`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.bdp p.b :: p.H

def hout (p : P) : X → List (Nat × Nat)
  | (_, q, b') => (q, 4 * b'.alloc) :: p.H

/-- The arguments: `a0 = a`, `a1 = b` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpInit.memBV)]

structure Res (p : P) : Prop where
  stk : StkRes p.sp 576
  va : p.a.Valid
  /-- `mp_grow` and the `memset` read `b`'s header (`b` shaped; its sign is overwritten). -/
  sb : p.b.Shape
  /-- `a->used + 1` is an `int` (`mp_grow`'s size). -/
  ua : p.a.used + 1 < 2 ^ 30
  /-- The operands' digit arrays are nonempty (initialised `mp_int`s). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- `b`'s struct is off the arena (`mp_grow` reads and writes it). -/
  boff : OffHeap p.pb 24

/-- What `b` holds after: shaped, live, placed, grown only; on `MP_OKAY` `2 a`. -/
structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) (lay p .bD) (site' p x)
  grow : p.b.alloc ≤ x.2.2.alloc
  valid : x.1 = true → x.2.2.Valid
  val : x.1 = true → x.2.2.val = 2 * p.a.val

def Q (p : P) (x : X) : Prop := Out p x

/-- **`mp_mul_2(a, b)` with growth, `b` distinct.** -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .bD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.Mul2HD
