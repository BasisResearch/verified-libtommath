import Tom.Machine.Api.SqrAlg
import Tom.Machine.Api.Two
import Tom.Machine.Api.Un
import Tom.Spec.SqrFastGStep

/-!
# `s_mp_sqr_fast(a, b)` and `s_mp_sqr_fast(a, a)` with growth: the allocating contracts

`Api/SqrFast.lean` assumes `2 a->used ≤ b->alloc` (D5). `mp_sqr` calls the comba squarer below
`KARATSUBA_SQR_CUTOFF` on any `b`, and `bn_s_mp_sqr_fast.c` opens with
`if (b->alloc < 2 a->used) mp_grow(b, 2 a->used)` (`blt` at `7060`, the call at `7150`, then its
own copy of the loop set-up at `7158`): `b`'s digits may be re-placed (or `MP_MEM`, everything
kept). Regions `Api/Two.lean`'s (`Api/Un.lean`'s in place), the site `b`'s digits; results and
`Q` as `mp_sqr`'s algorithms (`Api.SqrAlg.Out`: on `MP_OKAY` valid with `|b'| = |a|²`, grown
only, placed). Stack: the 2208-byte frame (with `W[MP_WARRAY]`) and `mp_grow`'s 544 below it.
-/

namespace Tom.Machine.Api.SqrFastH

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.Two (R isW ws)
open Tom.Machine.Api.MpSqr (X)

def entry : BitVec 64 := 0x80007010#64

/-- The stack depth (a plain `def`: a literal in `lay`'s arm breaks its equation lemmas). -/
def F : Nat := 2752

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
  | .stk => ⟨p.sp - F, F⟩
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

def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpInit.memBV)]

/-- What `s_mp_sqr_fast(a, b)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 2752
  /-- The loops read `a`'s digits below `used`. -/
  sa : p.a.Shape
  /-- `b`'s old digits above the result are zeroed only up to its old `used`. -/
  sb : p.b.Shape
  /-- `mp_clamp` keeps the sign word for a nonzero result (`SqrFastPost.spec`). -/
  bsign : p.b.sign = Layout.mpZpos ∨ p.b.sign = Layout.mpNeg
  /-- `MP_WARRAY` (`2 a->used + 1 < 512`, which `mp_sqr` checks): every column fits 64 bits. -/
  warr : 2 * p.a.used + 1 < 512
  /-- Nonempty digit arrays (`HContract.pos`). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- `b`'s struct is off the arena (`mp_grow` reads and writes it). -/
  boff : OffHeap p.pb 24

def Q (p : P) (x : X) : Prop := SqrAlg.Out p.a p.b.alloc (hin p) (lay p .bD) x

/-- **`s_mp_sqr_fast(a, b)` on the machine, growing `b`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .bD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.SqrFastH
