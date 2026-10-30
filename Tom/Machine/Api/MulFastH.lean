import Tom.Machine.Api.SMpMulDigs
import Tom.Machine.Api.MpMul
import Tom.Machine.Api.MulFast

/-!
# `s_mp_mul_digs_fast(a, b, c, digs)` with growth: the allocating contract (a named premise)

`Api/MulFast.lean` (`Fn.MulFast.correct`) assumes `digs ≤ c->alloc` (D5: no `mp_grow`).
`mp_mul` calls the fast multiplier with `digs = a->used + b->used + 1` on any `c`
(karatsuba's `x0y0` has `2B` digits, so `mp_grow` always reallocates there): the code's
`if (c->alloc < digs) mp_grow(c, digs)` at its entry may re-place `c`'s digits or fail
(`MP_MEM`, everything kept). This file states that contract; it is **not proved** (the
growing path of `s_mp_mul_digs_fast` over `Api/StdHeapFn.lean`'s `mpGrowH`): a named
premise of `mp_mul`'s proof, reported to the parent.

Regions, parameters and heap as `Api/SMpMulDigs.lean`; results as `Api/MpMul.lean`
(`(ok, q, c')`). Stack: the 2192 bytes of `Api/MulFast.lean` and `mp_grow`'s 544 below them.
-/

namespace Tom.Machine.Api.MulFastH

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.SMpMulDigs (R P kind isW ws)
open Tom.Machine.Api.MpMul (X)

def entry : BitVec 64 := 0x800042f0#64

/-- The stack depth: `s_mp_mul_digs_fast`'s 2192 and `mp_grow`'s 544 (a plain `def`: a literal in
`lay`'s arm breaks its equation lemmas, `Api/SMpMulDigsW.lean`). -/
def F : Nat := 2736

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .cS => ⟨p.pc, 24⟩
  | .cD => ⟨p.cdp, 4 * p.c.alloc⟩
  | .code => textIv

def out (p : P) : X → R → Kind
  | (_, q, c'), .cS => .mpS p.pc q c'
  | (_, q, c'), .cD => .mpD q c'.alloc c'.digit
  | _, r => kind p r

def site' (_ : P) : X → Iv
  | (_, q, c') => ⟨q, 4 * c'.alloc⟩

def hin (p : P) : List (Nat × Nat) := digBlk p.cdp p.c :: p.H

def hout (p : P) : X → List (Nat × Nat)
  | (_, q, c') => (q, 4 * c'.alloc) :: p.H

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpInit.memBV)]

structure Res (p : P) : Prop where
  stk : StkRes p.sp 2736
  sa : p.a.ShapeU
  sb : p.b.ShapeU
  sc : p.c.Shape
  csign : p.c.sign = Layout.mpZpos ∨ p.c.sign = Layout.mpNeg
  /-- `MulFast.Cond`: `digs < MP_WARRAY`, `min ≤ MP_MAXFAST`, the `int` sums. -/
  cond : Api.MulFast.Cond p.a p.b p.digs
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  cpos : 0 < p.c.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24

/-- What `c` holds after: shaped and live; on `MP_OKAY` the truncated product, clamped. -/
structure Out (p : P) (ok : Bool) (c' : MpInt) : Prop where
  shape : c'.Shape
  sign : c'.sign = Layout.mpZpos ∨ c'.sign = Layout.mpNeg
  pos : 0 < c'.alloc
  mag : ok = true → c'.mag = (p.a.mag * p.b.mag) % radix ^ p.digs
  top : ok = true → 0 < c'.used → c'.digit (c'.used - 1) ≠ 0
  /-- `c`'s block kept or grown (`mp_grow(c, digs)` only when `c->alloc < digs`). -/
  grow : p.c.alloc ≤ c'.alloc
  /-- A nonnegative destination stays nonnegative (the clamp resets a zero result's sign, else keeps
  `c`'s; `mp_reduce`'s `q3 m`). -/
  zsign : p.c.sign = Layout.mpZpos → c'.sign = Layout.mpZpos

def Q (p : P) : X → Prop
  | (ok, _, c') => Out p ok c'

/-- **`s_mp_mul_digs_fast` with growth** (named premise, not proved). -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: Api.SMpMulDigs.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MulFastH
