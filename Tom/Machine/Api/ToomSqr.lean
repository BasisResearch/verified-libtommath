import Tom.Machine.Api.SqrAlg

/-!
# `s_mp_toom_sqr(a, b)` (`b` distinct, and `b = a`): the contracts

`vendor/libtommath/bn_s_mp_toom_sqr.c`, compiled at `0x800072cc` (frame 160): Toom-3
squaring (Chung–Hasan SQR_3): `B = a->used / 3`, `a = a2 x² + a1 x + a0` (`x = radix^B`),
`S0 = a0²`, `(a0 + a2 + a1)²`, `(a0 + a2 - a1)²` (in `b`), `2 a1 a2` (`mp_mul`, `mp_mul_2`),
`a2²`, the interpolation (`mp_add`, `mp_sub`, `mp_div_2`) and the recomposition (`mp_lshd`,
`mp_add`) into `b`. It uses `b` as a temporary, so on `MP_MEM` `b` is only shaped.

`mp_sqr` calls it only with `a->used ≥ TOOM_SQR_CUTOFF = 400` (`B ≥ 133`; every recursive
`mp_sqr` is on at most `B + 2` digits). Its `mp_mul(&a1, &a2, &a1)` reads `mp_mul`'s cut-offs
(the regions `km`, `tm` of `Api.MpSqr`).
-/

namespace Tom.Machine.Api.ToomSqr

open Tom.Machine Tom.Machine.Api

def entry : BitVec 64 := 0x800072cc#64

/-- What `s_mp_toom_sqr(a, b)` needs. -/
structure Res (p : MpSqr.P) : Prop extends SqrAlg.Base p where
  /-- `mp_sqr`'s dispatch: `a->used ≥ TOOM_SQR_CUTOFF = 400`. -/
  tmin : 400 ≤ p.a.used
  /-- The recursive `mp_sqr`s below the measure. -/
  ih : SqrRec.SqrBelow p.a.used

def Spec (p : MpSqr.P) : Prop := SqrAlg.SpecR entry Res p

/-- **`s_mp_toom_sqr(a, b)` on the machine.** -/
def Statement : Prop := ∀ p : MpSqr.P, Spec p

/-- What `s_mp_toom_sqr(a, a)` needs. -/
structure ResA (p : MpSqrA.P) : Prop extends SqrAlg.BaseA p where
  tmin : 400 ≤ p.a.used
  ih : SqrRec.SqrBelow p.a.used

def SpecA (p : MpSqrA.P) : Prop := SqrAlg.SpecRA entry ResA p

/-- **`s_mp_toom_sqr(a, a)` on the machine.** -/
def StatementA : Prop := ∀ p : MpSqrA.P, SpecA p

end Tom.Machine.Api.ToomSqr
