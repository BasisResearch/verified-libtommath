import Tom.Machine.Api.SqrAlg

/-!
# `s_mp_karatsuba_sqr(a, b)` (`b` distinct, and `b = a`): the contracts

`vendor/libtommath/bn_s_mp_karatsuba_sqr.c`, compiled at `0x80006794` (frame 192):
`B = a->used >> 1`; six temporaries by `mp_init_size` (`x0` of `B` digits, `x1` of
`a->used - B`, `t1`, `t2` of `2 a->used`, `x0x0` of `2B`, `x1x1` of `2 (a->used - B)`), the
digits copied (`x0 = a mod R`, `x1 = a / R`, `R = radix^B`), `x0` clamped,
`x0x0 = x0²`, `x1x1 = x1²` (`mp_sqr`), `t1 = x1 + x0` (`s_mp_add`), `t1 := t1²`
(`mp_sqr(&t1, &t1)`), `t2 = x0x0 + x1x1` (`s_mp_add`), `t1 := t1 - t2` (`s_mp_sub`),
`t1 := t1 R`, `x1x1 := x1x1 R²` (`mp_lshd`), `t1 := x0x0 + t1`, `b := t1 + x1x1`
(`mp_add`), the six `mp_clear`s; any failure (`MP_MEM`) jumps to the clears of the
temporaries allocated so far. `karatsuba_sqr_val`: `|b'| = |a|²`.

`mp_sqr` calls it only with `120 ≤ a->used < 400`, so `B ≥ 60` and every recursive
`mp_sqr` is on `a->used - 59` digits or fewer: the residue carries those facts and the
induction hypothesis.
-/

namespace Tom.Machine.Api.KSqr

open Tom.Machine Tom.Machine.Api

def entry : BitVec 64 := 0x80006794#64

/-- What `s_mp_karatsuba_sqr(a, b)` needs. -/
structure Res (p : MpSqr.P) : Prop extends SqrAlg.Base p where
  /-- `mp_sqr`'s dispatch: `a->used ≥ KARATSUBA_SQR_CUTOFF = 120`. -/
  kmin : 120 ≤ p.a.used
  /-- `mp_sqr`'s dispatch: `a->used < TOOM_SQR_CUTOFF = 400` (toom is tested first). -/
  kmax : p.a.used < 400
  /-- The recursive `mp_sqr`s below the measure. -/
  ih : SqrRec.SqrBelow p.a.used

def Spec (p : MpSqr.P) : Prop := SqrAlg.SpecR entry Res p

/-- **`s_mp_karatsuba_sqr(a, b)` on the machine.** -/
def Statement : Prop := ∀ p : MpSqr.P, Spec p

/-- What `s_mp_karatsuba_sqr(a, a)` needs. -/
structure ResA (p : MpSqrA.P) : Prop extends SqrAlg.BaseA p where
  kmin : 120 ≤ p.a.used
  kmax : p.a.used < 400
  ih : SqrRec.SqrBelow p.a.used

def SpecA (p : MpSqrA.P) : Prop := SqrAlg.SpecRA entry ResA p

/-- **`s_mp_karatsuba_sqr(a, a)` on the machine.** -/
def StatementA : Prop := ∀ p : MpSqrA.P, SpecA p

end Tom.Machine.Api.KSqr
