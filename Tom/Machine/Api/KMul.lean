import Tom.Machine.Api.MulAlg

/-!
# `s_mp_karatsuba_mul(a, b, c)`, `c` distinct: the contract

`vendor/libtommath/bn_s_mp_karatsuba_mul.c`, compiled at `0x80003a98` (frame 240):
`B = min(a->used, b->used) >> 1`; seven temporaries by `mp_init_size` (`x0`, `y0` of
`B` digits, `x1`, `y1` of `a->used - B`, `b->used - B`, `t1`, `x0y0`, `x1y1` of `2B`;
structs at `sp+8`, `sp+56`, `sp+32`, `sp+80`, `sp+104`, `sp+128`, `sp+152`), the digits
copied (`x0 = a mod R`, `x1 = a / R`, `R = radix^B`, `natUpTo_split`), `x0`, `y0` clamped,
`x0y0 = x0 y0`, `x1y1 = x1 y1` (`mp_mul`), `t1 = x1 + x0`, `x0 := y1 + y0` (`s_mp_add`),
`t1 := t1 x0` (`mp_mul(&t1, &x0, &t1)`), `x0 := x0y0 + x1y1` (`mp_add`),
`t1 := t1 - x0` (`s_mp_sub`, `karatsuba_ge`), `t1 := t1 R`, `x1y1 := x1y1 R²` (`mp_lshd`),
`t1 := x0y0 + t1`, `c := t1 + x1y1` (`mp_add`), the seven `mp_clear`s; any failure
(`MP_MEM`) jumps to the clears of the temporaries allocated so far. `karatsuba_val`:
`|c'| = |a| |b|`.

`mp_mul` calls it only with `KARATSUBA_MUL_CUTOFF ≤ min` and not balanced (`max < 2 min`),
so `B ≥ 40` and every recursive `mp_mul` is on measure `≤ μ - 78`: the
residue carries those facts and the induction hypothesis.
-/

namespace Tom.Machine.Api.KMul

open Tom.Machine Tom.Machine.Api
open Tom.Machine.Api.MpMul (P μ)

def entry : BitVec 64 := 0x80003a98#64

/-- What `s_mp_karatsuba_mul(a, b, c)` needs. -/
structure Res (p : P) : Prop extends MulAlg.Base p where
  /-- `mp_mul`'s dispatch: `min ≥ KARATSUBA_MUL_CUTOFF = 80`. -/
  kmin : 80 ≤ min p.a.used p.b.used
  /-- `mp_mul`'s dispatch: not the balanced case (`s_mp_balance_mul` is tested first). -/
  kbal : max p.a.used p.b.used < 2 * min p.a.used p.b.used
  /-- The recursive `mp_mul`s below the measure. -/
  ih : MulRec.MulBelow (μ p.a p.b)

def Spec (p : P) : Prop := MulAlg.SpecR entry Res p

/-- **`s_mp_karatsuba_mul(a, b, c)` on the machine.** -/
def Statement : Prop := ∀ p : P, Spec p

end Tom.Machine.Api.KMul
