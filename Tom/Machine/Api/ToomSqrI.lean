import Tom.Machine.Api.ToomSqr
import Tom.Machine.Api.MpSubH
import Tom.Machine.Api.Mul2H
import Tom.Machine.Api.MpSqrS
import Tom.Machine.Api.MpMulA

/-!
# What toom squaring's generated assembly proves

`s_mp_toom_sqr(a, b)`'s contract (`Api.ToomSqr.Statement`, the induction hypothesis in its
residue) from its callees' contracts (named premises, `Gaps`; all proved and discharged by
`Fn.ToomSqrG5.correctClosed`, `Fn/ToomSqrClosed.lean`, with `mulA` from `Fn.MulGroupB.mulCorrect`):

* `sub`, `subA`: the growing `mp_sub(a, b, c)`, `mp_sub(a, b, a)` (`Api/MpSubH.lean`);
* `mul2`: the growing `mp_mul_2(a, a)` (`Api/Mul2H.lean`);
* `sqrS`, `sqrSA`: `mp_sqr` below 120 digits without the room (`Api/MpSqrS.lean`): the frozen
  `Api.MpSqr.Res.room` is not met by `mp_sqr(&a0, &S0)` and `mp_sqr(b, b)` (see there), so the
  induction hypothesis (`SqrBelow`, over the frozen contract) covers those two calls only from
  120 digits on;
* `mulA`: `mp_mul(a, b, a)`.

The growing `mp_add`/`mp_lshd` are proved.
-/

namespace Tom.Machine.Api.ToomSqrI

structure Gaps : Prop where
  sub : MpSubH.Statement
  subA : MpSubHA.Statement
  mul2 : Mul2H.Statement
  sqrS : MpSqrS.Statement
  sqrSA : MpSqrSA.Statement
  mulA : MpMulA.Statement

def Statement : Prop := Gaps → ToomSqr.Statement

end Tom.Machine.Api.ToomSqrI
