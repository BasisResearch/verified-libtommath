import Tom.Machine.Api.MpSubAlias
import Tom.Machine.Api.MpAddAlias

/-!
# `mp_sub(a, b, a)` and `mp_add(a, b, a)` on their subtracting branches

`Api/MpSubAlias.lean`/`Api/MpAddAlias.lean` assume `max(used) + 1 ≤ a->alloc` for the
`s_mp_add` branch. When the signs decide that the branch is `s_mp_sub` (`mp_sub` of two
operands of the same sign, `mp_add` of two of different signs), the C needs only
`max(used) ≤ a->alloc` (`s_mp_sub(a, b, a)` writes `a->used` digits, `s_mp_sub(b, a, a)`
`b->used`). `mp_div` has exactly that room: after `mp_mul_2d` grows `x` to `x.used` digits,
`mp_sub(&x, &y, &x)` and the add-back `mp_add(&x, &t1, &x)` (`x < 0 ≤ t1`) run with
`x.used = x.alloc`.
-/

namespace Tom.Machine.Api.MpSubAddS

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.BinA

/-- What `mp_sub(a, b, a)` with `a`, `b` of the same sign needs. -/
structure PreS (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop
    extends Base m 64 sp pa adp pb bdp a b ra where
  va : a.Valid
  vb : b.Valid
  /-- The signs pick `s_mp_sub` (`mp_sub`'s `a->sign == b->sign` branch). -/
  same : a.sign = b.sign
  /-- D5 for `s_mp_sub(a, b, a)` / `s_mp_sub(b, a, a)`. -/
  room : max a.used b.used ≤ a.alloc
  lay : Sound (MpSubAlias.lay sp pa adp pb bdp a b) isWA

/-- What `mp_add(a, b, a)` with `a`, `b` of different signs needs. -/
structure PreD (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop
    extends Base m 64 sp pa adp pb bdp a b ra where
  va : a.Valid
  vb : b.Valid
  /-- The signs pick `s_mp_sub` (`mp_add`'s `a->sign != b->sign` branch). -/
  diff : a.sign ≠ b.sign
  /-- D5 for `s_mp_sub(a, b, a)` / `s_mp_sub(b, a, a)`. -/
  room : max a.used b.used ≤ a.alloc
  lay : Sound (MpAddAlias.lay sp pa adp pb bdp a b) isWA

/-- **`mp_sub(a, b, a)`, same signs, on the machine.** -/
def StatementS : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    PreS m sp pa adp pb bdp a b ra →
    Triple (At MpSubAlias.entry (Fn.SSub.entryL ra s0 sp pa pb pa) m v.keepR outp)
      (MpSubAlias.RetCA m v outp sp pa adp pb bdp a b ra s0)

/-- **`mp_add(a, b, a)`, different signs, on the machine.** -/
def StatementD : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    PreD m sp pa adp pb bdp a b ra →
    Triple (At MpAddAlias.entry (Fn.SSub.entryL ra s0 sp pa pb pa) m v.keepR outp)
      (MpAddAlias.RetCA m v outp sp pa adp pb bdp a b ra s0)

end Tom.Machine.Api.MpSubAddS
