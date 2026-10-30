import Tom.Spec.Ledger
import Tom.Spec.Reduce

/-!
# `mp_mulmod`: the model steps over the Ledger

`bn_mp_mulmod.c` at `0x80005d90` (frame 96, `t` at `sp + 24`): `mp_init_size(&t, c->used)`
(`Api/StdHeapFn.lean` `mpInitSize`), `mp_mul(a, b, &t)` (`Api/MpMul.lean`: `t` distinct from `a`,
`b`; `Out.post` gives `MulPost a b t'` on `MP_OKAY`), `mp_mod(&t, c, d)`, `mp_clear(&t)`.
Post: `MulmodPost a b c d'` (`Tom/Spec/Reduce.lean`), stated for `c > 0`; checked against the C and
the disassembly (for `c < 0` the C leaves `(a b).fmod c`, which `MulmodPost` does not state).

Callee Posts: `mp_mul` as `Api/MpMul.lean` gives it; `mp_mod` has **no machine contract yet**: the
step is over its Spec Post `ModPost` (`Tom/Spec/Div.lean`, `Tom/Spec/MpModStep.lean`).
-/

namespace Tom.MpMulmodStep

open MpInt Ledger Reduce

variable {a b c t d' : MpInt}

/-- The run's fixed facts (`c > 0`). -/
structure Env (c : MpInt) : Prop where
  vc : c.Valid
  c0 : 0 < c.used
  cz : c.sign = Layout.mpZpos

theorem Env.cpos (e : Env c) : 0 < c.val := by
  rw [val_zpos e.cz]; exact Int.ofNat_lt.2 (e.vc.mag_pos e.c0)

/-- `mp_init_size(&t, c->used)`, `mp_mul(a, b, &t)`: `t = a b`. -/
theorem t_of (h : MulPost a b t) : HasVal t (a.val * b.val) := ⟨h.valid, h.val⟩

/-- The product's digit count (`mp_mod`'s `mp_div` needs `t->used + 3 < 2^30`). -/
theorem t_used (ha : a.Shape) (hb : b.Shape) (h : MulPost a b t) : t.used ≤ a.used + b.used := by
  refine used_le_of_lt h.valid ?_
  rw [← natAbs_val, h.val, Int.natAbs_mul, natAbs_val, natAbs_val, Nat.pow_add]
  exact Nat.mul_lt_mul'' (MpInt.mag_lt ha) (MpInt.mag_lt hb)

/-- `mp_mod(&t, c, d)`: `MulmodPost`. -/
theorem fin (e : Env c) (ht : HasVal t (a.val * b.val)) (hm : ModPost t c d') : MulmodPost a b c d' :=
  have h := xfer_mod ht.valid e.vc e.c0 e.cpos hm
  ⟨h.valid, by rw [h.val, ht.val]⟩

end Tom.MpMulmodStep
