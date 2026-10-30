import Tom.Spec.Ledger
import Tom.Spec.Reduce

/-!
# `mp_reduce_setup`: the model steps over the Ledger

`bn_mp_reduce_setup.c` at `0x800063a8` (frame 32): `mp_2expt(a, b->used * 2 * MP_DIGIT_BIT)`
(`slliw`/`subw`/`slliw`: `56 b->used`, an `int`), then the tail call `mp_div(a, b, a, NULL)`
(`a2 = a`, `a3 = 0` at `80006404`). Post: `ReduceSetupPost b a'` (`Tom/Spec/Reduce.lean`), checked
against the C and the disassembly; it is stated for `b > 0` (for `b < 0` the C leaves `-mu`).

Callee Posts: `mp_2expt` as `Api/Expt2.lean` (`Std.mp2expt`) gives it (`Expt2Post`, room D5);
`mp_div`: the frozen `Api/MpDiv.lean` covers `c`, `d` non-NULL and the four operands apart (D6);
this call passes `d = NULL` and `c = a`: **not covered**. The step is over the Spec Post
`DivQuot a b a a'` (`Tom/Spec/Div.lean`, the `c` half of that contract's `Q`); the C reads `a`
only before it writes `c` (`a->used`, the copy `x`, `neg`, and `x.sign` "before writing to c").
-/

namespace Tom.MpReduceSetupStep

open MpInt Ledger Reduce

variable {a b a2 a' : MpInt}

/-- The run's fixed facts (`b > 0`). -/
structure Env (a b : MpInt) : Prop where
  sa : a.Shape
  vb : b.Valid
  b0 : 0 < b.used
  bz : b.sign = Layout.mpZpos
  /-- `mp_2expt`'s `int b` (`Api/Expt2.lean` `k_lt`). -/
  k_lt : b.used * 2 * Layout.digitBits < 2 ^ 31
  /-- D5 for `mp_2expt` (`Api/Expt2.lean` `room`). -/
  room : b.used * 2 * Layout.digitBits / Layout.digitBits + 1 ≤ a.alloc

/-- `mp_2expt(a, b->used * 2 * MP_DIGIT_BIT)`: `a = radix^(2 b->used)`. -/
theorem a2_of (e : Env a b) (h : Expt2Post a (b.used * 2 * Layout.digitBits) a2) :
    Settled a2 a.alloc (radix ^ (2 * b.used)) Layout.mpZpos := by
  have s := xfer_expt2 e.room e.sa.alloc_lt h
  rwa [show b.used * 2 * Layout.digitBits = Layout.digitBits * (2 * b.used) by ac_rfl, Nat.pow_mul] at s

/-- `mp_div(a, b, a, NULL)`: `mu = ⌊radix^(2 b->used) / b⌋`. -/
theorem fin (e : Env a b) (h2 : Settled a2 a.alloc (radix ^ (2 * b.used)) Layout.mpZpos) (hq : DivQuot a2 b a2 a') :
    ReduceSetupPost b a' := by
  have hu : a2.used ≤ 2 * b.used + 1 :=
    used_le_of_lt h2.valid (by rw [h2.mag]; exact Nat.pow_lt_pow_right (by decide) (by omega))
  have s := xfer_divQuot h2.valid e.vb e.b0
    (by have hk := e.k_lt; rw [show Layout.digitBits = 28 from rfl] at hk; omega) h2.valid.alloc_lt hq
  refine ⟨s.valid, by rw [s.mag, h2.mag], ?_⟩
  rcases s.sign with h | h
  · exact h
  · rw [h, h2.zpos, e.bz]; simp [divSign]

end Tom.MpReduceSetupStep
