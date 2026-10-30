import Tom.Machine.Api.SMpMulDigs

/-!
# `s_mp_mul_digs`'s fast path: the result of the tail call

The tail call `s_mp_mul_digs_fast(a, b, c, digs)` at `42c4` (`"tail" … "flat"`,
`experiments/asm/smdigs.asm.json`); its post becomes the contract's by `HPost.inplace`
(Kit/Run.lean). `fast_q`: `MulFastPost` as the contract's `Q` (`|c'| = |a||b| mod R^digs`).
-/

namespace Tom.Machine.Fn.SMpMulDigsG5K

open Tom.Machine Tom.Machine.Api
open Tom.Machine.Api.SMpMulDigs (P Q Fast Res)

theorem fast_q {p : P} {c' : MpInt} (hres : Res p) (hf : Fast p.a p.b p.digs)
    (hq : MulFastPost p.a p.b p.c c' p.digs) : Q p (some (p.cdp, c')) := by
  have hsp := MulFastPost.spec hres.sa hres.sb (hres.room hf) hres.sc.alloc_lt hres.csign hq
  refine ⟨hsp.1, ?_, fun _ => ⟨rfl, hq⟩, fun h => absurd hf h⟩
  by_cases hd : p.a.used + p.b.used ≤ p.digs
  · rw [hsp.2.2 hd]
    refine (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ?_ (Nat.pow_le_pow_right radix_pos hd))).symm
    rw [Nat.pow_add]; exact Nat.mul_lt_mul'' hres.sa.mag_lt hres.sb.mag_lt
  · rw [hsp.2.1, Nat.min_eq_left (by omega)]

end Tom.Machine.Fn.SMpMulDigsG5K
