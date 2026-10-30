import Tom.Machine.Api.SMpMulHighDigs

/-!
# `s_mp_mul_high_digs`'s fast path: the result of the tail call

The tail call `s_mp_mul_high_digs_fast(a, b, a, digs)` at `6bb8` (`"tail" … "flat"`,
`experiments/asm/mhdigs.asm.json`); its post becomes the contract's by `HPost.inplace`
(Kit/Run.lean). `fast_q`: `MulHighFastPost` as the contract's `Q`.
-/

namespace Tom.Machine.Fn.SMpMulHighDigsG5K

open Tom.Machine Tom.Machine.Api
open Tom.Machine.Api.SMpMulHighDigs (P Q Fast Res)

theorem fast_q {p : P} {a' : MpInt} (hres : Res p) (hf : Fast p.a p.b)
    (hq : Reduce.MulHighFastPost p.a p.b p.a a' p.digs) : Q p (some (p.adp, a')) :=
  ⟨(Reduce.MulHighFastPost.spec hres.sa hres.sb hres.sa hres.dg_le (hres.room hf) hres.asign hq).1,
    fun _ => ⟨rfl, hq⟩, fun h => absurd hf h⟩

end Tom.Machine.Fn.SMpMulHighDigsG5K
