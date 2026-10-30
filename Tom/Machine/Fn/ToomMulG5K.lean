import Tom.Machine.Api.ToomMul
import Tom.Machine.Api.Std_r11a
import Tom.Machine.Api.Std_gap9
import Tom.Machine.Api.Std_multi8
import Tom.Machine.Kit.Run
import Tom.Machine.Kit.Sites
import Tom.Machine.Kit.DOut
import Tom.Machine.Kit.AnnFacts
import Tom.Spec.IntFacts
import Tom.Spec.ToomMulStep
import Tom.Machine.Fn.ToomMulG
import Tom.Machine.Fn.KMulG5K
import Tom.Machine.Fn.GrowH
import Tom.Machine.Fn.GrowSubH

/-!
# Toom-3 multiplication's assembly: helpers

`s_mp_toom_mul` allocates nine temporaries: `S1 S2 T1` by `mp_init_multi`, `a0 a1 a2 b0 b1 b2` by `mp_init_size`. The assembly (`Fn/ToomMulMainG.lean`,
annotation `tmul.asm.json`, style `"pre"`) runs over the contract's regions plus the nine digit arrays
`dS1 … dB2` (the region type, `soundG` and `GPre` generated from the annotation's `"region"`).
`c`'s digits are re-placed by five calls (`c = b2 + b1`, `c += b2`, `c <<= 1`, `c += b0`, `c = b1 + a0`):
`TQ` is `MulAlg.Q` with the placement from the entry's block (`DOut`, Kit/DOut.lean), carried along by
`DOut.next0`. The three-site residues (`al3`, …) are Kit/AnnFacts.lean's.
-/


namespace Tom.Machine.Fn.ToomMulG5K

open Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpMul (P kind hin)

/-- Toom's split `B = min(a->used, b->used) / 3` (a `def`: `omega` keeps it an atom). -/
def Bt (p : P) : Nat := min p.a.used p.b.used / 3

/-- What the code leaves in `c` (`x = (ok, q, c')`): `MulAlg.Q` and the placement of `c'`'s digits
from `c`'s block at the entry. -/
abbrev TQ (p : P) : MpMul.X → Prop := DOut (p.a.mag * p.b.mag) 0 (MulAlg.lay p .cD) (hin p)

theorem TQ.q {p : P} {x : MpMul.X} (h : TQ p x) : MulAlg.Q p x := by
  obtain ⟨_, _, _⟩ := x; exact ⟨h.shape, h.pos, h.valid, h.mag⟩

/-- `c` as it was. -/
theorem outKeep {p : P} (h : ToomMul.Res p) : TQ p (false, p.cdp, p.c) :=
  ⟨h.sc, h.cpos, (fun e => nomatch e), (fun e => nomatch e), Place.keep, Nat.zero_le _⟩

end Tom.Machine.Fn.ToomMulG5K
