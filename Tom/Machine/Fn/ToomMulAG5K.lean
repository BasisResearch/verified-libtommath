import Tom.Machine.Fn.ToomMulG5K
import Tom.Machine.Api.MulAlgA

/-!
# Toom-3 multiplication in place (`s_mp_toom_mul(a, b, a)`): helpers

`Fn/ToomMulG5K.lean` with `c = a`: the contract's regions are `Api.MpMulA`'s (no `cS`, `cD`; the
destination is `a` itself, read only by the three copy loops into `a0 a1 a2` and written first by
`mp_add(&b2, &b1, a)` after them), and the nine temporaries' digit arrays beside them. `TQA` is `MulAlgA.Q` with the placement of `a`'s digits from its block at the entry
(`DOut`). For `Fn/ToomMulAMainG.lean` (`tmula.asm.json`).
-/

namespace Tom.Machine.Fn.ToomMulAG5K

open Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpMulA (P kind hin)

/-- Toom's split `B = min(a->used, b->used) / 3` (a `def`: `omega` keeps it an atom). -/
def Bt (p : P) : Nat := min p.a.used p.b.used / 3

/-- What the code leaves in `a` (`x = (ok, q, a')`): `MulAlgA.Q` and the placement of `a'`'s digits
from `a`'s block at the entry (`DOut`, Kit/DOut.lean). -/
abbrev TQA (p : P) : MpMul.X → Prop := DOut (p.a.mag * p.b.mag) 0 (MulAlgA.lay p .aD) (hin p)

theorem TQA.q {p : P} {x : MpMul.X} (h : TQA p x) : MulAlgA.Q p x := by
  obtain ⟨_, _, _⟩ := x; exact ⟨h.shape, h.pos, h.valid, h.mag⟩

/-- `a` as it was. -/
theorem outKeep {p : P} (h : ToomMulA.Res p) : TQA p (false, p.adp, p.a) :=
  ⟨h.va.toShape, h.apos, (fun e => nomatch e), (fun e => nomatch e), Place.keep, Nat.zero_le _⟩

end Tom.Machine.Fn.ToomMulAG5K
