import Tom.Machine.Fn.ToomSqrG5K

/-!
# Toom-3 squaring in place (`s_mp_toom_sqr(a, a)`): helpers

`Fn/ToomSqrG5K.lean` with `b = a`: the contract's regions are `Api.MpSqrA`'s (no `bS`, `bD`; the
destination is `a` itself), and the four temporaries' digit arrays beside them. `a` is read only
by the three copy loops (`a->used`, `a->dp[i]`), before the first call into `b = a`
(`mp_sub(&a0, &a1, b)`); from there on the contract's `QA` is carried as `Q` is in the distinct case
(`DOut.next`, `DOut.same`, `DOut.fin`, Kit/DOut.lean). The region type is generated.
-/

namespace Tom.Machine.Fn.ToomSqrAG5K

open Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpSqrA (P kind hin)

/-- `a` as it was (before any call into it). -/
theorem outKeep {p : P} (h : ToomSqr.ResA p) : SqrAlg.QA p (false, p.adp, p.a) :=
  ⟨h.va.toShape, h.apos, (fun e => nomatch e), (fun e => nomatch e), Place.keep, Nat.le_refl _⟩

end Tom.Machine.Fn.ToomSqrAG5K

namespace Tom.Machine.Api.ToomSqrAI

/-- What the in-place assembly proves: `s_mp_toom_sqr(a, a)` from the callee premises
`ToomSqrI.Gaps`. -/
def Statement : Prop := ToomSqrI.Gaps → ToomSqr.StatementA

end Tom.Machine.Api.ToomSqrAI
