import Tom.Machine.Fn.KSqrG5K

/-!
# Karatsuba squaring in place (`s_mp_karatsuba_sqr(a, a)`): helpers

`Fn/KSqrG5K.lean` with `b = a`: the contract's regions are `Api.MpSqrA`'s (no `bS`, `bD`; the
destination is `a` itself), and the six temporaries' digit arrays beside them (generated). The callee
contracts (`sqrBK`, `sqrABK`) and the heap lemmas are shared.
-/

namespace Tom.Machine.Fn.KSqrAG5K

open Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpSqrA (P kind hin)

theorem outKeep {p : P} (h : KSqr.ResA p) : SqrAlg.QA p (false, p.adp, p.a) :=
  ⟨h.va.toShape, h.apos, (fun e => nomatch e), (fun e => nomatch e), Place.keep, Nat.le_refl _⟩

end Tom.Machine.Fn.KSqrAG5K
