import Tom.Machine.Fn.KMulG5K
import Tom.Machine.Api.MulAlgA

/-!
# Karatsuba multiplication in place (`s_mp_karatsuba_mul(a, b, a)`): helpers

`Fn/KMulG5K.lean` with `c = a`: the contract's regions are `Api.MpMulA`'s (no `cS`, `cD`; the
destination is `a` itself, written only by the last `mp_add(&t1, &x1y1, a)` after the copies
read it), and the seven temporaries' digit arrays beside them (generated). The callee contracts
(`mpMulBK`, `mpMulABK`) are shared. For `Fn/KMulAMainG.lean` (`kmula.asm.json`).
-/

namespace Tom.Machine.Fn.KMulAG5K

open Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpMulA (P kind hin)

/-- `a` as it was (an `MP_MEM` before the last `mp_add`). -/
theorem outKeep {p : P} (h : KMulA.Res p) : MulAlgA.Q p (false, p.adp, p.a) :=
  ⟨h.va.toShape, h.apos, (fun e => nomatch e), (fun e => nomatch e)⟩

end Tom.Machine.Fn.KMulAG5K
