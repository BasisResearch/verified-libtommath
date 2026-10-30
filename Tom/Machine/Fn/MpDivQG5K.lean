import Tom.Machine.Api.MpDivQ
import Tom.Machine.Fn.MpDivG5K
import Tom.Machine.Kit.OneSite
import Tom.Machine.Kit.Sites
import Tom.Spec.MpDivNullStep

/-!
# `mp_div(a, b, a, NULL)`'s assembly: helpers

For the generated `Fn/MpDivQMainG.lean` (annotation `experiments/asm/mdivq.asm.json`, a variant of
`mdiv.asm.json` with `c` renamed `a`; its region type generated): `Res.ablk`.
-/

namespace Tom.Machine.Api.MpDivQ
open Tom.Machine.Api.Heap

/-- `a`'s digits are live: the front block (`mp_init_copy(&x, a)`'s source). -/
theorem Res.ablk {p : P} (_ : Res p) : digBlk p.adp p.a ∈ hin p := List.mem_cons_self ..

end Tom.Machine.Api.MpDivQ

namespace Tom.Machine.Fn.MpDivQG5K

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpDivQ (P lay kind isW ws hin hout out site' Q Res)
open Tom

end Tom.Machine.Fn.MpDivQG5K
