import Tom.Machine.Conventions
import Tom.Machine.Fn.MpLshdGMainG
import Tom.Spec.GrowHStep

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_lshd`: the concise specification (SPECS.lean), from `Fn.MpLshdGG5.correct` -/

namespace Tom.Machine.Api.MpLshdG

/-- **`mp_lshd(a, k)`**: `a ← a · radix^k` (`k` digits shifted in), growing `a`; `MP_MEM` only when
`a` had to grow. -/
theorem _root_.Specs.mp_lshd {p : P} (cv : Conv m ra p.sp F (hin p)) (sound : Sound (lay p) isW)
    (a : MpOut m p.pa p.adp p.a) (va : p.a.Valid) (size : p.a.used + p.k < 2 ^ 31) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.k] optRet fun x M =>
      OptRes x (p.a.alloc < p.a.used + p.k)
        (fun a' => a'.Valid ∧ a'.mag = p.a.mag * radix ^ p.k ∧ a'.sign = p.a.sign) ∧
      HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.MpLshdGG5.correct cv.ra_al
    ⟨cv.stk, a.shape, by omega, size, a.pos, a.off⟩ sound) cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => let h := LshdPost.grown_spec va size hq; ⟨h.1, h.2.1, h.2.2.1⟩

end Tom.Machine.Api.MpLshdG
