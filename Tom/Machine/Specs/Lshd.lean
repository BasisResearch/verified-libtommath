import Tom.Machine.Conventions
import Tom.Machine.Fn.MpLshdGMainG
import Tom.Spec.GrowHStep

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_lshd`: the concise specification (SPECS.lean), from `Fn.MpLshdGG5.correct` -/

namespace Tom.Machine.Api.MpLshdG

def eff (p : P) := Eff.heap (lay p) isW ws .aD (out p) (site' p) (hin p) (hout p) optView

/-- **`mp_lshd(a, k)`**: `a ← a · radix^k` (`k` digits shifted in), growing `a`; `MP_MEM` only when
`a` had to grow. -/
theorem _root_.Specs.mp_lshd {p : P} (cv : Conv m ra p.sp F (eff p)) (a : MpOut m p.pa p.adp p.a)
    (va : p.a.Valid) (size : CInt (p.a.used + p.k)) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.k] (eff p)
      (mem := p.a.alloc < p.a.used + p.k) fun a' =>
      a'.Valid ∧ a'.mag = p.a.mag * radix ^ p.k ∧ a'.sign = p.a.sign :=
  ApiTriple.of (Reg.call (Fn.MpLshdGG5.correct cv.ra_al
    ⟨cv.stk, a.shape, by unfold CInt at size; omega, size, a.pos, a.off⟩
    cv.sound) cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => let h := LshdPost.grown_spec va size hq; ⟨h.1, h.2.1, h.2.2.1⟩

end Tom.Machine.Api.MpLshdG
