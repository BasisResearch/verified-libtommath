import Tom.Machine.Conventions
import Tom.Machine.Fn.Expt2GMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_2expt`: the concise specification (SPECS.lean), from `Fn.Expt2GG5.correct` -/

namespace Tom.Machine.Api.Expt2G

def eff (p : P) := Eff.heap (lay p) isW ws .aD (out p) (site' p) (hin p) (hout p) optView

/-- **`mp_2expt(a, b)`**: `a ← 2^b`, growing `a`; `MP_MEM` only when `a` had to grow. -/
theorem _root_.Specs.mp_2expt {p : P} (cv : Conv m ra p.sp F (eff p)) (a : MpOut m p.pa p.adp p.a)
    (hb : CInt p.b) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.b] (eff p)
      (mem := p.a.alloc < p.b / Layout.digitBits + 1) fun a' => a'.Valid ∧ a'.val = 2 ^ p.b :=
  ApiTriple.of (Reg.call (Fn.Expt2GG5.correct cv.ra_al ⟨cv.stk, a.shape, hb, a.pos, a.off⟩ cv.sound)
    cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => (Expt2Post.specG a.shape.alloc_lt hb hq.post).imp_right And.right

end Tom.Machine.Api.Expt2G
