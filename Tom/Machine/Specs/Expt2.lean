import Tom.Machine.Conventions
import Tom.Machine.Fn.Expt2GMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_2expt`: the concise specification (SPECS.lean), from `Fn.Expt2GG5.correct` -/

namespace Tom.Machine.Api.Expt2G

/-- **`mp_2expt(a, b)`**: `a ← 2^b`, growing `a`; `MP_MEM` only when `a` had to grow. -/
theorem _root_.Specs.mp_2expt {p : P} (cv : Conv m ra p.sp F (hin p)) (sound : Sound (lay p) isW)
    (a : MpOut m p.pa p.adp p.a) (hb : p.b < 2 ^ 31) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.b] optRet fun x M =>
      OptRes x (p.a.alloc < p.b / Layout.digitBits + 1) (fun a' => a'.Valid ∧ a'.val = 2 ^ p.b) ∧
      HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.Expt2GG5.correct cv.ra_al ⟨cv.stk, a.shape, hb, a.pos, a.off⟩ sound)
    cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => (Expt2Post.specG a.shape.alloc_lt hb hq.post).imp_right And.right

end Tom.Machine.Api.Expt2G
