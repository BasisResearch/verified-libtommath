import Tom.Machine.Conventions
import Tom.Machine.Fn.MulDGMainG
import Tom.Machine.Fn.MulDGAMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_mul_d`: the concise specifications (SPECS.lean), from `Fn.MulDGG5.correct`,
`Fn.MulDGAG5.correct` -/

namespace Tom.Machine.Api.MulDG

def eff (p : P) := Eff.heap (lay p) isW ws .cD (out p) (site' p) (hin p) (hout p) optView

/-- **`mp_mul_d(a, b, c)`**: `c ← a · b` for a digit `b`, growing `c`; `MP_MEM` only when `c` had
to grow. -/
theorem _root_.Specs.mp_mul_d {p : P} (cv : Conv m ra p.sp F (eff p))
    (a : MpOwn m p.H p.pa p.adp p.a) (c : MpOut m p.pc p.cdp p.c) (hb : p.b < radix)
    (size : CInt (p.a.used + 1)) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.b, p.pc] (eff p)
      (mem := p.c.alloc < p.a.used + 1) fun c' => c'.Valid ∧ c'.val = p.a.val * p.b :=
  ApiTriple.of (Reg.call (Fn.MulDGG5.correct cv.ra_al
    ⟨cv.stk, a.valid.toShape, a.pos, a.valid.sign_ok, c.shape, hb, size, c.pos, c.off⟩ cv.sound)
    cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => (MulDPost.spec a.valid hb (mulDIn_room _ _)
        (mulDIn_grown c.shape size).shape.alloc_lt hq).imp_right And.right

end Tom.Machine.Api.MulDG

namespace Tom.Machine.Api.MulDGA

def eff (p : P) := Eff.heap (lay p) isW ws .aD (out p) (site' p) (hin p) (hout p) optView

/-- **`mp_mul_d(a, b, a)`**: `a ← a · b` (`mp_mul_d` with `c := a`). -/
theorem _root_.Specs.mp_mul_d_inplace {p : P} (cv : Conv m ra p.sp F (eff p))
    (a : MpOut m p.pa p.adp p.a) (va : p.a.Valid) (hb : p.b < radix) (size : CInt (p.a.used + 1)) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.b, p.pa] (eff p)
      (mem := p.a.alloc < p.a.used + 1) fun a' => a'.Valid ∧ a'.val = p.a.val * p.b :=
  ApiTriple.of (Reg.call (Fn.MulDGAG5.correct cv.ra_al
    ⟨cv.stk, a.shape, a.pos, va.sign_ok, hb, size, a.off⟩ cv.sound) cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => (MulDPost.spec va hb (mulDIn_room _ _)
        (mulDIn_grown a.shape size).shape.alloc_lt hq).imp_right And.right

end Tom.Machine.Api.MulDGA
