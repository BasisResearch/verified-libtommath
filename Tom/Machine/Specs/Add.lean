import Tom.Machine.Conventions
import Tom.Machine.Fn.MpAddGMainG
import Tom.Machine.Fn.MpAddGAMainG
import Tom.Machine.Fn.MpAddGBMainG
import Tom.Spec.GrowHStep
import Tom.Spec.GrowAStep

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_add`: the concise specifications (SPECS.lean), from `Fn.MpAddG*G5.correct` -/

namespace Tom.Machine.Api.MpAddG

def eff (p : P) := Eff.heap (lay p) isW ws .cD (out p) (site' p) (hin p) (hout p) optView

/-- **`mp_add(a, b, c)`**: `c ← a + b`, growing `c`; `MP_MEM` only when `c` had to grow. -/
theorem _root_.Specs.mp_add {p : P} (cv : Conv m ra p.sp F (eff p)) (a : MpOwn m p.H p.pa p.adp p.a)
    (b : MpOwn m p.H p.pb p.bdp p.b) (c : MpOut m p.pc p.cdp p.c)
    (size : CInt (max p.a.used p.b.used + 1)) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb, p.pc] (eff p)
      (mem := p.c.alloc < addSize p.a p.b) fun c' => c'.Valid ∧ c'.val = p.a.val + p.b.val :=
  ApiTriple.of (Reg.call (Fn.MpAddGG5.correct cv.ra_al
    ⟨cv.stk, a.valid, b.valid, c.shape, size, a.pos, b.pos, c.pos, c.off⟩
    cv.sound) cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => (Tom.AddG.spec a.valid b.valid c.shape size hq).imp_right And.left

end Tom.Machine.Api.MpAddG

namespace Tom.Machine.Api.MpAddGA

def eff (p : P) := Eff.heap (lay p) isW ws .aD (out p) (site' p) (hin p) (hout p) optView

/-- **`mp_add(a, b, a)`**: `a ← a + b` (`mp_add` with `c := a`). -/
theorem _root_.Specs.mp_add_ca {p : P} (cv : Conv m ra p.sp F (eff p)) (a : MpOut m p.pa p.adp p.a)
    (va : p.a.Valid) (b : MpOwn m p.H p.pb p.bdp p.b) (size : CInt (max p.a.used p.b.used + 1)) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb, p.pa] (eff p)
      (mem := p.a.alloc < addSize p.a p.b) fun a' => a'.Valid ∧ a'.val = p.a.val + p.b.val :=
  ApiTriple.of (Reg.call (Fn.MpAddGAG5.correct cv.ra_al
    ⟨cv.stk, va, b.valid, size, a.pos, b.pos, a.off⟩ cv.sound) cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => (Tom.AddG.specA va b.valid size hq).imp_right And.left

end Tom.Machine.Api.MpAddGA

namespace Tom.Machine.Api.MpAddGB

def eff (p : P) := Eff.heap (lay p) isW ws .bD (out p) (site' p) (hin p) (hout p) optView

/-- **`mp_add(a, b, b)`**: `b ← a + b` (`mp_add` with `c := b`). -/
theorem _root_.Specs.mp_add_cb {p : P} (cv : Conv m ra p.sp F (eff p))
    (a : MpOwn m p.H p.pa p.adp p.a) (b : MpOut m p.pb p.bdp p.b) (vb : p.b.Valid)
    (size : CInt (max p.a.used p.b.used + 1)) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb, p.pb] (eff p)
      (mem := p.b.alloc < addSize p.a p.b) fun b' => b'.Valid ∧ b'.val = p.a.val + p.b.val :=
  ApiTriple.of (Reg.call (Fn.MpAddGBG5.correct cv.ra_al
    ⟨cv.stk, a.valid, vb, size, a.pos, b.pos, b.off⟩ cv.sound) cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => (Tom.AddG.specB a.valid vb size hq).imp_right And.left

end Tom.Machine.Api.MpAddGB
