import Tom.Machine.Conventions
import Tom.Machine.Fn.MpSubGMainG
import Tom.Machine.Fn.MpSubGAMainG
import Tom.Machine.Fn.MpSubGBMainG
import Tom.Spec.SubGStep
import Tom.Spec.SubGBStep

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_sub`: the concise specifications (SPECS.lean), from `Fn.MpSubG*G5.correct` -/

namespace Tom.Machine.Api.MpSubG
open Tom.Machine.Api.MpAddG (P R lay kind isW ws args Res)

def eff (p : P) := Eff.heap (lay p) isW ws .cD (out p) (site' p) (hin p) (hout p) optView

/-- **`mp_sub(a, b, c)`**: `c ← a - b`, growing `c`; `MP_MEM` only when `c` had to grow. -/
theorem _root_.Specs.mp_sub {p : P} (cv : Conv m ra p.sp F (eff p)) (a : MpOwn m p.H p.pa p.adp p.a)
    (b : MpOwn m p.H p.pb p.bdp p.b) (c : MpOut m p.pc p.cdp p.c)
    (size : CInt (max p.a.used p.b.used + 1)) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb, p.pc] (eff p)
      (mem := p.c.alloc < subSize p.a p.b) fun c' => c'.Valid ∧ c'.val = p.a.val - p.b.val :=
  ApiTriple.of (Reg.call (Fn.MpSubGG5.correct cv.ra_al
    ⟨cv.stk, a.valid, b.valid, c.shape, size, a.pos, b.pos, c.pos, c.off⟩
    cv.sound) cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => (Tom.SubG.spec a.valid b.valid c.shape size hq).imp_right And.left

end Tom.Machine.Api.MpSubG

namespace Tom.Machine.Api.MpSubGA
open Tom.Machine.Api.MpAddGA (P R lay kind isW ws args Res)

def eff (p : P) := Eff.heap (lay p) isW ws .aD (out p) (site' p) (hin p) (hout p) optView

/-- **`mp_sub(a, b, a)`**: `a ← a - b` (`mp_sub` with `c := a`). -/
theorem _root_.Specs.mp_sub_ca {p : P} (cv : Conv m ra p.sp F (eff p)) (a : MpOut m p.pa p.adp p.a)
    (va : p.a.Valid) (b : MpOwn m p.H p.pb p.bdp p.b) (size : CInt (max p.a.used p.b.used + 1)) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb, p.pa] (eff p)
      (mem := p.a.alloc < subSize p.a p.b) fun a' => a'.Valid ∧ a'.val = p.a.val - p.b.val :=
  ApiTriple.of (Reg.call (Fn.MpSubGAG5.correct cv.ra_al
    ⟨cv.stk, va, b.valid, size, a.pos, b.pos, a.off⟩ cv.sound) cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => (Tom.SubG.specA va b.valid size hq).imp_right And.left

end Tom.Machine.Api.MpSubGA

namespace Tom.Machine.Api.MpSubGB
open Tom.Machine.Api.MpAddGB (P R lay kind isW ws args Res)

def eff (p : P) := Eff.heap (lay p) isW ws .bD (out p) (site' p) (hin p) (hout p) optView

/-- **`mp_sub(a, b, b)`**: `b ← a - b` (`mp_sub` with `c := b`). -/
theorem _root_.Specs.mp_sub_cb {p : P} (cv : Conv m ra p.sp F (eff p))
    (a : MpOwn m p.H p.pa p.adp p.a) (b : MpOut m p.pb p.bdp p.b) (vb : p.b.Valid)
    (size : CInt (max p.a.used p.b.used + 1)) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb, p.pb] (eff p)
      (mem := p.b.alloc < subSize p.a p.b) fun b' => b'.Valid ∧ b'.val = p.a.val - p.b.val :=
  ApiTriple.of (Reg.call (Fn.MpSubGBG5.correct cv.ra_al
    ⟨cv.stk, a.valid, vb, size, a.pos, b.pos, b.off⟩ cv.sound) cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => (Tom.SubG.specB a.valid vb size hq).imp_right And.left

end Tom.Machine.Api.MpSubGB
