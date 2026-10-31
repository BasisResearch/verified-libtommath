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

/-- **`mp_add(a, b, c)`**: `c ← a + b`, growing `c`; `MP_MEM` only when `c` had to grow. -/
theorem _root_.Specs.mp_add {p : P} (cv : Conv m ra p.sp F (hin p)) (sound : Sound (lay p) isW)
    (a : MpOwn m p.H p.pa p.adp p.a) (b : MpOwn m p.H p.pb p.bdp p.b) (c : MpOut m p.pc p.cdp p.c)
    (size : max p.a.used p.b.used + 1 < 2 ^ 31) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb, p.pc] optRet fun x M =>
      OptRes x (p.c.alloc < addSize p.a p.b) (fun c' => c'.Valid ∧ c'.val = p.a.val + p.b.val) ∧
      HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.MpAddGG5.correct cv.ra_al
    ⟨cv.stk, a.valid, b.valid, c.shape, size, a.pos, b.pos, c.pos, c.off⟩ sound) cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => (Tom.AddG.spec a.valid b.valid c.shape size hq).imp_right And.left

end Tom.Machine.Api.MpAddG

namespace Tom.Machine.Api.MpAddGA

/-- **`mp_add(a, b, a)`**: `a ← a + b` (`mp_add` with `c := a`). -/
theorem _root_.Specs.mp_add_ca {p : P} (cv : Conv m ra p.sp F (hin p)) (sound : Sound (lay p) isW)
    (a : MpOut m p.pa p.adp p.a) (va : p.a.Valid) (b : MpOwn m p.H p.pb p.bdp p.b)
    (size : max p.a.used p.b.used + 1 < 2 ^ 31) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb, p.pa] optRet fun x M =>
      OptRes x (p.a.alloc < addSize p.a p.b) (fun a' => a'.Valid ∧ a'.val = p.a.val + p.b.val) ∧
      HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.MpAddGAG5.correct cv.ra_al
    ⟨cv.stk, va, b.valid, size, a.pos, b.pos, a.off⟩ sound) cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => (Tom.AddG.specA va b.valid size hq).imp_right And.left

end Tom.Machine.Api.MpAddGA

namespace Tom.Machine.Api.MpAddGB

/-- **`mp_add(a, b, b)`**: `b ← a + b` (`mp_add` with `c := b`). -/
theorem _root_.Specs.mp_add_cb {p : P} (cv : Conv m ra p.sp F (hin p)) (sound : Sound (lay p) isW)
    (a : MpOwn m p.H p.pa p.adp p.a) (b : MpOut m p.pb p.bdp p.b) (vb : p.b.Valid)
    (size : max p.a.used p.b.used + 1 < 2 ^ 31) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb, p.pb] optRet fun x M =>
      OptRes x (p.b.alloc < addSize p.a p.b) (fun b' => b'.Valid ∧ b'.val = p.a.val + p.b.val) ∧
      HPost (lay p) ws .bD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.MpAddGBG5.correct cv.ra_al
    ⟨cv.stk, a.valid, vb, size, a.pos, b.pos, b.off⟩ sound) cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => (Tom.AddG.specB a.valid vb size hq).imp_right And.left

end Tom.Machine.Api.MpAddGB
