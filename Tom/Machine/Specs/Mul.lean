import Tom.Machine.Conventions
import Tom.Machine.Fn.MulGroupB

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_mul`: the concise specifications (SPECS.lean), from `Fn.MulGroupB.mulCorrectU`,
`Fn.MulGroupB.mulCorrect` -/

namespace Tom.Machine.Api.MpMul

def eff (p : P) := Eff.heap (lay p) isW ws .cD (out p) (site' p) (hin p) (hout p) okView

/-- **`mp_mul(a, b, c)`**: `c ← a · b`, growing `c`. -/
theorem _root_.Specs.mp_mul {p : P} (cv : Conv m ra p.sp (F p) (eff p)) (cut : Cutoffs m)
    (a : MpOwn m p.H p.pa p.adp p.a) (b : MpOwn m p.H p.pb p.bdp p.b) (c : MpOut m p.pc p.cdp p.c)
    (size : CIdx (μ p.a p.b)) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb, p.pc] (eff p)
      fun c' => c'.Valid ∧ c'.val = p.a.val * p.b.val :=
  ApiTriple.of (Reg.call (Fn.MulGroupB.mulCorrectU p cv.ra_al ⟨cv.stk, a.valid.toU, b.valid.toU,
    c.shape, c.sign, size, a.pos, b.pos, c.pos, a.off, b.off, c.off⟩
    cv.sound) cv.heap (by mp_regions))
    fun | (_, _, _), hq => .okView fun h => ⟨(hq.post h).valid, (hq.post h).val⟩

end Tom.Machine.Api.MpMul

namespace Tom.Machine.Api.MpMulA
open Tom.Machine.Api.MpMul (entry kcAddr tcAddr μ Fm kcV tcV X)

def eff (p : P) := Eff.heap (lay p) isW ws .aD (out p) (site' p) (hin p) (hout p) okView

/-- **`mp_mul(a, b, a)`**: `a ← a · b` (`mp_mul` with `c := a`). -/
theorem _root_.Specs.mp_mul_inplace {p : P} (cv : Conv m ra p.sp (F p) (eff p)) (cut : Cutoffs m)
    (a : MpOut m p.pa p.adp p.a) (va : p.a.Valid) (b : MpOwn m p.H p.pb p.bdp p.b)
    (size : CIdx (μ p.a p.b)) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb, p.pa] (eff p)
      fun a' => a'.Valid ∧ a'.val = p.a.val * p.b.val :=
  ApiTriple.of (Reg.call (Fn.MulGroupB.mulCorrect.2 p cv.ra_al
    ⟨cv.stk, va, b.valid, size, a.pos, b.pos, a.off, b.off⟩ cv.sound) cv.heap (by mp_regions))
    fun | (_, _, _), hq => .okView fun h => ⟨(hq.post h).valid, (hq.post h).val⟩

end Tom.Machine.Api.MpMulA
