import Tom.Machine.Conventions
import Tom.Machine.Fn.Mul2HDMainG
import Tom.Machine.Fn.Mul2HMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_mul_2`: the concise specifications (SPECS.lean), from `Fn.Mul2HDG5.correct`,
`Fn.Mul2HG5.correct` -/

namespace Tom.Machine.Api.Mul2HD
open Tom.Machine.Api.Two (R isW ws)
open Tom.Machine.Api.MpSqr (X)

def eff (p : P) := Eff.heap (lay p) isW ws .bD (out p) (site' p) (hin p) (hout p) okView

/-- **`mp_mul_2(a, b)`**: `b ← 2a`, growing `b`. -/
theorem _root_.Specs.mp_mul_2 {p : P} (cv : Conv m ra p.sp F (eff p))
    (a : MpOwn m p.H p.pa p.adp p.a) (b : MpOut m p.pb p.bdp p.b) (ua : CIdx (p.a.used + 1)) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb] (eff p)
      fun b' => b'.Valid ∧ b'.val = 2 * p.a.val :=
  ApiTriple.of (Reg.call (Fn.Mul2HDG5.correct cv.ra_al
    ⟨cv.stk, a.valid, b.shape, ua, a.pos, b.pos, b.off⟩ cv.sound) cv.heap (by mp_regions))
    fun _ hq => .okView fun h => ⟨hq.valid h, hq.val h⟩

end Tom.Machine.Api.Mul2HD

namespace Tom.Machine.Api.Mul2H
open Tom.Machine.Api.Un (R isW ws)
open Tom.Machine.Api.MpSqr (X)

def eff (p : P) := Eff.heap (lay p) isW ws .aD (out p) (site' p) (hin p) (hout p) okView

/-- **`mp_mul_2(a, a)`**: `a ← 2a` (`mp_mul_2` with `b := a`). -/
theorem _root_.Specs.mp_mul_2_inplace {p : P} (cv : Conv m ra p.sp 576 (eff p))
    (a : MpOut m p.pa p.adp p.a) (va : p.a.Valid) (ua : CIdx (p.a.used + 1)) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pa] (eff p)
      fun a' => a'.Valid ∧ a'.val = 2 * p.a.val :=
  ApiTriple.of (Reg.call (Fn.Mul2HG5.correct cv.ra_al ⟨cv.stk, va, ua, a.pos, a.off⟩ cv.sound)
    cv.heap (by mp_regions)) fun _ hq => .okView fun h => ⟨hq.valid h, hq.val h⟩

end Tom.Machine.Api.Mul2H
