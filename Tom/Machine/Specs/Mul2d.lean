import Tom.Machine.Conventions
import Tom.Machine.Fn.MpMul2dMain
import Tom.Machine.Fn.MpMul2dIMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_mul_2d`: the concise specifications (SPECS.lean), from `Fn.MpMul2d.correct`,
`Fn.MpMul2dIG5.correct` -/

namespace Tom.Machine.Api.MpMul2d
open Tom.Machine.Api.Two

/-- **`mp_mul_2d(a, b, c)`**: `c ← a · 2^b`, `c` with room. -/
theorem _root_.Specs.mp_mul_2d {sp pa adp pc cdp : Nat} {a c : MpInt} {b : Nat} {s0 : BitVec 64}
    (cv : ConvS m ra sp 80 (lay sp pa adp pc cdp a c) isW) (ha : MpVal m pa adp a)
    (hc : MpOut m pc cdp c) (hb : CInt b) (room : a.used + b / Layout.digitBits + 1 ≤ c.alloc) :
    ApiTripleS m v outp ra s0 entry sp [pa, b, pc] 0#64 fun c' M =>
      (c'.Valid ∧ c'.val = a.val * 2 ^ b) ∧ Post m sp pa adp pc cdp a b c c' M :=
  ApiTripleS.of (Fn.MpMul2d.correct ⟨ha.mpAt, hc.mpAt, ha.valid, hc.shape, ha.geom, hc.geom, hb,
    room, cv.stk.ram, cv.stk.al, cv.sp_ge, cv.ra_al, cv.img, cv.sound⟩) fun _ _ h =>
    (Mul2dPost.spec ha.valid room hc.shape.alloc_lt h.mul).imp_right And.right

end Tom.Machine.Api.MpMul2d

namespace Tom.Machine.Api.MpMul2dI

def eff (p : P) := Eff.heap (lay p) isW ws .aD (out p) (site' p) (hin p) (hout p) optView

/-- **`mp_mul_2d(a, b, a)`**: `a ← a · 2^b`, growing `a`; `MP_MEM` only when `a` had to grow. -/
theorem _root_.Specs.mp_mul_2d_inplace {p : P} (cv : Conv m ra p.sp F (eff p))
    (a : MpOut m p.pa p.adp p.a) (va : p.a.Valid) (hb : CInt p.b)
    (size : CInt (p.a.used + p.b / 28 + 1)) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.b, p.pa] (eff p)
      (mem := p.a.alloc < p.a.used + p.b / 28 + 1) fun a' =>
      a'.Valid ∧ a'.val = p.a.val * 2 ^ p.b :=
  ApiTriple.of (Reg.call (Fn.MpMul2dIG5.correct cv.ra_al
    ⟨cv.stk, a.shape, hb, size, a.pos, a.off⟩ cv.sound) cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => (Mul2dPost.spec va (mul2dIn_room _ _)
        (mul2dIn_grown a.shape size).shape.alloc_lt hq).imp_right And.right

end Tom.Machine.Api.MpMul2dI
