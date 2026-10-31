import Tom.Machine.Conventions
import Tom.Machine.Fn.AddDMain

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_add_d`: the concise specification (SPECS.lean), from `Fn.AddD.correct` -/

namespace Tom.Machine.Api.AddD
open Tom.Machine.Api.Two

/-- **`mp_add_d(a, b, c)`**: `c ← a + b` for a digit `b`, `c` with room. -/
theorem _root_.Specs.mp_add_d {sp pa adp pc cdp : Nat} {a c : MpInt} {b : Nat}
    {s0 : BitVec 64} (cv : ConvS m ra sp 128) (sound : Sound (lay 128 sp pa adp pc cdp a c) isW)
    (ha : MpVal m pa adp a) (hc : MpOut m pc cdp c) (hb : b < radix) (room : a.used + 1 ≤ c.alloc) :
    ApiTripleS m v outp ra s0 entry sp [pa, b, pc] 0#64 fun c' M =>
      (c'.Valid ∧ c'.val = a.val + b) ∧ Post 128 m sp pa adp pc cdp a b c c' M :=
  ApiTripleS.of (Fn.AddD.correct ⟨ha.mpAt, hc.mpAt, ha.valid, hc.shape, hb, ha.geom, hc.geom, room,
    cv.stk.ram, cv.stk.al, cv.sp_ge, cv.ra_al, cv.img, sound⟩) fun _ _ h =>
    AddDPost.spec ha.valid hb room hc.shape.alloc_lt h.addd

end Tom.Machine.Api.AddD
