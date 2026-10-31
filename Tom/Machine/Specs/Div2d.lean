import Tom.Machine.Conventions
import Tom.Machine.Fn.MpDiv2dMain

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_div_2d`: the concise specifications (SPECS.lean), from `Fn.MpDiv2d.correct`,
`Fn.MpDiv2d.correct_inplace` -/

namespace Tom.Machine.Api.MpDiv2d

/-- **`mp_div_2d(a, b, c, NULL)`**: `c ← a / 2^b` (truncated: `|c| = ⌊|a| / 2^b⌋`, the sign of `a`),
`c` with room. -/
theorem _root_.Specs.mp_div_2d {sp pa adp pc cdp : Nat} {a c : MpInt} {b : Nat}
    {s0 : BitVec 64} (cv : ConvS m ra sp 96) (sound : Sound (lay sp pa adp pc cdp a c) Two.isW)
    (ha : MpVal m pa adp a) (hc : MpOut m pc cdp c) (hb : b < 2 ^ 31) (room : a.used ≤ c.alloc) :
    ApiTripleS m v outp ra s0 entry sp [pa, b, pc, 0] 0#64 fun c' M =>
      (c'.Valid ∧ c'.mag = a.mag / 2 ^ b) ∧ Post m sp pa adp pc cdp a b c c' M :=
  ApiTripleS.of (Fn.MpDiv2d.correct ⟨ha.mpAt, hc.mpAt, ha.valid, hc.shape, ha.geom, hc.geom, hb,
    room, cv.stk.ram, cv.stk.al, cv.sp_ge, cv.ra_al, cv.img, sound⟩) fun _ _ h =>
    let s := Div2dPost.spec ha.valid room hc.shape.alloc_lt h.div; ⟨s.1, s.2.1⟩

/-- **`mp_div_2d(a, b, a, NULL)`**: `a ← a / 2^b` (truncated). -/
theorem _root_.Specs.mp_div_2d_inplace {sp pa adp : Nat} {a : MpInt} {b : Nat}
    {s0 : BitVec 64} (cv : ConvS m ra sp 96) (sound : Sound (layI sp pa adp a) Un.isW)
    (ha : MpVal m pa adp a) (hb : b < 2 ^ 31) :
    ApiTripleS m v outp ra s0 entry sp [pa, b, pa, 0] 0#64 fun a' M =>
      (a'.Valid ∧ a'.mag = a.mag / 2 ^ b) ∧ PostI m sp pa adp a b a' M :=
  ApiTripleS.of (Fn.MpDiv2d.correct_inplace ⟨ha.mpAt, ha.valid, ha.geom, hb, cv.stk.ram, cv.stk.al,
    cv.sp_ge, cv.ra_al, cv.img, sound⟩) fun _ _ h =>
    let s := Div2dPost.spec ha.valid ha.valid.used_le ha.valid.alloc_lt h.div; ⟨s.1, s.2.1⟩

end Tom.Machine.Api.MpDiv2d
