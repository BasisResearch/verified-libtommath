import Tom.Machine.Conventions
import Tom.Machine.Fn.MpMod2dMain
import Tom.Machine.Fn.MpMod2dIMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_mod_2d`: the concise specifications (SPECS.lean), from `Fn.MpMod2d.correct`,
`Fn.MpMod2dIG5.correct` -/

namespace Tom.Machine.Api.MpMod2d
open Tom.Machine.Api.Two

/-- **`mp_mod_2d(a, b, c)`**: `c ← a mod 2^b` (`|c| = |a| mod 2^b`, the sign of `a`), `c` with room. -/
theorem _root_.Specs.mp_mod_2d {sp pa adp pc cdp : Nat} {a c : MpInt} {b : Nat} {s0 : BitVec 64}
    (cv : ConvS m ra sp 80 (lay sp pa adp pc cdp a c) isW) (ha : MpVal m pa adp a)
    (hc : MpOut m pc cdp c) (fa : Fits a) (hb : CInt b) (room : a.used ≤ c.alloc) :
    ApiTripleS m v outp ra s0 entry sp [pa, b, pc] 0#64 fun c' M =>
      (c'.Valid ∧ c'.mag = a.mag % 2 ^ b) ∧ Post m sp pa adp pc cdp a b c c' M :=
  ApiTripleS.of (Fn.MpMod2d.correct ⟨ha.mpAt, hc.mpAt, ha.valid, hc.shape, ha.geom, hc.geom, hb, fa,
    room, cv.stk.ram, cv.stk.al, cv.sp_ge, cv.ra_al, cv.img, cv.sound⟩) fun _ _ h =>
    let s := Mod2dPost.spec ha.valid room hc.shape.alloc_lt h.mod; ⟨s.1, s.2.1⟩

end Tom.Machine.Api.MpMod2d

namespace Tom.Machine.Api.MpMod2dI

/-- **`mp_mod_2d(a, b, a)`**: `a ← a mod 2^b`, for `b > 0`. -/
theorem _root_.Specs.mp_mod_2d_inplace {sp pa adp : Nat} {a : MpInt} {b : Nat} {s0 : BitVec 64}
    (cv : ConvS m ra sp 48 (lay sp pa adp a) Un.isW) (ha : MpVal m pa adp a) (fa : Fits a)
    (hb0 : 0 < b) (hb : CInt b) :
    ApiTripleS m v outp ra s0 entry sp [pa, b, pa] 0#64 fun a' M =>
      (a'.Valid ∧ a'.mag = a.mag % 2 ^ b) ∧ Post m sp pa adp a b a' M :=
  ApiTripleS.of (Fn.MpMod2dIG5.correct ⟨ha.mpAt, ha.valid, ha.geom, hb0, hb, fa, cv.stk.ram,
    cv.stk.al, cv.sp_ge, cv.ra_al, cv.img, cv.sound⟩) fun _ _ h =>
    let s := Mod2dPost.spec ha.valid ha.valid.used_le ha.valid.alloc_lt h.mod; ⟨s.1, s.2.1⟩

end Tom.Machine.Api.MpMod2dI
