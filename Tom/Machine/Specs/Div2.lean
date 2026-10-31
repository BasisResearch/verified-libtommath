import Tom.Machine.Conventions
import Tom.Machine.Fn.Div2Main
import Tom.Machine.Fn.Div2InPlace

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_div_2`: the concise specifications (SPECS.lean), from `Fn.Div2.correct`,
`Fn.Div2.correct_inplace` -/

namespace Tom.Machine.Api.Div2
open Tom.Machine.Api.Two

/-- **`mp_div_2(a, b)`**: `b ← a / 2` (truncated), `b` with room. -/
theorem _root_.Specs.mp_div_2 {sp pa adp pb bdp : Nat} {a b : MpInt} {s0 : BitVec 64}
    (cv : ConvS m ra sp 32) (sound : Sound (lay sp pa adp pb bdp a b) isW)
    (ha : MpVal m pa adp a) (hb : MpOut m pb bdp b) (room : a.used ≤ b.alloc) :
    ApiTripleS m v outp ra s0 entry sp [pa, pb] 0#64 fun b' M =>
      (b'.Valid ∧ b'.val = a.val.tdiv 2) ∧ Post m sp pa adp pb bdp a b b' M :=
  ApiTripleS.of (Fn.Div2.correct ⟨ha.mpAt, hb.mpAt, ha.valid, hb.shape, ha.geom, hb.geom, room,
    cv.stk.ram, cv.stk.al, cv.sp_ge, cv.ra_al, cv.img, sound⟩) fun _ _ h =>
    (Div2Post.spec ha.valid room hb.shape.alloc_lt h.div2).imp_right And.right

/-- **`mp_div_2(a, a)`**: `a ← a / 2` (truncated). -/
theorem _root_.Specs.mp_div_2_inplace {sp pa adp : Nat} {a : MpInt} {s0 : BitVec 64}
    (cv : ConvS m ra sp 32) (sound : Sound (Un.lay 32 sp pa adp a) Un.isW) (ha : MpVal m pa adp a) :
    ApiTripleS m v outp ra s0 entry sp [pa, pa] 0#64 fun a' M =>
      (a'.Valid ∧ a'.val = a.val.tdiv 2) ∧ PostI m sp pa adp a a' M :=
  ApiTripleS.of (Fn.Div2.correct_inplace ⟨ha.mpAt, ha.valid, ha.geom, ha.valid.used_le, cv.stk.ram,
    cv.stk.al, cv.sp_ge, cv.ra_al, cv.img, sound⟩) fun _ _ h =>
    (Div2Post.spec ha.valid ha.valid.used_le ha.valid.alloc_lt h.div2).imp_right And.right

end Tom.Machine.Api.Div2
