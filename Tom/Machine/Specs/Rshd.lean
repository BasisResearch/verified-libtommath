import Tom.Machine.Conventions
import Tom.Machine.Fn.MpRshdMain

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_rshd`: the concise specification (SPECS.lean), from `Fn.MpRshd.correct` -/

namespace Tom.Machine.Api.MpRshd
open Tom.Machine.Api.Un

/-- **`mp_rshd(a, b)`**: `|a| ← ⌊|a| / radix^b⌋` (`b` digits shifted out; `void`). -/
theorem _root_.Specs.mp_rshd {sp pa adp : Nat} {a : MpInt} {b : Nat} {s0 : BitVec 64}
    (cv : ConvS m ra sp 32) (sound : Sound (lay sp pa adp a) isW) (ha : MpVal m pa adp a)
    (hb : b < 2 ^ 31) :
    Triple (At entry ((1, ra) :: (2, BitVec.ofNat 64 sp) :: (8, s0) :: callArgs 10 [pa, b]) m v.keepR outp)
      fun cf => ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0)] M v.keepR outp cf ∧
        (a'.Valid ∧ a'.mag = a.mag / radix ^ b) ∧ Post m sp pa adp a b a' M :=
  Triple.rmap (fun _ ⟨a', M, hat, h⟩ => ⟨a', M, hat, RshdPost.spec ha.valid h.rshd, h⟩)
    (Fn.MpRshd.correct ⟨ha.mpAt, ha.valid.toShape, ha.geom, hb, cv.stk.ram, cv.stk.al, cv.sp_ge,
      cv.ra_al, cv.img, sound⟩)

end Tom.Machine.Api.MpRshd
