import Tom.Machine.Conventions
import Tom.Machine.Fn.Reduce2kMain
import Tom.Machine.Fn.Reduce2kLMain

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_reduce_is_2k`, `mp_reduce_is_2k_l`: the concise specifications (SPECS.lean), from
`Fn.Reduce2k.correct`, `Fn.Reduce2kL.correct` -/

namespace Tom.Machine.Api.Reduce2k
open Tom.Machine.Api.Un

/-- **`mp_reduce_is_2k(a)`**: `isReduce2k a` (`1` iff `|a| = 2^p - d` for one digit `d`, the C's bit
test). Only the stack is written. -/
theorem _root_.Specs.mp_reduce_is_2k {sp pa adp : Nat} {a : MpInt} {s0 : BitVec 64}
    (cv : ConvS m ra sp 16) (sound : Sound (lay sp pa adp a) fun | R.stk => true | _ => false)
    (ha : MpVal m pa adp a) (fa : Fits a) :
    Triple (At entry ((1, ra) :: (2, BitVec.ofNat 64 sp) :: (8, s0) :: callArgs 10 [pa]) m v.keepR outp)
      fun cf => ∃ M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0),
        (10, BitVec.ofNat 64 (isReduce2k a))] M v.keepR outp cf ∧ Frm (lay sp pa adp a) [R.stk] m M :=
  Fn.Reduce2k.correct ⟨ha.mpAt, ha.valid, ha.geom, fa, cv.stk.ram, cv.stk.al, cv.sp_ge, cv.ra_al,
    cv.img, sound⟩

end Tom.Machine.Api.Reduce2k

namespace Tom.Machine.Api.Reduce2kL

/-- **`mp_reduce_is_2k_l(a)`**: `isReduce2kL a` (`1` iff `a` has one digit or at least half of its
digits are `radix - 1`). -/
theorem _root_.Specs.mp_reduce_is_2k_l {pa adp : Nat} {a : MpInt}
    (cv : ConvL m ra) (ha : MpVal m pa adp a) :
    ApiPure m v outp ra entry [pa] (BitVec.ofNat 64 (isReduce2kL a)) :=
  Fn.Reduce2kL.correct ⟨ha.mpAt, ha.valid.toShape, ha.geom, cv.ra_al, cv.img⟩

end Tom.Machine.Api.Reduce2kL
