import Tom.Machine.Conventions
import Tom.Machine.Fn.MpZeroMain

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_zero`: the concise specification (SPECS.lean), from `Fn.MpZero.correct` -/

namespace Tom.Machine.Api.MpZero
open Tom.Machine.Api.Un

/-- **`mp_zero(a)`**: `a ← 0` (`void`). -/
theorem _root_.Specs.mp_zero {sp pa adp : Nat} {a : MpInt} (cv : ConvM m ra (lay sp pa adp a) isW)
    (ha : MpOut m pa adp a) :
    Triple (At entry ((1, ra) :: callArgs 10 [pa]) m v.keep outp) fun cf =>
      ∃ a' M, At ra [(1, ra)] M v.keep outp cf ∧ (a'.Valid ∧ a'.val = 0) ∧ Post m sp pa adp a a' M :=
  Triple.rmap (fun _ ⟨a', M, hat, h⟩ => ⟨a', M, hat,
      let s := ZeroPost.spec ha.shape h.zero; ⟨s.1, s.2.2⟩, h⟩)
    (Fn.MpZero.correct ⟨ha.mpAt, ha.shape, ha.geom, cv.ra_al, cv.img, cv.sound⟩)

end Tom.Machine.Api.MpZero
