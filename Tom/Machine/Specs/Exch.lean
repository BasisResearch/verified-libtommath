import Tom.Machine.Conventions
import Tom.Machine.Fn.ExchMain

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_exch`: the concise specification (SPECS.lean), from `Fn.Exch.correct` -/

namespace Tom.Machine.Api.Exch
open Tom.Machine.Api.Two

/-- **`mp_exch(a, b)`**: swaps the structs: after, `a`'s struct holds `b` (digits at `bdp`) and
`b`'s holds `a` (`Post`; `void`). -/
theorem _root_.Specs.mp_exch {sp pa adp pb bdp : Nat} {a b : MpInt}
    (cv : ConvL m ra) (sound : Sound (lay sp pa adp pb bdp a b) isW2)
    (ha : MpVal m pa adp a) (hb : MpVal m pb bdp b) :
    Triple (At entry ((1, ra) :: callArgs 10 [pa, pb]) m v.keep outp) fun cf =>
      ∃ M, At ra [(1, ra)] M v.keep outp cf ∧ Post m sp pa adp pb bdp a b M :=
  Fn.Exch.correct ⟨ha.mpAt, hb.mpAt, ha.geom, hb.geom,
    by rcases ha.valid.sign_ok with h | h <;> rw [h] <;> decide, cv.ra_al, cv.img, sound⟩

end Tom.Machine.Api.Exch
