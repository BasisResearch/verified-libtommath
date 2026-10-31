import Tom.Machine.Conventions
import Tom.Machine.Fn.DrSetupMain

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_dr_setup`: the concise specification (SPECS.lean), from `Fn.DrSetup.correct` -/

namespace Tom.Machine.Api.DrSetup

/-- **`mp_dr_setup(a, d)`**: `*d ← drSetupDigit a` (`radix - a[0]`, the diminished-radix `d`;
`Post`, `void`). -/
theorem _root_.Specs.mp_dr_setup {pa adp pd dv : Nat} {a : MpInt}
    (cv : ConvM m ra (lay pd pa adp a) isW) (ha : MpOut m pa adp a) (d : DigOut m pd dv) :
    Triple (At entry ((1, ra) :: callArgs 10 [pa, pd]) m v.keep outp) fun cf =>
      ∃ M, At ra [(1, ra)] M v.keep outp cf ∧ Post m pa adp pd a M :=
  Fn.DrSetup.correct ⟨ha.mpAt, ha.shape, ha.geom, ha.pos, d.dig.ram, d.dig.al, cv.ra_al, cv.img,
    cv.sound⟩

end Tom.Machine.Api.DrSetup
