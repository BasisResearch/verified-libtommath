import Tom.Machine.Conventions
import Tom.Machine.Fn.Clamp

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_clamp`: the concise specification (SPECS.lean), from `Fn.Clamp.correctU` -/

namespace Tom.Machine.Fn.Clamp
open LeanRV64DExecutable.Functions Tom.Machine.Seg

/-- **`mp_clamp(a)`**: `a.used` lowered past the high zero digits, `-0` made `+0` (`Post`:
`ClampPost`, `a'` valid with `a`'s magnitude); `PreU`: `a` in memory with `ShapeU` (digits below
the radix, not yet clamped), its struct off the code. -/
theorem _root_.Specs.mp_clamp {p dp : Nat} {a : MpInt} (hra : ra.toNat % 4 = 0) (pre : PreU m p dp a) :
    Triple (At entry ((1, ra) :: callArgs 10 [p]) m v.keep outp) fun cf =>
      ∃ a' M, At ra [(1, ra), (10, BitVec.ofNat 64 p)] M v.keep outp cf ∧ Post m p dp a a' M :=
  correctU ra v outp p dp a m hra pre

end Tom.Machine.Fn.Clamp
