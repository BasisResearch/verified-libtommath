import Tom.Machine.Conventions
import Tom.Machine.Fn.MpGrowMain

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_grow`: the concise specification (SPECS.lean): the allocator-level contract, its
precondition structure `Pre` kept whole -/

namespace Tom.Machine.Api.MpGrow
open LeanRV64DExecutable.Functions

/-- **`mp_grow(a, size)`**: `a`'s digits moved to a block of at least `size` digits (`realloc`), the
value kept (nothing changed if `size ≤ alloc`), or `MP_MEM` (`Post`). `Pre`: `a` shaped with its
digits the front live block, `size < 2^31`, the allocator's context. -/
theorem _root_.Specs.mp_grow {H : List (Nat × Nat)} {sp p dp : Nat} {a : MpInt} {size : Nat}
    (pre : Pre m v H sp p dp a size ra) :
    Triple (At Fn.MpGrowR.entry ((1, ra) :: callArgs 10 [p, size]) m v.keep outp) fun cf =>
      ∃ r M, At ra [(1, ra), (10, r)] M v.keep outp cf ∧ Post m M H sp p dp a size r :=
  Fn.MpGrowR.correct pre

end Tom.Machine.Api.MpGrow
