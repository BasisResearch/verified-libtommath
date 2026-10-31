import Tom.Machine.Conventions
import Tom.Machine.Fn.MpClearMain
import Tom.Machine.Fn.MpClearMultiMain

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_clear`, `mp_clear_multi`: the concise specifications (SPECS.lean): the allocator-level
contracts, their precondition structure `Pre` kept whole -/

namespace Tom.Machine.Api.MpClear

/-- **`mp_clear(a)`**: `a`'s digit block freed, `a` the cleared `mp_int` (`dp = NULL`; `Post`;
`void`). `Pre`: `a` at `pa` with its digits the front live block of the heap, the allocator's
context. -/
theorem _root_.Specs.mp_clear {H : List (Nat × Nat)} {sp pa adp : Nat} {a : MpInt}
    (pre : Pre m v H sp pa adp a ra) :
    Triple (At Fn.MpClear.entry ((1, ra) :: callArgs 10 [pa]) m v.keep outp) fun cf =>
      ∃ M, At ra [(1, ra)] M v.keep outp cf ∧ Post m H sp pa adp a M :=
  Fn.MpClear.correct pre

end Tom.Machine.Api.MpClear

namespace Tom.Machine.Api.MpClearMulti
open Tom.Machine.Api.Multi

/-- **`mp_clear_multi(a₁, …, aₖ, NULL)`**: `mp_clear` of each (`Post`; `void`). -/
theorem _root_.Specs.mp_clear_multi {H : List (Nat × Nat)} {sp : Nat} {xs : List Arg}
    (pre : Pre m v H sp xs ra) :
    Triple (At Fn.MpClearMulti.entry ((1, ra) :: argRegs 0 (args (ptrs xs))) m v.keep outp) fun cf =>
      ∃ M, At ra [(1, ra)] M v.keep outp cf ∧ Post m H sp xs M :=
  Fn.MpClearMulti.correct pre

end Tom.Machine.Api.MpClearMulti
