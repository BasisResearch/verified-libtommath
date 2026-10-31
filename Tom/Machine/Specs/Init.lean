import Tom.Machine.Conventions
import Tom.Machine.Fn.MpInitMain
import Tom.Machine.Fn.MpInitCopyMain
import Tom.Machine.Fn.MpInitMultiMain

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_init`, `mp_init_copy`, `mp_init_multi`, `mp_init_size`: the concise specifications
(SPECS.lean): the allocator-level contracts, their precondition structure `Pre` kept whole -/

namespace Tom.Machine.Api.MpInit
open LeanRV64DExecutable.Functions

/-- **`mp_init(a)`**: `a ← 0` with `MP_PREC` fresh digits (`Post.ok`: a fresh block `q`, `a` live
with `zeroN defPrec`) or `MP_MEM` (`Post.mem`). `Pre`: the heap with the live blocks `H`, `a`'s
24 bytes (RAM, 8-aligned, off the allocator), the allocator's context `ACtx` with `F` bytes of
stack, `ra`, `Sound`. -/
theorem _root_.Specs.mp_init {H : List (Nat × Nat)} {sp pa : Nat} (pre : Pre m v H sp pa Finit ra) :
    Triple (At Fn.MpInit.initEntry ((1, ra) :: callArgs 10 [pa]) m v.keep outp) fun cf =>
      ∃ r M, At ra [(1, ra), (10, r)] M v.keep outp cf ∧ Post m M H sp pa Finit defPrec r :=
  Fn.MpInit.init_correct pre

/-- **`mp_init_size(a, size)`**: as `mp_init` with `max(size, MP_MIN_PREC)` digits (`initPrec`). -/
theorem _root_.Specs.mp_init_size {H : List (Nat × Nat)} {sp pa size : Nat}
    (pre : Pre m v H sp pa Fsize ra) (hs : CInt size) :
    Triple (At Fn.MpInit.sizeEntry ((1, ra) :: callArgs 10 [pa, size]) m v.keep outp) fun cf =>
      ∃ r M, At ra [(1, ra), (10, r)] M v.keep outp cf ∧ Post m M H sp pa Fsize (initPrec size) r :=
  Fn.MpInit.size_correct pre hs

end Tom.Machine.Api.MpInit

namespace Tom.Machine.Api.MpInitCopy
open LeanRV64DExecutable.Functions

/-- **`mp_init_copy(a, b)`**: `a ← b` in a fresh block of `initPrec b.used` digits, or `MP_MEM`
(`Post`); `Pre` as `mp_init`'s with `b` live and valid. -/
theorem _root_.Specs.mp_init_copy {H : List (Nat × Nat)} {sp pa pb bdp : Nat} {b : MpInt}
    (pre : Pre m v H sp pa pb bdp b ra) :
    Triple (At Fn.MpInitCopy.entry ((1, ra) :: callArgs 10 [pa, pb]) m v.keep outp) fun cf =>
      ∃ r M, At ra [(1, ra), (10, r)] M v.keep outp cf ∧ Post m M H sp pa pb bdp b (initPrec b.used) r :=
  Fn.MpInitCopy.correct pre

end Tom.Machine.Api.MpInitCopy

namespace Tom.Machine.Api.MpInitMulti
open Tom.Machine.Api.Multi

/-- **`mp_init_multi(a₁, …, aₖ, NULL)`**: each `aᵢ ← 0` with `MP_PREC` digits, or `MP_MEM` with the
ones initialized before the failure cleared (`Post`); `Pre`: the structs, the stack-passed
arguments (`a` registers first). -/
theorem _root_.Specs.mp_init_multi {H : List (Nat × Nat)} {sp : Nat} {xs : List Nat}
    (pre : Pre m v H sp xs ra) :
    Triple (At Fn.MpInitMulti.entry ((1, ra) :: argRegs 0 (args xs)) m v.keep outp) fun cf =>
      ∃ r M, At ra [(1, ra), (10, r)] M v.keep outp cf ∧ Post m M H sp xs r :=
  Fn.MpInitMulti.correct pre

end Tom.Machine.Api.MpInitMulti
