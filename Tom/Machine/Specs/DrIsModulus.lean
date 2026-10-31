import Tom.Machine.Conventions
import Tom.Machine.Fn.DrIsModulusMain

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_dr_is_modulus`: the concise specification (SPECS.lean), from `Fn.DrIsModulus.correct` -/

namespace Tom.Machine.Api.DrIsModulus

/-- **`mp_dr_is_modulus(a)`**: `1` iff `a` has at least two digits, all but the lowest
`radix - 1` (`IsDrModulus`). -/
theorem _root_.Specs.mp_dr_is_modulus {pa adp : Nat} {a : MpInt}
    (cv : ConvL m ra) (ha : MpVal m pa adp a) :
    ApiPure m v outp ra entry [pa] (BitVec.ofNat 64 (if IsDrModulus a then 1 else 0)) :=
  Fn.DrIsModulus.correct ⟨ha.mpAt, ha.valid.toShape, ha.geom, cv.ra_al, cv.img⟩

end Tom.Machine.Api.DrIsModulus
