import Tom.Machine.Conventions
import Tom.Machine.Fn.MpSetMain

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_set`: the concise specification (SPECS.lean), from `Fn.MpSet.correct` -/

namespace Tom.Machine.Api.MpSet
open Tom.Machine.Api.Un

/-- **`mp_set(a, b)`**: `a ← b mod radix` (`void`). -/
theorem _root_.Specs.mp_set {sp pa adp : Nat} {a : MpInt} {bn : Nat}
    (cv : ConvM m ra (lay sp pa adp a) isW) (ha : MpOut m pa adp a) :
    Triple (At entry ((1, ra) :: callArgs 10 [pa, bn]) m v.keep outp) fun cf =>
      ∃ a' M, At ra [(1, ra)] M v.keep outp cf ∧
        (a'.Valid ∧ a'.val = ((bn % radix : Nat) : Int)) ∧ Post m sp pa adp a bn a' M :=
  Triple.rmap (fun _ ⟨a', M, hat, h⟩ => ⟨a', M, hat,
      let s := SetPost.spec ha.shape ha.pos (Nat.mod_lt _ (by decide)) h.set; ⟨s.1, s.2.2⟩, h⟩)
    (Fn.MpSet.correct ⟨ha.mpAt, ha.shape, ha.geom, ha.pos, cv.ra_al, cv.img, cv.sound⟩)

end Tom.Machine.Api.MpSet
