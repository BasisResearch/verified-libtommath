import Tom.Machine.Conventions
import Tom.Machine.Fn.CntLsbMain
import Tom.Machine.Fn.CountBitsMain
import Tom.Spec.MpGcdStep

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_cnt_lsb`, `mp_count_bits`: the concise specifications (SPECS.lean), from
`Fn.CntLsb.correct`, `Fn.CountBits.correct` -/

namespace Tom.Machine.Api.CntLsb

/-- **`mp_cnt_lsb(a)`**: the number of trailing zero bits of `|a|` (`0` for `a = 0`). -/
theorem _root_.Specs.mp_cnt_lsb {pa adp : Nat} {a : MpInt}
    (cv : ConvL m ra) (ha : MpVal m pa adp a) (fa : Fits a) :
    ApiPure m v outp ra entry [pa] (BitVec.ofNat 64 (Gcd.lsb a.mag)) := by
  rw [← (GcdStep.cntLsb_eq ha.valid).1]
  exact Fn.CntLsb.correct ⟨ha.mpAt, ha.valid, ha.geom, fa, cv.ra_al, cv.img⟩

end Tom.Machine.Api.CntLsb

namespace Tom.Machine.Api.CountBits

/-- **`mp_count_bits(a)`**: the bit length of `|a|` (`0` for `a = 0`). -/
theorem _root_.Specs.mp_count_bits {pa adp : Nat} {a : MpInt}
    (cv : ConvL m ra) (ha : MpVal m pa adp a) (fa : Fits a) :
    ApiPure m v outp ra entry [pa] (BitVec.ofNat 64 (bitLen a.mag)) := by
  rw [← countBits_spec ha.valid]
  exact Fn.CountBits.correct ⟨ha.mpAt, ha.valid, ha.geom, fa, cv.ra_al, cv.img⟩

end Tom.Machine.Api.CountBits
