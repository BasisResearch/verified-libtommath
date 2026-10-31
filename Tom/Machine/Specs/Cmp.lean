import Tom.Machine.Conventions
import Tom.Machine.Fn.CmpSMain
import Tom.Machine.Fn.CmpDMain
import Tom.Machine.Fn.CmpMag
import Tom.Spec.Cmp
import Tom.Spec.Algo

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_cmp`, `mp_cmp_d`, `mp_cmp_mag`: the concise specifications (SPECS.lean), from
`Fn.CmpS.correct`, `Fn.CmpD.correct`, `Fn.CmpMag.correctS` -/

namespace Tom.Machine.Api.CmpS

/-- **`mp_cmp(a, b)`**: `MP_LT`/`MP_EQ`/`MP_GT` as `a < b`, `a = b`, `a > b`. -/
theorem _root_.Specs.mp_cmp {pa adp pb bdp : Nat} {a b : MpInt}
    (cv : ConvL m ra) (ha : MpVal m pa adp a) (hb : MpVal m pb bdp b) :
    ApiPure m v outp ra entry [pa, pb] (BitVec.ofInt 64 (ordCode (compare a.val b.val))) := by
  rw [← cmpS_spec ha.valid hb.valid]
  exact Fn.CmpS.correct ⟨ha.mpAt, hb.mpAt, ha.valid, hb.valid, ha.geom, hb.geom, cv.ra_al, cv.img⟩

end Tom.Machine.Api.CmpS

namespace Tom.Machine.Api.CmpD

/-- **`mp_cmp_d(a, b)`**: `a` against the digit `b`. -/
theorem _root_.Specs.mp_cmp_d {pa adp : Nat} {a : MpInt} {b : Nat}
    (cv : ConvL m ra) (ha : MpVal m pa adp a) (pos : 0 < a.alloc) (hb : b < radix) :
    ApiPure m v outp ra entry [pa, b] (BitVec.ofInt 64 (ordCode (compare a.val b))) := by
  rw [← cmpD_spec ha.valid hb]
  exact Fn.CmpD.correct ⟨ha.mpAt, ha.valid, ha.geom, pos, hb, cv.ra_al, cv.img⟩

end Tom.Machine.Api.CmpD

namespace Tom.Machine.Fn.CmpMag

/-- **`mp_cmp_mag(a, b)`**: `|a|` against `|b|`. -/
theorem _root_.Specs.mp_cmp_mag {pa adp pb bdp : Nat} {a b : MpInt}
    (cv : ConvL m ra) (ha : MpVal m pa adp a) (hb : MpVal m pb bdp b) :
    ApiPure m v outp ra 0x80000764#64 [pa, pb] (BitVec.ofInt 64 (ordCode (compare a.mag b.mag))) := by
  rw [← cmpMag_eq ha.valid hb.valid]
  exact correctS ra v outp pa adp pb bdp a b m cv.ra_al
    ⟨ha.mpAt, hb.mpAt, ha.valid.toShape, hb.valid.toShape, ha.geom, hb.geom, cv.img.mpCmpMag⟩

end Tom.Machine.Fn.CmpMag
