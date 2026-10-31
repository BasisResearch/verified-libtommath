import Tom.Machine.Conventions
import Tom.Machine.Fn.ReadRadixMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_read_radix`: the concise specification (SPECS.lean), from `Fn.ReadRadixG5.correct` -/

namespace Tom.Machine.Api.ReadRadix
open Tom.Radix

/-- **`mp_read_radix(a, str, radix)`**: `a ← readVal radix s` for the string `s` at `str` (its
digits up to the first invalid character, `'-'` first for a negative), returning `readRet radix s`
(`MP_VAL` for a bad radix), `a` with room. -/
theorem _root_.Specs.mp_read_radix {sp pa adp pstr radix : Nat} {a : MpInt} {s : List Nat}
    {s0 : BitVec 64} (cv : ConvS m ra sp F) (sound : Sound (lay sp pa adp pstr a s) isW)
    (ha : MpOut m pa adp a) (str : StrAt m pstr s) (hr : radix < 2 ^ 31)
    (room : 6 * s.length ≤ Layout.digitBits * (a.alloc - 1)) :
    ApiTripleS m v outp ra s0 entry sp [pa, pstr, radix] (BitVec.ofInt 64 (readRet radix s))
      fun a' M => (a'.Valid ∧ a'.val = readVal radix s) ∧ Post m sp pa adp pstr a s radix a' M :=
  ApiTripleS.of (Fn.ReadRadixG5.correct ⟨ha.mpAt, ha.shape, ha.geom, str, hr, room, cv.stk.ram,
    cv.stk.al, cv.sp_ge, cv.ra_al, cv.img, sound⟩) fun _ _ h =>
    let s := ReadRadixPost.spec h.read; ⟨s.1, s.2.1⟩

end Tom.Machine.Api.ReadRadix
