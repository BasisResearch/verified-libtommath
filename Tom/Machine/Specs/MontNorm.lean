import Tom.Machine.Conventions
import Tom.Machine.Fn.MontNormGMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_montgomery_calc_normalization`: the concise specification (SPECS.lean), from
`Fn.MontNormGG5.correct` -/

namespace Tom.Machine.Api.MontNormG

/-- **`mp_montgomery_calc_normalization(a, b)`**: `a ← radix^k mod b`, `k = b.used`, for odd
`b > 1`, growing `a`. -/
theorem _root_.Specs.mp_montgomery_calc_normalization {p : P} (cv : Conv m ra p.sp F (hin p))
    (sound : Sound (lay p) isW)
    (a : MpOut m p.pa p.adp p.a) (b : MpOwn m p.H p.pb p.bdp p.b) (fb : Fits p.b)
    (odd : p.b.mag % 2 = 1) (gt1 : 1 < p.b.mag) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb] okRet fun x M =>
      OkRes x (fun a' => a'.Valid ∧ a'.val = (radix ^ p.b.used % p.b.mag : Nat)) ∧
      HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.MontNormGG5.correct cv.ra_al
    ⟨cv.stk, a.shape, b.valid, odd, gt1, fb, a.pos, a.off⟩ sound) cv.heap (by mp_regions))
    fun _ hq h => let s := Mont.NormPost.spec b.valid odd gt1 (hq.post h); ⟨s.1, s.2.2⟩

end Tom.Machine.Api.MontNormG
