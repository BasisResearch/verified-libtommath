import Tom.Machine.Conventions
import Tom.Machine.Fn.MpReduceSetupGMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_reduce_setup`: the concise specification (SPECS.lean), from
`Fn.MpReduceSetupGG5.correct` -/

namespace Tom.Machine.Api.MpReduceSetupG
open Tom.Machine.Api.MpReduceSetup (entry P R lay kind isW ws args)

/-- **`mp_reduce_setup(a, b)`**: `a ← ⌊radix^(2k) / b⌋` (`k = b.used`, Barrett's `mu`), for `b > 0`,
growing `a`. -/
theorem _root_.Specs.mp_reduce_setup {p : P}
    (cv : Conv m ra p.sp F (hin p)) (sound : Sound (lay p) isW)
    (a : MpOut m p.pa p.adp p.a) (b : MpOwn m p.H p.pb p.bdp p.b)
    (b0 : 0 < p.b.used) (bz : p.b.sign = Layout.mpZpos)
    (k_lt : p.b.used * 2 * Layout.digitBits < 2 ^ 31) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb]
      (fun | .mem .. => MpInit.memBV | .ok .. => 0#64) fun x M =>
      (match x with
        | .mem _ a' => 0 < a'.alloc
        | .ok _ a' => a'.Valid ∧ a'.val = (radix ^ (2 * p.b.used) / p.b.mag : Nat)) ∧
      HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.MpReduceSetupGG5.correct cv.ra_al
    ⟨cv.stk, a.shape, b.valid, b0, bz, k_lt, a.pos, a.off, b.off, b.blk⟩ sound) cv.heap (by mp_regions)) fun
    | .mem .., hq => hq
    | .ok .., hq => ⟨hq.valid, by simp [MpInt.val, hq.sign, hq.mag, Layout.mpZpos, Layout.mpNeg]⟩

end Tom.Machine.Api.MpReduceSetupG
