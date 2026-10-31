import Tom.Machine.Conventions
import Tom.Machine.Fn.MontRedGrMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_montgomery_reduce`: the concise specification (SPECS.lean), from
`Fn.MontRedGrG5.correct` -/

namespace Tom.Machine.Api.MontRedGr
open Tom.Mont
open Tom.Machine.Api.MpReduce2k (R P kind)

/-- **`mp_montgomery_reduce(x, n, rho)`**: `x ← x · radix^(-k) mod n` (`k = n.used`, `rho = -1/n`
mod the radix), for `|x| < n · radix^k`. -/
theorem _root_.Specs.mp_montgomery_reduce {p : P}
    (cv : Conv m ra p.sp F (hin p)) (sound : Sound (lay p) MpReduce2k.isW)
    (a : MpOut m p.pa p.adp p.a) (va : p.a.Valid) (n : MpOwn m p.H p.pn p.ndp p.n)
    (rho : (p.n.mag * p.d + 1) % radix = 0) (hr : p.d < radix)
    (hx : p.a.mag < p.n.mag * radix ^ p.n.used) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pn, p.d] okRet fun x M =>
      OkRes x (fun a' => a'.Valid ∧ a'.mag < p.n.mag ∧
        a'.mag * radix ^ p.n.used % p.n.mag = p.a.mag % p.n.mag) ∧
      HPost (lay p) MpReduce2k.ws .aD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.MontRedGrG5.correct cv.ra_al
    ⟨cv.stk, va, n.valid, rho, hr, hx, a.pos, a.off, n.off⟩ sound) cv.heap (by mp_regions))
    fun _ hq h => MontRedFastGStep.RedcV.spec rho hx (ReduxG.Out.post hq h)

end Tom.Machine.Api.MontRedGr
