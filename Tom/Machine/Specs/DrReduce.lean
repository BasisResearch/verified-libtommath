import Tom.Machine.Conventions
import Tom.Machine.Fn.DrReduceGMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_dr_reduce`: the concise specification (SPECS.lean), from `Fn.DrReduceGG5.correct` -/

namespace Tom.Machine.Api.DrReduceG
open Tom.Reduce
open Tom.Machine.Api.MpReduce2k (R P kind)

/-- **`mp_dr_reduce(a, n, d)`**: `|a| ← |a| mod n` for a diminished-radix `n = radix^k - d`
(`hk`: for the meaning only), `|a| < radix^(2k)`. -/
theorem _root_.Specs.mp_dr_reduce {p : P}
    (cv : Conv m ra p.sp F (hin p)) (sound : Sound (lay p) MpReduce2k.isW)
    (a : MpOut m p.pa p.adp p.a) (va : p.a.Valid) (n : MpOwn m p.H p.pn p.ndp p.n)
    (npos : 0 < p.n.mag) (hb : p.d < radix) (hx : p.a.mag < radix ^ (2 * p.n.used))
    (hk : p.n.mag + p.d = radix ^ p.n.used) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pn, p.d] okRet fun x M =>
      OkRes x (fun a' => a'.Valid ∧ a'.mag = p.a.mag % p.n.mag) ∧
      HPost (lay p) MpReduce2k.ws .aD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.DrReduceGG5.correct cv.ra_al
    ⟨cv.stk, va, n.valid, npos, hb, hx, a.pos, a.off, n.off⟩ sound) cv.heap (by mp_regions))
    fun _ hq h => DrReducePost.spec npos hk hx (ReduxG.Out.post hq h)

end Tom.Machine.Api.DrReduceG
