import Tom.Machine.Conventions
import Tom.Machine.Fn.MpReduce2kGMainG
import Tom.Machine.Fn.MpReduce2kLGMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_reduce_2k`, `mp_reduce_2k_l`: the concise specifications (SPECS.lean), from
`Fn.MpReduce2kGG5.correct`, `Fn.MpReduce2kLGG5.correct` -/

namespace Tom.Machine.Api.MpReduce2kG
open Tom.Reduce Tom.Mont
open Tom.Machine.Api.MpReduce2k (R P kind)

/-- **`mp_reduce_2k(a, n, d)`**: `|a| ← |a| mod n` for `n = 2^⌈log₂ n⌉ - d`, `d` a digit. -/
theorem _root_.Specs.mp_reduce_2k {p : P}
    (cv : Conv m ra p.sp F (hin p)) (sound : Sound (lay p) MpReduce2k.isW)
    (a : MpOut m p.pa p.adp p.a) (va : p.a.Valid) (n : MpOwn m p.H p.pn p.ndp p.n)
    (fa : Fits p.a) (fn : Fits p.n) (npos : 0 < p.n.mag) (hb : p.d < radix)
    (hd : p.n.mag + p.d = 2 ^ nbits p.n.mag) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pn, p.d] okRet fun x M =>
      OkRes x (fun a' => a'.Valid ∧ a'.mag = p.a.mag % p.n.mag) ∧
      HPost (lay p) MpReduce2k.ws .aD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.MpReduce2kGG5.correct cv.ra_al
    ⟨cv.stk, va, n.valid, npos, hb, hd, fn, fa, a.pos, a.off, n.off⟩ sound) cv.heap (by mp_regions))
    fun _ hq h => Reduce2kPost.spec npos hd (ReduxG.Out.post hq h)

end Tom.Machine.Api.MpReduce2kG

namespace Tom.Machine.Api.MpReduce2kLG
open Tom.Reduce Tom.Mont
open Tom.Machine.Api.MpReduce2kL (entry R all P kind isW ws args)

/-- **`mp_reduce_2k_l(a, n, d)`**: `|a| ← |a| mod n` for `n = 2^⌈log₂ n⌉ - d`, `d` an `mp_int`. -/
theorem _root_.Specs.mp_reduce_2k_l {p : P}
    (cv : Conv m ra p.sp (F (p := p)) (hin p)) (cut : Cutoffs m)
    (sound : Sound (lay p) isW) (a : MpOut m p.pa p.adp p.a) (va : p.a.Valid)
    (n : MpOwn m p.H p.pn p.ndp p.n) (d : MpOwn m p.H p.pd p.ddp p.d) (fa : Fits p.a)
    (fn : Fits p.n) (npos : 0 < p.n.mag) (hd : p.n.mag + p.d.mag = 2 ^ nbits p.n.mag)
    (usz : p.a.used + 1 < 2 ^ 31) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pn, p.pd] okRet fun x M =>
      OkRes x (fun a' => a'.Valid ∧ a'.mag = p.a.mag % p.n.mag) ∧
      HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.MpReduce2kLGG5.correct cv.ra_al ⟨cv.stk, va, n.valid, d.valid, npos,
    hd, fn, fa, usz, a.pos, d.pos, a.off, n.off, d.off⟩ sound) cv.heap (by mp_regions))
    fun _ hq h => Reduce2kPost.spec npos hd (hq.post h)

end Tom.Machine.Api.MpReduce2kLG
