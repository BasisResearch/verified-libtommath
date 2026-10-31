import Tom.Machine.Conventions
import Tom.Machine.Fn.MulGroupB

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_sqr`: the concise specifications (SPECS.lean), from `Fn.MulGroupB.sqrCorrect` -/

namespace Tom.Machine.Api.MpSqr

/-- **`mp_sqr(a, b)`**: `b ← a²`, growing `b` (`room`: the fast path's room below the Karatsuba
cut-off). -/
theorem _root_.Specs.mp_sqr {p : P}
    (cv : Conv m ra p.sp (F p) (hin p)) (cut : Cutoffs m) (sound : Sound (lay p) isW)
    (a : MpOwn m p.H p.pa p.adp p.a) (b : MpOut m p.pb p.bdp p.b)
    (au : p.a.used < 2 ^ 29) (room : p.a.used < 120 → 2 * p.a.used ≤ p.b.alloc) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb] okRet fun x M =>
      OkRes x (fun b' => b'.Valid ∧ b'.val = p.a.val * p.a.val) ∧
      HPost (lay p) ws .bD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.MulGroupB.sqrCorrect.1 p cv.ra_al
    ⟨cv.stk, a.valid, b.shape, b.sign, au, room, a.pos, b.pos, a.off, b.off⟩ sound) cv.heap
    (by mp_regions)) fun _ hq h => ⟨(hq.post h).valid, (hq.post h).val⟩

end Tom.Machine.Api.MpSqr

namespace Tom.Machine.Api.MpSqrA
open Tom.Machine.Api.MpSqr (entry ksAddr tsAddr kmAddr tmAddr ksV tsV kmV tmV Fs X)

/-- **`mp_sqr(a, a)`**: `a ← a²` (`mp_sqr` with `b := a`). -/
theorem _root_.Specs.mp_sqr_inplace {p : P}
    (cv : Conv m ra p.sp (F p) (hin p)) (cut : Cutoffs m) (sound : Sound (lay p) isW)
    (a : MpOut m p.pa p.adp p.a) (va : p.a.Valid)
    (au : p.a.used < 2 ^ 29) (room : p.a.used < 120 → 2 * p.a.used ≤ p.a.alloc) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pa] okRet fun x M =>
      OkRes x (fun a' => a'.Valid ∧ a'.val = p.a.val * p.a.val) ∧
      HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.MulGroupB.sqrCorrect.2 p cv.ra_al
    ⟨cv.stk, va, au, room, a.pos, a.off⟩ sound) cv.heap (by mp_regions))
    fun _ hq h => ⟨(hq.post h).valid, (hq.post h).val⟩

end Tom.Machine.Api.MpSqrA
