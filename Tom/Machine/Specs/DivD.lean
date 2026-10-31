import Tom.Machine.Conventions
import Tom.Machine.Fn.MpDivDMainG
import Tom.Machine.Fn.MpDivDIMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_div_d`: the concise specifications (SPECS.lean), from `Fn.MpDivDG5.correct`,
`Fn.MpDivDIG5.correct` -/

namespace Tom.Machine.Api.MpDivD

/-- **`mp_div_d(a, b, c, d)`**: `c ← a / b` (truncated), `*d ← |a| mod b` (`rem p`, in `out`), for a
digit `b > 0` and `c` with room (`a0`: `retv`, `MP_VAL` for `b = 0`). -/
theorem _root_.Specs.mp_div_d {p : P}
    {dv : Nat} (cv : Conv m ra p.sp F (hin p)) (sound : Sound (lay p) isW)
    (a : MpOwn m p.H p.pa p.adp p.a) (c : MpOut m p.pc p.cdp p.c) (d : DigOut m p.pd dv)
    (c_nn : p.pc ≠ 0) (hv : 0 < p.v) (hb : p.v < radix) (room : p.a.used ≤ p.c.alloc) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.v, p.pc, p.pd] (retv p) fun x M =>
      OptRes x True (fun c' => c'.Valid ∧ c'.val = p.a.val.tdiv p.v) ∧
      HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.MpDivDG5.correct cv.ra_al
    ⟨cv.stk, a.valid, c.shape, a.pos, c.pos, a.off, c.off, c_nn, d.nn, d.dig.al, d.off, hb, room⟩
    sound) cv.heap (by mp_regions)) fun
    | none, _ => trivial
    | some _, hq => (DivDQuot.spec a.valid hv room c.shape.alloc_lt hq).imp_right And.right

end Tom.Machine.Api.MpDivD

namespace Tom.Machine.Api.MpDivDI

/-- **`mp_div_d(a, b, a, d)`**: `a ← a / b` (truncated), `*d ← |a| mod b`, for a digit `b ≥ 2` and
`a ≠ 0`. -/
theorem _root_.Specs.mp_div_d_inplace {p : P}
    {dv : Nat} (cv : Conv m ra p.sp F (hin p)) (sound : Sound (lay p) isW)
    (a : MpOut m p.pa p.adp p.a) (va : p.a.Valid) (d : DigOut m p.pd dv)
    (hv : 2 ≤ p.v) (hb : p.v < radix) (ha : 0 < p.a.used) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.v, p.pa, p.pd] optRet fun x M =>
      OptRes x True (fun a' => a'.Valid ∧ a'.val = p.a.val.tdiv p.v) ∧
      HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.MpDivDIG5.correct cv.ra_al
    ⟨cv.stk, va, a.pos, a.off, hv, ha, d.nn, d.dig.al, d.off, hb⟩ sound) cv.heap (by mp_regions)) fun
    | none, _ => trivial
    | some _, hq => (DivDQuot.spec va (by omega) va.used_le a.shape.alloc_lt hq).imp_right And.right

end Tom.Machine.Api.MpDivDI
