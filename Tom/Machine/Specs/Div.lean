import Tom.Machine.Conventions
import Tom.Machine.Fn.MpDivMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_div`: the concise specification (SPECS.lean), from `Fn.MpDivG5.correct` -/

namespace Tom.Machine.Api.MpDiv

/-- The effect: `Post2`, `HPost` with two results (`c`'s and `d`'s digits). -/
def eff (p : P) : Eff Out (MpInt × MpInt) where
  lay := lay p
  isW := isW
  hin := hin p
  res | .mem => none | .small c' d' | .big _ c' _ d' => some (c', d')
  frame x m M := Post2 (lay p) ws .cD .dD (out p x) (siteC p x) (siteD p x) (hin p) (hout p x) m M

/-- **`mp_div(a, b, c, d)`**: `c ← a / b`, `d ← a mod b` (truncated: `a = b·c + d`, `d` with the
sign of `a`), for `b ≠ 0`, growing `c` and `d`; `MP_MEM` only when `|a| ≥ |b|`. -/
theorem _root_.Specs.mp_div {p : P} (cv : Conv m ra p.sp F (eff p)) (a : MpOwn m p.H p.pa p.adp p.a)
    (b : MpOwn m p.H p.pb p.bdp p.b) (c : MpOut m p.pc p.cdp p.c) (d : MpOut m p.pd p.ddp p.d)
    (cnn : p.pc ≠ 0) (dnn : p.pd ≠ 0) (fb : Fits p.b) (bnz : 0 < p.b.used)
    (au : CIdx (p.a.used + 3)) (droom : p.a.used ≤ p.d.alloc) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb, p.pc, p.pd] (eff p)
      (mem := p.b.mag ≤ p.a.mag) fun (c', d') =>
      c'.Valid ∧ c'.val = p.a.val.tdiv p.b.val ∧ d'.Valid ∧ d'.val = p.a.val.tmod p.b.val :=
  have quot := fun {c'} h => (DivQuot.spec a.valid b.valid bnz (by unfold CIdx at au; omega)
    c.shape.alloc_lt h (c' := c'))
  have rem := fun {d'} h => (DivRem.spec a.valid b.valid bnz droom d.shape.alloc_lt h (d' := d'))
  ApiTriple.of (Reg.call (Fn.MpDivG5.correct cv.ra_al ⟨cv.stk, a.valid, b.valid, bnz, fb, au, droom,
    c.pos, d.pos, cnn, dnn, a.off, b.off, c.off, d.off, c.shape, d.shape, a.blk, a.pos, b.blk⟩
    cv.sound)
    cv.heap (by mp_regions)) fun
    | .mem, hq => hq
    | .small .., hq | .big .., hq =>
      ⟨(quot hq.2.1).1, (quot hq.2.1).2.2, (rem hq.2.2).1, (rem hq.2.2).2.2⟩

end Tom.Machine.Api.MpDiv
