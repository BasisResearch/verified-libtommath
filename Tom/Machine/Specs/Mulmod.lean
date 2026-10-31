import Tom.Machine.Conventions
import Tom.Machine.Fn.MpMulmodMainG
import Tom.Machine.Fn.MulGroupB

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_mulmod`: the concise specification (SPECS.lean), from `Fn.MpMulmodG5.correct` (its
`mp_mul` premise by `Fn.MulGroupB.mulCorrect`) -/

namespace Tom.Machine.Api.MpMulmod

def eff (p : P) := Eff.heap (lay p) isW ws .dD (out p) (site' p) (hin p) (hout p)
  fun | .mem _ => none | .ok _ d' => some d'

/-- **`mp_mulmod(a, b, c, d)`**: `d ← a · b mod c` (in `[0, c)`), for `c > 0`, growing `d`
(`MP_MEM` changes at most `d`'s sign: SPECS_UNFOLDED.lean). -/
theorem _root_.Specs.mp_mulmod {p : P}
    (cv : Conv m ra p.sp (2864 + 8 * (p.a.used + p.b.used)) (eff p)) (cut : Cutoffs m)
    (a : MpOwn m p.H p.pa p.adp p.a) (b : MpOwn m p.H p.pb p.bdp p.b)
    (c : MpOwn m p.H p.pc p.cdp p.c) (d : MpOut m p.pd p.ddp p.d) (hc : 0 < p.c.val) (fc : Fits p.c)
    (uab : CIdx (p.a.used + p.b.used + 3)) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb, p.pc, p.pd] (eff p)
      fun d' => d'.Valid ∧ d'.val = p.a.val * p.b.val % p.c.val :=
  have cz : p.c.sign = Layout.mpZpos := DivStep.sign_of_val_nonneg c.valid (by omega)
  have c0 : 0 < p.c.used := Nat.pos_of_ne_zero fun h => by
    have : p.c.mag = 0 := by simp [MpInt.mag, h, natUpTo]
    unfold MpInt.val at hc; split at hc <;> omega
  ApiTriple.of (Reg.call (Fn.MpMulmodG5.correct cv.ra_al ⟨cv.stk, Fn.MulGroupB.mulCorrect.1,
    a.valid, b.valid, uab, a.pos, b.pos, c.valid, c0, cz, fc, d.shape, d.pos, a.off, b.off, c.off,
    d.off, c.blk⟩ cv.sound) cv.heap (by mp_regions)) fun
    | .mem _, _ => trivial
    | .ok .., hq => let s := Reduce.MulmodPost.spec hc hq; ⟨s.1, s.2.2.2⟩

end Tom.Machine.Api.MpMulmod
