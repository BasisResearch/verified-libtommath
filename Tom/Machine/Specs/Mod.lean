import Tom.Machine.Conventions
import Tom.Machine.Fn.MpModMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_mod`: the concise specification (SPECS.lean), from `Fn.MpModG5.correct` -/

namespace Tom.Machine.Api.MpMod

def eff (p : P) := Eff.heap (lay p) isW ws .cD (out p) (site' p) (hin p) (hout p)
  fun | .mem _ => none | .ok _ c' => some c'

/-- **`mp_mod(a, b, c)`**: `c ← a mod b` (floored: the sign of `b`), for `b ≠ 0`, growing `c`
(`MP_MEM` changes at most `c`'s sign: SPECS_UNFOLDED.lean). -/
theorem _root_.Specs.mp_mod {p : P} (cv : Conv m ra p.sp F (eff p)) (a : MpOwn m p.H p.pa p.adp p.a)
    (b : MpOwn m p.H p.pb p.bdp p.b) (c : MpOut m p.pc p.cdp p.c) (fb : Fits p.b)
    (bnz : 0 < p.b.used) (au : CIdx (p.a.used + 3)) (bsize : CInt (p.b.used + 1)) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb, p.pc] (eff p)
      fun c' => c'.Valid ∧ c'.val = p.a.val.fmod p.b.val :=
  ApiTriple.of (Reg.call (Fn.MpModG5.correct cv.ra_al ⟨cv.stk, a.valid, b.valid, bnz, fb, au,
    c.shape, bsize, c.pos, a.off, b.off, c.off, a.blk, a.pos, b.blk⟩
    cv.sound) cv.heap (by mp_regions)) fun
    | .mem _, _ => trivial
    | .ok .., hq => let s := ModPost.spec a.valid b.valid bnz hq; ⟨s.valid, s.val⟩

end Tom.Machine.Api.MpMod
