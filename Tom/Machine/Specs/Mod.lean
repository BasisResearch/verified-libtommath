import Tom.Machine.Conventions
import Tom.Machine.Fn.MpModMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_mod`: the concise specification (SPECS.lean), from `Fn.MpModG5.correct` -/

namespace Tom.Machine.Api.MpMod

/-- **`mp_mod(a, b, c)`**: `c ← a mod b` (floored: the sign of `b`), for `b ≠ 0`, growing `c`
(`MP_MEM` changes at most `c`'s sign). -/
theorem _root_.Specs.mp_mod {p : P} (cv : Conv m ra p.sp F (hin p)) (sound : Sound (lay p) isW)
    (a : MpOwn m p.H p.pa p.adp p.a) (b : MpOwn m p.H p.pb p.bdp p.b) (c : MpOut m p.pc p.cdp p.c)
    (fb : Fits p.b) (bnz : 0 < p.b.used) (au : p.a.used + 3 < 2 ^ 30)
    (bsize : p.b.used + 1 < 2 ^ 31) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb, p.pc]
      (fun | .mem _ => MpInit.memBV | .ok .. => 0#64) fun x M =>
      (match x with
        | .mem c' => c' = { p.c with sign := c'.sign }
        | .ok _ c' => c'.Valid ∧ c'.val = p.a.val.fmod p.b.val) ∧
      HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.MpModG5.correct cv.ra_al ⟨cv.stk, a.valid, b.valid, bnz, fb, au,
    c.shape, bsize, c.pos, a.off, b.off, c.off, a.blk, a.pos, b.blk⟩ sound) cv.heap (by mp_regions)) fun
    | .mem _, hq => hq
    | .ok .., hq => let s := ModPost.spec a.valid b.valid bnz hq; ⟨s.valid, s.val⟩

end Tom.Machine.Api.MpMod
