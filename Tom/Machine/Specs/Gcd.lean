import Tom.Machine.Conventions
import Tom.Machine.Fn.MpGcdMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_gcd`: the concise specification (SPECS.lean), from `Fn.MpGcdG5.correct` -/

namespace Tom.Machine.Api.MpGcd

def eff (p : P) := Eff.heap (lay p) isW ws .cD (out p) (site' p) (hin p) (hout p)
  fun | .ok c' => some c' | _ => none

/-- **`mp_gcd(a, b, c)`**: `c ← gcd(a, b)` (`c` with room, its digits a live block of `H`);
`MP_MEM` from the second `mp_init_copy` leaks the first copy's block (README, bug 6; its `Fresh`
block: SPECS_UNFOLDED.lean). -/
theorem _root_.Specs.mp_gcd {p : P} (cv : Conv m ra p.sp F (eff p)) (a : MpOwn m p.H p.pa p.adp p.a)
    (b : MpOwn m p.H p.pb p.bdp p.b) (c : MpOut m p.pc p.cdp p.c) (cb : digBlk p.cdp p.c ∈ p.H)
    (fa : Fits p.a) (fb : Fits p.b) (room : max p.a.used p.b.used + 1 ≤ p.c.alloc) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb, p.pc] (eff p)
      fun c' => c'.Valid ∧ c'.val = Int.gcd p.a.val p.b.val :=
  ApiTriple.of (Reg.call (Fn.MpGcdG5.correct cv.ra_al ⟨cv.stk, a.valid, b.valid, c.shape, fa, fb,
    room, a.blk, b.blk, a.pos, b.pos, a.off, b.off, c.off⟩ cv.sound) cv.heap (by mp_regions)) fun
    | .ok _, hq => ⟨(GcdPost.spec hq.1).1, GcdPost.spec_int hq.1⟩
    | .memU, _ | .memV _, _ => trivial

end Tom.Machine.Api.MpGcd
