import Tom.Machine.Conventions
import Tom.Machine.Fn.MpGcdMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_gcd`: the concise specification (SPECS.lean), from `Fn.MpGcdG5.correct` -/

namespace Tom.Machine.Api.MpGcd

/-- **`mp_gcd(a, b, c)`**: `c ← gcd(a, b)` (`c` with room, its digits a live block of `H`);
`MP_MEM` from the second `mp_init_copy` leaks the first copy's block `q` (README, bug 6). -/
theorem _root_.Specs.mp_gcd {p : P} (cv : Conv m ra p.sp F (hin p)) (sound : Sound (lay p) isW)
    (a : MpOwn m p.H p.pa p.adp p.a) (b : MpOwn m p.H p.pb p.bdp p.b) (c : MpOut m p.pc p.cdp p.c)
    (cb : digBlk p.cdp p.c ∈ p.H) (fa : Fits p.a) (fb : Fits p.b)
    (room : max p.a.used p.b.used + 1 ≤ p.c.alloc) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb, p.pc]
      (fun | .ok _ => 0#64 | _ => MpInit.memBV) fun x M =>
      (match x with
        | .ok c' => c'.Valid ∧ c'.val = Int.gcd p.a.val p.b.val
        | .memU => True
        | .memV q => Fresh p.H q (4 * initPrec p.a.used)) ∧
      HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.MpGcdG5.correct cv.ra_al ⟨cv.stk, a.valid, b.valid, c.shape, fa, fb,
    room, a.blk, b.blk, a.pos, b.pos, a.off, b.off, c.off⟩ sound) cv.heap (by mp_regions)) fun
    | .ok _, hq => ⟨(GcdPost.spec hq.1).1, GcdPost.spec_int hq.1⟩
    | .memU, hq => hq
    | .memV _, hq => hq

end Tom.Machine.Api.MpGcd
