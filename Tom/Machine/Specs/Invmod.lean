import Tom.Machine.Conventions
import Tom.Machine.Fn.Invmod

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_invmod`: the concise specification (SPECS.lean), from `Fn.Invmod.correctG` -/

namespace Tom.Machine.Api.MpInvmodG
open Tom.Machine.Api.Invmod

def eff (p : P) := Eff.heap (lay p) isW ws .cD (out p) (site' p) (hin p) (hout p)
  fun | .err r => errView r p.c | .ok _ c' => some c'

/-- **`mp_invmod(a, b, c)`**: `c ← a⁻¹ mod b` (in `[0, b)`), for `b > 1` and `a` invertible mod
`b`, `a ≥ 0` or `b` even (README, bug 2: `a < 0` with odd `b` returns a negative `c`). -/
theorem _root_.Specs.mp_invmod {p : P} (cv : Conv m ra p.sp F (eff p))
    (a : MpOwn m p.H p.pa p.adp p.a) (b : MpOwn m p.H p.pb p.bdp p.b) (c : MpOut m p.pc p.cdp p.c)
    (au : CIdx (p.a.used + 3)) (hb : 1 < p.b.val) (hg : (invmodRem p.a p.b).gcd p.b.mag = 1)
    (hs : 0 ≤ p.a.val ∨ p.b.mag % 2 = 0) :
    ApiTriple m v outp ra MpInvmod.entry p.sp [p.pa, p.pb, p.pc] (eff p)
      fun c' => c'.Valid ∧ 0 ≤ c'.val ∧ c'.val < p.b.val ∧ p.a.val * c'.val % p.b.val = 1 :=
  have spec := fun {c' : MpInt} {r : Int} (h : InvmodPost p.a p.b p.c c' r) =>
    InvmodPost.spec_ok a.valid hb hg hs h
  ApiTriple.of (Reg.call (Fn.Invmod.correctG cv.ra_al ⟨cv.stk, a.valid, b.valid, au, c.pos,
    a.blk, b.blk, a.pos, b.pos, a.off, b.off, c.off⟩ cv.sound) cv.heap (by mp_regions))
    (fun | .err _, hq => .errView (hq.imp_right spec) | .ok .., hq => (spec hq).2)
    (hr := fun
      | .err _, hq => congrArg (fun b => [(1, ra), (10, b)]) (errView_ret (hq.imp_right spec))
      | .ok .., _ => rfl)

end Tom.Machine.Api.MpInvmodG
