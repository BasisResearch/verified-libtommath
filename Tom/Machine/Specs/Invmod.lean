import Tom.Machine.Conventions
import Tom.Machine.Fn.Invmod

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_invmod`: the concise specification (SPECS.lean), from `Fn.Invmod.correctG` -/

namespace Tom.Machine.Api.MpInvmodG
open Tom.Machine.Api.Invmod

/-- **`mp_invmod(a, b, c)`**: `c ← a⁻¹ mod b` (in `[0, b)`), for `b > 1` and `a` invertible mod
`b`, `a ≥ 0` or `b` even (README, bug 2: `a < 0` with odd `b` returns a negative `c`). -/
theorem _root_.Specs.mp_invmod {p : P} (cv : Conv m ra p.sp F (hin p)) (sound : Sound (lay p) isW)
    (a : MpOwn m p.H p.pa p.adp p.a) (b : MpOwn m p.H p.pb p.bdp p.b) (c : MpOut m p.pc p.cdp p.c)
    (au : p.a.used + 3 < 2 ^ 30) (hb : 1 < p.b.val) (hg : (invmodRem p.a p.b).gcd p.b.mag = 1)
    (hs : 0 ≤ p.a.val ∨ p.b.mag % 2 = 0) :
    ApiTriple m v outp ra MpInvmod.entry p.sp [p.pa, p.pb, p.pc]
      (fun | .err r => BitVec.ofInt 64 r | .ok .. => 0#64) fun x M =>
      (match x with
        | .err r => r = Layout.mpMem ∨ r = Layout.mpOkay ∧ p.c.Valid ∧ 0 ≤ p.c.val ∧
            p.c.val < p.b.val ∧ p.a.val * p.c.val % p.b.val = 1
        | .ok _ c' => c'.Valid ∧ 0 ≤ c'.val ∧ c'.val < p.b.val ∧ p.a.val * c'.val % p.b.val = 1) ∧
      HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M :=
  have spec := fun {c' : MpInt} {r : Int} (h : InvmodPost p.a p.b p.c c' r) =>
    InvmodPost.spec_ok a.valid hb hg hs h
  ApiTriple.of (Reg.call (Fn.Invmod.correctG cv.ra_al ⟨cv.stk, a.valid, b.valid, au, c.pos, a.blk,
    b.blk, a.pos, b.pos, a.off, b.off, c.off⟩ sound) cv.heap (by mp_regions)) fun
    | .err _, hq => hq.imp_right fun h => (spec h).1 ▸ ⟨rfl, (spec h).2⟩
    | .ok .., hq => (spec hq).2

end Tom.Machine.Api.MpInvmodG
