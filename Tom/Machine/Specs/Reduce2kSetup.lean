import Tom.Machine.Conventions
import Tom.Machine.Fn.Reduce2kSetupGrMainG
import Tom.Machine.Fn.Reduce2kSetupLGMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_reduce_2k_setup`, `mp_reduce_2k_setup_l`: the concise specifications (SPECS.lean), from
`Fn.Reduce2kSetupGrG5.correct`, `Fn.Reduce2kSetupLGG5.correct` -/

namespace Tom.Machine.Api.Reduce2kSetupGr
open Tom.Machine.Api.Reduce2kSetup (R P)

def eff (p : P) := Eff.heap (lay p) isW ws .dD (out p) (fun _ => lay p .dD) p.H (fun _ => p.H) id

/-- **`mp_reduce_2k_setup(a, &d)`**: `*d ← 2^⌈log₂ a⌉ - |a|` when that is one digit (README, bug 1: it
is the low digit otherwise). -/
theorem _root_.Specs.mp_reduce_2k_setup {p : P} (cv : Conv m ra p.sp F (eff p))
    (a : MpOwn m p.H p.pa p.adp p.a) (d : DigOut m p.pd p.d.v) (fa : Fits p.a) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pd] (eff p)
      fun d' => 2 ^ Mont.nbits p.a.mag - p.a.mag < radix → p.a.mag + d' = 2 ^ Mont.nbits p.a.mag :=
  ApiTriple.of (Reg.call (Fn.Reduce2kSetupGrG5.correct cv.ra_al ⟨cv.stk, a.valid, fa, a.pos⟩
  cv.sound)
    cv.heap (by mp_regions)) fun
    | none, _ => trivial
    | some _, hq => fun hs => Reduce.Setup2kPost.spec hq hs

end Tom.Machine.Api.Reduce2kSetupGr

namespace Tom.Machine.Api.Reduce2kSetupLG
open Tom.Reduce Tom.Mont
open Tom.Machine.Api.Reduce2kSetupL (entry P R all isW ws args)

def eff (p : P) := Eff.heap (lay p) isW ws .dD (out p) (site' p) (hin p) (hout p) optView

/-- **`mp_reduce_2k_setup_l(a, d)`**: `d ← 2^⌈log₂ a⌉ - |a|`; `MP_MEM` leaves `d` as it was. -/
theorem _root_.Specs.mp_reduce_2k_setup_l {p : P} (cv : Conv m ra p.sp F (eff p))
    (a : MpOwn m p.H p.pa p.adp p.a) (d : MpOut m p.pd p.ddp p.d) (fa : Fits p.a) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pd] (eff p)
      fun d' => p.a.mag + d'.mag = 2 ^ Mont.nbits p.a.mag :=
  ApiTriple.of (Reg.call (Fn.Reduce2kSetupLGG5.correct cv.ra_al
    ⟨cv.stk, a.valid, fa, d.shape, d.sign, a.pos, d.pos, d.off⟩
    cv.sound) cv.heap (by mp_regions)) fun
    | none, _ => trivial
    | some _, hq => Reduce.Setup2kLPost.spec hq

end Tom.Machine.Api.Reduce2kSetupLG
