import Tom.Machine.Api.Un
import Tom.Machine.Fn.MpLshd
import Tom.Spec.DigitShift

/-!
# `mp_lshd`: the standard contract

From the entry, `mp_lshd(a, b)` with `a` shaped, `0 ≤ b < 2^31` and
`a->used + b ≤ a->alloc` (so no `mp_grow`, D5) returns `MP_OKAY` with
`LshdPost a b a'` (for a valid `a`: valid, `mag a' = mag a * radix^b`), the
callee-saved registers restored, memory changed only in `Un.ws` (stack
depth 32: its frame around `memset`). Regions as `Api/Un.lean`.
-/

namespace Tom.Machine.Api.MpLshd

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Un

abbrev lay (sp pa adp : Nat) (a : MpInt) := Un.lay 32 sp pa adp a

/-- What `mp_lshd(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  b_lt : b < 2 ^ 31
  room : a.used + b ≤ a.alloc
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp a) isW

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  lshd : LshdPost a b a'
  frame : Frm (lay sp pa adp a) ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra s0 : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra (Fn.MpLshd.retL ra s0 sp) M v.keepR outp cf ∧ Post m sp pa adp a b a' M

def entry : BitVec 64 := 0x800015b8#64

/-- **`mp_lshd` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {b : Nat} {ra s0 : BitVec 64},
    Pre m sp pa adp a b ra →
    Triple (At entry (Fn.MpLshd.entryL ra s0 sp pa b) m v.keepR outp) (Ret m v outp sp pa adp a b ra s0)

end Tom.Machine.Api.MpLshd
