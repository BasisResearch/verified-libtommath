import Tom.Machine.Api.Un
import Tom.Machine.Fn.MpMod2d
import Tom.Spec.Div2d

/-!
# `mp_mod_2d(a, b, a)`: the in-place contract

`mp_div_2d(a, b, c, d)` with `d = a` (its only callers with `d != NULL`, `mp_reduce_2k` and
`mp_reduce_2k_l`, pass `mp_div_2d(a, p, &q, a)`) calls `mp_mod_2d(a, b, a)`. From the entry,
with `a` valid, `0 < b < 2^31` and `28 a->used < 2^31`, it returns `MP_OKAY` with
`Mod2dPost a b a a'` (`Mod2dPost.spec`: `a'` valid, `|a'| = |a| mod 2^b`, the sign of `a`),
`a->alloc` and `a->dp` kept, the callee-saved registers restored, and memory changed only in
its 48-byte frame `[sp - 48, sp)` and `a` (`mp_copy(a, a)` returns at once, without a frame;
`memset`, `mp_clamp` and libgcc use no stack). Regions as `Api/Un.lean` (`a` written).
-/

namespace Tom.Machine.Api.MpMod2dI

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

def entry : BitVec 64 := 0x800057a4#64

abbrev lay (sp pa adp : Nat) (a : MpInt) := Un.lay 48 sp pa adp a

/-- What `mp_mod_2d(a, b, a)` needs. -/
structure Pre (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  va : a.Valid
  ga : MpGeom pa adp a.alloc
  /-- `b > 0`: `mp_div_2d` calls `mp_mod_2d` only on its shifting path (`b ≤ 0` copies and
  zeroes `d` itself), so the `b ≤ 0` branch (`mp_zero`) is not needed here. -/
  b_pos : 0 < b
  /-- The C's `int b`. -/
  b_lt : b < 2 ^ 31
  /-- The C's `a->used * MP_DIGIT_BIT` does not overflow (as `Api.MpMod2d`). -/
  bits : Layout.digitBits * a.used < 2 ^ 31
  rs : Ram (sp - 48) 48
  sp_al : sp % 16 = 0
  sp_ge : 48 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp a) Un.isW

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  mod : Mod2dPost a b a a'
  frame : Frm (lay sp pa adp a) Un.ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (b : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp a b a' M

/-- **`mp_mod_2d(a, b, a)` on the machine** (in place). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {b : Nat} {ra s0 : BitVec 64},
    Pre m sp pa adp a b ra →
    Triple (At entry (Fn.MpMod2d.entryL ra s0 sp pa b pa) m v.keepR outp) (Ret m v outp sp pa adp a b ra s0)

end Tom.Machine.Api.MpMod2dI
