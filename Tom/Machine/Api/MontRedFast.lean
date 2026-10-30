import Tom.Machine.Api.Two
import Tom.Spec.Reduce

/-!
# `s_mp_montgomery_reduce_fast`: the standard contract

From the entry, `s_mp_montgomery_reduce_fast(x, n, rho)` with `x`, `n` valid,
`rho` from `mp_montgomery_setup` (`n rho ≡ -1 (mod radix)`, `rho < radix`), distinct (D6), `|x| < |n| R` (`R = radix^(n->used)`, so
`x->used ≤ 2 n->used`), `1 ≤ n->used ≤ 255` (`n->used < MP_MAXFAST`: no column
overflows `mp_word`) and `x->alloc > n->used` (no `mp_grow`, D5), returns
`MP_OKAY` with `RedcPost x n rho x'` (`RedcPost.spec`: `x'` valid, `|x'| < |n|`,
`|x'| R ≡ |x| (mod |n|)`), the callee-saved registers restored, and memory
changed only in `Two.ws`: the stack `[sp - 4256, sp)` (its frame, with
`W[MP_WARRAY]`; `__muldi3`, `memset`, `mp_clamp`, `mp_cmp_mag` use none, the
tail-called `s_mp_sub` runs in the frame's top 48 bytes) and `x`. Regions as
`Api/Two.lean` with `n` read (Two's `a`) and `x` written (Two's `b`).
-/

namespace Tom.Machine.Api.MontRedFast

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Mont

def entry : BitVec 64 := 0x80003d9c#64

/-- The arguments: `a0 = x`, `a1 = n`, `a2 = rho`. -/
def entryL (ra s0 : BitVec 64) (sp px pn rho : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 px), (11, BitVec.ofNat 64 pn),
   (12, BitVec.ofNat 64 rho)]

/-- `n` read (Two's `a`), `x` written (Two's `b`). -/
abbrev lay (sp px xdp pn ndp : Nat) (x n : MpInt) := Two.lay 4256 sp pn ndp px xdp n x

/-- What `s_mp_montgomery_reduce_fast(x, n, rho)` needs. -/
structure Pre (m : Mem) (sp px xdp pn ndp : Nat) (x n : MpInt) (rho : Nat) (ra : BitVec 64) : Prop where
  rx : MpAt m px xdp x
  rn : MpAt m pn ndp n
  vx : x.Valid
  vn : n.Valid
  gx : MpGeom px xdp x.alloc
  gn : MpGeom pn ndp n.alloc
  rho_ok : (n.mag * rho + 1) % radix = 0
  rho_lt : rho < radix
  x_lt : x.mag < n.mag * radix ^ n.used
  nu_pos : 1 ≤ n.used
  nu_le : n.used ≤ 255
  room : n.used < x.alloc
  rs : Ram (sp - 4256) 4256
  sp_al : sp % 16 = 0
  sp_ge : 4256 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp px xdp pn ndp x n) Two.isW

/-- What it leaves. -/
structure Post (m : Mem) (sp px xdp pn ndp : Nat) (x n : MpInt) (rho : Nat) (x' : MpInt) (M : Mem) : Prop where
  repr : MpAt M px xdp x'
  redc : RedcPost x n rho x'
  frame : Frm (lay sp px xdp pn ndp x n) Two.ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp px xdp pn ndp : Nat) (x n : MpInt) (rho : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ x' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp px xdp pn ndp x n rho x' M

/-- **`s_mp_montgomery_reduce_fast` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp px xdp pn ndp : Nat} {x n : MpInt} {rho : Nat}
    {ra s0 : BitVec 64}, Pre m sp px xdp pn ndp x n rho ra →
    Triple (At entry (entryL ra s0 sp px pn rho) m v.keepR outp) (Ret m v outp sp px xdp pn ndp x n rho ra s0)

end Tom.Machine.Api.MontRedFast
