import Tom.Machine.Api.Two
import Tom.Spec.Reduce

/-!
# `mp_dr_reduce`: the standard contract

From the entry, `mp_dr_reduce(x, n, k)` with `x`, `n` valid and distinct (D6),
`n` nonzero, `k < radix` (an `mp_digit`), `|x| < radix^(2 n->used)` (the C
asks for `x ≤ (n - 1)^2`) and `x->alloc ≥ 2 n->used` (no `mp_grow`, D5),
returns `MP_OKAY` with `DrReducePost x n k x'` (`DrReducePost.spec`: for
`n + k = radix^(n->used)`, `x'` valid and `|x'| = |x| mod |n|`), the
callee-saved registers restored, and memory changed only in `Two.ws`: the
stack `[sp - 176, sp)` (its frame of 128 bytes and the 48 of `s_mp_sub`;
`__muldi3`, `memset`, `mp_clamp`, `mp_cmp_mag` use none) and `x`. Regions as
`Api/Two.lean` with `n` read (Two's `a`) and `x` written (Two's `b`).
-/

namespace Tom.Machine.Api.DrReduce

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Reduce

def entry : BitVec 64 := 0x800055e4#64

/-- The arguments: `a0 = x`, `a1 = n`, `a2 = k`. -/
def entryL (ra s0 : BitVec 64) (sp px pn k : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 px), (11, BitVec.ofNat 64 pn),
   (12, BitVec.ofNat 64 k)]

/-- `n` read (Two's `a`), `x` written (Two's `b`). -/
abbrev lay (sp px xdp pn ndp : Nat) (x n : MpInt) := Two.lay 176 sp pn ndp px xdp n x

/-- What `mp_dr_reduce(x, n, k)` needs. -/
structure Pre (m : Mem) (sp px xdp pn ndp : Nat) (x n : MpInt) (k : Nat) (ra : BitVec 64) : Prop where
  rx : MpAt m px xdp x
  rn : MpAt m pn ndp n
  vx : x.Valid
  vn : n.Valid
  gx : MpGeom px xdp x.alloc
  gn : MpGeom pn ndp n.alloc
  n_pos : 0 < n.mag
  k_lt : k < radix
  x_lt : x.mag < radix ^ (2 * n.used)
  room : 2 * n.used ≤ x.alloc
  rs : Ram (sp - 176) 176
  sp_al : sp % 16 = 0
  sp_ge : 176 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp px xdp pn ndp x n) Two.isW

/-- What it leaves. -/
structure Post (m : Mem) (sp px xdp pn ndp : Nat) (x n : MpInt) (k : Nat) (x' : MpInt) (M : Mem) : Prop where
  repr : MpAt M px xdp x'
  dr : DrReducePost x n k x'
  /-- No `mp_grow` (D5): `x`'s digits stay in place. -/
  alloc : x'.alloc = x.alloc
  frame : Frm (lay sp px xdp pn ndp x n) Two.ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp px xdp pn ndp : Nat) (x n : MpInt) (k : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ x' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp px xdp pn ndp x n k x' M

/-- **`mp_dr_reduce` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp px xdp pn ndp : Nat} {x n : MpInt} {k : Nat} {ra s0 : BitVec 64},
    Pre m sp px xdp pn ndp x n k ra →
    Triple (At entry (entryL ra s0 sp px pn k) m v.keepR outp) (Ret m v outp sp px xdp pn ndp x n k ra s0)

end Tom.Machine.Api.DrReduce
