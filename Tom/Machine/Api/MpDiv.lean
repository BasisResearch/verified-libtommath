import Tom.Machine.Api.StdHeapFn
import Tom.Spec.Div
import Tom.Spec.Init

/-!
# `mp_div(a, b, c, d)`: the allocating contract, `c` and `d` non-NULL

`vendor/libtommath/bn_mp_div.c` as compiled at `0x80000898`. With `b ≠ 0`:

* `|a| < |b|` (`mp_cmp_mag(a, b) == MP_LT`): `mp_copy(a, d)`, `mp_zero(c)`, both in place
  (`small`; `DivQuot.small`, `DivRem.small`).
* otherwise the five temporaries `q` (`mp_init_size(&q, a->used + 2)`), `t1`, `t2`
  (`mp_init`), `x`, `y` (`mp_init_copy` of `a`, `b`), structs in the 272-byte frame, digits on
  the heap; the normalised long division (`DivInv`); then `mp_clamp(&q)`, `mp_exch(&q, c)`,
  `c->sign := neg`, `mp_div_2d(&x, norm, &x, NULL)`, `mp_exch(&x, d)` and the five
  `mp_clear`s, which free `c`'s and `d`'s old digit arrays: `c'` lives in `q`'s block `qc`,
  `d'` in `x`'s block `qd` (`big`; `DivQuot.big`, `DivRem.big`).
* `MP_MEM` from an allocation (the five `mp_init*`, or the `realloc` of a growing
  `mp_mul_2d`/`mp_lshd`/`mp_mul_d` on `x`, `y`, `t1`): every temporary is cleared, `c`, `d`
  and the heap's blocks are as before (`mem`).

So `c' = a.tdiv b`, `d' = a.tmod b` (`DivQuot.spec`, `DivRem.spec`, `div_spec`).

Two sites are re-placed (`c`'s and `d`'s digit arrays), so the post is `Post2`, `HPost`
(`Kit/MeetHeap.lean`) with two sites. The temporaries' sizes are fixed by the code, and they
grow (`mp_mul_2d(&x, norm, &x)` needs `a->used + 1 > max(3, a->used)` digits as soon as
`a->used ≥ 3`): no room assumption is made on them. Memory changes only in the stack
`[sp - 896, sp)` (the frame and `mp_init_copy`'s 624; the growing callees need at most 624),
`c`, `d` and the allocator's footprint.

Without `dsh` the statement is refutable: `mp_copy`
leaves `d`'s digits above its old `used`), `ablk`, `apos`, `bblk` (`mp_init_copy`'s source is a
live nonempty block). Not covered (named fields of `Res`): `b = 0` (`MP_VAL`), `c` or `d` NULL (`mp_mod` passes
`c = NULL`, `mp_reduce_setup` tail-calls `mp_div(a, b, a, NULL)`), aliasing between the four
operands (D6; the layout's soundness keeps the written regions apart from all others).
-/

namespace Tom.Machine.Api.MpDiv

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x80000898#64

inductive R | stk | aS | aD | bS | bD | cS | cD | dS | dD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .cS, .cD, .dS, .dD, .code] := by
  cases r <;> simp

/-- The stack depth: the 272-byte frame and `mp_init_copy`'s (the deepest callee). -/
abbrev F : Nat := 272 + MpInitCopy.F

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  pc : Nat
  cdp : Nat
  pd : Nat
  ddp : Nat
  a : MpInt
  b : MpInt
  c : MpInt
  d : MpInt
  H : List (Nat × Nat)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .cS => ⟨p.pc, 24⟩
  | .cD => ⟨p.cdp, 4 * p.c.alloc⟩
  | .dS => ⟨p.pd, 24⟩
  | .dD => ⟨p.ddp, 4 * p.d.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .bS => .mpS p.pb p.bdp p.b
  | .bD => .mpD p.bdp p.b.alloc p.b.digit
  | .cS => .mpS p.pc p.cdp p.c
  | .cD => .mpD p.cdp p.c.alloc p.c.digit
  | .dS => .mpS p.pd p.ddp p.d
  | .dD => .mpD p.ddp p.d.alloc p.d.digit
  | .code => .code

/-- What `mp_div` returns: `MP_MEM`, the copy/zero case in place, or the long division with
`c'` at `q`'s block `qc` and `d'` at `x`'s block `qd`. -/
inductive Out
  | mem
  | small (c' d' : MpInt)
  | big (qc : Nat) (c' : MpInt) (qd : Nat) (d' : MpInt)

def out (p : P) : Out → R → Kind
  | .small c' _, .cS => .mpS p.pc p.cdp c'
  | .small c' _, .cD => .mpD p.cdp p.c.alloc c'.digit
  | .small _ d', .dS => .mpS p.pd p.ddp d'
  | .small _ d', .dD => .mpD p.ddp p.d.alloc d'.digit
  | .big qc c' _ _, .cS => .mpS p.pc qc c'
  | .big qc c' _ _, .cD => .mpD qc c'.alloc c'.digit
  | .big _ _ qd d', .dS => .mpS p.pd qd d'
  | .big _ _ qd d', .dD => .mpD qd d'.alloc d'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .cS | .cD | .dS | .dD => true
  | _ => false

def ws : List R := [.stk, .cS, .cD, .dS, .dD]

/-- Where `c`'s digits are after. -/
def siteC (p : P) : Out → Iv
  | .big qc c' _ _ => ⟨qc, 4 * c'.alloc⟩
  | _ => lay p .cD

/-- Where `d`'s digits are after. -/
def siteD (p : P) : Out → Iv
  | .big _ _ qd d' => ⟨qd, 4 * d'.alloc⟩
  | _ => lay p .dD

/-- `c`'s and `d`'s digits are the front live blocks. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.cdp p.c :: digBlk p.ddp p.d :: p.H

/-- After the long division: the old blocks freed, `q`'s and `x`'s (now `c`'s, `d`'s) live. -/
def hout (p : P) : Out → List (Nat × Nat)
  | .big qc c' qd d' => (qc, 4 * c'.alloc) :: (qd, 4 * d'.alloc) :: p.H
  | _ => hin p

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = c`, `a3 = d` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
   (12, BitVec.ofNat 64 p.pc), (13, BitVec.ofNat 64 p.pd)]

def rets (_ : P) (x : Out) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | .mem => MpInit.memBV | _ => 0#64)]

/-- What `mp_div(a, b, c, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_cmp_mag`, `mp_init_copy` and the long division read `a`, `b` as valid integers. -/
  va : p.a.Valid
  vb : p.b.Valid
  /-- `b ≠ 0`: the `MP_VAL` return (`8a8`) is not covered. -/
  bnz : 0 < p.b.used
  /-- `mp_count_bits(&y)` is an `int` (`Std.cntBits`). -/
  bits : Layout.digitBits * p.b.used < 2 ^ 31
  /-- `mp_init_size(&q, a->used + 2)` and every `int` index of the loops (`i ≤ a->used`,
  `x.used ≤ a->used + 1`, byte offsets `4 i`) fit. -/
  au : p.a.used + 3 < 2 ^ 30
  /-- D5 for the small case: `mp_copy(a, d)` does not call `mp_grow`. -/
  droom : p.a.used ≤ p.d.alloc
  /-- `c`'s old digits are freed by `mp_clear(&q)` after the exchange: a live, nonempty block. -/
  cpos : 0 < p.c.alloc
  /-- `d`'s old digits are freed by `mp_clear(&x)` after the exchange: a live, nonempty block. -/
  dpos : 0 < p.d.alloc
  /-- `c != NULL`: the branches at `974` and `b64` are taken the non-NULL way. -/
  cnn : p.pc ≠ 0
  /-- `d != NULL`: the branches at `960` and `b90` are taken the non-NULL way. -/
  dnn : p.pd ≠ 0
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24
  doff : OffHeap p.pd 24
  /-- `mp_zero(c)` in the small case (`Std.mpZero`: the `memset` over `c->alloc` digits). -/
  csh : p.c.Shape
  /-- `mp_copy(a, d)` in the small case zeroes `d`'s digits only up to the old `d->used`: the
  ones above must be zero already for `d' = a` (`DivRem.small`; refutable without). -/
  dsh : p.d.Shape
  /-- `mp_init_copy(&x, a)` copies from a live block (`MpInitCopy.Pre.live`), nonempty. -/
  ablk : digBlk p.adp p.a ∈ p.H
  apos : 0 < p.a.alloc
  /-- `mp_init_copy(&y, b)` copies from a live block. -/
  bblk : digBlk p.bdp p.b ∈ p.H

/-- What `c` and `d` hold, with the case the code took. -/
def Q (p : P) : Out → Prop
  | .mem => p.b.mag ≤ p.a.mag
  | .small c' d' => p.a.mag < p.b.mag ∧ DivQuot p.a p.b p.c c' ∧ DivRem p.a p.b p.d d'
  | .big _ c' _ d' => p.b.mag ≤ p.a.mag ∧ DivQuot p.a p.b p.c c' ∧ DivRem p.a p.b p.d d'

/-- What an allocating function with two re-placed sites `sc`, `sd` leaves (`HPost` with a
second site): the written regions but the sites witnessed in place, each site at its new
placement, the two placements apart, the frame from the entry, the heap after, and the
allocator's footprint grown only by the sites' old blocks. -/
structure Post2 {R : Type} (lay : R → Iv) (ws : List R) (sc sd : R) (out : R → Kind) (Jc Jd : Iv)
    (hin hout : List (Nat × Nat)) (m M : Mem) : Prop where
  wit : ∀ r, r ∈ ws → r ≠ sc → r ≠ sd → (out r).Fits (lay r) ∧ (out r).Wit (lay r) M
  wsc : (out sc).Fits Jc ∧ (out sc).Wit Jc M
  wsd : (out sd).Fits Jd ∧ (out sd).Wit Jd M
  placec : Place hin (lay sc) Jc
  placed : Place hin (lay sd) Jd
  sep : Jc.Disj Jd
  frame : HFrm lay ws hin m M
  heap : AHeap M hout
  foot : ∀ a, Foot hout a → Foot hin a ∨ (lay sc).In a ∨ (lay sd).In a
  offc : Off Jc hout
  offd : Off Jd hout

/-- **`mp_div(a, b, c, d)` on the machine**, `c`, `d` non-NULL, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        Post2 (lay p) ws .cD .dD (out p x) (siteC p x) (siteD p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpDiv
