import Tom.Machine.Api.StdHeapFn
import Tom.Machine.Api.MpMulAF
import Tom.Machine.Fn.MpReduce2kLG
import Tom.Spec.MpReduce2kLStep
import Tom.Spec.Init

/-!
# `mp_reduce_2k_l(a, n, d)`: the allocating contract

(`Api/Reduce2kL.lean` is `mp_reduce_is_2k_l`.) `bn_mp_reduce_2k_l.c` at `0x80005f70` (frame 96, `q` at
`sp + 8`): `mp_init(&q)` (`MP_PREC = 32` digits), `p = mp_count_bits(n)`, then `top: mp_div_2d(a, p,
&q, a)`, `mp_mul(&q, d, &q)`, `s_mp_add(a, &q, a)`, and while `mp_cmp_mag(a, n) ≠ MP_LT`:
`s_mp_sub(a, n, a)`, `goto top`; finally `mp_clear(&q)`. On success `a` holds `Reduce2kPost a n |d| a'`
(`MpReduce2kLStep`: for `n = 2^p - |d|`, `|a'| = |a| mod |n|`) with `a->alloc` and `a->dp` kept. On
`MP_MEM` from `mp_init` nothing is changed; from `mp_mul` (a later pass) `a` holds a shaped value
congruent to nothing in particular (`err` is returned, `a`'s block kept).

Assumptions beyond `Valid`/D6 (named fields of `Res`):
* `n = 2^p - |d|` (`hd`), `n ≠ 0`: the fold `|a| mod 2^p + |d| (|a| / 2^p)` does not grow `a` and each
  subtraction makes it smaller, so the loop terminates.
* No `mp_grow` (D5): every value of `a` is at most `|a|`, so `a->used + 1 ≤ a->alloc` covers
  `s_mp_add(a, &q, a)`; `q`'s 32 digits cover `mp_copy(a, &q)` in `mp_div_2d` when `a->used ≤ MP_PREC`
  (`qroom`), and `mp_mul(&q, d, &q)` keeps or grows `q`'s block on the comba path (`MpMulAF`), which
  `qroom` and `dsmall` select (`q->used < 80`, `q->used + d->used + 1 < MP_WARRAY`; proved:
  `Fn.MpMulAFClosed.correct`).
* `28 n->used < 2^31` (`mp_count_bits`'s `int`).
Memory changes only in the stack `[sp - 6952, sp)` (the 96-byte frame and `mp_mul`'s
`2768 + 8 (q->used + d->used)` below it), `a` and the allocator's footprint.
-/

namespace Tom.Machine.Api.MpReduce2kL

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Reduce Tom.Mont

def entry : BitVec 64 := 0x80005f70#64

inductive R | stk | aS | aD | nS | nD | dS | dD | kc | tc | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .nS, .nD, .dS, .dD, .kc, .tc, .code] := by cases r <;> simp

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pn : Nat
  ndp : Nat
  pd : Nat
  ddp : Nat
  a : MpInt
  n : MpInt
  d : MpInt
  H : List (Nat × Nat)

/-- The stack depth: the 96-byte frame and `mp_mul`'s `2768 + 8 (q->used + d->used)` at
`q->used + d->used < MP_WARRAY` (`dsmall`): `96 + 2768 + 8 · 511`. -/
def F : Nat := 6952

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .nS => ⟨p.pn, 24⟩
  | .nD => ⟨p.ndp, 4 * p.n.alloc⟩
  | .dS => ⟨p.pd, 24⟩
  | .dD => ⟨p.ddp, 4 * p.d.alloc⟩
  | .kc => ⟨MpMul.kcAddr, 4⟩
  | .tc => ⟨MpMul.tcAddr, 4⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .nS => .mpS p.pn p.ndp p.n
  | .nD => .mpD p.ndp p.n.alloc p.n.digit
  | .dS => .mpS p.pd p.ddp p.d
  | .dD => .mpD p.ddp p.d.alloc p.d.digit
  | .kc => .mpD MpMul.kcAddr 1 MpMul.kcV
  | .tc => .mpD MpMul.tcAddr 1 MpMul.tcV
  | .code => .code

/-- After: `(ok, a')`, `a` in place. -/
abbrev X : Type := Bool × MpInt

def out (p : P) : X → R → Kind
  | (_, a'), .aS => .mpS p.pa p.adp a'
  | (_, a'), .aD => .mpD p.adp p.a.alloc a'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .aS | .aD => true
  | _ => false

def ws : List R := [.stk, .aS, .aD]

/-- `a`'s digits stay where they are. -/
def site' (p : P) (_ : X) : Iv := lay p .aD

def hin (p : P) : List (Nat × Nat) := p.H

def hout (p : P) (_ : X) : List (Nat × Nat) := p.H

/-- The arguments: `a0 = a`, `a1 = n`, `a2 = d` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pn),
   (12, BitVec.ofNat 64 p.pd)]

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpInit.memBV)]

/-- What `mp_reduce_2k_l(a, n, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  vn : p.n.Valid
  vd : p.d.Valid
  /-- `n ≠ 0`: `p > 0` and a loop that ends. -/
  npos : 0 < p.n.mag
  /-- `n = 2^p - |d|`, `p = mp_count_bits(n)` (`mp_reduce_2k_setup_l`). -/
  hd : p.n.mag + p.d.mag = 2 ^ nbits p.n.mag
  /-- `mp_count_bits(n)`'s `int` result. -/
  bits : Layout.digitBits * p.n.used < 2 ^ 31
  /-- D5 for `a`: `s_mp_add(a, &q, a)` has room on every pass. -/
  aroom : p.a.used + 1 ≤ p.a.alloc
  /-- D5 for `q` (`mp_init`'s `MP_PREC = 32` digits): `mp_copy(a, &q)` in `mp_div_2d`. -/
  qroom : p.a.used ≤ defPrec
  /-- `mp_mul(&q, d, &q)` on the comba path (`MpMulAF.Small`). -/
  dsmall : defPrec + p.d.used + 1 < 512
  dpos : 0 < p.d.alloc
  aoff : OffHeap p.pa 24
  noff : OffHeap p.pn 24
  doff : OffHeap p.pd 24

/-- What `a` holds after. -/
structure Red (p : P) (a' : MpInt) : Prop where
  red : Reduce2kPost p.a p.n p.d.mag a'
  /-- Not reallocated (D5). -/
  alloc : a'.alloc = p.a.alloc

def Q (p : P) : X → Prop
  | (true, a') => Red p a'
  | (false, a') => a'.Shape ∧ a'.alloc = p.a.alloc

/-- **`mp_reduce_2k_l(a, n, d)` on the machine**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpReduce2kL
