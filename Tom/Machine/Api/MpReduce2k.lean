import Tom.Machine.Api.StdHeapFn
import Tom.Machine.Fn.Reduce2kG
import Tom.Spec.Reduce
import Tom.Spec.Init

/-!
# `mp_reduce_2k(a, n, d)`: the allocating contract (fresh set; over `Kit/MeetHeap.lean`)

(`Api/Reduce2k.lean` is `mp_reduce_is_2k`.) `mp_init(&q)` (struct in the frame
at `sp - 88`, `MP_PREC = 32` digits), `p = mp_count_bits(n)`, then
`top: mp_div_2d(a, p, &q, a)` (`q = |a| / 2^p`, `a = |a| mod 2^p`),
`mp_mul_d(&q, d, &q)` unless `d = 1`, `s_mp_add(a, &q, a)`, and while
`mp_cmp_mag(a, n) ≠ MP_LT`: `s_mp_sub(a, n, a)`, `goto top`; finally
`mp_clear(&q)`. On success `a` holds `Reduce2kPost a n d a'` (`.spec`: for
`n = 2^p - d`, `|a'| = |a| mod |n|`, valid) with `a->alloc` and `a->dp` kept.
On `MP_MEM` from `mp_init` nothing is changed. The heap's blocks are the same
after (`q`'s block is allocated and freed; `a` is not reallocated): the site is
`a`'s digit array, kept in place (`Place.keep`).

Assumptions beyond `Valid`/D6 (named fields of `Res`):
* `n = 2^p - d` (`hd`), `n ≠ 0`: the fold `|a| mod 2^p + d (|a| / 2^p)` does not
  grow `a` and each subtraction makes it smaller, so the loop terminates (for
  other `d` the C loop can run forever); `d` an `mp_digit` (`d < radix`, `mp_mul_d`).
* No `mp_grow` anywhere (D5): every value of `a` in the loop is at most `|a|`, so
  `a->used + 1 ≤ a->alloc` covers `s_mp_add(a, &q, a)`; `q`'s 32 digits cover
  `mp_copy(a, &q)` in `mp_div_2d` and `mp_mul_d(&q, d, &q)` when
  `a->used + 1 ≤ MP_PREC` (`qroom`; no `HContract` for a growing `mp_copy` or
  `mp_mul_d` exists).
* `28 n->used < 2^31` (`mp_count_bits`'s `int`, as `Api/Reduce2k.lean`).

Memory changes only in the stack `[sp - 656, sp)` (the 96-byte frame and
`mp_init`'s 560; `mp_clear` 544, the others less), `a` and the allocator's
footprint.
-/

namespace Tom.Machine.Api.MpReduce2k

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Reduce Tom.Mont

def entry : BitVec 64 := 0x80005e48#64

inductive R | stk | aS | aD | nS | nD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .nS, .nD, .code] := by cases r <;> simp

/-- The stack depth: the 96-byte frame and `mp_init`'s. -/
abbrev F : Nat := 96 + MpInit.Finit

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pn : Nat
  ndp : Nat
  d : Nat
  a : MpInt
  n : MpInt
  H : List (Nat × Nat)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .nS => ⟨p.pn, 24⟩
  | .nD => ⟨p.ndp, 4 * p.n.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .nS => .mpS p.pn p.ndp p.n
  | .nD => .mpD p.ndp p.n.alloc p.n.digit
  | .code => .code

/-- After: `none` on `MP_MEM`, `some a'` in place. -/
def out (p : P) : Option MpInt → R → Kind
  | none, r => kind p r
  | some a', .aS => .mpS p.pa p.adp a'
  | some a', .aD => .mpD p.adp p.a.alloc a'.digit
  | some _, r => kind p r

def isW : R → Bool
  | .stk | .aS | .aD => true
  | _ => false

def ws : List R := [.stk, .aS, .aD]

/-- `a`'s digits stay where they are. -/
def site' (p : P) (_ : Option MpInt) : Iv := lay p .aD

/-- The heap's blocks (`a`'s and `n`'s digits among them or off the arena). -/
def hin (p : P) : List (Nat × Nat) := p.H

def hout (p : P) (_ : Option MpInt) : List (Nat × Nat) := p.H

/-- The arguments: `a0 = a`, `a1 = n`, `a2 = d` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pn),
   (12, BitVec.ofNat 64 p.d)]

def rets (_ : P) (x : Option MpInt) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpInit.memBV | some _ => 0#64)]

/-- What `mp_reduce_2k(a, n, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_div_2d`'s `a` (`Api.MpDiv2d`), `s_mp_add`'s and `s_mp_sub`'s operand. -/
  va : p.a.Valid
  vn : p.n.Valid
  /-- `n ≠ 0`: `p > 0` (`mp_div_2d`'s shifting path) and a loop that ends. -/
  npos : 0 < p.n.mag
  /-- `d` an `mp_digit` (`mp_mul_d(&q, d, &q)`). -/
  d_lt : p.d < radix
  /-- `n = 2^p - d`, `p = mp_count_bits(n)` (`mp_reduce_2k_setup` for an `mp_reduce_is_2k`
  modulus): the fold keeps the residue and does not grow `a`, so the loop terminates. -/
  hd : p.n.mag + p.d = 2 ^ nbits p.n.mag
  /-- `mp_count_bits(n)`'s `int` result (`Std.cntBits`). -/
  bits : Layout.digitBits * p.n.used < 2 ^ 31
  /-- D5 for `a`: `s_mp_add(a, &q, a)` has room (`max(used) + 1 ≤ alloc`) on every pass. -/
  aroom : p.a.used + 1 ≤ p.a.alloc
  /-- D5 for `q` (`mp_init`'s `MP_PREC = 32` digits): `mp_copy(a, &q)` in `mp_div_2d` and
  `mp_mul_d(&q, d, &q)` do not call `mp_grow`. -/
  qroom : p.a.used + 1 ≤ defPrec
  aoff : OffHeap p.pa 24
  noff : OffHeap p.pn 24

/-- What `a` holds after. -/
structure Red (p : P) (a' : MpInt) : Prop where
  red : Reduce2kPost p.a p.n p.d a'
  /-- Not reallocated (D5). -/
  alloc : a'.alloc = p.a.alloc

def Q (p : P) : Option MpInt → Prop
  | none => True
  | some a' => Red p a'

/-- **`mp_reduce_2k(a, n, d)` on the machine**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpReduce2k
