import Tom.Machine.Api.MpDiv

/-!
# `mp_div(a, b, a, NULL)`: the quotient in place of the dividend

`mp_reduce_setup`'s tail call (`mv a2, a0; li a3, 0` at `80006400`). The code is
`Api/MpDiv.lean`'s with `c = a` and the branches on `d` taken the `NULL` way (`960`, `b90`): the
small case is `mp_zero(a)` alone (`err = MP_OKAY`); the long division skips `mp_div_2d`/`mp_exch`
on `x` (`mp_clear(&x)` frees `x`'s own block), and `mp_exch(&q, a)` puts `a`'s old digits in `q`,
freed by `mp_clear(&q)`. The C reads `a` only before it writes it (`a->used`, the copy `x`, the
signs). So one site is re-placed, `a`'s digits (`HPost`): in the big case `a'` lives in `q`'s
block `qa`.

* `ok q a'`: `DivQuot a b a a'` (`a' = a.tdiv b`, `div_spec`): `|a| < |b|` with `q = a->dp` (`a' = 0`
  in place, `DivQuot.small`), or the long division with `q` `q`'s block (`DivQuot.big`);
* `mem`: an allocation failed, `a` and the heap as before.
-/

namespace Tom.Machine.Api.MpDivQ

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x80000898#64

inductive R | stk | aS | aD | bS | bD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .code] := by cases r <;> simp

/-- The stack depth (`Api.MpDiv.F`). -/
abbrev F : Nat := 272 + MpInitCopy.F

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt
  H : List (Nat × Nat)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .bS => .mpS p.pb p.bdp p.b
  | .bD => .mpD p.bdp p.b.alloc p.b.digit
  | .code => .code

/-- `MP_MEM`, the zero in place, or the quotient at `q`'s block `qa`. -/
inductive Out
  | mem
  | ok (q : Nat) (a' : MpInt)

def out (p : P) : Out → R → Kind
  | .ok q a', .aS => .mpS p.pa q a'
  | .ok q a', .aD => .mpD q a'.alloc a'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .aS | .aD => true
  | _ => false

def ws : List R := [.stk, .aS, .aD]

def site' (p : P) : Out → Iv
  | .ok q a' => ⟨q, 4 * a'.alloc⟩
  | .mem => lay p .aD

/-- `a`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.adp p.a :: p.H

def hout (p : P) : Out → List (Nat × Nat)
  | .ok q a' => (q, 4 * a'.alloc) :: p.H
  | .mem => hin p

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = a`, `a3 = NULL`. -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
   (12, BitVec.ofNat 64 p.pa), (13, BitVec.ofNat 64 0)]

def rets (_ : P) (x : Out) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | .mem => MpInit.memBV | _ => 0#64)]

/-- What `mp_div(a, b, a, NULL)` needs (`Api.MpDiv.Res` with `c = a`, without `d`'s fields). -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_cmp_mag`, `mp_init_copy` and the long division read `a`, `b` as valid integers. -/
  va : p.a.Valid
  vb : p.b.Valid
  /-- `b ≠ 0`: the `MP_VAL` return is not covered. -/
  bnz : 0 < p.b.used
  /-- `mp_count_bits(&y)` is an `int`. -/
  bits : Layout.digitBits * p.b.used < 2 ^ 31
  /-- `mp_init_size(&q, a->used + 2)` and the loops' `int` indices fit. -/
  au : p.a.used + 3 < 2 ^ 30
  /-- `a`'s old digits are freed by `mp_clear(&q)` after the exchange: a nonempty block (live: the
  front of `hin`). -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  /-- `mp_init_copy(&y, b)` copies from a live block. -/
  bblk : digBlk p.bdp p.b ∈ p.H

/-- What `a` holds, -/
def Q (p : P) : Out → Prop
  | .mem => p.b.mag ≤ p.a.mag
  | .ok _ a' => DivQuot p.a p.b p.a a' ∧ 0 < a'.alloc

/-- **`mp_div(a, b, a, NULL)` on the machine**, as an allocating contract (site: `a`'s digits). -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpDivQ
