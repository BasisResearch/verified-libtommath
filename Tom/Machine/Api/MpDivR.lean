import Tom.Machine.Api.MpDiv

/-!
# `mp_div(a, b, NULL, d)`: the remainder only

`mp_mod`'s call (`li a2, 0` at `800016d8`). The code is `Api/MpDiv.lean`'s with the branches on
`c` taken the `NULL` way (`974`, `b64`): the small case is `mp_copy(a, d)` alone; the long
division keeps `q` (no `mp_clamp`/`mp_exch`/sign store) and `mp_clear(&q)` frees `q`'s own block.
So one site is re-placed, `d`'s digits (`HPost`, `Kit/MeetHeap.lean`): in the big case `d'`
lives in `x`'s block `qd`, `d`'s old block freed.

* `ok q d'`: `DivRem a b d d'` (`d' = a.tmod b`, `div_spec`): `|a| < |b|` with `q = d->dp` (the copy
  in place, `DivRem.small`), or the long division with `q` `x`'s block (`DivRem.big`);
* `mem`: an allocation failed, `d` and the heap as before.

`droom` is needed only in the small case: `mp_mod`'s `d` is `t` of `mp_init_size(&t, b->used)`,
shorter than `a` in general.
-/

namespace Tom.Machine.Api.MpDivR

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x80000898#64

inductive R | stk | aS | aD | bS | bD | dS | dD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .dS, .dD, .code] := by cases r <;> simp

/-- The stack depth (`Api.MpDiv.F`). -/
abbrev F : Nat := 272 + MpInitCopy.F

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  pd : Nat
  ddp : Nat
  a : MpInt
  b : MpInt
  d : MpInt
  H : List (Nat × Nat)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .dS => ⟨p.pd, 24⟩
  | .dD => ⟨p.ddp, 4 * p.d.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .bS => .mpS p.pb p.bdp p.b
  | .bD => .mpD p.bdp p.b.alloc p.b.digit
  | .dS => .mpS p.pd p.ddp p.d
  | .dD => .mpD p.ddp p.d.alloc p.d.digit
  | .code => .code

/-- `MP_MEM`, the copy in place, or the remainder at `x`'s block `qd`. -/
inductive Out
  | mem
  | ok (q : Nat) (d' : MpInt)

def out (p : P) : Out → R → Kind
  | .ok q d', .dS => .mpS p.pd q d'
  | .ok q d', .dD => .mpD q d'.alloc d'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .dS | .dD => true
  | _ => false

def ws : List R := [.stk, .dS, .dD]

def site' (p : P) : Out → Iv
  | .ok q d' => ⟨q, 4 * d'.alloc⟩
  | .mem => lay p .dD

/-- `d`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.ddp p.d :: p.H

def hout (p : P) : Out → List (Nat × Nat)
  | .ok q d' => (q, 4 * d'.alloc) :: p.H
  | .mem => hin p

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = NULL`, `a3 = d`. -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
   (12, BitVec.ofNat 64 0), (13, BitVec.ofNat 64 p.pd)]

def rets (_ : P) (x : Out) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | .mem => MpInit.memBV | _ => 0#64)]

/-- What `mp_div(a, b, NULL, d)` needs (`Api.MpDiv.Res` without `c`'s fields). -/
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
  /-- D5 for the small case only: `mp_copy(a, d)` does not call `mp_grow`. -/
  droom : p.a.mag < p.b.mag → p.a.used ≤ p.d.alloc
  /-- `d`'s old digits are freed by `mp_clear(&x)` after the exchange: a live, nonempty block. -/
  dpos : 0 < p.d.alloc
  /-- `d != NULL`: the branches at `960` and `b90` are taken the non-NULL way. -/
  dnn : p.pd ≠ 0
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  doff : OffHeap p.pd 24
  /-- `mp_copy(a, d)` zeroes `d`'s digits only up to the old `d->used`. -/
  dsh : p.d.Shape
  /-- `mp_init_copy(&x, a)`, `mp_init_copy(&y, b)` copy from live blocks. -/
  ablk : digBlk p.adp p.a ∈ p.H
  apos : 0 < p.a.alloc
  bblk : digBlk p.bdp p.b ∈ p.H

/-- What `d` holds, -/
def Q (p : P) : Out → Prop
  | .mem => p.b.mag ≤ p.a.mag
  | .ok _ d' => DivRem p.a p.b p.d d' ∧ 0 < d'.alloc

/-- **`mp_div(a, b, NULL, d)` on the machine**, as an allocating contract (site: `d`'s digits). -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .dD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpDivR
