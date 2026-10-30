import Tom.Machine.Api.MpDivR
import Tom.Machine.Api.MpAddG

/-!
# `mp_mod(a, b, c)`: the allocating contract

`vendor/libtommath/bn_mp_mod.c` at `0x80001680` (frame 80, `t` at `sp + 24`, `err` spilled at
`sp + 8`): `mp_init_size(&t, b->used)`, `mp_div(a, b, NULL, &t)` (`Api/MpDivR.lean`), then
`MP_IS_ZERO(&t) || t.sign == b->sign` (`16ec`–`16fc`): `mp_exch(&t, c)`, else
`mp_add(b, &t, c)` (`Api/MpAddG.lean`, growing `c`); `mp_clear(&t)`. One site is re-placed, `c`'s
digits (`HPost`):

* `ok q c'`: `MP_OKAY`, `c'` at `q` with `ModPost a b c'` (`ModPost.spec`: `c' = a.fmod b`); `q` is
  `t`'s block (exchange; `c`'s old block freed by `mp_clear(&t)`) or the block `mp_add` left;
* `mem c'`: an allocation failed (`mp_init_size`, `mp_div`'s temporaries, `mp_add`'s `mp_grow`);
  `c`'s digits and the heap as before, `c'` its header: only its sign may differ (`mp_add`'s
  `MP_MEM` path stores `c->sign` first).

Memory changes only in the stack `[sp - 976, sp)` (the 80-byte frame and `mp_div`'s 896), `c` and
the allocator's footprint. `a`, `b`, `c` are distinct (D6).
-/

namespace Tom.Machine.Api.MpMod

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x80001680#64

/-- The stack depth: the 80-byte frame and `mp_div`'s (the deepest callee). -/
abbrev F : Nat := 80 + MpDivR.F

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  pc : Nat
  cdp : Nat
  a : MpInt
  b : MpInt
  c : MpInt
  H : List (Nat × Nat)

inductive R | stk | aS | aD | bS | bD | cS | cD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .cS, .cD, .code] := by cases r <;> simp

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .cS => ⟨p.pc, 24⟩
  | .cD => ⟨p.cdp, 4 * p.c.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .bS => .mpS p.pb p.bdp p.b
  | .bD => .mpD p.bdp p.b.alloc p.b.digit
  | .cS => .mpS p.pc p.cdp p.c
  | .cD => .mpD p.cdp p.c.alloc p.c.digit
  | .code => .code

/-- `MP_MEM` (`c`'s header after), or `MP_OKAY` with `c'`'s digits at `q`. -/
inductive Out
  | mem (c' : MpInt)
  | ok (q : Nat) (c' : MpInt)

def out (p : P) : Out → R → Kind
  | .mem c', .cS => .mpS p.pc p.cdp c'
  | .ok q c', .cS => .mpS p.pc q c'
  | .ok q c', .cD => .mpD q c'.alloc c'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .cS | .cD => true
  | _ => false

def ws : List R := [.stk, .cS, .cD]

def site' (p : P) : Out → Iv
  | .ok q c' => ⟨q, 4 * c'.alloc⟩
  | .mem _ => lay p .cD

/-- `c`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.cdp p.c :: p.H

def hout (p : P) : Out → List (Nat × Nat)
  | .ok q c' => (q, 4 * c'.alloc) :: p.H
  | .mem _ => hin p

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = c`. -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
   (12, BitVec.ofNat 64 p.pc)]

def rets (_ : P) (x : Out) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | .mem _ => MpInit.memBV | .ok _ _ => 0#64)]

/-- What `mp_mod(a, b, c)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_div` reads `a`, `b` as valid integers. -/
  va : p.a.Valid
  vb : p.b.Valid
  /-- `b ≠ 0`: `mp_div`'s `MP_VAL` is not covered. -/
  bnz : 0 < p.b.used
  /-- `mp_div`'s `mp_count_bits(&y)` is an `int`. -/
  bits : Layout.digitBits * p.b.used < 2 ^ 31
  /-- `mp_div`'s `mp_init_size(&q, a->used + 2)` and its loops' indices fit. -/
  au : p.a.used + 3 < 2 ^ 30
  /-- `mp_add(b, &t, c)`: `c`'s old digits above the sum are zeroed only up to its old `used`. -/
  sc : p.c.Shape
  /-- `mp_add`'s `mp_grow` size (`t->used ≤ b->used`). -/
  bsize : p.b.used + 1 < 2 ^ 31
  /-- `c`'s digits: the block `mp_clear(&t)` frees after the exchange, `mp_add`'s `realloc`'s. -/
  cpos : 0 < p.c.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24
  /-- `mp_div`'s `mp_init_copy(&x, a)`, `mp_init_copy(&y, b)` copy from live nonempty blocks. -/
  ablk : digBlk p.adp p.a ∈ p.H
  apos : 0 < p.a.alloc
  bblk : digBlk p.bdp p.b ∈ p.H

/-- What `c` holds. -/
def Q (p : P) : Out → Prop
  | .mem c' => c' = { p.c with sign := c'.sign }
  | .ok _ c' => ModPost p.a p.b c'

/-- **`mp_mod(a, b, c)` on the machine**, as an allocating contract (site: `c`'s digits). -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpMod
