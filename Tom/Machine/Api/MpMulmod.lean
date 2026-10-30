import Tom.Machine.Api.MpMod
import Tom.Machine.Api.MpMul
import Tom.Spec.Reduce

/-!
# `mp_mulmod(a, b, c, d)`: the allocating contract

`vendor/libtommath/bn_mp_mulmod.c` at `0x80005d90` (frame 96, `t` at `sp + 24`, `err` spilled at
`sp + 8`): `mp_init_size(&t, c->used)`, `mp_mul(a, b, &t)` (`Api/MpMul.lean`), on `MP_OKAY`
`mp_mod(&t, c, d)` (`Api/MpMod.lean`), `mp_clear(&t)`. One site is re-placed, `d`'s digits:

* `ok q d'`: `MP_OKAY`, `d'` at `q` with `MulmodPost a b c d'` (`d' = a b mod c`, `c > 0`);
* `mem d'`: an allocation failed; `d`'s digits and the heap as before, only `d`'s sign may differ.

`mp_mul` is proved conditionally (`Api/MulRec.lean`, `Fn/MulGroupK.lean`): its contract is the
named premise `mul`. The stack depth is `mp_mul`'s at `a->used + b->used` below the 96-byte frame
(`mp_mod`'s 976 is less). `a`, `b`, `c`, `d` are distinct (D6).
-/

namespace Tom.Machine.Api.MpMulmod

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x80005d90#64

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

/-- The stack depth: the 96-byte frame and `mp_mul`'s `MpMul.Fm (a->used + b->used)` (the
annotation's `F`; the contract states it as the sum itself). -/
def F {p : P} : Nat := 2864 + 8 * (p.a.used + p.b.used)

inductive R | stk | aS | aD | bS | bD | cS | cD | dS | dD | kc | tc | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .cS, .cD, .dS, .dD, .kc, .tc, .code] := by
  cases r <;> simp

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - (2864 + 8 * (p.a.used + p.b.used)), 2864 + 8 * (p.a.used + p.b.used)⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .cS => ⟨p.pc, 24⟩
  | .cD => ⟨p.cdp, 4 * p.c.alloc⟩
  | .dS => ⟨p.pd, 24⟩
  | .dD => ⟨p.ddp, 4 * p.d.alloc⟩
  | .kc => ⟨MpMul.kcAddr, 4⟩
  | .tc => ⟨MpMul.tcAddr, 4⟩
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
  | .kc => .mpD MpMul.kcAddr 1 MpMul.kcV
  | .tc => .mpD MpMul.tcAddr 1 MpMul.tcV
  | .code => .code

/-- `MP_MEM` (`d`'s header after), or `MP_OKAY` with `d'`'s digits at `q`. -/
inductive Out
  | mem (d' : MpInt)
  | ok (q : Nat) (d' : MpInt)

def out (p : P) : Out → R → Kind
  | .mem d', .dS => .mpS p.pd p.ddp d'
  | .ok q d', .dS => .mpS p.pd q d'
  | .ok q d', .dD => .mpD q d'.alloc d'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .dS | .dD => true
  | _ => false

def ws : List R := [.stk, .dS, .dD]

def site' (p : P) : Out → Iv
  | .ok q d' => ⟨q, 4 * d'.alloc⟩
  | .mem _ => lay p .dD

/-- `d`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.ddp p.d :: p.H

def hout (p : P) : Out → List (Nat × Nat)
  | .ok q d' => (q, 4 * d'.alloc) :: p.H
  | .mem _ => hin p

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = c`, `a3 = d`. -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
   (12, BitVec.ofNat 64 p.pc), (13, BitVec.ofNat 64 p.pd)]

def rets (_ : P) (x : Out) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | .mem _ => MpInit.memBV | .ok _ _ => 0#64)]

/-- What `mp_mulmod(a, b, c, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp (2864 + 8 * (p.a.used + p.b.used))
  /-- `mp_mul`'s contract (proved conditionally on the mp_mul group's gaps). -/
  mul : MpMul.Statement
  /-- `mp_mul` reads valid operands. -/
  va : p.a.Valid
  vb : p.b.Valid
  /-- `mp_mul`'s `int` sums; `mp_mod`'s `mp_div` needs `t->used + 3 < 2^30` (`t->used ≤ a->used + b->used`). -/
  uab : p.a.used + p.b.used + 3 < 2 ^ 30
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- The modulus: valid, positive (`MulmodPost` is stated for `c > 0`; `mp_div`'s `b ≠ 0`). -/
  vc : p.c.Valid
  c0 : 0 < p.c.used
  cz : p.c.sign = Layout.mpZpos
  /-- `mp_mod`'s `mp_div` (`mp_count_bits` an `int`) and `mp_add` (`c->used + 1`). -/
  cbits : Layout.digitBits * p.c.used < 2 ^ 31
  /-- `mp_mod(&t, c, d)` writes `d`: shaped, a live nonempty block. -/
  sd : p.d.Shape
  dpos : 0 < p.d.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24
  doff : OffHeap p.pd 24
  /-- `mp_mod`'s `mp_div` copies `c` (`mp_init_copy(&y, c)`) from a live block. -/
  cblk : digBlk p.cdp p.c ∈ p.H

/-- What `d` holds. -/
def Q (p : P) : Out → Prop
  | .mem d' => d' = { p.d with sign := d'.sign }
  | .ok _ d' => Reduce.MulmodPost p.a p.b p.c d'

/-- **`mp_mulmod(a, b, c, d)` on the machine**, as an allocating contract (site: `d`'s digits). -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .dD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpMulmod
