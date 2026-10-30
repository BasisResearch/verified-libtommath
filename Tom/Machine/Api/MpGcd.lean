import Tom.Machine.Api.StdHeapFn
import Tom.Spec.Gcd
import Tom.Spec.Init

/-!
# `mp_gcd(a, b, c)`: the allocating contract (over `Kit/MeetHeap.lean`)

`vendor/libtommath/bn_mp_gcd.c`, compiled at `0x8000105c` (133 instructions):
`a = 0` or `b = 0` tail-calls `mp_abs` (`j mp_abs`); otherwise the temporaries
`u = a`, `v = b` (`mp_init_copy`, structs in the 96-byte frame at `sp - 80`,
`sp - 56`) are made nonnegative, the common power of two `k = min(lsb u, lsb v)`
(`mp_cnt_lsb`) and the remaining twos divided out (`mp_div_2d(·, ·, ·, NULL)` in
place; the compiler merged the C's two `u_lsb != k`/`v_lsb != k` tests, only one
can hold), the binary loop runs (`mp_cmp_mag`, `mp_exch`, `s_mp_sub(&v, &u, &v)`,
`mp_div_2d(&v, mp_cnt_lsb(&v), &v, NULL)`) until `v = 0`, then
`c = u * 2^k` (`mp_mul_2d`), `c->sign := MP_ZPOS`, `mp_clear(&u)`, `mp_clear(&v)`.
The result meets `GcdPost a b c'` (`Tom/Spec/Gcd.lean`: `c'` valid, nonnegative,
`|c'| = gcdC |a| |b| = gcd(|a|, |b|)`).

As an allocating contract (the shape of `Api/SMpSqr.lean`): the site is `c`'s digit
array, kept in place (D5: `c` has room, `mp_copy`/`mp_mul_2d` do not grow it); the
heap's blocks are the same at the end on success. The C's error paths, as they are:

* the first `mp_init_copy(&u, a)` fails: `MP_MEM`, nothing allocated (`memU`);
* the second `mp_init_copy(&v, b)` fails: the C jumps to `LBL_U`, which clears `v`
  (`v.dp == NULL` after the failed `mp_init_size`, so a no-op) and **not** `u`:
  `u`'s block leaks (`memV q`: the heap keeps the fresh block `q`). This is a bug of
  libtommath 1.2's `mp_gcd` (the labels are swapped), stated as the code does it.

The other callees cannot fail under the room assumptions (their contracts return
`MP_OKAY`). Memory changes only in the stack `[sp - 720, sp)` (the frame and
`mp_init_copy`'s 624 bytes; `mp_clear` 544, `mp_div_2d` 96, `mp_mul_2d` 80,
`s_mp_sub` 48, the tail-called `mp_abs` 64 need less), `c`, and the allocator's
footprint.
-/

namespace Tom.Machine.Api.MpGcd

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x8000105c#64

inductive R | stk | aS | aD | bS | bD | cS | cD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .cS, .cD, .code] := by cases r <;> simp

/-- The stack depth: the 96-byte frame and `mp_init_copy`'s. -/
abbrev F : Nat := 96 + MpInitCopy.F

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

/-- The outcome: `c'` on success; `MP_MEM` from the first `mp_init_copy`; `MP_MEM`
from the second, with `u`'s block `q` leaked. -/
inductive Out
  | ok (c' : MpInt)
  | memU
  | memV (q : Nat)

/-- After: `c'` in `c` on success, everything else as it was. -/
def out (p : P) : Out → R → Kind
  | .ok c', .cS => .mpS p.pc p.cdp c'
  | .ok c', .cD => .mpD p.cdp c'.alloc c'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .cS | .cD => true
  | _ => false

def ws : List R := [.stk, .cS, .cD]

/-- `c`'s digits stay where they are. -/
def site' (p : P) (_ : Out) : Iv := lay p .cD

def hin (p : P) : List (Nat × Nat) := p.H

/-- After: the same blocks, or `u`'s leaked block in front. -/
def hout (p : P) : Out → List (Nat × Nat)
  | .memV q => (q, 4 * initPrec p.a.used) :: p.H
  | _ => p.H

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
   (12, BitVec.ofNat 64 p.pc)]

def rets (_ : P) (x : Out) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | .ok _ => 0#64 | _ => MpInit.memBV)]

/-- What `mp_gcd(a, b, c)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_init_copy` copies valid operands; `mp_cnt_lsb` and the loop read their values. -/
  va : p.a.Valid
  vb : p.b.Valid
  /-- `mp_abs` and `mp_mul_2d` write a shaped `c`. -/
  sc : p.c.Shape
  /-- `mp_cnt_lsb`'s `int` count (`28 used < 2^31`, `Api/CntLsb.lean`); the shifts stay below it. -/
  abits : Layout.digitBits * p.a.used < 2 ^ 31
  bbits : Layout.digitBits * p.b.used < 2 ^ 31
  /-- D5: `mp_abs`'s `mp_copy` and `mp_mul_2d(&u, k, c)` (`|u| 2^k ≤ min(|a|, |b|)`) do not grow `c`. -/
  room : max p.a.used p.b.used + 1 ≤ p.c.alloc
  /-- `mp_init_copy` reads the sources' digit blocks: live and nonempty (`IcRes`). -/
  ablk : digBlk p.adp p.a ∈ p.H
  bblk : digBlk p.bdp p.b ∈ p.H
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- The structs lie off the arena (`IcRes`: the source's). -/
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24

/-- The gcd, and `c`'s allocation kept; a leaked block is fresh. -/
def Q (p : P) : Out → Prop
  | .ok c' => GcdPost p.a p.b c' ∧ c'.alloc = p.c.alloc
  | .memU => True
  | .memV q => Fresh p.H q (4 * initPrec p.a.used)

/-- **`mp_gcd(a, b, c)` on the machine**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpGcd
