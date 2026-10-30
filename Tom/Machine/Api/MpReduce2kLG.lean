import Tom.Machine.Api.MpReduce2kL
import Tom.Spec.MpReduce2kLGStep

/-!
# `mp_reduce_2k_l(a, n, d)` with `a` and `q` growing: the allocating contract

`Api/MpReduce2kL.lean` keeps `a` in place (`aroom`) and `q` within `mp_init`'s `MP_PREC` digits
(`qroom`: `a->used ≤ 32`). Here `mp_div_2d(a, p, &q, a)` grows `q` (`Api/MpDiv2dRG.lean`) and
`s_mp_add(a, &q, a)` grows `a` (`Std.sAddGA`), so the site is `a`'s digit array and the result is
`(ok, q, a')` as `Api/MpReduce.lean`'s: on `MP_MEM` (an allocation failed) `a'` is shaped and live at
its block; on `MP_OKAY` `Reduce2kPost a n |d| a'`. `mp_mul(&q, d, &q)` at any size. Regions and arguments as `Api/MpReduce2kL.lean`; the stack
depth `F` is the operands'.
-/

namespace Tom.Machine.Api.MpReduce2kLG

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Reduce Tom.Mont
open Tom.Machine.Api.MpReduce2kL (entry R all P kind isW ws args)

/-- The stack depth: the 96-byte frame and `mp_mul(&q, d, &q)`'s `2768 + 8 (q->used + d->used)`, with
`q->used + d->used ≤ a->used + n->used + 1` (`quo_used`, `EnvG.dused`); `mp_div_2d`'s 640, `s_mp_add`'s
608 below it. (`Api/MpReduce2kL.lean`'s fixed 6952 covers every comba product; this one is what a
caller with small operands can reserve.) -/
def F {p : P} : Nat := 2872 + 8 * (p.a.used + p.n.used)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F (p := p), F (p := p)⟩
  | r => MpReduce2kL.lay p r

/-- `(ok, q, a')`: `a'`'s digits at `q`. -/
abbrev X : Type := Bool × Nat × MpInt

def out (p : P) : X → R → Kind
  | (_, q, a'), .aS => .mpS p.pa q a'
  | (_, q, a'), .aD => .mpD q a'.alloc a'.digit
  | _, r => kind p r

def site' (_ : P) : X → Iv
  | (_, q, a') => ⟨q, 4 * a'.alloc⟩

/-- `a`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.adp p.a :: p.H

def hout (p : P) : X → List (Nat × Nat)
  | (_, q, a') => (q, 4 * a'.alloc) :: p.H

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpInit.memBV)]

/-- What `mp_reduce_2k_l(a, n, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp (F (p := p))
  va : p.a.Valid
  vn : p.n.Valid
  vd : p.d.Valid
  /-- `n ≠ 0`: `p > 0` and a loop that ends. -/
  npos : 0 < p.n.mag
  /-- `n = 2^p - |d|`, `p = mp_count_bits(n)` (`mp_reduce_2k_setup_l`). -/
  hd : p.n.mag + p.d.mag = 2 ^ nbits p.n.mag
  /-- `mp_count_bits(n)`'s `int` result. -/
  bits : Layout.digitBits * p.n.used < 2 ^ 31
  /-- `mp_div_2d`'s `mp_mod_2d(a, p, a)`: `a->used * MP_DIGIT_BIT` does not overflow. -/
  abits : Layout.digitBits * p.a.used < 2 ^ 31
  /-- `s_mp_add`'s `mp_grow(a, max + 1)`'s `int`. -/
  usz : p.a.used + 1 < 2 ^ 31
  apos : 0 < p.a.alloc
  dpos : 0 < p.d.alloc
  aoff : OffHeap p.pa 24
  noff : OffHeap p.pn 24
  doff : OffHeap p.pd 24

/-- What `a` holds after: shaped, live, placed; on `MP_OKAY` the reduction. -/
structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) (lay p .aD) (site' p x)
  post : x.1 = true → Reduce2kPost p.a p.n p.d.mag x.2.2

def Q (p : P) (x : X) : Prop := Out p x

/-- **`mp_reduce_2k_l(a, n, d)` on the machine, `a` and `q` growing**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpReduce2kLG
