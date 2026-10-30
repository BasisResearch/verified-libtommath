import Tom.Machine.Api.ReduxG
import Tom.Spec.Reduce

/-!
# `mp_reduce_2k(a, n, d)` with `a` and `q` growing: the allocating contract

`Api/MpReduce2k.lean` keeps `a` in place (`aroom`) and `q` within `mp_init`'s `MP_PREC` digits
(`qroom`). Regions, parameters and the allocating frame are
`Api/ReduxG.lean`'s: the site is `a`'s digit array, the result `(ok, q, a')`; on `MP_MEM` (an
allocation failed) `a'` is shaped and live at its block; on `MP_OKAY` `Reduce2kPost a n d a'`
(`.spec`: for `n = 2^p - d`, `|a'| = |a| mod |n|`, valid). The C's `int`s only: `mp_count_bits(n)`,
`mp_mod_2d`'s `a->used * MP_DIGIT_BIT`, `mp_grow`'s sizes.

Memory changes only in the stack `[sp - 736, sp)` (the 96-byte frame and `mp_div_2d`'s 640; `mp_init`
560, `mp_mul_d` 624, `s_mp_add` 608, `mp_clear` 544), `a` and the allocator's footprint.
-/

namespace Tom.Machine.Api.MpReduce2kG

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std Tom.Reduce Tom.Mont
open Tom.Machine.Api.MpReduce2k (R P kind)

def entry : BitVec 64 := 0x80005e48#64

/-- The stack depth: the 96-byte frame and `mp_div_2d`'s 640 (the deepest callee). -/
def F : Nat := 736

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | r => MpReduce2k.lay p r

abbrev X := ReduxG.X
abbrev out := ReduxG.out
abbrev site' := ReduxG.site'
abbrev hin := ReduxG.hin
abbrev hout := ReduxG.hout
abbrev rets := ReduxG.rets

/-- What `mp_reduce_2k(a, n, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  vn : p.n.Valid
  /-- `n ≠ 0`: `p > 0` and a loop that ends. -/
  npos : 0 < p.n.mag
  /-- `d` an `mp_digit`. -/
  d_lt : p.d < radix
  /-- `n = 2^p - d`, `p = mp_count_bits(n)` (`mp_reduce_2k_setup`). -/
  hd : p.n.mag + p.d = 2 ^ nbits p.n.mag
  /-- `mp_count_bits(n)`'s `int` result. -/
  bits : Layout.digitBits * p.n.used < 2 ^ 31
  /-- `mp_div_2d`'s `mp_mod_2d(a, p, a)`: `a->used * MP_DIGIT_BIT` does not overflow. -/
  abits : Layout.digitBits * p.a.used < 2 ^ 31
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  noff : OffHeap p.pn 24

def Q (p : P) (x : X) : Prop := ReduxG.Out p (lay p .aD) (Reduce2kPost p.a p.n p.d) x

/-- **`mp_reduce_2k(a, n, d)` on the machine, `a` and `q` growing**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) MpReduce2k.isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: MpReduce2k.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) MpReduce2k.ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpReduce2kG
