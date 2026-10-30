import Tom.Machine.Api.ReduxG
import Tom.Machine.Api.Std_grow6G
import Tom.Spec.Reduce

/-!
# `mp_dr_reduce(x, n, k)` growing `x`: the allocating contract

`Api/DrReduce.lean` asks for room (`x->alloc ≥ 2 n->used`, D5). Here the code's own
`if (x->alloc < m + m) mp_grow(x, m + m)` runs (`Std.mpGrowF`): on `MP_MEM` `x` is as it was, at
its block; otherwise `x`'s digits are at `q` (its old block, or a fresh one of `2 m` digits) and the
fold-and-subtract loop of `Api/DrReduce.lean` runs on them: `DrReducePost x n k x'`
(`DrReducePost.spec`: for `n + k = radix^m`, `x'` valid and `|x'| = |x| mod |n|`). Regions,
parameters and the allocating frame are `Api/ReduxG.lean`'s (`a` is `x`, `d` is `k`); `x` and `n`
distinct (D6), `x`'s digits a live heap block. The C's `int`s (`m + m`, `x->used - m`) are small by
`n`'s and `x`'s blocks in memory.

Memory changes only in the stack `[sp - 672, sp)` (the 128-byte frame and `mp_grow`'s 544; `s_mp_sub`
48, `__muldi3`, `memset`, `mp_clamp`, `mp_cmp_mag` none), `x` and the allocator's footprint.
-/

namespace Tom.Machine.Api.DrReduceG

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std Tom.Reduce
open Tom.Machine.Api.MpReduce2k (R P kind)

def entry : BitVec 64 := 0x800055e4#64

/-- The stack depth: the 128-byte frame and `mp_grow`'s. -/
abbrev F : Nat := 128 + MpGrow.F

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | r => MpReduce2k.lay p r

abbrev X := ReduxG.X
abbrev out := ReduxG.out
abbrev site' := ReduxG.site'
abbrev hin := ReduxG.hin
abbrev hout := ReduxG.hout
abbrev rets := ReduxG.rets

/-- What `mp_dr_reduce(x, n, k)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  vn : p.n.Valid
  /-- `n ≠ 0`: at least one digit, and a loop that ends. -/
  npos : 0 < p.n.mag
  /-- `k` an `mp_digit` (`mp_dr_setup`). -/
  d_lt : p.d < radix
  /-- The C asks for `x ≤ (n - 1)^2`; the fold needs `x < radix^(2 m)`. -/
  x_lt : p.a.mag < radix ^ (2 * p.n.used)
  /-- `x`'s digits are `realloc`'s block: live and nonempty. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  noff : OffHeap p.pn 24

def Q (p : P) (x : X) : Prop := ReduxG.Out p (lay p .aD) (DrReducePost p.a p.n p.d) x

/-- **`mp_dr_reduce(x, n, k)` on the machine, growing `x`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) MpReduce2k.isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: MpReduce2k.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) MpReduce2k.ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.DrReduceG
