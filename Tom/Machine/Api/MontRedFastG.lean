import Tom.Machine.Api.ReduxG
import Tom.Machine.Api.Std_grow6G
import Tom.Spec.MontRedFastGStep

/-!
# `s_mp_montgomery_reduce_fast(x, n, rho)` growing `x`: the allocating contract

`Api/MontRedFast.lean` asks for room (`x->alloc > n->used`, D5). Here the code's own
`if (x->alloc < n->used + 1) mp_grow(x, n->used + 1)` runs (`Std.mpGrowF`): on `MP_MEM` `x` is as it
was, at its block; otherwise `x`'s digits are at `q` (its old block, or a fresh one of
`n->used + 1` digits, `MontRedFastGStep.mfIn`) and the column algorithm runs on them:
`RedcV x n rho x'` (`RedcPost` without the block, of the grown `x`, which has `x`'s value and sign;
`RedcV.spec`: `x'` valid, `|x'| < |n|`, `|x'| R ≡ |x| (mod |n|)`). Regions, parameters and the allocating frame
are `Api/ReduxG.lean`'s (`a` is `x`, `d` is `rho`); `x` and `n` distinct (D6), `x`'s digits a live heap
block. `1 ≤ n->used ≤ 255` (`n->used < MP_MAXFAST`: the caller's test; no column overflows `mp_word`)
and `|x| < |n| R` (REDC's input range, so `x->used ≤ 2 n->used ≤ MP_WARRAY`) as in the room contract.

Memory changes only in the stack `[sp - 4800, sp)` (the 4256-byte frame with `W[MP_WARRAY]` and
`mp_grow`'s 544; `__muldi3`, `memset`, `mp_clamp`, `mp_cmp_mag` none, the tail-called `s_mp_sub` 48 in
the popped frame), `x` and the allocator's footprint.
-/

namespace Tom.Machine.Api.MontRedFastG

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std Tom.Mont
open Tom.Machine.Api.MpReduce2k (R P kind)

def entry : BitVec 64 := 0x80003d9c#64

/-- The stack depth: the 4256-byte frame and `mp_grow`'s 544. -/
def F : Nat := 4800

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | r => MpReduce2k.lay p r

abbrev X := ReduxG.X
abbrev out := ReduxG.out
abbrev site' := ReduxG.site'
abbrev hin := ReduxG.hin
abbrev hout := ReduxG.hout
abbrev rets := ReduxG.rets

/-- What `s_mp_montgomery_reduce_fast(x, n, rho)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  vn : p.n.Valid
  /-- `rho` from `mp_montgomery_setup(n, &rho)`: `n rho ≡ -1 (mod radix)`. -/
  rho_ok : (p.n.mag * p.d + 1) % radix = 0
  rho_lt : p.d < radix
  /-- REDC's input range: `|x| < |n| R`. -/
  x_lt : p.a.mag < p.n.mag * radix ^ p.n.used
  /-- `n->used < MP_MAXFAST` (the callers' test). -/
  nu_le : p.n.used ≤ 255
  /-- `x`'s digits are `realloc`'s block: live and nonempty. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  noff : OffHeap p.pn 24

def Q (p : P) (x : X) : Prop :=
  ReduxG.Out p (lay p .aD) (MontRedFastGStep.RedcV p.a p.n p.d) x

/-- **`s_mp_montgomery_reduce_fast(x, n, rho)` on the machine, growing `x`**, as an allocating
contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) MpReduce2k.isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: MpReduce2k.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) MpReduce2k.ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MontRedFastG
