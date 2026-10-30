import Tom.Machine.Api.MontRedFastG

/-!
# `mp_montgomery_reduce(x, n, rho)` growing `x`: the allocating contract

`Api/MontRed.lean` asks for room (`x->alloc ≥ 2 n->used + 1`, D5). Here both of the code's paths run
at any size: for `digs = 2 n->used + 1 < MP_WARRAY`, `x->used ≤ MP_WARRAY` and `n->used < MP_MAXFAST`
it tail-calls `s_mp_montgomery_reduce_fast` (`Api/MontRedFastG.lean`: `x` grown to `n->used + 1`);
otherwise its own rows after `if (x->alloc < digs) mp_grow(x, digs)` (`Std.mpGrowF`; `x` re-placed,
`MontRedFastGStep.mrIn`), `mp_clamp`, `mp_rshd(x, n->used)`, `mp_cmp_mag` and the tail call
`s_mp_sub(x, n, x)`. On `MP_MEM` `x` is as it was (the slow path's `mp_grow`) or as the fast routine
left it; on `MP_OKAY` `RedcV x n rho x'` (`RedcV.spec`: `x'` valid, `|x'| < |n|`,
`|x'| R ≡ |x| (mod |n|)`). Regions, parameters and the allocating frame are `Api/ReduxG.lean`'s
(`a` is `x`, `d` is `rho`).

Memory changes only in the stack `[sp - 4800, sp)` (the fast routine's, run in the popped frame; the
112-byte frame with `mp_grow`'s 544, `mp_rshd`'s 32 and `s_mp_sub`'s 48 below it), `x` and the
allocator's footprint.
-/

namespace Tom.Machine.Api.MontRedGr

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std Tom.Mont
open Tom.Machine.Api.MpReduce2k (R P kind)

def entry : BitVec 64 := 0x800059e0#64

/-- The stack depth: `s_mp_montgomery_reduce_fast`'s (`Api.MontRedFastG.F`), above the slow path's. -/
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

/-- What `mp_montgomery_reduce(x, n, rho)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  vn : p.n.Valid
  /-- `rho` from `mp_montgomery_setup(n, &rho)`: `n rho ≡ -1 (mod radix)`. -/
  rho_ok : (p.n.mag * p.d + 1) % radix = 0
  rho_lt : p.d < radix
  /-- REDC's input range: `|x| < |n| R`. -/
  x_lt : p.a.mag < p.n.mag * radix ^ p.n.used
  /-- `x`'s digits are `realloc`'s block: live and nonempty. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  noff : OffHeap p.pn 24

def Q (p : P) (x : X) : Prop := ReduxG.Out p (lay p .aD) (MontRedFastGStep.RedcV p.a p.n p.d) x

/-- **`mp_montgomery_reduce(x, n, rho)` on the machine, growing `x`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) MpReduce2k.isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: MpReduce2k.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) MpReduce2k.ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MontRedGr
