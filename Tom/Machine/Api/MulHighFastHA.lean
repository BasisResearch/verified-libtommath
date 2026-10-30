import Tom.Machine.Api.SMpMulHighDigs
import Tom.Machine.Api.MulFastH

/-!
# `s_mp_mul_high_digs_fast(a, b, a, digs)` with growth: the allocating contract

`Api/MulHighFast.lean` (`Fn.MulHighFast.correct`) assumes `a->used + b->used ≤ a->alloc`
(D5: no `mp_grow`), which is false for `mp_reduce`'s call. The code grows its
destination, `if (c->alloc < pa) mp_grow(c, pa)` with `pa = a->used + b->used`: in place
(`c = a`) `a`'s digits may be re-placed (`MP_MEM`: everything kept), then the columns
`digs .. pa - 1` are read from `a` at its block after the grow and written back above `digs`,
`a->used := pa`, `mp_clamp(a)`. No `MP_ZERO_DIGITS`: in place `olduse = a->used ≤ pa`.

Regions, parameters and heap as `Api/SMpMulHighDigs.lean` (`stk aS aD bS bD code`, written
`stk aS aD`, the site `a`'s digits); results as `Api/MpMul.lean`'s `(ok, q, a')`. Stack: the
routine's 2192 bytes and `mp_grow`'s 544 below them. The residue is the C's fast test
(`SMpMulHighDigs.Fast`: `pa + 1 < MP_WARRAY`, `MP_MIN(a->used, b->used) < MP_MAXFAST`), `digs ≤ pa`
and `b` nonempty (`MulHighFast.Cond`). Proved: `Fn.MulHighFastGAG5.correct`
(`experiments/asm/mhfastga.asm.json`, rows `experiments/segs/mhfastg.rows.json`, model steps
`Tom/Spec/MulHighFastGStep.lean`).
-/

namespace Tom.Machine.Api.MulHighFastHA

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std Tom.Reduce
open Tom.Machine.Api.SMpMulHighDigs (R P kind isW ws args Fast)
open Tom.Machine.Api.MpMul (X)

def entry : BitVec 64 := 0x80006be4#64

/-- The stack depth: the 2192-byte frame and `mp_grow`'s 544. -/
def F : Nat := 2736

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .code => textIv

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

/-- What `s_mp_mul_high_digs_fast(a, b, a, digs)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 2736
  sa : p.a.Shape
  sb : p.b.Shape
  /-- The routine keeps `a`'s sign word for a nonzero result. -/
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  /-- The C's `int digs`, nonnegative. -/
  dg_lt : p.digs < 2 ^ 31
  /-- No column below `digs` is skipped past `pa` (`MulHighFast.Cond.dg_le`). -/
  dg_le : p.digs ≤ p.a.used + p.b.used
  /-- `MulHighFast.Cond.ub_pos`. -/
  ub_pos : 1 ≤ p.b.used
  /-- The C's fast test (`pa` below `MP_WARRAY`, the shorter operand below `MP_MAXFAST`). -/
  fast : Fast p.a p.b
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

/-- What `a` holds after: on `MP_MEM` (`ok = false`) `a` itself; else the old digits below `digs`
plus the high product (`MulHighFastPost.spec` over the grown `a`). -/
structure Out (p : P) (ok : Bool) (a' : MpInt) : Prop where
  shape : a'.Shape
  pos : 0 < a'.alloc
  /-- `a`'s block kept or grown (`mp_grow` never shrinks). -/
  grow : p.a.alloc ≤ a'.alloc
  /-- The sign kept, or reset for a zero result. -/
  sign : a'.sign = Layout.mpZpos ∨ a'.sign = p.a.sign
  valid : ok = true → a'.Valid
  mag : ok = true → a'.mag = natUpTo p.a.digit p.digs + highProd p.a.digit p.b.digit p.a.used p.b.used p.digs

def Q (p : P) : X → Prop
  | (ok, _, a') => Out p ok a'

/-- **`s_mp_mul_high_digs_fast(a, b, a, digs)` with growth.** -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MulHighFastHA
