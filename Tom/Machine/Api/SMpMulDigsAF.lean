import Tom.Machine.Api.SMpMulDigsA

/-!
# `s_mp_mul_digs(a, b, a, digs)` on the fast path, growing

`Api/SMpMulDigsA.lean`'s in-place call on the other branch: when `Fast a b digs` (`digs < 512`,
`min(a->used, b->used) < 256`), `s_mp_mul_digs` tail-calls `s_mp_mul_digs_fast(a, b, a, digs)`
(`40fc`–`4124`, `j` at `42c4`), whose contract with growth is `Api.MulFastHA` (proved:
`Fn.MulFastGAG5.correct`): `mp_grow(a, digs)` may re-place `a`'s digits (`a->alloc ≤ a'->alloc`,
`MulFastHA.Out.grow`), or fail with `MP_MEM` (everything kept). So this contract is `MulFastHA`'s at
`s_mp_mul_digs`'s entry, with `Fast` and the C's `int digs` in the residue: regions, results, layout
(the 2736 bytes of the tail-called routine with `mp_grow`) are `MulFastHA`'s. `mp_reduce` calls
`s_mp_mul_digs(&q, m, &q, um + 1)` here for `um < 255`. Proved by `Fn.SMpMulDigsAFG5.correct` (`experiments/asm/smdigsaf.asm.json`).
-/

namespace Tom.Machine.Api.SMpMulDigsAF

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.SMpMulDigsA (R P kind isW ws args)
open Tom.Machine.Api.SMpMulDigs (Fast)
open Tom.Machine.Api.MulFastHA (lay)

/-- The stack depth (`MulFastHA.F`: the tail-called routine with `mp_grow`). -/
def F : Nat := 2736

abbrev out := MulFastHA.out
abbrev site' := MulFastHA.site'
abbrev hin := MulFastHA.hin
abbrev hout := MulFastHA.hout
abbrev rets := MulFastHA.rets
abbrev Q := MulFastHA.Q

/-- What `s_mp_mul_digs(a, b, a, digs)` needs on the fast path. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 2736
  sa : p.a.Shape
  sb : p.b.Shape
  /-- The fast routine keeps `a`'s sign word for a nonzero result. -/
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  /-- The C's `int digs`, nonnegative. -/
  dg_lt : p.digs < 2 ^ 31
  /-- The C's `int` sums stay small. -/
  uab : p.a.used + p.b.used < 2 ^ 30
  /-- The fast path: the tail call. -/
  fast : Fast p.a p.b p.digs
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

/-- **`s_mp_mul_digs(a, b, a, digs)` on the fast path, `a` grown as needed.** -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At SMpMulDigs.entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.SMpMulDigsAF
