import Tom.Machine.Api.MulHighFastHA

/-!
# `s_mp_mul_high_digs(a, b, a, digs)` on the fast path, growing

`Api/SMpMulHighDigs.lean`'s in-place call with its fast test true (`Fast a b`: `pa + 1 < MP_WARRAY`,
`MP_MIN(a->used, b->used) < MP_MAXFAST`): the tail call `s_mp_mul_high_digs_fast(a, b, a, digs)`
(`69e0`–`6a0c`, `6ba4`–`6bb8`), whose contract with growth is `Api.MulHighFastHA` (proved:
`Fn.MulHighFastGAG5.correct`). `SMpMulHighDigs.Res.room` (D5) is false for `mp_reduce`'s call with a
Barrett `mu`; this contract replaces it there, its statement is unchanged. So this is
`MulHighFastHA`'s contract at `s_mp_mul_high_digs`'s entry: regions, residue, results and layout are
its. Proved by `Fn.SMpMulHighDigsAFG5.correct` (`experiments/asm/mhdigsaf.asm.json`).
-/

namespace Tom.Machine.Api.SMpMulHighDigsAF

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.SMpMulHighDigs (R P kind isW ws args)
open Tom.Machine.Api.MulHighFastHA (lay)

/-- The stack depth (`MulHighFastHA.F`: the tail-called routine with `mp_grow`). -/
def F : Nat := 2736

abbrev Res := MulHighFastHA.Res
abbrev out := MulHighFastHA.out
abbrev site' := MulHighFastHA.site'
abbrev hin := MulHighFastHA.hin
abbrev hout := MulHighFastHA.hout
abbrev rets := MulHighFastHA.rets
abbrev Q := MulHighFastHA.Q

/-- **`s_mp_mul_high_digs(a, b, a, digs)` on the fast path, `a` grown as needed.** -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At SMpMulHighDigs.entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.SMpMulHighDigsAF
