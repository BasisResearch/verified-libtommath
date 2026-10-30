import Tom.Machine.Api.MpMulGA
import Tom.Machine.Api.MpMulAF

/-!
# `mp_mul(a, b, a)` on the comba path: what its generated assembly proves

`Api/MpMulGA.lean` (the in-place contract under the recursion hypothesis and the in-place callees'
contracts, `MpMulGA.Gaps`) with operands small enough for the comba path (`MpMulAF.Small`) and the
output record `MpMulAF.Out` (`MpMulA.Out` and `grow`). The generated proof is `Fn.MpMulAFG5.correct`
(`experiments/asm/mmulaf.asm.json`, a variant of `mmula.asm.json`: the Karatsuba/Toom/balance and
schoolbook branches contradict `Small`); `Fn/MpMulAFClosed.lean` discharges the residue.
-/

namespace Tom.Machine.Api.MpMulGAF

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpMulA (P lay kind out isW ws site' hin hout args rets)

structure Res (p : P) : Prop extends toGA : MpMulGA.Res p where
  small : MpMulAF.Small p.a p.b

def SpecR (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At MpMul.entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ MpMulAF.Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

/-- **`mp_mul(a, b, a)` on the comba path**, under `MpMulGA`'s residue. -/
def Statement : Prop := ∀ p : P, SpecR Res p

end Tom.Machine.Api.MpMulGAF
