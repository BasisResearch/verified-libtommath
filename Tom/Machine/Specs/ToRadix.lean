import Tom.Machine.Conventions
import Tom.Machine.Fn.MpToRadixMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_to_radix`: the concise specification (SPECS.lean), from `Fn.MpToRadixG5.correct` -/

namespace Tom.Machine.Api.MpToRadix
open Tom.Radix

/-- **`mp_to_radix(a, str, maxlen, NULL, radix)`**: `str ← a` in base `radix` (`toRadixStr`: the
digits, `'-'` first for `a < 0`, then `'\\0'`) when `2 ≤ radix ≤ 64` and it fits; else
`MP_VAL`/`MP_BUF` (`ToRadixPost`, SPECS_UNFOLDED.lean) or `MP_MEM`. -/
theorem _root_.Specs.mp_to_radix {p : P} (cv : Conv m ra p.sp F p.H) (sound : Sound (lay p) isW)
    (a : MpOwn m p.H p.pa p.adp p.a) (str : BufOut m p.m0 p.pstr p.maxlen) (hr : p.radix < 2 ^ 31) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pstr, p.maxlen, 0, p.radix] (fun x => BitVec.ofInt 64 x.1)
      fun x M =>
      (x.1 = Layout.mpMem ∨ (radixOk p.radix → (toRadixStr p.a p.radix).length ≤ p.maxlen →
        2 ≤ p.maxlen → x.1 = Layout.mpOkay ∧ ∀ i, bytesOf x.2 p.pstr p.maxlen i =
          (toRadixStr p.a p.radix).getD i (bytesOf p.m0 p.pstr p.maxlen i))) ∧
      HPost (lay p) ws .str (out p x) (site' p x) p.H p.H m M :=
  ApiTriple.of (Reg.call (Fn.MpToRadixG5.correct cv.ra_al
    ⟨cv.stk, a.valid, a.blk, a.pos, a.off, hr⟩ sound) cv.heap (by mp_regions)) fun _ hq => by
    rcases hq with hq | hq
    · refine .inr fun hok hfit hm => ?_
      have := ToRadixPost.spec_ok a.valid hok (by simpa using hfit) hm hq
      simpa using ⟨this.1, this.2.1⟩
    · exact .inl hq

end Tom.Machine.Api.MpToRadix
