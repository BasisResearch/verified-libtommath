import Tom.Machine.Conventions
import Tom.Machine.Fn.MpToRadixMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_to_radix`: the concise specification (SPECS.lean), from `Fn.MpToRadixG5.correct` -/

namespace Tom.Machine.Api.MpToRadix
open Tom.Radix

def eff (p : P) := Eff.heap (lay p) isW ws .str (out p) (site' p) p.H (fun _ => p.H)
  fun x => errView x.1 (bytesOf x.2 p.pstr p.maxlen)

/-- **`mp_to_radix(a, str, maxlen, NULL, radix)`**: `str ← a` in base `radix` (`toRadixStr`: the
digits, `'-'` first for `a < 0`, then `'\\0'`), for `2 ≤ radix ≤ 64` and a buffer it fits (else
`MP_VAL`/`MP_BUF`: `ToRadixPost`, SPECS_UNFOLDED.lean); the result: the buffer's bytes. -/
theorem _root_.Specs.mp_to_radix {p : P} (cv : Conv m ra p.sp F (eff p))
    (a : MpOwn m p.H p.pa p.adp p.a) (str : BufOut m p.m0 p.pstr p.maxlen) (hr : radixOk p.radix)
    (fit : (toRadixStr p.a p.radix).length ≤ p.maxlen) (two : 2 ≤ p.maxlen) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pstr, p.maxlen, 0, p.radix] (eff p)
      fun s => ∀ i, s i = (toRadixStr p.a p.radix).getD i (bytesOf p.m0 p.pstr p.maxlen i) :=
  have e := fun {x : Int × Mem} (hq : Q p x) => hq.symm.imp_right fun h =>
    have s := ToRadixPost.spec_ok a.valid hr (by simpa using fit) two h; ⟨s.1, by simpa using s.2.1⟩
  ApiTriple.of (Reg.call (Fn.MpToRadixG5.correct cv.ra_al
    ⟨cv.stk, a.valid, a.blk, a.pos, a.off, by have := hr.2; unfold radixOk at hr; omega⟩ cv.sound)
    cv.heap (by mp_regions)) (fun _ hq => .errView (e hq))
    (hr := fun _ hq => congrArg (fun b => [(1, ra), (10, b)]) (errView_ret (e hq)))

end Tom.Machine.Api.MpToRadix
