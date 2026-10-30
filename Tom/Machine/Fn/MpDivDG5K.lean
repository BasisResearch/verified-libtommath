import Tom.Machine.Api.MpDivD

/-!
# `mp_div_d`'s assembly: the return word per path

`MpDivD.retv` decides `MP_VAL` on `b = 0` before the result: the generated exits
(`Fn/MpDivDMainG.lean`, `experiments/asm/mdivd.asm.json`) rewrite `rets` to the list the
path returns. The rest of r6e's helpers are generator features or Kit rules now (`Rk` "R" and
the store rule "w", `St.seqR`, `Dig.of_frz1`, `HPost.keep`/`inplace`, `tail` to an
`HContract` by `tail_heap` over the contract's layout; Kit/Run.lean).
-/

namespace Tom.Machine.Fn.MpDivDG5K

open Tom.Machine Tom.Machine.Api

theorem rets_val {p : MpDivD.P} (hv : p.v = 0) (x : Option (Nat × MpInt)) (ra : BitVec 64) :
    MpDivD.rets p x ra = [(1, ra), (10, MpDivD.valBV)] := by
  simp [MpDivD.rets, MpDivD.retv, hv]

theorem rets_none {p : MpDivD.P} (hv : p.v ≠ 0) (ra : BitVec 64) :
    MpDivD.rets p none ra = [(1, ra), (10, MpInit.memBV)] := by
  simp [MpDivD.rets, MpDivD.retv, hv]

theorem rets_some {p : MpDivD.P} (hv : p.v ≠ 0) (y : Nat × MpInt) (ra : BitVec 64) :
    MpDivD.rets p (some y) ra = [(1, ra), (10, 0#64)] := by
  simp [MpDivD.rets, MpDivD.retv, hv]

end Tom.Machine.Fn.MpDivDG5K
