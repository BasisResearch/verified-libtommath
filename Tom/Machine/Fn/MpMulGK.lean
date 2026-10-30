import Tom.Machine.Kit.Gen
import Tom.Machine.Kit.WordVal
import Tom.Spec.MpMulStep
import Tom.Spec.IntFacts

/-!
# `mp_mul`'s segments: the branch-guard closer

`mp_mul`'s value lemmas (`sub01`, `sgn01`, `slliw`/`addw`/`slti` of small values) are Kit/WordVal.lean's
(`Tom.Machine.WV`), `ng_eq` is Tom/Spec/IntFacts.lean's; here the `seg_leaf` extension
that closes the branch guards with them.
-/

namespace Tom.Machine.Fn.MpMulGK

end Tom.Machine.Fn.MpMulGK

/-- `mp_mul`'s branch guards on `slliw`/`addw`/`slti` values (the `seg_leaf` extension point). -/
macro_rules | `(tactic| seg_leaf_ext [$ds,*]) => `(tactic|
  ((first | leaf_nf [$ds,*] | skip)
   (try seg_vnf [])
   (try simp (disch := omega) only [Tom.Machine.WV.sllw1, Tom.Machine.WV.addw3])
   try simp (disch := omega) only [Tom.Machine.WV.slti_beqz]
   try simp (disch := omega) only [Tom.Machine.blt_ofNat]
   simp only [decide_eq_true_eq, decide_eq_false_iff_not]
   all_goals omega))
