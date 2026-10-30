import Tom.Machine.Kit.Auto

/-!
# Segments that store through a loaded pointer

`code_frame` closes a code-frame leaf from the store addresses in the
register list; when a store's address is a value the segment loaded (`ld a5,
8(sp); sw zero, 8(a5)`: `mp_set`'s `dp[0]`, `mp_abs`'s reloaded `b`), the
address is a load term. `frame_eqs [defs] [eqs]` folds it back to the total
read (`rd8_bytesD`), rewrites it by the caller's equations `eqs`, and closes
the bound by `omega`. `seg_step_eq` is `seg_step` with this closer added for
the leaves `leaf_auto` leaves.
-/

syntax "frame_eqs" " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| frame_eqs [$ds,*] [$es,*]) => `(tactic|
      (code_frame [$ds,*]
       all_goals (simp only [Tom.Machine.rd8_bytesD, BitVec.signExtend_eq, $es,*, BitVec.add_zero,
                    Tom.Machine.ofNat_add_ofNat, BitVec.toNat_ofNat]
                  omega)))

syntax "seg_step_eq " term:max ppSpace term:max ppSpace term:max ppSpace term:max ppSpace term:max
  " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term:max : tactic
macro_rules
  | `(tactic| seg_step_eq $bs $pc $lds $ks $kk [$ds,*] [$ps,*] [$es,*] $hc) => do
      let b ← `(Lean.Parser.Tactic.simpLemma| $bs:term)
      let l1 : Array (Lean.TSyntax ``Lean.Parser.Tactic.simpLemma) := #[b] ++ ds.getElems
      let l2 := l1 ++ ps.getElems
      `(tactic|
        (refine Tom.Machine.seg_at' $bs (pc1 := $pc) $lds $ks $kk ?_ ?_ ?_ ?_
         · tom_facts $hc
           all_goals first
             | (leaf_auto [$ds,*] [$es,*]; done)
             | frame_eqs [$ds,*] [$es,*]
         · seg_nfo [$l1,*]
           try (try val_nf [$es,*]
                exact Tom.Machine.ret_target' _ (by assumption))
         · sub_auto [$l2,*] [$es,*]
         · seg_nfo [$l1,*]
           try val_nf [$es,*]
           try regs_close))
