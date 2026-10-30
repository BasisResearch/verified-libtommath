import Tom.Machine.Kit.Gen
import Tom.Machine.Kit.Shift

/-!
# The parity test `lw; andi 1; bnez` as a segment-leaf closer

`MP_IS_ODD(x)`/`MP_IS_EVEN(x)` compile to `lw a5, 0(dp); andi a5, a5, 1; bnez/beqz a5`: the guard
`(BitVec.ofNat 64 (d % 2^32) &&& 1#64 != 0#64) = b` of a digit `d`. `seg_go`'s guard closer has no
lemma for the `andi`; this `seg_leaf_ext` alternative normalises the leaf, rewrites the mask by
`and1_ofNat` (Kit/Shift.lean) and closes the comparison of `d % 2` by `seg_cmp` + `omega`. Rows
import this file (`"imports"`) when they test a parity (`mp_invmod`, `s_mp_invmod_fast`,
`s_mp_invmod_slow`).
-/

macro_rules
  | `(tactic| seg_leaf_ext [$ds,*]) => `(tactic|
      ((first | gleaf_nf [$ds,*] | skip)
       (try seg_vnf [])
       simp only [Tom.Machine.and1_ofNat]
       seg_cmp
       all_goals omega_split))
