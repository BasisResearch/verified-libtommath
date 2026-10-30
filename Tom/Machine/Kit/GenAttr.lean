import Lean

/-!
# The value-lemma registry of `seg_go` (`Kit/Gen.lean`)

`@[seg_val]` marks a normal-form lemma for register and write-log values
(`BitVec` arithmetic on `ofNat` operands, side conditions by `omega`). `seg_go`
rewrites with every lemma of the set (`simp (disch := omega) only [seg_val]`),
so a new ALU shape is one tagged lemma, not a new segment tactic.
The attribute is registered here, apart from its users (a simp set cannot be
used in the file that registers it).
-/

register_simp_attr seg_val

/-! Fixed lemma lists of `seg_go`'s closers as simp sets: a `simp only [l₁, …, lₙ]`
elaborates and indexes its n lemmas at every call (≈ a third of `simp`'s time in a
generated file); a set is indexed once. Members are tagged in `Kit/Gen.lean`. -/

/-- `seg_go` simp set: instruction-literal decoding (`mkLine`, `decodeM`). -/
register_simp_attr seg_dec

/-- `seg_go` simp set: a leaf's register lookups and address arithmetic (`leaf_nf`'s last phase). -/
register_simp_attr seg_lnf

/-- `seg_go` simp set: a code-frame leaf's chain memory (`seg_frame`, first phase). -/
register_simp_attr seg_fr1

/-- `seg_go` simp set: a code-frame leaf's write log decoding (`seg_frame`, second phase). -/
register_simp_attr seg_fr2

/-- `seg_go` simp set: a code-frame leaf's write-log entries (`seg_frame`, last phase). -/
register_simp_attr seg_fr3

/-- `seg_go` simp set: load data back to total reads. -/
register_simp_attr seg_rd5

/-- `seg_go` simp set: immediate and shift-amount literals. -/
register_simp_attr seg_imm

/-- `seg_go` simp set: the register-value normal form (`val_nf`). -/
register_simp_attr seg_vset

/-- `seg_go` simp set: the compare lemmas of `Kit/Arith.lean` (`seg_cmp`). -/
register_simp_attr seg_cmps

/-- `seg_go` simp set: a chain's block structure (`seg_nfo`, first phase). -/
register_simp_attr seg_n1

/-- `seg_go` simp set: a chain's register and log evaluation (`seg_nfo`, last phase). -/
register_simp_attr seg_n3

/-- `seg_go` simp set: register-equation normal forms (`seg_close`). -/
register_simp_attr seg_cls
