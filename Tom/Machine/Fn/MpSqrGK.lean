import Tom.Machine.Kit.Gen

/-! `mp_sqr`'s comba-path test (`6434`–`6448`): below `KARATSUBA_SQR_CUTOFF = 120`,
`slti(2 a->used, 511)` and `slti(a->used, 128)` are both set. -/

namespace Tom.Machine.Fn.MpSqrG

open LeanRV64DExecutable LeanRV64DExecutable.Functions

theorem warr_tab : ∀ u, u < 120 →
    (BitVec.ofNat 64 (bool_to_bit (zopz0zI_s (BitVec.signExtend 64
      (Sail.shift_bits_left (BitVec.ofNat 32 (u % 4294967296)) 1#5)) 511#64)).toNat == 0#64) = false := by
  decide

theorem fast_tab : ∀ u, u < 120 →
    (BitVec.ofNat 64 (bool_to_bit (zopz0zI_s (BitVec.ofNat 64 (u % 4294967296)) 128#64)).toNat != 0#64) = true := by
  decide

@[seg_val] theorem warr_set (u : Nat) (h : u < 120) :
    (BitVec.ofNat 64 (bool_to_bit (zopz0zI_s (BitVec.signExtend 64
      (Sail.shift_bits_left (BitVec.ofNat 32 (u % 4294967296)) 1#5)) 511#64)).toNat == 0#64) = false :=
  warr_tab u h

@[seg_val] theorem fast_set (u : Nat) (h : u < 120) :
    (BitVec.ofNat 64 (bool_to_bit (zopz0zI_s (BitVec.ofNat 64 (u % 4294967296)) 128#64)).toNat != 0#64) = true :=
  fast_tab u h

theorem fast_tab' : ∀ u, u < 120 →
    (BitVec.ofNat 64 (bool_to_bit (zopz0zI_s (BitVec.ofNat 64 u) 128#64)).toNat != 0#64) = true := by
  decide

@[seg_val] theorem fast_set' (u : Nat) (h : u < 120) :
    (BitVec.ofNat 64 (bool_to_bit (zopz0zI_s (BitVec.ofNat 64 u) 128#64)).toNat != 0#64) = true :=
  fast_tab' u h

/-- The branch leaves above close by the normal form with these lemmas (`leaf_nf`, then
`seg_vnf`), which `seg_leaf`'s standard closers do not try before failing. -/
macro_rules | `(tactic| seg_leaf_ext [$ds,*]) => `(tactic| ((first | leaf_nf [$ds,*] | skip); (try seg_vnf []); done))

end Tom.Machine.Fn.MpSqrG
