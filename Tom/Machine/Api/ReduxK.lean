import Tom.Machine.Api.Redux
import Tom.Machine.Api.Exptmod
import Tom.Machine.Kit.TabState
import Tom.Spec.SMpExptmodFastMode

/-!
# `redux` in mode `md` for its callers: the routine's residue from the Spec's `Cond`

`s_mp_exptmod_fast` calls `redux(&x, P, mp)` through `jalr` (`Std.reduxH md`) on `x = a b` for
residues `a, b < P` (a square or a product of the table's entries). `resK_of` builds the routine's
needs (`Std.ResK md`) from the setup's `Cond`, the modulus' D5 rooms and `x`'s size; `htgtR` is the
`jalr` target, `reduxE_al` its alignment; `rp_red` reads the contract's relation as the Spec's.
Once per callee, for its callers (as `Std.mulF_res`, `Api/MpMulAF.lean`).
-/

namespace Tom.Machine.Api.ReduxK

open Tom Tom.Machine Tom.Machine.Std Tom.SMpExptmodFastStep
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- **`redux`'s residue in mode `md`** on a product of two residues. -/
theorem resK_of {md : Nat} {p : Api.MpReduce2k.P} (hc : Cond p.n md p.d)
    (hdr : md = 1 → 0 < p.n.digit 0)
    (hr2k : 2 ≤ md → 2 * p.n.used + 1 ≤ defPrec ∧ Api.SMpExptmodFast.Exact2k p.n)
    (hva : p.a.Valid) (hlt : p.a.mag ≤ (p.n.mag - 1) * (p.n.mag - 1)) (hau : p.a.used ≤ 2 * p.n.used)
    (hal : 2 * p.n.used + 1 ≤ p.a.alloc) (hsmall : p.n.used < 80) (hbits : Layout.digitBits * p.n.used < 2 ^ 31) :
    ResK md p := by
  have hvn := hc.valid
  have hg := hc.gt1
  have hm := MpInt.mag_lt hvn.toShape
  have hu : 0 < p.n.used := WindowStep.used_pos (by omega)
  have hsq : p.a.mag < radix ^ p.n.used * radix ^ p.n.used :=
    Nat.lt_of_le_of_lt hlt (Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) (by omega))
  rcases md with _ | _ | md
  · obtain ⟨ho, hd⟩ := hc.mont rfl
    refine ⟨hva, hvn, ?_, ?_, ?_, hu, by omega, by omega⟩
    · have e := Tom.Mont.MpInt.mag_mod_radix hvn.toShape
      have hs := Tom.Mont.setupRho_spec _ (digit0_odd hvn.toShape ho)
      have hdm := Nat.div_add_mod p.n.mag radix
      rw [e] at hdm
      rw [hd, ← hdm, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_mul_mod_self_left]
      exact hs
    · rw [hd]; exact Tom.Mont.setupRho_lt _
    · exact Nat.lt_of_le_of_lt hlt (Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) (by omega))
  · obtain ⟨_, hd⟩ := hc.dr rfl
    have h0 := hdr rfl
    refine ⟨hva, hvn, by omega, ?_, ?_, by omega⟩
    · rw [hd]; unfold drSetupDigit; have := radix_pos; omega
    · rw [Nat.two_mul, Nat.pow_add]; exact hsq
  · have hs := hc.r2k (by omega)
    obtain ⟨hq, hx⟩ := hr2k (by omega)
    refine ⟨hva, hvn, by omega, ?_, ?_, hbits, by omega, by omega⟩
    · rw [hs.val]; exact Nat.mod_lt _ radix_pos
    · rw [hs.val]; exact hx

/-- The `jalr s8` target: the routine of mode `k`. -/
theorem htgtR {re k : Nat} (h : BitVec.ofNat 64 re = reduxE k) :
    BitVec.update (BitVec.ofNat 64 re + sign_extend (m := 64) (0#12 : BitVec 12)) 0 0#1 = reduxE k := by
  rw [h]; rcases k with _ | _ | k
  · decide
  · decide
  · exact (by decide : BitVec.update (Api.MpReduce2k.entry + sign_extend (m := 64) (0#12 : BitVec 12)) 0 0#1 = Api.MpReduce2k.entry)

/-- The routine's entry is word aligned. -/
theorem reduxE_al (k : Nat) : (reduxE k).toNat % 4 = 0 := by
  rcases k with _ | _ | k
  · decide
  · decide
  · exact (by decide : (Api.MpReduce2k.entry).toNat % 4 = 0)


/-- The setup's digit is a digit. -/
theorem Cond.d_lt {P : MpInt} {md d : Nat} (hc : Cond P md d) (hdr : md = 1 → 0 < P.digit 0) : d < radix := by
  rcases md with _ | _ | md
  · rw [(hc.mont rfl).2]; exact Tom.Mont.setupRho_lt _
  · rw [(hc.dr rfl).2]; unfold drSetupDigit; have := hdr rfl; have := radix_pos; omega
  · rw [(hc.r2k (by omega)).val]; exact Nat.mod_lt _ radix_pos

end Tom.Machine.Api.ReduxK
