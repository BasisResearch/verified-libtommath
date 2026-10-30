import Tom.Machine.Fn.Memset
import Tom.Machine.Img
import Tom.Machine.Kit.Jal
import Vsa.Sim.TripleCat

/-!
# Calls into library routines from a function over named regions

* `memset_pre`: `Memset.Pre m d 0 n` for a zero fill `[d, d + n)` inside a
  region `r` that the layout keeps apart from the code region `c` (the text
  section, `Img`): the `MP_ZERO_DIGITS` calls of `mp_zero`, `mp_set`,
  `mp_copy`, `mp_rshd`, `mp_lshd`.
* `jal_step pc w imm L' hc [defs] [keepdefs]`: the `jal ra, target` step at
  `pc` (word `w`, offset `imm`) as `jal_at` with its side conditions closed
  (the word from `hc : CodeAt …`, decode by `decodeW`, the pins `L'` from the
  register list by `simp [defs]`, the kept registers by `simp [keepdefs]`).
-/

namespace Tom.Machine

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic

theorem Iv.Sub.trans {I J K : Iv} (h1 : I.Sub J) (h2 : J.Sub K) : I.Sub K := by
  unfold Iv.Sub at *; omega

theorem memset_pre {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} (hS : Sound ρ isW)
    {r c : ι} {m : Mem} {d n : Nat} (himg : Img m) (hc : textIv.Sub (ρ c)) (hI : Iv.Sub ⟨d, n⟩ (ρ r))
    (hram : Ram d n) (hsep : Sep isW r c = true := by decide) : Fn.Memset.Pre m d 0 n :=
  { byte := by decide, code := himg.memset, ram := hram
    code_off := by
      have : Code.memsetCode.length = 55 := rfl
      rw [this]
      exact hS.sub hI (Iv.Sub.trans (⟨by decide, by decide⟩ : Iv.Sub ⟨Code.memsetBase, 4 * 55⟩ textIv) hc) hsep }

/-- **A `memset(d, 0, n)` call**: the `jal` step `hjal` (from `jal_step`) into
`Fn.Memset.correct_zero`, run with the callee-saved registers `w` (whose pins
`hK` finds among the caller's), back at `ret` with the registers `Lr` (`hLr`,
`hKr`: from `ra`, `a0 = d` and `w`). -/
theorem memset_jal {pc tgt r ret : BitVec 64} {L L' Lr : GRegs} {m : Mem} {keep : GRegs}
    {outp : Array String} {d n : Nat} (w : Abi)
    (hjal : Triple (At pc L m keep outp) (At tgt ((1, r) :: L') m keep outp)) (htgt : tgt = Fn.Memset.entry)
    (hr : r = ret)
    (hL : ∀ p ∈ Fn.Memset.entryL ret d 0#64 n, p ∈ ((1, ret) :: L') ++ keep)
    (hK : ∀ p ∈ w.keep, p ∈ ((1, ret) :: L') ++ keep) (hret : ret.toNat % 4 = 0)
    (hP : Fn.Memset.Pre m d 0 n)
    (hLr : ∀ p ∈ Lr, p ∈ [(1, ret), (10, BitVec.ofNat 64 d)] ++ w.keep)
    (hKr : ∀ p ∈ keep, p ∈ [(1, ret), (10, BitVec.ofNat 64 d)] ++ w.keep) :
    Triple (At pc L m keep outp)
      (fun c => ∃ M', At ret Lr M' keep outp c ∧ Fn.Memset.Post m d n 0#8 M') := by
  subst htgt; rw [hr] at hjal
  exact Triple.seq hjal (Triple.conseq (Fn.Memset.correct_zero ret w outp m d n hret hP)
    (fun _ h => h.reshape hL hK) (fun _ ⟨M', hat, hp⟩ => ⟨M', hat.reshape hLr hKr, hp⟩))

end Tom.Machine

/-- `jal ra, target` at `pc` (`jal_step pc w imm L' hc [defs] [keepdefs]`). -/
syntax "jal_step " term:max ppSpace term:max ppSpace term:max ppSpace term:max ppSpace term:max
  " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]" : term
macro_rules
  | `(jal_step $pc $w $imm $L' $hc [$ds,*] [$ks,*]) => `(
      Tom.Machine.jal_at (pc := $pc) (w := $w) (imm := $imm) (L' := $L')
        (Tom.Machine.CodeAt.word $hc (a := ($pc : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
        (fun s h1 h2 h3 => Vsa.Sim.decodeW s h1 h2 h3)
        ⟨by decide, Vsa.Sim.fetchOK_of_le (by simp [Vsa.Sim.tohostAddr]), by decide⟩ (by decide)
        (by simp [$ds,*]) (by simp [Vsa.Sim.keysG]) (by simp [$ks,*, Vsa.Sim.sKeepL, Vsa.Sim.keysG]))
