import Tom.Machine.Kit.Run
import Tom.Machine.Kit.Copy
import Tom.Machine.Kit.Bytes

/-!
# A struct copied into an own-frame snapshot

`s_mp_balance_mul` copies the shorter operand's struct onto its stack (`B = *b`, three `ld`/`sd`
pairs) and passes `&B` to `mp_mul`: the frame piece holding the copy is a snapshot (`.frz F`,
its stores tracked by `St.seqWs`), whose bytes are the source's header. `Hdr.copy3` (doublewords
in address order) and `Hdr.copy3d` (the `dp` doubleword first) read the header off the log;
`St.frzS` re-kinds the piece as the struct `.mpS q dp a` (its witness reads only its 24 bytes).
-/

namespace Tom.Machine

open Vsa.Sim

/-- The copy's header, the doublewords stored in address order. -/
theorem Hdr.copy3 {m M : Mem} {p q q8 q16 dp : Nat} {a : MpInt} (h : Hdr M p dp a) (hg : MpGeom q dp a.alloc)
    (e8 : q8 = q + 8) (e16 : q16 = q + 16) :
    Hdr (writeLog m [(q, 8, bytesT8 M p), (q8, 8, bytesT8 M (p + 8)), (q16, 8, BitVec.ofNat 64 dp)]) q dp a := by
  subst e8 e16
  refine { used := ?_, alloc := ?_, sign := ?_, dpv := ?_, geom := hg }
  · have := bytesT4_log_sd [(q, 8, bytesT8 M p), (q + 8, 8, bytesT8 M (p + 8)), (q + 16, 8, BitVec.ofNat 64 dp)]
      m M 0 q p 0 (by decide) rfl (by simp [OutLRange] <;> omega)
    simp only [Nat.add_zero] at this; rw [this]; exact h.used
  · have := bytesT4_log_sd [(q, 8, bytesT8 M p), (q + 8, 8, bytesT8 M (p + 8)), (q + 16, 8, BitVec.ofNat 64 dp)]
      m M 0 q p 4 (by decide) rfl (by simp [OutLRange] <;> omega)
    rw [this]; exact h.alloc
  · have := bytesT4_log_sd [(q, 8, bytesT8 M p), (q + 8, 8, bytesT8 M (p + 8)), (q + 16, 8, BitVec.ofNat 64 dp)]
      m M 1 (q + 8) (p + 8) 0 (by decide) rfl (by simp [OutLRange] <;> omega)
    simp only [Nat.add_zero] at this; rw [this]; exact h.sign
  · rd_log

/-- The copy's header, the `dp` doubleword stored first. -/
theorem Hdr.copy3d {m M : Mem} {p q q8 q16 dp : Nat} {a : MpInt} (h : Hdr M p dp a) (hg : MpGeom q dp a.alloc)
    (e8 : q8 = q + 8) (e16 : q16 = q + 16) :
    Hdr (writeLog m [(q16, 8, BitVec.ofNat 64 dp), (q, 8, bytesT8 M p), (q8, 8, bytesT8 M (p + 8))]) q dp a := by
  subst e8 e16
  refine { used := ?_, alloc := ?_, sign := ?_, dpv := ?_, geom := hg }
  · have := bytesT4_log_sd [(q + 16, 8, BitVec.ofNat 64 dp), (q, 8, bytesT8 M p), (q + 8, 8, bytesT8 M (p + 8))]
      m M 1 q p 0 (by decide) rfl (by simp [OutLRange] <;> omega)
    simp only [Nat.add_zero] at this; rw [this]; exact h.used
  · have := bytesT4_log_sd [(q + 16, 8, BitVec.ofNat 64 dp), (q, 8, bytesT8 M p), (q + 8, 8, bytesT8 M (p + 8))]
      m M 1 q p 4 (by decide) rfl (by simp [OutLRange] <;> omega)
    rw [this]; exact h.alloc
  · have := bytesT4_log_sd [(q + 16, 8, BitVec.ofNat 64 dp), (q, 8, bytesT8 M p), (q + 8, 8, bytesT8 M (p + 8))]
      m M 2 (q + 8) (p + 8) 0 (by decide) rfl (by simp [OutLRange] <;> omega)
    simp only [Nat.add_zero] at this; rw [this]; exact h.sign
  · rd_log

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind} {m M : Mem}

/-- **A snapshot piece re-read as a struct**: its snapshot holds an `mp_int` header at its base. -/
theorem St.frzS (h : St ρ isW W κ m M) (r : ι) {F : Mem} (hk : κ r = .frz F) {p dp : Nat} {a : MpInt}
    (hs : Iv.Sub ⟨p, 24⟩ (ρ r)) (hd : Hdr F p dp a) : St ρ isW W (Kind.set κ r (.mpS p dp a)) m M := by
  refine ⟨h.sound, fun r' => ?_, h.frm⟩
  unfold Kind.set
  by_cases hr : r' = r
  · subst hr; simp only [if_true]
    have hw := (h.wit r').2; rw [hk] at hw
    have hf : (Kind.mpS p dp a).Fits (ρ r') := hs
    exact ⟨hf, Kind.reads (r := r') hf F M (fun x hx => hw.2 x (by
      rcases hx with hx | hx
      · exact hx
      · exact hx.elim)) hd⟩
  · simp only [hr, if_false]; exact h.wit r'

end

end Tom.Machine
