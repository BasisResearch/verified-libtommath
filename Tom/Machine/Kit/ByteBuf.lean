import Tom.Machine.Kit.MeetHeap
import Tom.Machine.Kit.MemStore
import Tom.Spec.Mont

/-!
# Byte buffers over `St` (for `mp_to_radix`)

A caller's byte buffer (a string) has no kind of its own (`Kind`: RAM, snapshots, code, `mp_int`
structs and digit arrays): it is held as a snapshot region (`.frz B`) and read as the byte
function `bytesOf B s n` (`Tom/Spec`'s form: `ToRadixPost`, `Tape`). This file adds:

* `bytesOf`, `bytesOf_congr`, `bytesOf_store` (a byte store as `Mont.upd` of the byte function);
* `St.snapK`: an untracked RAM region re-read as the snapshot of the current memory (the entry
  of a buffer the contract gives as RAM);
* `St.unslotK`: a one-word digit slot (a callee's out-parameter, `mp_div_d`'s `*d`) forgotten back
  to RAM before a loop's back edge;
* `St.bytesOf`: a snapshot region's bytes are the current memory's;
* `Iv.upd_upd`: a site re-placed twice (a loop around an allocating call), for `St.congrL`.
-/

namespace Tom.Machine

open Vsa.Sim

/-- The bytes `[s, s + n)` of `B` as a byte function, `0` past `n`. -/
def bytesOf (B : Mem) (s n : Nat) (j : Nat) : Nat := if j < n then (bytesT1 B (s + j)).toNat else 0

theorem bytesOf_congr {B B' : Mem} {s n : Nat} (h : ∀ x, s ≤ x → x < s + n → B'[x]? = B[x]?) :
    bytesOf B' s n = bytesOf B s n := by
  funext j; unfold bytesOf; split
  · simp only [bytesT1]; rw [h (s + j) (by omega) (by omega)]
  · rfl

theorem bytesOf_store {B : Mem} {s n a k v : Nat} (ha : a = s + k) (hk : k < n) (hv : v < 256) :
    bytesOf (writeLog B [(a, 1, BitVec.ofNat 64 v)]) s n = Mont.upd (bytesOf B s n) k v := by
  subst ha
  funext j
  simp only [bytesOf, Mont.upd, writeLog_single, Vsa.Sim.bytesT1, getElem?_applyW_sb]
  by_cases e : j = k
  · subst e
    simp only [hk, if_true, Option.getD_some]
    simp [sbData, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt (show v < 2 ^ 64 by omega)]
  · simp only [e, if_false, show ¬ s + j = s + k by omega]

/-! ## State rules -/

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind} {m M : Mem}

/-- An untracked RAM region re-read as the snapshot of the current memory. -/
theorem St.snapK {T : Prop} (h : St ρ isW W κ m M) (r : ι) (hk : κ r = .ram)
    (k : St ρ isW W (Kind.set κ r (.frz M)) m M → T) : T := by
  refine k ⟨h.sound, fun r' => ?_, h.frm⟩
  unfold Kind.set
  by_cases hr : r' = r
  · subst hr; rw [if_pos rfl]
    have hw := (h.wit r').2; rw [hk] at hw
    exact ⟨trivial, hw, fun _ _ => rfl⟩
  · rw [if_neg hr]; exact h.wit r'

/-- A one-word digit slot (a callee's out-parameter) forgotten back to untracked RAM. -/
theorem St.unslotK {T : Prop} (h : St ρ isW W κ m M) (r : ι) {dp : Nat} {f : Nat → Nat}
    (hk : κ r = .mpD dp 1 f) (hl : (ρ r).Sub ⟨dp, 4⟩)
    (k : St ρ isW W (Kind.set κ r .ram) m M → T) : T := by
  refine k ⟨h.sound, fun r' => ?_, h.frm⟩
  unfold Kind.set
  by_cases hr : r' = r
  · subst hr; rw [if_pos rfl]
    have hw := (h.wit r').2; rw [hk] at hw
    exact ⟨trivial, Ram.sub hw.ram hl.1 (by have := hl.2; simp only at this; omega)⟩
  · rw [if_neg hr]; exact h.wit r'

/-- The bytes of a snapshot region `⟨s, n⟩` are the current memory's. -/
theorem St.bytesOf {r : ι} {F : Mem} {s n : Nat} (h : St ρ isW W κ m M) (hk : κ r = .frz F)
    (hl : ρ r = ⟨s, n⟩) : bytesOf M s n = bytesOf F s n := by
  have hw := (h.wit r).2; rw [hk, hl] at hw
  exact bytesOf_congr fun x h1 h2 => hw.2 x ⟨h1, h2⟩

end

/-- A site re-placed twice. -/
theorem Iv.upd_upd {ι : Type} [DecidableEq ι] (ρ : ι → Iv) (r : ι) (I J : Iv) :
    ∀ r', Iv.upd (Iv.upd ρ r I) r J r' = Iv.upd ρ r J r' := by
  intro r'; unfold Iv.upd; split <;> rfl

end Tom.Machine
