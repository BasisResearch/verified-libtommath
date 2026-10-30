import Tom.Machine.Kit.Run
import Tom.Machine.Kit.DOut

/-!
# A contract region re-placed by a callee: the layout given back and the layers normalised

Two growing callers re-place one of their own regions by a callee and then need the layout with the
region at its new place:
* a tail call that runs on the whole stack after the re-placement (`mp_reduce_setup(&mu, P)`: `mp_2expt`
  re-places `mu`'s digits, then `mp_div(mu, P, mu, NULL)` is tail-called): the state is given back over
  `Iv.upd lay r J` (`St.flat`'s target, gen_asm tail option `"flat": {"lay", "ins"}`) — soundness
  `Split.sound_upd`, the pieces inside it `Split.sub_upd`, the heap checkpoint `HP.unsplit_upd`;
* a loop whose head holds two re-placed regions, one placed twice more along a pass and the other once
  (`mp_reduce_2k_l`: `q` by `mp_div_2d` and `mp_mul`, `a` by `s_mp_add`): `Iv.upd_back1`, `Iv.upd_back2`
  collapse the layers to the head's two (gen_asm jump options `"st"`, `"hp"`).
-/

namespace Tom.Machine

section
variable {R : Type} [DecidableEq R] {L : R → Iv} {isW : R → Bool} {s r : R} {f : Nat} {J : Iv}

theorem Sep.comm (isW : R → Bool) (a b : R) : Sep isW a b = Sep isW b a := by
  unfold Sep; by_cases h : a = b
  · subst h; rfl
  · simp [h, Ne.symm h, Bool.or_comm]

/-- The pieces with `r` re-placed lie in the layout with `r` re-placed (`e` the pieces' regions). -/
theorem Split.sub_upd {e : Option R → R} (he0 : e none = s) (he : ∀ t, e (some t) = t) (hrs : r ≠ s)
    (hf : f ≤ (L s).len) (y : Option R) : (Iv.upd (Split.lay L s f) (some r) J y).Sub (Iv.upd L r J (e y)) := by
  cases y with
  | none =>
    rw [he0]; show (if (none : Option R) = some r then J else _).Sub (if s = r then J else L s)
    rw [if_neg (by simp), if_neg (Ne.symm hrs)]; exact Split.sub_none hf
  | some t =>
    rw [he]; show (if some t = some r then J else _).Sub (if t = r then J else L t)
    by_cases ht : t = r
    · subst ht; rw [if_pos rfl, if_pos rfl]; exact Iv.sub_self _
    · rw [if_neg (by simpa using ht), if_neg ht]; exact Split.sub_some t

/-- **Sound, given back**: the layout with `r` re-placed at a nonempty `J`. -/
theorem Split.sound_upd (hrs : r ≠ s) (hJ : 0 < J.len) (hf : f ≤ (L s).len) (hS : Sound L isW)
    (h : Sound (Iv.upd (Split.lay L s f) (some r) J) (Split.wr isW)) : Sound (Iv.upd L r J) isW := by
  have key : ∀ t, t ≠ r → Sep isW r t = true → J.Disj (L t) := by
    intro t htr hsep
    have h2 := h (some r) (some t) (by simpa [Sep, Split.wr, htr, Ne.symm htr] using hsep)
    have e1 : Iv.upd (Split.lay L s f) (some r) J (some r) = J := if_pos rfl
    have e2 : Iv.upd (Split.lay L s f) (some r) J (some t) = Split.lay L s f (some t) :=
      if_neg (by simpa using htr)
    rw [e1, e2] at h2
    by_cases hts : t = s
    · subst hts
      have h1 := h (some r) none (by simp [Sep, Split.wr])
      have e3 : Iv.upd (Split.lay L t f) (some r) J none = Split.lay L t f none := if_neg (by simp)
      rw [e1, e3] at h1
      simp only [Split.lay, ↓reduceIte, Iv.Disj, Disj] at h1 h2
      unfold Iv.Disj Disj; omega
    · simpa [Split.lay, hts] using h2
  intro a b hab
  show (if a = r then J else L a).Disj (if b = r then J else L b)
  by_cases ha : a = r <;> by_cases hb : b = r
  · subst ha hb; simp [Sep] at hab
  · subst ha; rw [if_pos rfl, if_neg hb]; exact key b hb hab
  · subst hb; rw [if_neg ha, if_pos rfl]
    exact Disj.symm (key a ha (by rw [Sep.comm]; exact hab))
  · rw [if_neg ha, if_neg hb]; exact hS a b hab

/-- **The heap checkpoint, given back** over the layout with `r` re-placed. -/
theorem HP.unsplit_upd {H0 H : List (Nat × Nat)} {Wr0 : Nat → Prop} {m0 m : Mem} (hrs : r ≠ s)
    (hs : isW s = true) (hf : f ≤ (L s).len) (hram : Ram (L s).base (L s).len)
    (h : HP (Iv.upd (Split.lay L s f) (some r) J) (Split.wr isW) H0 H Wr0 m0 m) :
    HP (Iv.upd L r J) isW H0 H Wr0 m0 m := by
  have es : Iv.upd (Split.lay L s f) (some r) J (some s) = ⟨(L s).base, (L s).len - f⟩ := by
    show (if some s = some r then J else Split.lay L s f (some s)) = _
    rw [if_neg (by simpa using Ne.symm hrs)]; simp [Split.lay]
  have en : Iv.upd (Split.lay L s f) (some r) J none = ⟨(L s).base + (L s).len - f, f⟩ := if_neg (by simp)
  have ex : ∀ t, t ≠ s → Iv.upd (Split.lay L s f) (some r) J (some t) = Iv.upd L r J t := by
    intro t ht
    show (if some t = some r then J else Split.lay L s f (some t)) = if t = r then J else L t
    by_cases htr : t = r
    · subst htr; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (by simpa using htr), if_neg htr]; simp [Split.lay, ht]
  have eu : Iv.upd L r J s = L s := if_neg (Ne.symm hrs)
  refine ⟨h.heap, h.frm0, h.foot, fun t ht a ha => ?_, fun t => ?_, fun t ht => ?_⟩
  · by_cases hts : t = s
    · subst hts; rw [eu] at ha
      by_cases hlo : a < (L t).base + (L t).len - f
      · exact h.cov (some t) hs a (by rw [es]; unfold Iv.In at *; simp only; omega)
      · exact h.cov none rfl a (by rw [en]; unfold Iv.In at *; simp only; omega)
    · exact h.cov (some t) ht a (by rw [ex t hts]; exact ha)
  · by_cases hts : t = s
    · subst hts; rw [eu]
      have o1 := h.off (some t); have o2 := h.off none
      rw [es] at o1; rw [en] at o2
      exact ⟨o1.lo, fun a ha => by
          by_cases hlo : a < (L t).base + (L t).len - f
          · exact o1.pt a (by unfold Iv.In at *; simp only; omega)
          · exact o2.pt a (by unfold Iv.In at *; simp only; omega),
        fun h0 => o1.edge (by simp only; omega)⟩
    · rw [← ex t hts]; exact h.off (some t)
  · by_cases hts : t = s
    · subst hts; rw [eu]; exact hram
    · rw [← ex t hts]; exact h.ram (some t) ht

end



section
variable {ι : Type} [DecidableEq ι] (ρ : ι → Iv) {r s : ι}

theorem Iv.upd_back1 (h : r ≠ s) (J0 A0 J2 : Iv) :
    ∀ y, Iv.upd (Iv.upd (Iv.upd ρ r J0) s A0) r J2 y = Iv.upd (Iv.upd ρ r J2) s A0 y := by
  intro y; unfold Iv.upd
  by_cases hs : y = s
  · subst hs; simp [Ne.symm h]
  · by_cases hr : y = r
    · subst hr; simp [hs]
    · simp [hs, hr]

theorem Iv.upd_back2 (h : r ≠ s) (J0 A0 J3 A3 : Iv) :
    ∀ y, Iv.upd (Iv.upd (Iv.upd (Iv.upd ρ r J0) s A0) r J3) s A3 y = Iv.upd (Iv.upd ρ r J3) s A3 y := by
  intro y; unfold Iv.upd
  by_cases hs : y = s
  · simp [hs]
  · by_cases hr : y = r
    · subst hr; simp [hs]
    · simp [hs, hr]

end

end Tom.Machine
