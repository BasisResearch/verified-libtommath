import Tom.Machine.Kit.Bridge
import Tom.Machine.Api.StdHeap

/-!
# A callee's allocating contract over a deeper stack

Two contracts of one routine whose layouts differ only in one written RAM region (the stack), the
second's containing the first's: the entry hypotheses go from the wider layout to the narrower
(`Entry.sub`) and the allocating post back. `Triple.widenCv` strings them together (reading the callee's results through a map): a contract proved over a
shallow stack is one over any deeper stack (`mp_sqr(a, a)` above `KARATSUBA_SQR_CUTOFF` under the
comba path's depth, `Fn/MpSqrAGClosed.lean`; the slow paths of `s_mp_mul_digs` and
`s_mp_mul_high_digs` under their fast paths' depth, `Fn/SMpMulDigsAGClosed.lean`).
-/

namespace Tom.Machine

open Vsa.Logic Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

section
variable {ι : Type} [DecidableEq ι] {lay lay' : ι → Iv}

/-- **An allocating post over a wider written region** (a callee's post over the caller's
deeper stack): the layouts equal but at `s`, written, not the site, and containing the old one. -/
theorem HPost.widen {ws : List ι} {site : ι} {out : ι → Kind}
    {J : Iv} {hin hout : List (Nat × Nat)} {m M : Mem} (s : ι) (hs : s ≠ site)
    (hl : ∀ r, r ≠ s → lay' r = lay r) (hsub : (lay s).Sub (lay' s))
    (hw : (out s).Fits (lay' s) ∧ (out s).Wit (lay' s) M)
    (h : HPost lay ws site out J hin hout m M) : HPost lay' ws site out J hin hout m M where
  wit r hr hrs := by
    by_cases e : r = s
    · subst e; exact hw
    · rw [hl r e]; exact h.wit r hr hrs
  wsite := h.wsite
  place := by rw [hl site (Ne.symm hs)]; exact h.place
  frame a ha := h.frame a fun h' => ha (h'.imp (fun hi => by
    obtain ⟨w, hw', hx⟩ := hi.exists
    refine InAny.of_mem hw' ?_
    by_cases e : w = s
    · subst e; unfold Iv.Sub Iv.In at *; omega
    · rw [hl w e]; exact hx) id)
  heap := h.heap
  foot a ha := (h.foot a ha).imp id fun hi => by rw [hl site (Ne.symm hs)]; exact hi
  off := h.off

/-- **The entry hypotheses on a narrower layout**: the layouts equal but at `s`, a RAM region
inside the wider one's. -/
theorem Entry.sub {isW : ι → Bool} {kind : ι → Kind} {m : Mem} {H : List (Nat × Nat)} (s : ι)
    (hl : ∀ r, r ≠ s → lay r = lay' r) (hsub : (lay s).Sub (lay' s)) (hk : kind s = .ram)
    (hpos : 0 < (lay s).len) (hS : Sound lay' isW) (hB : Bundle lay' kind m)
    (hoff : ∀ r, Off (lay' r) H) : Sound lay isW ∧ Bundle lay kind m ∧ ∀ r, Off (lay r) H := by
  have hsr : ∀ r, (lay r).Sub (lay' r) := fun r => by
    by_cases e : r = s
    · subst e; exact hsub
    · rw [hl r e]; exact Iv.sub_self _
  refine ⟨fun r t h => ?_, Bundle.pull id hB hsr (fun _ => rfl) (fun r => ?_), fun r => ?_⟩
  · have hd := hS r t h; have h1 := hsr r; have h2 := hsr t
    unfold Iv.Disj Tom.Machine.Disj Iv.Sub at *; omega
  · by_cases e : r = s
    · subst e; rw [hk]; trivial
    · rw [hl r e]; exact (hB r).1
  · by_cases e : r = s
    · subst e; exact (hoff r).sub hsub (.inl hpos)
    · rw [hl r e]; exact hoff r

/-- **A contract over a shallow stack is one over a deeper stack, its results renamed**: the callee's
run from the narrower entry hypotheses (`h`, first, so that it fixes the narrow layout and the result
type `O`), each result `o` read as `cv o` (`MP_MEM`'s `none` as `(false, a->dp, a)`; `cv := id` when the
types agree), the post widened at the RAM region `s`. -/
theorem Triple.widenCv {isW : ι → Bool} {kind : ι → Kind} {ws : List ι} {site : ι} {O X : Type}
    {outO : O → ι → Kind} {siteO : O → Iv} {houtO : O → List (Nat × Nat)}
    {out : X → ι → Kind} {site' : X → Iv} {hin : List (Nat × Nat)} {hout : X → List (Nat × Nat)} {m : Mem}
    {pre : Vsa.Machine.Config → Prop} {AO : O → Mem → Vsa.Machine.Config → Prop} {BO : O → Prop}
    {A : X → Mem → Vsa.Machine.Config → Prop} {B : X → Prop}
    (h : Sound lay isW → Bundle lay kind m → (∀ r, Off (lay r) hin) →
      Triple pre (fun cf => ∃ o M, AO o M cf ∧ BO o ∧ HPost lay ws site (outO o) (siteO o) hin (houtO o) m M))
    (cv : O → X) (hA : ∀ o M cf, AO o M cf → A (cv o) M cf) (hB : ∀ o, BO o → B (cv o))
    (ho : ∀ o, outO o = out (cv o)) (hsi : ∀ o, siteO o = site' (cv o)) (hho : ∀ o, houtO o = hout (cv o))
    (s : ι) (hs : s ≠ site) (hl : ∀ r, r ≠ s → lay r = lay' r) (hsub : (lay s).Sub (lay' s)) (hk : kind s = .ram)
    (hr : ∀ x, out x s = .ram) (hpos : 0 < (lay s).len) (hS : Sound lay' isW) (hBd : Bundle lay' kind m)
    (hoff : ∀ r, Off (lay' r) hin) :
    Triple pre (fun cf => ∃ x M, A x M cf ∧ B x ∧ HPost lay' ws site (out x) (site' x) hin (hout x) m M) := by
  obtain ⟨hS', hB', hoff'⟩ := Entry.sub s hl hsub hk hpos hS hBd hoff
  refine Triple.rmap (fun cf ⟨o, M, ha, hb, hp⟩ => ⟨cv o, M, hA o M cf ha, hB o hb, ?_⟩) (h hS' hB' hoff')
  rw [ho, hsi, hho] at hp
  have hw : (out (cv o) s).Fits (lay' s) ∧ (out (cv o) s).Wit (lay' s) M := by
    have := (hBd s).2; rw [hk] at this; rw [hr]; exact ⟨trivial, this⟩
  exact HPost.widen s hs (fun r e => (hl r e).symm) hsub hw hp

end

/-- A stack residue for a shallower callee. -/
theorem Std.StkRes.mono {sp F G : Nat} (h : Std.StkRes sp F) (hG : G ≤ F) : Std.StkRes sp G :=
  ⟨h.al, by have := h.lo; omega, h.hi⟩

/-- The shallower callee's stack inside the deeper one's. -/
theorem Std.StkRes.sub {sp F G : Nat} (h : Std.StkRes sp F) (hG : G ≤ F) : Iv.Sub ⟨sp - G, G⟩ ⟨sp - F, F⟩ := by
  have := h.lo; unfold Iv.Sub; dsimp only; omega

end Tom.Machine
