import Tom.Machine.Kit.Run
import Tom.Machine.Api.StdHeapFn

/-!
# One re-placed site: the contract's post from the final state

The exits of an allocating function whose contract re-places one site (`HPost`, `Kit/MeetHeap.lean`),
once for every such function (they were per-function helpers in `Fn/MpDivG5K.lean`):

* `HPost.inPlace`: the site kept where it was (`MP_MEM`, or written in place), the heap as before;
* `HPost.fresh'`: the site moved to a block fresh for the heap before; the allocator's footprint
  after is the one before or the site, because the other written regions are off the arena
  (`OffHeap`: the stack, the structs).
-/

namespace Tom.Machine

open Vsa.Sim Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

section
variable {R : Type} [DecidableEq R] {lay : R → Iv} {ws : List R} {site : R} {out : R → Kind} {J : Iv}
  {hin hout : List (Nat × Nat)} {m M : Mem}

/-- An allocator footprint byte is in no off-arena range. -/
theorem foot_offHeap {H : List (Nat × Nat)} {a b n : Nat} (hf : Foot H a) (ho : OffHeap b n) (h1 : b ≤ a)
    (h2 : a < b + n) : False := by
  have eL : allocLo = 0x800188a0 := rfl; have eE : heapEnd = 0x87800000 := rfl
  have eS : heapStart = 0x80019d10 := rfl
  unfold OffHeap at ho
  rcases hf with hg | ⟨h3, h4, _⟩
  · unfold Global at hg; omega
  · omega

/-- **The site in place**: written there or untouched, the heap's blocks as before. -/
theorem HPost.inPlace (hJ : J = lay site) (hH : hout = hin)
    (hw : ∀ r, r ∈ ws → r ≠ site → (out r).Fits (lay r) ∧ (out r).Wit (lay r) M)
    (hs : (out site).Fits (lay site) ∧ (out site).Wit (lay site) M) (hfr : HFrm lay ws hin m M)
    (hh : AHeap M hin) (hoff : Off (lay site) hin) : HPost lay ws site out J hin hout m M := by
  subst hJ hH; exact ⟨hw, hs, .keep, hfr, hh, fun _ h => .inl h, hoff⟩

/-- **The site moved to a fresh block** `⟨q, n⟩` (in front of the heap's other blocks `T`), the other
written regions off the arena. -/
theorem HPost.fresh' {q n : Nat} {T : List (Nat × Nat)} (hJ : J = ⟨q, n⟩) (hH : hout = (q, n) :: T)
    (hw : ∀ r, r ∈ ws → r ≠ site → (out r).Fits (lay r) ∧ (out r).Wit (lay r) M)
    (hs : (out site).Fits ⟨q, n⟩ ∧ (out site).Wit ⟨q, n⟩ M) (hfa : Fresh hin q n) (hn : 0 < n)
    (hfr : HFrm lay ws hin m M) (hh : AHeap M ((q, n) :: T))
    (hfoot : ∀ a, Foot ((q, n) :: T) a → InAny lay ws a ∨ Foot hin a)
    (hof : ∀ r, r ∈ ws → r ≠ site → OffHeap (lay r).base (lay r).len) (hoff : Off ⟨q, n⟩ ((q, n) :: T)) :
    HPost lay ws site out J hin hout m M := by
  subst hJ hH
  refine ⟨hw, hs, .fresh hfa hn, hfr, hh, fun a ha => ?_, hoff⟩
  rcases hfoot a ha with h | h
  · obtain ⟨r, hr, hra⟩ := h.exists
    by_cases e : r = site
    · subst e; exact .inr hra
    · exact (foot_offHeap ha (hof r hr e) hra.1 hra.2).elim
  · exact .inl h

end

end Tom.Machine
