import Tom.Machine.Kit.MeetHeapN
import Tom.Machine.Kit.MeetHeapIris

/-!
# Multi-site calls on the Iris heap

`Kit/MeetHeapN.lean`'s state after a multi-site call is an ordinary `St`/`HP` pair, so
`Kit/MeetHeapIris.lean`'s bridge applies to it unchanged (`aheap_isHeap` at `hout`, `off_split`
for each region, `sound_split` for two `Sep` regions). The one new fact: the bytes of the
sites' placements `J s` (pairwise apart, `HPostN.apart`) split into one `blockOwn` per site
(`sites_split`): `mp_init_multi`'s `k` fresh blocks are `k` separate `blockOwn`s carved from
what it owned, as `alloc_mach` hands out one.
-/

namespace Tom.Machine.HeapIris

open Iris Iris.BI Iris.ProofMode VsaIris VsaIris.VsaHeap

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The sites' blocks, one `blockOwn` each. -/
def sitesOwn {R : Type} (J : R → Iv) : List R → IProp GF
  | [] => iprop(emp)
  | s :: ss => iprop(blockOwn (J s).base (J s).len ∗ sitesOwn J ss)

/-- **The sites' bytes are their blocks**: owning `D ⊇ ⋃ J s` splits into one `blockOwn` per
site and the rest. -/
theorem sites_split {R : Type} {m : Tom.Machine.Mem} (J : R → Iv) :
    ∀ (ss : List R) (D : Nat → Prop), ss.Pairwise (fun s t => (J s).Disj (J t)) →
      (∀ s ∈ ss, ∀ a, (J s).In a → D a) →
      memOwn (GF := GF) m D ⊢ sitesOwn J ss ∗ memOwn m (fun a => D a ∧ ¬ ∃ s ∈ ss, (J s).In a)
  | [], D, _, _ => by
    unfold sitesOwn
    exact (ownSet_iff (S := D) _ (fun a => ⟨fun h => ⟨h, fun ⟨_, hs, _⟩ => absurd hs List.not_mem_nil⟩,
      fun h => h.1⟩)).trans emp_sep.2
  | s :: ss, D, hpw, hD => by
    have ⟨hs, hpw'⟩ := List.pairwise_cons.1 hpw
    rw [show sitesOwn (GF := GF) J (s :: ss) = iprop(blockOwn (J s).base (J s).len ∗ sitesOwn J ss) from rfl]
    iintro Hm
    ihave ⟨H1, H2⟩ := ownSet_split D (J s).In _ $$ Hm
    ihave H1' := ownSet_iff (S := fun a => D a ∧ (J s).In a) (T := (J s).In) _
      (fun a => ⟨fun h => h.2, fun h => ⟨hD s (List.mem_cons_self ..) a h, h⟩⟩) $$ H1
    ihave Hb := region_blockOwn (J s) $$ H1'
    ihave ⟨H3, H4⟩ := sites_split J ss (fun a => D a ∧ ¬ (J s).In a) hpw' (fun t ht a ha =>
      ⟨hD t (List.mem_cons_of_mem _ ht) a ha, fun h' => by
        have := hs t ht; unfold Iv.Disj Disj Iv.In at *; omega⟩) $$ H2
    isplitl [Hb H3]
    · isplitl [Hb]
      · iexact Hb
      · iexact H3
    · iapply ownSet_iff (S := fun a => (D a ∧ ¬ (J s).In a) ∧ ¬ ∃ t ∈ ss, (J t).In a) _ (fun a =>
        ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, fun ⟨t, ht, hx⟩ => (List.mem_cons.1 ht).elim
          (fun e => h2 (e ▸ hx)) (fun ht' => h3 ⟨t, ht', hx⟩)⟩,
         fun ⟨h1, h2⟩ => ⟨⟨h1, fun hx => h2 ⟨s, List.mem_cons_self .., hx⟩⟩,
          fun ⟨t, ht, hx⟩ => h2 ⟨t, List.mem_cons_of_mem _ ht, hx⟩⟩⟩) $$ H4

end Tom.Machine.HeapIris
