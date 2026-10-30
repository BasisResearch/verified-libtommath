import Tom.Machine.Kit.Run
import Tom.Machine.Kit.Grow

/-!
# Several heap temporaries beside a contract's regions

A function that allocates temporaries (Karatsuba squaring: six) runs over the contract's regions
plus the temporaries' digit arrays, laid at `Iv.nil` at the entry. The facts every such function
needs, once (they were per-function helpers in `Fn/KSqrG5K.lean`, `Fn/KSqrAG5K.lean`):

* `Bundle.lo`: every region of a bundle with exact layouts (`Kind.Exact`: a struct at its pointer, a
  digit array at its base, the code at `textBase`) lies at or above the RAM base;
* `Site.soundN`: `n` allocation sites (`Site.lay` `n` times) are sound beside a sound layout, and a
  region type naming them is sound by a renaming (`Sound.pull`; one lemma for every `n`,
  it replaced `Site.sound4` … `sound9`);
* `Fresh.mono`, `Place.drop`: a placement among more heap blocks is one among fewer (the temporaries'
  blocks dropped from the list behind the destination's); `fresh_of_place`: a re-placed block is fresh
  for what the old one was fresh for.
-/

namespace Tom.Machine

open Vsa.Sim Tom.Machine.Code Tom.Machine.Api.Alloc

/-- A kind's region placed exactly where its witness says. -/
def Kind.Exact : Kind → Iv → Prop
  | .ram, _ | .frz _, _ => True
  | .code, I => I.base = textBase
  | .mpS p _ _, I => I.base = p
  | .mpD dp _ _, I => I.base = dp

theorem Kind.lo {k : Kind} {I : Iv} {m : Mem} (hw : k.Wit I m) (hx : k.Exact I) : 0x80000000 ≤ I.base := by
  cases k with
  | ram => exact hw.lo_ge
  | frz _ => exact hw.1.lo_ge
  | code => rw [show I.base = textBase from hx]; decide
  | mpS p dp a => rw [show I.base = p from hx]; exact (Hdr.geom hw).st.lo_ge
  | mpD dp n f => rw [show I.base = dp from hx]; exact hw.ram.lo_ge

/-- **Every region of an exact bundle is RAM-based** (`hx` by `bundle_exact`). -/
theorem Bundle.lo {ι : Type} {ρ : ι → Iv} {κ : ι → Kind} {m : Mem} (hB : Bundle ρ κ m)
    (hx : ∀ r, (κ r).Exact (ρ r)) (r : ι) : 0x80000000 ≤ (ρ r).base :=
  Kind.lo (hB r).2 (hx r)

/-- A closed region type's layout is exact, region by region. -/
macro "bundle_exact" : tactic => `(tactic| (intro r; cases r <;> first | exact rfl | exact True.intro))

/-- `n` nested `Option`s over `R`: a layout with `n` allocation sites beside `R`'s regions, the
sites outermost first (`none`, `some none`, …). -/
def OptN : Nat → Type → Type
  | 0, R => R
  | n + 1, R => Option (OptN n R)

instance OptN.decEq : (n : Nat) → (R : Type) → [DecidableEq R] → DecidableEq (OptN n R)
  | 0, _, inst => inst
  | n + 1, R, _ => @Option.instDecidableEq (OptN n R) (OptN.decEq n R)

/-- `Site.lay` `n` times. -/
def Site.layN {R : Type} : (n : Nat) → (R → Iv) → OptN n R → Iv
  | 0, ρ => ρ
  | n + 1, ρ => Site.lay (Site.layN n ρ)

/-- `Site.wr` `n` times. -/
def Site.wrN {R : Type} : (n : Nat) → (R → Bool) → OptN n R → Bool
  | 0, w => w
  | n + 1, w => Site.wr (Site.wrN n w)

theorem Site.soundN_aux {R : Type} [DecidableEq R] {ρ : R → Iv} {isW : R → Bool} (hS : Sound ρ isW)
    (hlo : ∀ r, 0x80000000 ≤ (ρ r).base) :
    ∀ n, Sound (Site.layN n ρ) (Site.wrN n isW) ∧ ∀ x, 0x80000000 ≤ (Site.layN n ρ x).base
  | 0 => ⟨hS, hlo⟩
  | n + 1 => have ih := Site.soundN_aux hS hlo n; ⟨Site.sound ih.1 ih.2, Site.lo_all ih.2⟩

/-- **`n` allocation sites** beside a sound layout, named by a region type `ι` through `f` (the
generated `soundG` of a function with `n` heap temporaries; it replaces `Site.sound4` … `sound9`). -/
theorem Site.soundN {R ι : Type} [DecidableEq R] [DecidableEq ι] (n : Nat) {ρ : R → Iv} {isW : R → Bool}
    {σ : ι → Iv} {isW' : ι → Bool} (hS : Sound ρ isW) (hlo : ∀ r, 0x80000000 ≤ (ρ r).base)
    (f : ι → OptN n R) (ks : List ι) (hks : ∀ k, k ∈ ks) (hsub : ∀ k, (σ k).Sub (Site.layN n ρ (f k)))
    (hsep : SepPres (Site.wrN n isW) isW' f ks = true := by decide) : Sound σ isW' :=
  Sound.pull f ks hks (Site.soundN_aux hS hlo n).1 hsub hsep

theorem _root_.Tom.Machine.Api.Alloc.Fresh.mono {H H' : List (Nat × Nat)} {q n : Nat} (h : Fresh H q n)
    (hs : ∀ e ∈ H', e ∈ H) : Fresh H' q n :=
  { h with disj := fun e he => h.disj e (hs e he) }

/-- A placement for more blocks is one for fewer (the temporaries' blocks dropped). -/
theorem Place.drop {e : Nat × Nat} {T H : List (Nat × Nat)} {I J : Iv}
    (h : Place (e :: (T ++ H)) I J) : Place (e :: H) I J := by
  cases h with
  | nil => exact .nil
  | keep => exact .keep
  | fresh hf hn => exact .fresh (hf.mono fun x hx => by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ hx)) hn
  | @regrow H' _ _ hf hn hH =>
    obtain ⟨h1, h2⟩ := List.cons.inj hH
    subst h2
    exact .regrow (hf.mono fun x hx => List.mem_append_right _ hx) hn (by rw [h1])

/-- A re-placed block (`mp_mul_2d(&x)`, growing) is fresh for what `x`'s old block was fresh for. -/
theorem fresh_of_place {H0 Hx : List (Nat × Nat)} {q0 n0 q1 n1 : Nat} (hsub : ∀ e ∈ H0, e ∈ Hx)
    (hp : Place ((q0, n0) :: Hx) ⟨q0, n0⟩ ⟨q1, n1⟩) (hf0 : Fresh H0 q0 n0) (hn1 : 0 < n1) : Fresh H0 q1 n1 := by
  cases hp with
  | keep => exact hf0
  | fresh hf _ => exact hf.mono fun e he => List.mem_cons_of_mem _ (hsub e he)
  | regrow hf _ hH => simp at hH; obtain ⟨_, rfl⟩ := hH; exact hf.mono hsub
  | nil => simp at hn1

end Tom.Machine
