import Tom.Machine.Kit.Meet
import Tom.Machine.Kit.ArrDown
import Tom.Machine.Api.BinA

/-!
# Top-down digit loops over `St` (`Kit/Meet.lean`)

`St.seqOvl` is the store rule of a loop that counts up (`ovl g old i`). A loop
that counts down from `u - 1` to `0` (`mp_div_2d`'s bit loop) has written
`[x + 1, u)` when it is at `x`: its array kind is `ovlD g old (x + 1) u`
(`Kit/ArrDown.lean`), and one store of `g x` at element `x` makes it
`ovlD g old x u` (`St.seqOvlD`).

Also the `BinA` region family (`Api/BinA.lean`: two operands, `a` written under
`isWA`) as a kinded bundle (`BinA.kind`, `BinA.bundle`, `St.binA`, `Names`), for a
function `f(a, b)` that writes `a` and reads `b`.
-/

namespace Tom.Machine

open Vsa.Sim Vsa.Logic

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind} {m M : Mem}
  {pc pc' : BitVec 64} {L0 L L' K : GRegs} {o : Array String} {Q : Vsa.Machine.Config → Prop}

/-- **The top-down array step** (`ArrFrm.stepD` over `St`): a segment storing
`g x` into element `x` of the digit array `r` that holds `ovlD g old (x + 1) u`. -/
theorem St.seqOvlD (h : St ρ isW W κ m M) (r : ι) {dp n x u v : Nat} {g old : Nat → Nat}
    (hk : κ r = .mpD dp n (ovlD g old (x + 1) u))
    (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M [(dp + 4 * x, 4, BitVec.ofNat 64 v)]) K o))
    (hi : x < n) (hxu : x < u) (hv : v < 2 ^ 32) (hgv : v = g x)
    (k : ∀ M', St ρ isW W (Kind.set κ r (.mpD dp n (ovlD g old x u))) m M' → Triple (At pc' L' M' K o) Q)
    (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q := by
  have hf : (fun j => if j = x then v else ovlD g old (x + 1) u j) = ovlD g old x u := by
    funext j; simp only [ovlD]
    by_cases hj : j = x
    · subst hj; simp [hgv, hxu]
    · rw [if_neg hj]
      by_cases hl : x + 1 ≤ j ∧ j < u
      · rw [if_pos hl, if_pos (by omega)]
      · rw [if_neg hl, if_neg (by omega)]
  exact h.seqD r hk hseg hi hv (fun M' h' => k M' (by rw [← hf]; exact h')) hw hW hL

end

def BinA.kind (pa adp pb bdp : Nat) (a b : MpInt) : Api.BinA.R → Kind
  | .stk => .ram
  | .aS => .mpS pa adp a
  | .aD => .mpD adp a.alloc a.digit
  | .bS => .mpS pb bdp b
  | .bD => .mpD bdp b.alloc b.digit
  | .code => .code

theorem BinA.bundle {m : Mem} {F sp pa adp pb bdp : Nat} {a b : MpInt} (hra : MpAt m pa adp a)
    (hga : MpGeom pa adp a.alloc) (hrb : MpAt m pb bdp b) (hgb : MpGeom pb bdp b.alloc) (hrs : Ram (sp - F) F)
    (himg : Img m) : Bundle (Api.BinA.lay F sp pa adp pb bdp a b) (BinA.kind pa adp pb bdp a b) m
  | .stk => ⟨trivial, hrs⟩
  | .aS => ⟨Iv.sub_self _, Hdr.of_mpAt hra hga⟩
  | .aD => ⟨Iv.sub_self _, Dig.of_mpAt hra hga⟩
  | .bS => ⟨Iv.sub_self _, Hdr.of_mpAt hrb hgb⟩
  | .bD => ⟨Iv.sub_self _, Dig.of_mpAt hrb hgb⟩
  | .code => ⟨Iv.sub_self _, himg⟩

instance : Names Api.BinA.R := ⟨[.stk, .aS, .aD, .bS, .bD, .code]⟩

/-- The entry state of a two-operand function writing `a` (`isWA`) with an own frame of `f` bytes. -/
theorem St.binA {m : Mem} {F f sp pa adp pb bdp : Nat} {a b : MpInt} (hra : MpAt m pa adp a)
    (hga : MpGeom pa adp a.alloc) (hrb : MpAt m pb bdp b) (hgb : MpGeom pb bdp b.alloc) (hrs : Ram (sp - F) F)
    (himg : Img m) (hS : Sound (Api.BinA.lay F sp pa adp pb bdp a b) Api.BinA.isWA) (hf : f ≤ F) :
    St (Split.lay (Api.BinA.lay F sp pa adp pb bdp a b) .stk f) (Split.wr Api.BinA.isWA)
      [none, some .stk, some .aS, some .aD] (Split.kind (BinA.kind pa adp pb bdp a b) m) m m :=
  ⟨Split.sound hS rfl hf, Split.bundle (BinA.bundle hra hga hrb hgb hrs himg) rfl hf, Frm.refl _ _⟩

end Tom.Machine
