import Tom.Machine.Kit.MeetHeap

/-!
# A destination re-placed along a chain of calls

An algorithm whose destination (`b` of `s_mp_toom_sqr`, `c` of `s_mp_toom_mul`, `a` in place) is
passed to many calls, each of which may re-place its digits, while the contract's post speaks of the
placement from the entry's block. `DOut mg n0 I H x` is what the code leaves in it (`x = (ok, q, c')`):
shaped with live digits, valid with magnitude `mg` on `MP_OKAY`, its digits placed from `I` (the
entry's block) for the heap blocks `H`, grown from `n0` digits. `Api.SqrAlg.Out` is `DOut` at `|a|²`.
The lemmas carry it along, once (they were per-function helpers: `TQ.next` in `Fn/ToomMulG5K.lean`,
`TQA.next` in `Fn/ToomMulAG5K.lean`, `QA.next` in `Fn/ToomSqrAG5K.lean`, `SqrAlg.Q.next` in
`Kit/Replace.lean`):

* `Place.trans`: a placement after a placement (the second over the first's block and more blocks);
* `DOut.next` (`DOut.next0` with nothing to grow from), `DOut.same`, `DOut.fin`: after a call that
  re-placed the destination (behind the temporaries' blocks `T`), after an in-place change of the same
  size (`mp_div_2(b, b)`), and at the end (valid with the magnitude).
-/

namespace Tom.Machine

open Tom.Machine.Api.Alloc

theorem _root_.Tom.Machine.Api.Alloc.Fresh.mono {H H' : List (Nat × Nat)} {q n : Nat} (h : Fresh H q n)
    (hs : ∀ e ∈ H', e ∈ H) : Fresh H' q n :=
  { h with disj := fun e he => h.disj e (hs e he) }

/-- **A placement after a placement** (the second over the first's block and more blocks). -/
theorem Place.trans {I0 J K : Iv} {H L : List (Nat × Nat)}
    (h1 : Place ((I0.base, I0.len) :: H) I0 J) (hs : ∀ e ∈ H, e ∈ L)
    (h2 : Place ((J.base, J.len) :: L) J K) : Place ((I0.base, I0.len) :: H) I0 K := by
  cases h2 with
  | nil => exact .nil
  | keep => exact h1
  | fresh hf hn =>
    exact .regrow (hf.mono fun x hx => List.mem_cons_of_mem _ (hs x hx)) hn rfl
  | @regrow H' _ _ hf hn hH =>
    obtain ⟨_, h2⟩ := List.cons.inj hH
    subst h2
    exact .regrow (hf.mono fun x hx => hs x hx) hn rfl

/-- What the code leaves in a destination (`x = (ok, q, c')`) whose digits were at `I` (`n0` digits)
at the entry, for the heap blocks `H`. -/
structure DOut (mg n0 : Nat) (I : Iv) (H : List (Nat × Nat)) (x : Bool × Nat × MpInt) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  /-- `MP_OKAY`: valid with magnitude `mg`. -/
  valid : x.1 = true → x.2.2.Valid
  mag : x.1 = true → x.2.2.mag = mg
  /-- Where the digits are (`HPost.place`, restated for a caller that passes the site on). -/
  place : Place H I ⟨x.2.1, 4 * x.2.2.alloc⟩
  /-- The digits only grow (from `n0`). -/
  grow : n0 ≤ x.2.2.alloc

namespace DOut
variable {mg n0 : Nat} {I0 : Iv} {H : List (Nat × Nat)}

/-- After a call that re-placed the destination (`T`: the temporaries' blocks in front of it). -/
theorem next {q q' : Nat} {b b' : MpInt} {T : List (Nat × Nat)}
    (h : DOut mg n0 I0 ((I0.base, I0.len) :: H) (false, q, b)) (hs : b'.Shape) (hpos : 0 < b'.alloc)
    (hpl : Place ((q, 4 * b.alloc) :: (T ++ H)) ⟨q, 4 * b.alloc⟩ ⟨q', 4 * b'.alloc⟩)
    (hg : b.alloc ≤ b'.alloc) : DOut mg n0 I0 ((I0.base, I0.len) :: H) (false, q', b') where
  shape := hs
  pos := hpos
  valid := fun e => nomatch e
  mag := fun e => nomatch e
  place := Place.trans (J := ⟨q, 4 * b.alloc⟩) h.place (fun _ he => List.mem_append_right _ he) hpl
  grow := Nat.le_trans h.grow hg

/-- `next` with nothing to grow from (`n0 = 0`). -/
theorem next0 {q q' : Nat} {b b' : MpInt} {T : List (Nat × Nat)}
    (h : DOut mg 0 I0 ((I0.base, I0.len) :: H) (false, q, b)) (hs : b'.Shape) (hpos : 0 < b'.alloc)
    (hpl : Place ((q, 4 * b.alloc) :: (T ++ H)) ⟨q, 4 * b.alloc⟩ ⟨q', 4 * b'.alloc⟩) :
    DOut mg 0 I0 ((I0.base, I0.len) :: H) (false, q', b') where
  shape := hs
  pos := hpos
  valid := fun e => nomatch e
  mag := fun e => nomatch e
  place := Place.trans (J := ⟨q, 4 * b.alloc⟩) h.place (fun _ he => List.mem_append_right _ he) hpl
  grow := Nat.zero_le _

/-- Changed in place (`mp_div_2(b, b)`: the same block, the same size). -/
theorem same {H : List (Nat × Nat)} {q : Nat} {b b' : MpInt} (h : DOut mg n0 I0 H (false, q, b))
    (hs : b'.Shape) (ha : b'.alloc = b.alloc) : DOut mg n0 I0 H (false, q, b') where
  shape := hs
  pos := ha ▸ h.pos
  valid := fun e => nomatch e
  mag := fun e => nomatch e
  place := by have := h.place; simp only at this ⊢; rw [ha]; exact this
  grow := ha ▸ h.grow

/-- At the end: valid with the magnitude. -/
theorem fin {H : List (Nat × Nat)} {q : Nat} {b : MpInt} (h : DOut mg n0 I0 H (false, q, b)) (hv : b.Valid)
    (hm : b.mag = mg) : DOut mg n0 I0 H (true, q, b) :=
  { h with valid := fun _ => hv, mag := fun _ => hm }

end DOut

end Tom.Machine
