import Tom.Machine.Kit.Run
import Tom.Machine.Fn.AllocCap
import Tom.Machine.Api.Std_multi8

/-!
# Live blocks are small and nonempty

Facts about a temporary's digit block that a caller reads off its heap checkpoint instead of
carrying them through a loop:

* `HP.small`: a live block `(q, 4 * n)` lies in the arena, so `n < 2 ^ 25` — the `int` sizes of
  `mp_grow` (`max(a->used, b->used) + 1 < 2 ^ 31`) for temporaries an in-place `mp_add`/`mp_sub`
  may grow without bound (`s_mp_invmod_fast`'s coefficients);
* `HP.pos`: a site's live block `(q, 4 * n)` off the allocator is nonempty (`Off.edge` rules out an
  empty one inside the arena; the chunk's capacity, `Heap.cap`, puts `q` below `heapEnd`) — the
  `alloc > 0` of a destination re-placed by a callee whose post does not state it (`mp_mod`);
* `Heap.fresh_front`: the front block of a heap is fresh for the rest (its chunk's capacity is the
  allocator's footprint for the other blocks, `Heap.cap`): the placement of a destination that ends
  on a temporary's block (`mp_exch` then `mp_clear_multi`);
* `Std.fin_getD`, `Std.fin_argAt`: a varargs call's per-argument residue (`mp_init_multi`'s
  alignment and off-heap structs, `mp_clear_multi`'s nonempty blocks) from a fact about every list
  element, for any arity; `Std.sargs_null`/`sargs_nullC`: at arity 8 the one stack argument is
  the `NULL` the caller stored at its `sp`.
-/

namespace Tom.Machine

open Vsa.Sim Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- A live block starts 24 bytes below the arena's end at least (its chunk holds 32 bytes). -/
theorem Heap.lt_end {m : Mem} {H : List (Nat × Nat)} (h : Heap m H) {e : Nat × Nat} (he : e ∈ H) :
    e.1 + 24 ≤ heapEnd := by
  obtain ⟨sz, hc⟩ := Fn.Alloc.Heap.cap (Heap.pick h he)
  have := hc.hi; have := hc.min
  omega

/-- **A block off the allocator that is live is nonempty.** -/
theorem Off.pos_blk {q n : Nat} {H H' : List (Nat × Nat)} {m : Mem} (ho : Off ⟨q, 4 * n⟩ H)
    (hh : Heap m H') (he : (q, 4 * n) ∈ H') : 0 < n := by
  have h1 := Fn.Alloc.Heap.blk hh he
  have h2 := Heap.lt_end hh he
  simp only at h1 h2
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · have := ho.edge (by simp [h0]); simp only at this; omega
  · exact h0

/-- **The front block of a heap is fresh for the others.** -/
theorem Heap.fresh_front {m : Mem} {H : List (Nat × Nat)} {q n : Nat} (h : Heap m ((q, n) :: H)) :
    Fresh H q n := by
  obtain ⟨sz, hc⟩ := Fn.Alloc.Heap.cap h
  have hal := Std.Heap.al16 h (List.mem_cons_self ..)
  have e1 : heapStart = 0x80019d10 := rfl
  have := hc.lo; have := hc.room; have := hc.hi
  refine ⟨by omega, hal, by omega, by omega, fun e he a ha hb => ?_⟩
  unfold InBlk at ha; simp only at ha
  rcases hc.slack a ha.1 (by omega) with hg | ⟨_, _, hn⟩
  · have := Global.lt hg; omega
  · exact hn e he hb

section
variable {ι : Type} {ρ : ι → Iv} {isW : ι → Bool} {H0 H : List (Nat × Nat)}
  {Wr0 : Nat → Prop} {m0 M : Mem}

/-- **A live block's digit count is below `2 ^ 25`** (`4 n` bytes inside the arena). -/
theorem HP.small (hp : HP ρ isW H0 H Wr0 m0 M) {q n : Nat} (he : (q, 4 * n) ∈ H) : n < 2 ^ 25 := by
  have h := Fn.Alloc.Heap.blk hp.heap.heap he
  have e1 : heapStart = 0x80019d10 := rfl; have e2 : heapEnd = 0x87800000 := rfl
  simp only at h; omega

/-- **A region at a live block is nonempty.** -/
theorem HP.pos (hp : HP ρ isW H0 H Wr0 m0 M) {q n : Nat} (he : (q, 4 * n) ∈ H) (r : ι)
    (hr : ρ r = ⟨q, 4 * n⟩) : 0 < n :=
  Off.pos_blk (hr ▸ hp.off r) hp.heap.heap he

end

/-- `P` of every element: the conjunction a concrete list unfolds to (`⟨h₁, …, hₖ, trivial⟩`). -/
def Std.AllL {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | x :: xs => P x ∧ Std.AllL P xs

theorem Std.AllL.mem {α : Type} {P : α → Prop} : ∀ {l : List α}, Std.AllL P l → ∀ x ∈ l, P x
  | [], _, _, hx => absurd hx List.not_mem_nil
  | _ :: _, ⟨h1, h2⟩, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact Std.AllL.mem h2 x hx

/-- A fact about every element, at each index of the list. -/
theorem Std.fin_getD (l : List Nat) {P : Nat → Prop} (h : Std.AllL P l) (i : Fin l.length) : P (l.getD i 0) := by
  rw [Std.getD_idx i.2]; exact h.mem _ (List.getElem_mem _)

/-- A fact about every argument, at each index of the list. -/
theorem Std.fin_argAt (xs : List Api.Multi.Arg) {P : Api.Multi.Arg → Prop} (h : Std.AllL P xs)
    (i : Fin xs.length) : P (Std.argAt xs i) := by
  rw [Std.argAt_idx i.2]; exact h.mem _ (List.getElem_mem _)

/-- Arity 8: the one stack argument is the terminating `NULL`, at the callee's `sp`. -/
theorem Std.sargs_null {ps : List Nat} {m : Mem} {sp : Nat} (hl : ps.length = 8)
    (h : bytesT8 m sp = BitVec.ofNat 64 0) :
    ∀ j : Fin (8 - 7), bytesT8 m (sp + 8 * j) = BitVec.ofNat 64 ((Api.Multi.args ps).getD (8 + j) 0) := by
  intro ⟨j, hj⟩
  obtain rfl : j = 0 := by omega
  have e : (Api.Multi.args ps).getD 8 0 = 0 := by
    rw [Api.Multi.args, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl]; rfl
  show bytesT8 m (sp + 8 * 0) = BitVec.ofNat 64 ((Api.Multi.args ps).getD (8 + 0) 0)
  rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero, e]; exact h

/-- `Std.sargs_null` over `mp_clear_multi`'s arguments. -/
theorem Std.sargs_nullC {xs : List Api.Multi.Arg} {m : Mem} {sp : Nat} (hl : xs.length = 8)
    (h : bytesT8 m sp = BitVec.ofNat 64 0) :
    ∀ j : Fin (8 - 7), bytesT8 m (sp + 8 * j) =
      BitVec.ofNat 64 ((Api.Multi.args (Api.Multi.ptrs xs)).getD (8 + j) 0) :=
  Std.sargs_null (by rw [Api.Multi.ptrs, List.length_map, hl]) h

end Tom.Machine
