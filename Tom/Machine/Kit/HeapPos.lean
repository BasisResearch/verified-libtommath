import Tom.Machine.Fn.AllocRun
import Tom.Machine.Kit.MeetHeap

/-!
# A live block placed at a region is nonempty

A callee's post places its site at `⟨q, n⟩` with `(q, n)` a live block and the region off the
heap's footprint (`Off`): a live block starts strictly inside the arena (`Heap.blk_lt`: below the
top chunk's header, which `top + 16 ≤ brk` keeps below `heapEnd`), and `Off`'s empty case lies
outside it, so `n > 0` (`HP.pos_of`). Used where a contract's result does not state its block
nonempty (`mp_mod`'s `ModPost`) and the next call needs it (`mp_clear`, `mp_copy`).
-/

namespace Tom.Machine

open Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- **A live block starts inside the arena** (below `heapEnd`). -/
theorem Heap.blk_lt {m : Mem} {H : List (Nat × Nat)} (h : Heap m H) {e : Nat × Nat} (he : e ∈ H) :
    heapStart + 16 ≤ e.1 ∧ e.1 < heapEnd := by
  obtain ⟨_, m', ⟨_, top, brk, chunks, bins, W⟩⟩ := h
  obtain ⟨c, hc, _, h1, h2⟩ := W.heap.live e he
  have hb := W.heap.walk.chunk_bounds c hc
  have := W.heap.brk_le
  have := W.top_room
  have e1 : Vsa.Sim.DlHeap.heapEnd = heapEnd := rfl
  have e2 : Vsa.Sim.DlHeap.heapStart = heapStart := rfl
  omega

section
variable {ι : Type} {ρ : ι → Iv} {isW : ι → Bool} {H0 H : List (Nat × Nat)} {Wr0 : Nat → Prop}
  {m0 m : Mem}

/-- **A region at a live block is nonempty.** -/
theorem HP.pos_of (hp : HP ρ isW H0 H Wr0 m0 m) (r : ι) {q n : Nat} (hr : ρ r = ⟨q, n⟩) (he : (q, n) ∈ H) :
    0 < n := by
  have ho := hp.off r
  rw [hr] at ho
  have hb := Heap.blk_lt hp.heap.heap he
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · rcases ho.edge h0 with h1 | h1 <;> (simp only at hb h1; omega)
  · exact h0

end

end Tom.Machine
