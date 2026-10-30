import Tom.Machine.Fn.AllocMallocR

/-!
# A live block's chunk capacity (for `calloc`)

`_calloc_r` zeroes the whole usable capacity of the chunk `_malloc_r` returned,
`[p, p + sz - 8)` with `sz` the chunk size in the header at `p - 8`, not only the
requested `n` bytes. This file shows, from the invariant, that this is
harmless: for a live block `(p, n)` (`Heap.cap`)

* the header word at `p - 8` reads `sz` (flag bits aside), `n + 8 ≤ sz`;
* the slack `[p + n, p + sz - 8)` is the allocator's footprint (the chunk is
  `p`'s alone: no other live block meets it, `ChunkWalk.chunk_sep`);
* writing anything into `[p, p + sz - 8)` (or off the footprint) keeps `Heap` with the block `(p, n)`:
  the `HeapAt` reads no byte of an in-use chunk's payload (widen the block to
  the capacity, transport the shape across the writes with the
  `BlockHeapAt.transport_read`, narrow it back).
-/

namespace Tom.Machine.Fn.Alloc

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic Vsa.MemRepr
open Vsa.Sim.DlHeap (Chunk ChunkWalk HeapAt chunkSize)
open Tom.Machine Tom.Machine.Api.Alloc
open VsaIris VsaIris.VsaHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-! ## Overwriting a range of a memory -/

/-- `m` with the bytes `[a, a + k)` set to `f`'s. -/
def ovw (m : Mem) (f : Nat → BitVec 8) (a : Nat) : Nat → Mem
  | 0 => m
  | k + 1 => (ovw m f a k).insert (a + k) (f (a + k))

theorem ovw_get (m : Mem) (f : Nat → BitVec 8) (a : Nat) :
    ∀ k x, (ovw m f a k)[x]? = if a ≤ x ∧ x < a + k then some (f x) else m[x]?
  | 0, x => by simp [ovw]; omega
  | k + 1, x => by
    simp only [ovw, Std.ExtHashMap.getElem?_insert, beq_iff_eq, ovw_get m f a k x]
    by_cases h : a + k = x
    · subst h; simp
    · rw [if_neg h]
      by_cases h' : a ≤ x ∧ x < a + k
      · rw [if_pos h', if_pos (by omega)]
      · rw [if_neg h', if_neg (by omega)]

/-! ## Chunk headers -/

theorem walk_hdr {m : Mem} {p top : Nat} {cs : List Chunk} (h : ChunkWalk m p top cs) :
    ∀ c ∈ cs, ∃ hh, read64 m (c.addr + 8) = some hh ∧ chunkSize hh = c.size := by
  induction h with
  | top => intro c hc; cases hc
  | chunk hr _ _ _ _ _ ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨_, hr, rfl⟩
    · exact ih c hc

/-- A heap with the block `e` replaced by `e'` at the same chunk payload. -/
theorem heapAt_reblock {m : Mem} {H : List (Nat × Nat)} {p k k' top brk : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {c : Chunk}
    (h : HeapAt m ((p, k) :: H) (fun e => e ∈ (p, k) :: H) top brk chunks bins)
    (hc : c ∈ chunks) (hu : c.inuse = true) (hca : c.addr + 16 = p) (hk : k' + 8 ≤ c.size) :
    HeapAt m ((p, k') :: H) (fun e => e ∈ (p, k') :: H) top brk chunks bins :=
  { h with
    live := fun e he => by
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨c, hc, hu, by simp only; omega, by simp only; omega⟩
      · exact h.live e (List.mem_cons_of_mem _ he)
    exact := fun e he _ => by
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨c, hc, hu, hca, hk⟩
      · exact h.exact e (List.mem_cons_of_mem _ he) (List.mem_cons_of_mem _ he) }

/-- **The capacity of a live block** `(p, n)` and what writes into it keep. -/
structure Cap (M : Mem) (H : List (Nat × Nat)) (p n sz : Nat) : Prop where
  hdr : (bytesVal .ld (wordOf (img M) (p - 8))).toNat / 4 * 4 = sz
  room : n + 8 ≤ sz
  al : sz % 16 = 0
  min : 32 ≤ sz
  lo : heapStart + 16 ≤ p
  hi : p + (sz - 8) ≤ heapEnd
  slack : ∀ a, p ≤ a → a < p + (sz - 8) → Foot H a
  keep : ∀ M' : Mem, (∀ a, Foot ((p, n) :: H) a → ¬ (p ≤ a ∧ a < p + (sz - 8)) → M'[a]? = M[a]?) →
    Heap M' ((p, n) :: H)

theorem Heap.cap {M : Mem} {H : List (Nat × Nat)} {p n : Nat} (h : Heap M ((p, n) :: H)) :
    ∃ sz, Cap M H p n sz := by
  obtain ⟨st, m', ⟨ag, top, brk, chunks, bins, W⟩⟩ := h
  have HH := W.heap
  obtain ⟨c, hc, hu, hca, hcs⟩ := HH.exact (p, n) (List.mem_cons_self ..) (List.mem_cons_self ..)
  simp only at hca hcs
  obtain ⟨hh, hrd, hsz⟩ := walk_hdr HH.walk c hc
  have hb := HH.walk.chunk_bounds
  have hsep := HH.walk.chunk_sep
  have hbc := hb c hc
  have hlow := HH.walk.le
  have hbrk := HH.brk_le
  have hroom := W.top_room
  have eE : heapEnd = Vsa.Sim.DlHeap.heapEnd := rfl
  have eS : heapStart = Vsa.Sim.DlHeap.heapStart := rfl
  have e16 : c.size % 16 = 0 := by
    -- the walk's chunk sizes are multiples of 16
    have : ∀ {m : Mem} {q t : Nat} {cs : List Chunk}, ChunkWalk m q t cs → ∀ d ∈ cs, d.size % 16 = 0 := by
      intro m q t cs hw
      induction hw with
      | top => intro d hd; cases hd
      | chunk _ _ _ h16 _ _ ih =>
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact h16
        · exact ih d hd
    exact this HH.walk c hc
  -- the header bytes are the allocator's, so `m'` holds `M`'s
  have hfoot := foot_header ⟨HH, W.top_room⟩ (q := c.addr) (.inr ⟨c, hc, rfl⟩)
  have hp8 : p - 8 = c.addr + 8 := by omega
  have hhdr : bytesVal .ld (wordOf (img M) (p - 8)) = BitVec.ofNat 64 hh := by
    rw [hp8]
    refine wordOf_value (m := m') (fun k hk => ag _ (hfoot k hk)) ?_
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read64_lt _ _ _ hrd)]; exact hrd
  have hhlt := read64_lt _ _ _ hrd
  -- every other live block lies in another chunk
  have hoff : ∀ e ∈ H, ∀ a, p ≤ a → a < p + (c.size - 8) → ¬ InExt e a := by
    intro e he a h1 h2 hin
    obtain ⟨d, hd, _, hda, hds⟩ := HH.exact e (List.mem_cons_of_mem _ he) (List.mem_cons_of_mem _ he)
    have hne : e.1 ≠ p := fun h => (List.nodup_cons.1 st).1 (List.mem_map.2 ⟨e, he, h⟩)
    obtain ⟨hin1, hin2⟩ := hin
    have hbd := hb d hd
    rcases hsep d hd c hc with rfl | hs | hs
    · exact hne (by omega)
    · obtain ⟨_, hl⟩ := HH.live e (List.mem_cons_of_mem _ he)
      omega
    · omega
  refine ⟨c.size, ⟨?_, hcs, e16, hbc.2.2, by omega, by omega, ?_, ?_⟩⟩
  · rw [hhdr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhlt]; exact hsz
  · intro a h1 h2
    exact .inr ⟨by omega, by omega, fun e he => hoff e he a h1 h2⟩
  · intro M' hM'
    let K := c.size - 8
    let m2 := ovw m' (img M') p K
    have hm2 := ovw_get m' (img M') p K
    -- widen the block to the capacity, transport across the writes, narrow back
    have Wd : BlockHeapAt m' ((p, K) :: H) top brk chunks bins :=
      ⟨heapAt_reblock HH hc hu hca (by omega), W.top_room⟩
    have hag : AgreeP (vsaRead ((p, K) :: H)) m' m2 := fun a ha => by
      show m'[a]? = (ovw m' (img M') p K)[a]?
      rw [hm2, if_neg]
      rintro ⟨h1, h2⟩
      rcases ha.1 with hg | ⟨_, _, h3⟩
      · have := allocGlobal_off_arena a hg; omega
      · exact h3 (p, K) (List.mem_cons_self ..) ⟨h1, h2⟩
    have Pd : PHeapAt m2 ((p, K) :: H) top brk chunks bins :=
      PHeapAt.transport_read ⟨Wd, W.brk_page, W.bb_lt⟩ hag
    have HH2 := heapAt_reblock Pd.heap.heap hc hu hca (k' := n) hcs
    refine ⟨st, m2, ⟨fun a ha => ?_, top, brk, chunks, bins, ⟨HH2, Pd.heap.top_room, Pd.brk_page, Pd.bb_lt⟩⟩⟩
    show (ovw m' (img M') p K)[a]? = some (img M' a)
    rw [hm2]
    split
    · rfl
    · next hn =>
      rw [ag a ha]
      unfold img
      rw [hM' a ha hn]
