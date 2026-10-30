import Tom.Machine.Img
import Tom.Machine.Kit.At
import Vsa.Reloc.Alloc.DlHeap

/-!
# The allocator: `calloc`, `realloc` (grow), `free`

libtommath allocates through `MP_CALLOC`/`MP_REALLOC`/`MP_FREE`, i.e. newlib's
`calloc`, `realloc`, `free` (dlmalloc). This file states their machine
contracts in the standard `At` form, over a **heap invariant** `Heap m H`:
`H` is the list of live blocks `(p, n)` the caller owns, and `Heap m H` says
dlmalloc's state in `m` is well formed with exactly those blocks in use.

* **Footprint.** The allocator owns `Foot H`: its static data (`Global`) and
  every arena byte `[heapStart, heapEnd)` outside the live blocks. A client
  keeps its own data either in a live block (`e ∈ H`) or off the arena and the
  globals; such bytes are off `Foot H` (`Foot.off_blk`, `Foot.off_arena`).
* **Fresh blocks.** A returned block is `Fresh H p n`: non-null, 16-aligned,
  in the arena, disjoint from every live block (`FreshBlock`).
* **Frames.** Each call changes memory only in its footprint, the block it
  frees or reallocates, and its stack window `[sp - F, sp)` (`Keep`).
  `F = depth = 512` for `realloc`/`free` (the `allocHeadroom`: the function,
  `_malloc_r`, `_free_r`, `memcpy`, `_sbrk_r`), `callocDepth = 544` for
  `calloc` (`_calloc_r`'s 32-byte frame above `_malloc_r`'s 512; `__muldi3` and
  `memset` are leaves).
* **Failure.** Every call may fail (`calloc`/`realloc` return 0): dlmalloc
  runs out of arena. The failure branches keep the heap (and, for `realloc`,
  the old block).

The heap invariant is ship-your-interpreter's (`VsaIris.VsaHeap.pShape` over
`Vsa.Sim.DlHeap.HeapAt`, relocated to this image in
`Vsa/Reloc/Alloc/DlHeap.lean`), restated with named fields. Its bytes are
read totally (`getD 0`), as the machine reads them, so it does not depend on
which bytes are mapped.

The three contracts are proved: `Fn.Alloc.free_correct`,
`Fn.Alloc.realloc_correct` (from the `freeLocalRun_proved`/
`reallocLocalRun_proved`, `Fn/AllocFree.lean`, `Fn/AllocRealloc.lean`) and
`Fn.Calloc.calloc_correct` (`Fn/CallocMain.lean`: `__muldi3`, the
`malloc_all` from `_malloc_r`'s entry, `Fn.Memset.correct`; `_calloc_r` zeroes
the chunk's whole capacity, which `Fn.Alloc.Heap.cap` shows keeps `Heap` with
the requested block). `At` carries `AllGprs`, which the model needs.
-/

namespace Tom.Machine.Api.Alloc

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic Vsa.MemRepr
open Tom.Machine Tom.Machine.Code

/-! ## This image's allocator addresses -/

/-- `_end`: the first byte `_sbrk` hands out (`0x80019d10`). -/
abbrev heapStart : Nat := Vsa.Sim.DlHeap.heapStart

/-- `__heap_end` (`0x87800000`). -/
abbrev heapEnd : Nat := Vsa.Sim.DlHeap.heapEnd

/-- `__global_pointer$`: the allocator addresses its globals from `gp`. -/
def gpV : BitVec 64 := 0x80019090#64

/-- `_impure_ptr`, the word the wrappers load (`.data`, never written). -/
def impurePtr : Nat := 0x80019510

/-- Its contents: `&_impure_data` (`0x800190c8`), little-endian. -/
def impureBytes : List (BitVec 8) := [0xc8, 0x90, 0x01, 0x80, 0, 0, 0, 0]

/-- `_impure_ptr` holds `&_impure_data`. -/
def ImpureAt (m : Mem) : Prop := ∀ i b, impureBytes[i]? = some b → m[impurePtr + i]? = some b

/-- The entries: the wrappers libtommath calls. -/
def callocEntry : BitVec 64 := BitVec.ofNat 64 callocBase
def reallocEntry : BitVec 64 := BitVec.ofNat 64 reallocBase
def freeEntry : BitVec 64 := BitVec.ofNat 64 freeBase

/-- The stack depth of `realloc` and `free` with their callees (`allocHeadroom`). -/
def depth : Nat := 512

/-- The stack depth of `calloc`: `_calloc_r`'s frame (32) and `_malloc_r`'s `depth`. -/
def callocDepth : Nat := 544

/-! ## Footprint, blocks, frames -/

/-- Byte `a` lies in the block `e = (p, n)`. -/
def InBlk (e : Nat × Nat) (a : Nat) : Prop := e.1 ≤ a ∧ a < e.1 + e.2

/-- The allocator's static data (`allocGlobal`, relocated): `__malloc_av_`,
`_impure_data._errno`, `__malloc_sbrk_base` and `__malloc_trim_threshold`,
`brk.0` to `__malloc_top_pad`, `errno`, `__malloc_current_mallinfo`. -/
def Global (a : Nat) : Prop :=
  (0x800188a0 ≤ a ∧ a < 0x800190b0) ∨ (0x800190c8 ≤ a ∧ a < 0x800190cc) ∨
  (0x80019500 ≤ a ∧ a < 0x80019510) ∨ (0x80019530 ≤ a ∧ a < 0x80019550) ∨
  (0x80019558 ≤ a ∧ a < 0x8001955c) ∨ (0x800195b8 ≤ a ∧ a < 0x80019608)

/-- **The allocator's bytes** with live blocks `H` (`heapFoot`): its
globals and the arena outside the blocks. -/
def Foot (H : List (Nat × Nat)) (a : Nat) : Prop :=
  Global a ∨ (heapStart ≤ a ∧ a < heapEnd ∧ ∀ e ∈ H, ¬ InBlk e a)

/-- The stack window `[sp - F, sp)`. -/
def Stk (sp F a : Nat) : Prop := sp - F ≤ a ∧ a < sp

/-- `M` equals `m` outside `W`. -/
def Keep (W : Nat → Prop) (m M : Mem) : Prop := ∀ a, ¬ W a → M[a]? = m[a]?

/-- **A fresh block** `(p, n)` for the live blocks `H` (`FreshBlock`, with
the alignment `malloc` returns). -/
structure Fresh (H : List (Nat × Nat)) (p n : Nat) : Prop where
  nz : p ≠ 0
  al : p % 16 = 0
  lo : heapStart ≤ p
  hi : p + n ≤ heapEnd
  disj : ∀ e ∈ H, ∀ a, InBlk (p, n) a → ¬ InBlk e a

/-! ## The heap invariant -/

/-- dlmalloc's invariant in a memory `m'` (`PHeapAt`): the chunk walk,
bins and globals of `Vsa.Sim.DlHeap.HeapAt`, every live block inside a chunk
in use (`exact`: at its payload start), top room, a page-aligned break, the
`binblocks` map in 32 bits. -/
structure HeapWit (m' : Mem) (H : List (Nat × Nat)) (top brk : Nat)
    (chunks : List DlHeap.Chunk) (bins : Nat → List Nat) : Prop where
  heap : DlHeap.HeapAt m' H (fun e => e ∈ H) top brk chunks bins
  top_room : top + 16 ≤ brk
  brk_page : brk % 4096 = 0
  bb_lt : ∀ bb, read64 m' DlHeap.binblocksAddr = some bb → bb < 2 ^ 32

/-- `m'` holds `m`'s total reads on the footprint. -/
def Agree (H : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ a, Foot H a → m'[a]? = some ((m[a]?).getD 0)

/-- A witness memory for `Heap`. -/
structure Shape (m : Mem) (H : List (Nat × Nat)) (m' : Mem) : Prop where
  agree : Agree H m m'
  wit : ∃ top brk chunks bins, HeapWit m' H top brk chunks bins

/-- **The heap invariant** (`pShape (fun a => (m[a]?).getD 0) H`): the
blocks start at distinct addresses, and `m` read totally on `Foot H` is a
well-formed dlmalloc state with exactly the blocks `H` in use. -/
structure Heap (m : Mem) (H : List (Nat × Nat)) : Prop where
  starts : (H.map Prod.fst).Nodup
  shape : ∃ m', Shape m H m'

/-! ## The calls' common precondition -/


/-- What every allocator call needs besides its arguments: the code (`Img`,
which carries the `malloc` wrapper too) and `_impure_ptr`, `gp`, a 16-aligned `sp` with `F` bytes of stack above the arena
(and below 4 GiB), an aligned return address. -/
structure Ctx (m : Mem) (v : Abi) (sp F : Nat) (ra : BitVec 64) : Prop where
  img : Img m
  impure : ImpureAt m
  gp : v.gp = gpV
  sp_v : v.sp = BitVec.ofNat 64 sp
  sp_al : sp % 16 = 0
  sp_lo : heapEnd + F ≤ sp
  sp_hi : sp ≤ 0x100000000
  ra_al : ra.toNat % 4 = 0

/-! ## `calloc(n, sz)` -/

/-- A null result: the heap as it was. -/
structure Null (m M : Mem) (H : List (Nat × Nat)) (W : Nat → Prop) : Prop where
  heap : Heap M H
  keep : Keep W m M

/-- A fresh block `(p, n)`, now live. -/
structure Got (m M : Mem) (H : List (Nat × Nat)) (W : Nat → Prop) (p n : Nat) : Prop where
  fresh : Fresh H p n
  heap : Heap M ((p, n) :: H)
  keep : Keep W m M

/-- What `calloc` writes: its footprint and stack. -/
def callocW (H : List (Nat × Nat)) (sp : Nat) (a : Nat) : Prop := Foot H a ∨ Stk sp callocDepth a

/-- **What `calloc(n, sz)` leaves** with result `p`: null and the heap kept, or
the fresh block `(p, n * sz)`, zero-filled. -/
inductive CallocPost (m M : Mem) (H : List (Nat × Nat)) (sp N : Nat) : Nat → Prop
  | null (h : Null m M H (callocW H sp)) : CallocPost m M H sp N 0
  | ok {p : Nat} (h : Got m M H (callocW H sp) p N) (zero : ∀ i, i < N → M[p + i]? = some 0) :
      CallocPost m M H sp N p

def callocL (ra : BitVec 64) (n sz : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 n), (11, BitVec.ofNat 64 sz)]

def CallocRet (m : Mem) (v : Abi) (outp : Array String) (H : List (Nat × Nat)) (sp N : Nat)
    (ra : BitVec 64) (c : Vsa.Machine.Config) : Prop :=
  ∃ p M, At ra [(1, ra), (10, BitVec.ofNat 64 p)] M v.keep outp c ∧ CallocPost m M H sp N p

/-- **`calloc(n, sz)` on the machine** (`n`, `sz` below `2 ^ 32`: `_calloc_r`'s
one-`__muldi3` path; libtommath's `MP_CALLOC(size, sizeof(mp_digit))`). -/
def Calloc_Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp n sz : Nat}
    {ra : BitVec 64}, Ctx m v sp callocDepth ra → Heap m H → n < 2 ^ 32 → sz < 2 ^ 32 →
    Triple (At callocEntry (callocL ra n sz) m v.keep outp) (CallocRet m v outp H sp (n * sz) ra)

/-! ## `realloc(p, n)`, growing -/

/-- What `realloc(p, ·)` and `free(p)` write: the footprint with the block
`(p, n)` live, the block, the stack. -/
def blkW (H : List (Nat × Nat)) (p n sp : Nat) (a : Nat) : Prop :=
  Foot ((p, n) :: H) a ∨ InBlk (p, n) a ∨ Stk sp depth a

/-- **What `realloc(p, nNew)` leaves** (`nOld < nNew`) with result `q`: null,
the heap and the old block's bytes kept; or the fresh block `(q, nNew)` (fresh
for the other blocks: it may reuse `p`) holding the old block's `nOld` bytes,
the old block freed. -/
inductive ReallocPost (m M : Mem) (H : List (Nat × Nat)) (p nOld nNew sp : Nat) : Nat → Prop
  | null (h : Null m M ((p, nOld) :: H) (blkW H p nOld sp))
      (same : ∀ k, k < nOld → (M[p + k]?).getD 0 = (m[p + k]?).getD 0) :
      ReallocPost m M H p nOld nNew sp 0
  | ok {q : Nat} (h : Got m M H (blkW H p nOld sp) q nNew)
      (copy : ∀ k, k < nOld → (M[q + k]?).getD 0 = (m[p + k]?).getD 0) :
      ReallocPost m M H p nOld nNew sp q

def reallocL (ra : BitVec 64) (p n : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 p), (11, BitVec.ofNat 64 n)]

def ReallocRet (m : Mem) (v : Abi) (outp : Array String) (H : List (Nat × Nat))
    (p nOld nNew sp : Nat) (ra : BitVec 64) (c : Vsa.Machine.Config) : Prop :=
  ∃ q M, At ra [(1, ra), (10, BitVec.ofNat 64 q)] M v.keep outp c ∧ ReallocPost m M H p nOld nNew sp q

/-- **`realloc(p, nNew)` on the machine**, for a live block `(p, nOld)` and
`nOld < nNew` (libtommath's `mp_grow`; the `ReallocLocalRun` is grow-only). -/
def Realloc_Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp p nOld nNew : Nat}
    {ra : BitVec 64}, Ctx m v sp depth ra → Heap m ((p, nOld) :: H) → nOld < nNew →
    nNew < 2 ^ 64 →
    Triple (At reallocEntry (reallocL ra p nNew) m v.keep outp)
      (ReallocRet m v outp H p nOld nNew sp ra)

/-! ## `free(p)` -/

/-- **What `free(p)` leaves**: the heap without the block. -/
structure FreePost (m M : Mem) (H : List (Nat × Nat)) (p n sp : Nat) : Prop where
  heap : Heap M H
  keep : Keep (blkW H p n sp) m M

def freeL (ra : BitVec 64) (p : Nat) : GRegs := [(1, ra), (10, BitVec.ofNat 64 p)]

def FreeRet (m : Mem) (v : Abi) (outp : Array String) (H : List (Nat × Nat)) (p n sp : Nat)
    (ra : BitVec 64) (c : Vsa.Machine.Config) : Prop :=
  ∃ M, At ra [(1, ra)] M v.keep outp c ∧ FreePost m M H p n sp

/-- **`free(p)` on the machine**, for a live block `(p, n)`. -/
def Free_Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp p n : Nat}
    {ra : BitVec 64}, Ctx m v sp depth ra → Heap m ((p, n) :: H) →
    Triple (At freeEntry (freeL ra p) m v.keep outp) (FreeRet m v outp H p n sp ra)

/-! ## Client lemmas -/

/-- A byte of a live block is not the allocator's. -/
theorem Foot.off_blk {H : List (Nat × Nat)} {e : Nat × Nat} {a : Nat} (he : e ∈ H)
    (ha : InBlk e a) (hg : ¬ Global a) : ¬ Foot H a := by
  rintro (h | ⟨_, _, h⟩)
  · exact hg h
  · exact h e he ha

/-- A byte below the arena (code, data) or above it (stack), off the globals,
is not the allocator's. -/
theorem Foot.off_arena {H : List (Nat × Nat)} {a : Nat} (ha : a < heapStart ∨ heapEnd ≤ a)
    (hg : ¬ Global a) : ¬ Foot H a := by
  rintro (h | ⟨h1, h2, _⟩)
  · exact hg h
  · omega

/-- A live block is off the globals: the globals lie below the arena. -/
theorem Global.lt {a : Nat} (h : Global a) : a < heapStart := by
  have e : heapStart = 0x80019d10 := rfl
  unfold Global at h; omega

theorem Keep.mono {W W' : Nat → Prop} {m M : Mem} (h : Keep W m M) (hw : ∀ a, W a → W' a) :
    Keep W' m M := fun a ha => h a (fun hw' => ha (hw a hw'))

theorem Keep.trans {W W' : Nat → Prop} {m M M' : Mem} (h : Keep W m M) (h' : Keep W' M M') :
    Keep (fun a => W a ∨ W' a) m M' := fun a ha =>
  (h' a (fun hw => ha (.inr hw))).trans (h a (fun hw => ha (.inl hw)))

/-- The heap invariant reads only the footprint. -/
theorem Heap.frame {m M : Mem} {H : List (Nat × Nat)} (h : Heap m H)
    (hk : ∀ a, Foot H a → M[a]? = m[a]?) : Heap M H := by
  obtain ⟨st, m', S⟩ := h
  exact ⟨st, m', ⟨fun a ha => by rw [hk a ha]; exact S.agree a ha, S.wit⟩⟩

/-- The heap invariant does not depend on the blocks' order. -/
theorem Heap.perm {m : Mem} {H H' : List (Nat × Nat)} (h : Heap m H) (hp : H.Perm H') :
    Heap m H' := by
  obtain ⟨st, m', S⟩ := h
  have hmem : ∀ e, e ∈ H' ↔ e ∈ H := fun e => (hp.mem_iff).symm
  have hfoot : ∀ a, Foot H' a ↔ Foot H a := fun a => by
    unfold Foot
    exact or_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
      ⟨fun h e he => h e ((hmem e).2 he), fun h e he => h e ((hmem e).1 he)⟩))
  obtain ⟨top, brk, chunks, bins, W⟩ := S.wit
  have HH := W.heap
  refine ⟨(hp.map Prod.fst).nodup_iff.1 st, m', ⟨fun a ha => S.agree a ((hfoot a).1 ha),
    top, brk, chunks, bins, ⟨{ HH with
      live := fun e he => HH.live e ((hmem e).1 he)
      exact := fun e he hr => HH.exact e ((hmem e).1 he) ((hmem e).1 hr) }, W.top_room,
      W.brk_page, W.bb_lt⟩⟩⟩

/-- A fresh block misses every byte of a live block. -/
theorem Fresh.off {H : List (Nat × Nat)} {p n : Nat} (h : Fresh H p n) {e : Nat × Nat}
    (he : e ∈ H) {a : Nat} (ha : InBlk e a) : ¬ InBlk (p, n) a := fun hb => h.disj e he a hb ha

end Tom.Machine.Api.Alloc
