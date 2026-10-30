import Tom.Machine.Api.Alloc
import VsaIris.Vsa.AllocHoles
import VsaIris.Vsa.SWPReach

/-!
# The allocator interface against the relocated proofs (step 4)

`Tom/Machine/Api/Alloc.lean` states the heap and the footprint in this
repository's terms; the proofs (`VsaIris.VsaHeap.*LocalRun_proved`, built at
this image's addresses) state them as `vsaLayoutP` (`pShape`, `heapFoot`).
They are the same predicates: `Foot = vsaFoot` and `Heap m H ↔
vsaLayoutP.Shape (img m) H` are definitional.
-/

namespace Tom.Machine.Fn.Alloc

open Tom.Machine Tom.Machine.Api.Alloc
open VsaIris VsaIris.VsaHeap

/-- The total image of a memory, as `vsaModel` reads it. -/
def img (m : Mem) (a : Nat) : BitVec 8 := (m[a]?).getD 0

theorem global_iff (a : Nat) : Global a ↔ allocGlobal a := Iff.rfl

theorem foot_iff (H : List (Nat × Nat)) (a : Nat) : Foot H a ↔ vsaFoot H a := Iff.rfl

theorem foot_eq (H : List (Nat × Nat)) : heapFoot vsaLayoutP H = Foot H := rfl

/-- **The heap invariant is the shape** of the memory's total image. -/
theorem heap_iff (m : Mem) (H : List (Nat × Nat)) : Heap m H ↔ vsaLayoutP.Shape (img m) H := by
  constructor
  · rintro ⟨st, m', ⟨ag, top, brk, chunks, bins, W⟩⟩
    exact ⟨st, m', top, brk, chunks, bins, fun a ha => ag a ha, ⟨⟨W.heap, W.top_room⟩, W.brk_page, W.bb_lt⟩⟩
  · rintro ⟨st, m', top, brk, chunks, bins, ag, P⟩
    exact ⟨st, m', ⟨fun a ha => ag a ha, top, brk, chunks, bins,
      ⟨P.heap.heap, P.heap.top_room, P.brk_page, P.bb_lt⟩⟩⟩

/-- A shape of any image that `M` reads totally on the footprint is a `Heap`. -/
theorem heap_of_shape {M : Mem} {H : List (Nat × Nat)} {mv : Nat → BitVec 8}
    (h : vsaLayoutP.Shape mv H) (hag : ∀ a, Foot H a → (M[a]?).getD 0 = mv a) : Heap M H :=
  (heap_iff M H).2 (shapeLocal_vsaLayoutP H mv (img M) (fun a ha => (hag a ha).symm) h)

end Tom.Machine.Fn.Alloc

namespace Tom.Machine.Fn.Alloc

open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc

/-! ## The allocator's text is in the image -/

/-- Byte `k` (`< 4`) of a little-endian word. -/
def byteOf (w : BitVec 32) (k : Nat) : BitVec 8 := w.extractLsb' (8 * k) 8

/-- `b` is the byte at `a` of the words `ws` at `base` (decidable on literals). -/
def ByteIn (base : Nat) (ws : List (BitVec 32)) (a : Nat) (b : BitVec 8) : Bool :=
  decide (base ≤ a) && (match ws[(a - base) / 4]? with
    | some w => byteOf w ((a - base) % 4) == b
    | none => false)

theorem CodeAt.byte {m : Mem} {base : Nat} {ws : List (BitVec 32)} (h : CodeAt m base ws)
    {a : Nat} {b : BitVec 8} (hb : ByteIn base ws a b = true) : m[a]? = some b := by
  simp only [ByteIn, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨hle, hw⟩ := hb
  obtain ⟨j, k, hk, rfl⟩ : ∃ j k, k < 4 ∧ a = base + 4 * j + k :=
    ⟨(a - base) / 4, (a - base) % 4, Nat.mod_lt _ (by decide), by omega⟩
  have e1 : (base + 4 * j + k - base) / 4 = j := by omega
  have e2 : (base + 4 * j + k - base) % 4 = k := by omega
  rw [e1, e2] at hw
  split at hw
  · next w hj =>
    simp only [beq_iff_eq] at hw
    obtain ⟨h0, h1, h2, h3⟩ := h _ w hj
    subst hw
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · simpa [byteOf] using h0
    · simpa [byteOf] using h1
    · simpa [byteOf] using h2
    · simpa [byteOf] using h3
  · cases hw

/-- The `_impure_ptr` bytes. -/
def ImpByte (a : Nat) (b : BitVec 8) : Bool :=
  decide (impurePtr ≤ a) && impureBytes[a - impurePtr]? == some b

theorem ImpureAt.byte {m : Mem} (h : ImpureAt m) {a : Nat} {b : BitVec 8}
    (hb : ImpByte a b = true) : m[a]? = some b := by
  simp only [ImpByte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
  have := h _ _ hb.2
  rwa [Nat.add_sub_cancel' hb.1] at this

/-- Where each byte of `allocText` comes from. -/
def textChk (a : Nat) (b : BitVec 8) : Bool :=
  ByteIn sbrkBase sbrkCode a b || ByteIn mallocBase mallocCode a b || ByteIn freeBase freeCode a b ||
  ByteIn mallocRBase mallocRCode a b || ByteIn mallocLockBase mallocLockCode a b ||
  ByteIn mallocUnlockBase mallocUnlockCode a b || ByteIn reallocBase reallocCode a b ||
  ByteIn reallocRBase reallocRCode a b || ByteIn sbrkRBase sbrkRCode a b ||
  ByteIn errnoBase errnoCode a b ||
  ByteIn retargetLockAcquireRecursiveBase retargetLockAcquireRecursiveCode a b ||
  ByteIn retargetLockReleaseRecursiveBase retargetLockReleaseRecursiveCode a b ||
  ByteIn memmoveBase memmoveCode a b || ByteIn mallocTrimRBase mallocTrimRCode a b ||
  ByteIn freeRBase freeRCode a b || ImpByte a b

theorem allocText_chk : VsaIris.Sym.allocText.all (fun p => textChk p.1 p.2) = true := by
  decide +kernel

/-- **The allocator's text is loaded**: every byte of the `allocText` (at
this image's addresses) is in a memory with the image's code, the `malloc`
wrapper and `_impure_ptr`. -/
theorem textLoaded {m : Mem} {v : Abi} {sp F : Nat} {ra : BitVec 64} (h : Ctx m v sp F ra) :
    VsaIris.Sym.TextLoaded VsaIris.Sym.allocText m := by
  intro p hp
  have hc := List.all_eq_true.1 allocText_chk p hp
  have I := h.img
  simp only [textChk, Bool.or_eq_true] at hc
  rcases hc with ((((((((((((((hc | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc) |
    hc) | hc) | hc
  · exact CodeAt.byte I.sbrk hc
  · exact CodeAt.byte I.malloc hc
  · exact CodeAt.byte I.free hc
  · exact CodeAt.byte I.mallocR hc
  · exact CodeAt.byte I.mallocLock hc
  · exact CodeAt.byte I.mallocUnlock hc
  · exact CodeAt.byte I.realloc hc
  · exact CodeAt.byte I.reallocR hc
  · exact CodeAt.byte I.sbrkR hc
  · exact CodeAt.byte I.errno hc
  · exact CodeAt.byte I.retargetLockAcquireRecursive hc
  · exact CodeAt.byte I.retargetLockReleaseRecursive hc
  · exact CodeAt.byte I.memmove hc
  · exact CodeAt.byte I.mallocTrimR hc
  · exact CodeAt.byte I.freeR hc
  · exact ImpureAt.byte h.impure hc

end Tom.Machine.Fn.Alloc
