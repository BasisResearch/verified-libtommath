import Tom.Machine.Fn.AllocFree
import Tom.Machine.Fn.Memset
import Tom.Machine.Kit.Frame
import Tom.Machine.Kit.Jal
import Tom.Machine.Kit.Auto

/-!
# `mp_int`s in the heap: how every allocating contract describes memory

The allocator's contracts (`Api/Alloc.lean`) speak of a heap invariant
`Heap m H` over the live blocks `H : List (Nat × Nat)` (start, bytes). This
file fixes, once, how an `mp_int` and a function that allocates sit on it:

* **Digits are a live block.** An `mp_int` `a` at `p` with digits at `dp`
  owns the block `(dp, 4 * a.alloc)` (`digBlk dp a`): `MpLive m H p dp a` is
  `MpAt m p dp a`, that block `∈ H`, and the struct `OffHeap`. A function
  that owns several `mp_int`s keeps their blocks in its `H`; a function that
  allocates a temporary conses its block (`mp_init`: `H ↦ (q, 4 n) :: H`) and
  frees it (`mp_clear`: `(dp, 4 alloc) :: H ↦ H`); `mp_grow` replaces it
  (`(dp, 4 alloc) :: H ↦ (q, 4 size) :: H`). A block in the middle is brought
  to the front by `Heap.pick`.
* **Structs are off the allocator.** `OffHeap a n`: `[a, a + n)` lies below
  every allocator datum (`allocLo`, the first of its globals) or above the
  arena (the stack). Such bytes are off `Foot H` for every `H`, and off the
  blocks the allocator hands out (`OffHeap.off_foot`, `Fresh.off_heap`).
* **The frame.** A contract's frame is `HFrm ρ ws H m M`: memory changed only
  in the named written regions `ws` (`Kit/Frame.lean`: the stack, the
  structs, the digit arrays it owns, as for every other contract) and in the
  allocator's footprint `Foot H` for the blocks `H` it leaves alone. A
  freshly allocated block lies in `Foot H` (`Fresh.foot`); a freed one is a
  named region (the old digit array); `Foot (e :: H) ⊆ Foot H`
  (`Foot.of_cons`). Read-only facts move across an `HFrm` by `HFrm.keep`
  when their regions miss `ws` (closed, as `Frm.keep`) and `Foot H`
  (`OffFoot`: the regions are off-heap or live blocks of `H`).
* **The call context.** `ACtx m v sp F`: what an allocator call needs of the
  caller (code, `_impure_ptr`, `gp`, a 16-aligned stack of `F` bytes above
  the arena). `ACtx.ctx` gives `Api.Alloc.Ctx` for a callee frame inside.

Every GPR mapped (the model's invariant) is a field of `At` (`Kit/At.lean`),
so these contracts are plain `At` triples.
-/

namespace Tom.Machine.Api.Heap

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc

/-! ## Off the allocator -/

/-- The lowest allocator datum: `__malloc_av_` (`0x800188a0`); `_impure_ptr`,
the other globals and the arena lie above it. -/
abbrev allocLo : Nat := 0x800188a0

/-- `[a, a + n)` lies off everything the allocator owns or hands out: below its
data or above the arena. -/
def OffHeap (a n : Nat) : Prop := a + n ≤ allocLo ∨ heapEnd ≤ a

/-- The digit block of `a` at `dp`. -/
abbrev digBlk (dp : Nat) (a : MpInt) : Nat × Nat := (dp, 4 * a.alloc)

/-- **An `mp_int` on the heap**: `a` at `p`, its digits the live block
`(dp, 4 * a.alloc)` of `H`, its struct off the allocator. -/
structure MpLive (m : Mem) (H : List (Nat × Nat)) (p dp : Nat) (a : MpInt) : Prop where
  repr : MpAt m p dp a
  blk : digBlk dp a ∈ H
  soff : OffHeap p 24

theorem global_ge {x : Nat} (h : Global x) : allocLo ≤ x := by
  have eL : allocLo = 0x800188a0 := rfl
  unfold Global at h; omega

theorem OffHeap.off_foot {a n : Nat} (h : OffHeap a n) {H : List (Nat × Nat)} {x : Nat}
    (h1 : a ≤ x) (h2 : x < a + n) : ¬ Foot H x := by
  have eS : heapStart = 0x80019d10 := rfl
  have eE : heapEnd = 0x87800000 := rfl
  have eL : allocLo = 0x800188a0 := rfl
  rintro (hg | ⟨hs, he, _⟩)
  · have := global_ge hg; have := Global.lt hg; unfold OffHeap at h; omega
  · unfold OffHeap at h; omega

theorem OffHeap.sub {a n b k : Nat} (h : OffHeap a n) (h1 : a ≤ b) (h2 : b + k ≤ a + n) : OffHeap b k := by
  unfold OffHeap at *; omega

/-- A live block is off the footprint. -/
theorem blk_off_foot {m : Mem} {H : List (Nat × Nat)} (hH : Heap m H) {e : Nat × Nat} (he : e ∈ H)
    {x : Nat} (hx : InBlk e x) : ¬ Foot H x :=
  Foot.off_blk he hx fun hg => by
    have := Fn.Alloc.Heap.blk hH he; have := Global.lt hg; unfold InBlk at hx; omega


end Tom.Machine.Api.Heap

namespace Tom.Machine.Api.Alloc

open Vsa.Sim Tom.Machine Tom.Machine.Code Tom.Machine.Api.Heap

/-- A fresh block lies in the footprint. -/
theorem Fresh.foot {H : List (Nat × Nat)} {q n : Nat} (h : Fresh H q n) {x : Nat}
    (hx : InBlk (q, n) x) : Foot H x :=
  .inr ⟨by have := h.lo; unfold InBlk at hx; simp only at hx; omega,
    by have := h.hi; unfold InBlk at hx; simp only at hx; omega, fun e he => h.disj e he x hx⟩


/-- A fresh block misses a live one (both nonempty). -/
theorem Fresh.disj_blk {H : List (Nat × Nat)} {q n : Nat} (h : Fresh H q n) {e : Nat × Nat} (he : e ∈ H)
    (hn : 0 < n) (he0 : 0 < e.2) : Disj q n e.1 e.2 := by
  unfold Disj
  refine Classical.byContradiction fun hc => ?_
  by_cases hle : q ≤ e.1
  · exact h.disj e he e.1 ⟨by omega, by omega⟩ ⟨Nat.le_refl _, by omega⟩
  · exact h.disj e he q ⟨Nat.le_refl _, by omega⟩ ⟨by omega, by omega⟩

/-- A fresh block misses an off-heap range. -/
theorem Fresh.off_heap {H : List (Nat × Nat)} {q n : Nat} (h : Fresh H q n) {a k : Nat}
    (ho : OffHeap a k) : Disj q n a k := by
  have := h.lo; have := h.hi
  have eS : heapStart = 0x80019d10 := rfl
  have eE : heapEnd = 0x87800000 := rfl
  have eL : allocLo = 0x800188a0 := rfl
  unfold OffHeap at ho; unfold Disj; omega

theorem Foot.of_cons {H : List (Nat × Nat)} {e : Nat × Nat} {x : Nat} (h : Foot (e :: H) x) : Foot H x := by
  rcases h with hg | ⟨h1, h2, h3⟩
  · exact .inl hg
  · exact .inr ⟨h1, h2, fun e' he => h3 e' (List.mem_cons_of_mem _ he)⟩

/-- A block of `H` to the front. -/
theorem Heap.pick {m : Mem} {H : List (Nat × Nat)} (h : Heap m H) {e : Nat × Nat} (he : e ∈ H) :
    Heap m (e :: H.erase e) :=
  h.perm (List.perm_cons_erase he)



/-- An `mp_int` through a call's frame clause that misses its struct and digits. -/
theorem Keep.mpAt {W : Nat → Prop} {m M : Mem} {p dp : Nat} {a : MpInt} (hk : Keep W m M) (h : MpAt m p dp a)
    (hs : ∀ x, p ≤ x → x < p + 24 → ¬ W x) (hd : ∀ x, dp ≤ x → x < dp + 4 * a.alloc → ¬ W x) : MpAt M p dp a :=
  h.of_agree (fun x h1 h2 => hk x (hs x h1 h2)) (fun x h1 h2 => hk x (hd x h1 h2))

/-- The footprint for more blocks lies in the one for fewer. -/
theorem Foot.of_append {H H' : List (Nat × Nat)} {x : Nat} (h : Foot (H' ++ H) x) : Foot H x := by
  rcases h with hg | ⟨h1, h2, h3⟩
  · exact .inl hg
  · exact .inr ⟨h1, h2, fun e he => h3 e (List.mem_append_right _ he)⟩

/-- A read through a call's frame clause that misses it. -/
theorem Keep.bytesT8 {W : Nat → Prop} {m M : Mem} {a : Nat} (h : Keep W m M)
    (hw : ∀ x, a ≤ x → x < a + 8 → ¬ W x) : bytesT8 M a = bytesT8 m a :=
  bytesT8_congr fun x h1 h2 => h x (hw x h1 h2)

theorem Keep.bytesT4 {W : Nat → Prop} {m M : Mem} {a : Nat} (h : Keep W m M)
    (hw : ∀ x, a ≤ x → x < a + 4 → ¬ W x) : bytesT4 M a = bytesT4 m a :=
  bytesT4_congr fun x h1 h2 => h x (hw x h1 h2)

/-- The code through a call's frame clause that misses the text. -/
theorem Keep.img {W : Nat → Prop} {m M : Mem} (h : Keep W m M)
    (hw : ∀ x, textBase ≤ x → x < textBase + textLen → ¬ W x) (hi : Img m) : Img M :=
  @Img.reads Unit (fun _ => textIv) () (Iv.sub_self _) m M
    (fun x hx => hx.elim (fun h' => h x (hw x (by exact h'.1) (by exact h'.2))) (fun h' => h'.elim)) hi


/-- A word read totally depends only on the total reads of its bytes
(`realloc`'s copy clause). -/
theorem bytesT4_of_getD {m M : Mem} {a b : Nat} (h : ∀ k, k < 4 → (M[a + k]?).getD 0 = (m[b + k]?).getD 0) :
    bytesT4 M a = bytesT4 m b := by
  have h0 := h 0 (by decide); simp only [Nat.add_zero] at h0
  simp only [bytesT4]; rw [h0, h 1 (by decide), h 2 (by decide), h 3 (by decide)]

/-- `realloc`'s and `free`'s writes miss an off-heap byte outside their stack. -/
theorem blkW_off {H : List (Nat × Nat)} {p n sp x : Nat} (hb : heapStart ≤ p ∧ p + n ≤ heapEnd)
    (hx : OffHeap x 1) (hs : x < sp - depth ∨ sp ≤ x) : ¬ blkW H p n sp x := by
  rintro (hf | hb' | hk)
  · exact hx.off_foot (Nat.le_refl _) (by omega) hf
  · unfold OffHeap at hx; unfold InBlk at hb'; simp only at hb'
    have : allocLo ≤ heapStart := by decide
    omega
  · unfold Stk at hk; omega

/-- `calloc`'s writes miss an off-heap byte outside its stack. -/
theorem callocW_off {H : List (Nat × Nat)} {sp x : Nat} (hx : OffHeap x 1)
    (hs : x < sp - callocDepth ∨ sp ≤ x) : ¬ callocW H sp x := by
  rintro (hf | hk)
  · exact hx.off_foot (Nat.le_refl _) (by omega) hf
  · unfold Stk at hk; omega

theorem OffHeap.text {x : Nat} (h1 : textBase ≤ x) (h2 : x < textBase + textLen) : OffHeap x 1 := by
  have eL : allocLo = 0x800188a0 := rfl
  unfold OffHeap textBase textLen at *; omega

end Tom.Machine.Api.Alloc

namespace Tom.Machine.Api.Heap

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc

/-! ## The frame -/

section
variable {ι : Type} {ρ : ι → Iv}

/-- **The frame of an allocating call**: `M` equals `m` outside the named
regions `ws` and the allocator's footprint for the blocks `H` it leaves alone. -/
def HFrm (ρ : ι → Iv) (ws : List ι) (H : List (Nat × Nat)) (m M : Mem) : Prop :=
  Keep (fun x => InAny ρ ws x ∨ Foot H x) m M

theorem HFrm.of_frm {ws : List ι} {H : List (Nat × Nat)} {m M : Mem} (h : Frm ρ ws m M) : HFrm ρ ws H m M :=
  fun x hx => h x fun h' => hx (.inl h')

theorem HFrm.refl (ws : List ι) (H : List (Nat × Nat)) (m : Mem) : HFrm ρ ws H m m := fun _ _ => rfl

theorem HFrm.trans {ws : List ι} {H : List (Nat × Nat)} {m M M' : Mem} (h : HFrm ρ ws H m M)
    (h' : HFrm ρ ws H M M') : HFrm ρ ws H m M' := fun x hx => (h' x hx).trans (h x hx)


/-- A call whose frame clause is `W`, inside the names and the footprint. -/
theorem HFrm.ofKeep {ws : List ι} {H : List (Nat × Nat)} {m M : Mem} {W : Nat → Prop} (h : Keep W m M)
    (hW : ∀ x, W x → InAny ρ ws x ∨ Foot H x) : HFrm ρ ws H m M :=
  Keep.mono h hW

/-- A frame for fewer blocks left alone (more blocks owned) is one for more. -/
theorem HFrm.cons {ws : List ι} {H : List (Nat × Nat)} {e : Nat × Nat} {m M : Mem}
    (h : HFrm ρ ws (e :: H) m M) : HFrm ρ ws H m M :=
  Keep.mono h fun _ hx => Or.imp_right Foot.of_cons hx

theorem HFrm.mono {ws ws' : List ι} {H : List (Nat × Nat)} {m M : Mem} [DecidableEq ι]
    (h : HFrm ρ ws H m M) (hs : SubN ws ws' = true := by decide) : HFrm ρ ws' H m M :=
  Keep.mono h fun x hx => Or.imp_left (fun h' => by
    obtain ⟨w, hw, hxw⟩ := h'.exists
    exact InAny.of_mem (of_decide_eq_true (List.all_eq_true.1 hs w hw)) hxw) hx


/-- A callee's frame in its names is one in the caller's (`Frm.push`). -/
theorem HFrm.push {κ : Type} {σ : κ → Iv} (f : κ → ι) (hsub : ∀ k, (σ k).Sub (ρ (f k)))
    {ws : List κ} {H : List (Nat × Nat)} {m M : Mem} (h : HFrm σ ws H m M) : HFrm ρ (ws.map f) H m M :=
  Keep.mono h fun x hx => Or.imp_left (fun hx' => by
    obtain ⟨w, hw, hxw⟩ := hx'.exists
    have := hsub w
    exact InAny.of_mem (List.mem_map_of_mem hw) (by unfold Iv.Sub Iv.In at *; omega)) hx

/-- The regions `rs` are off the footprint. -/
def OffFoot (ρ : ι → Iv) (rs : List ι) (H : List (Nat × Nat)) : Prop :=
  ∀ x, InAny ρ rs x → ¬ Foot H x

/-- **The frame rule** across an allocating call. -/
theorem HFrm.keep [DecidableEq ι] {isW : ι → Bool} {rs ws : List ι} {H : List (Nat × Nat)}
    {P : Mem → Prop} {m M : Mem} (hS : Sound ρ isW) (hR : Reads ρ rs P) (hF : HFrm ρ ws H m M)
    (hoff : OffFoot ρ rs H) (h : P m) (hm : Misses isW rs ws = true := by decide) : P M :=
  hR m M (fun x hx => hF x fun hw => hw.elim
    (fun hw => by
      obtain ⟨r, hr, hxr⟩ := hx.exists
      obtain ⟨w, hw, hxw⟩ := hw.exists
      have hd := hS r w (List.all_eq_true.1 (List.all_eq_true.1 hm r hr) w hw)
      unfold Iv.Disj Tom.Machine.Disj Iv.In at *; omega)
    (fun hf => hoff x hx hf)) h

theorem OffFoot.nil (H : List (Nat × Nat)) : OffFoot ρ [] H := fun _ h => h.elim

theorem OffFoot.cons {r : ι} {rs : List ι} {H : List (Nat × Nat)} (h : ∀ x, (ρ r).In x → ¬ Foot H x)
    (hs : OffFoot ρ rs H) : OffFoot ρ (r :: rs) H := fun x hx => hx.elim (h x) (hs x)

theorem OffFoot.of_offHeap {r : ι} {H : List (Nat × Nat)} (h : OffHeap (ρ r).base (ρ r).len) :
    ∀ x, (ρ r).In x → ¬ Foot H x := fun _ hx => h.off_foot hx.1 hx.2

theorem OffFoot.of_blk {r : ι} {m : Mem} {H : List (Nat × Nat)} (hH : Heap m H)
    (he : ((ρ r).base, (ρ r).len) ∈ H) : ∀ x, (ρ r).In x → ¬ Foot H x :=
  fun _ hx => blk_off_foot hH he hx

end

/-- The text section is off the footprint. -/
theorem text_off_heap : OffHeap textIv.base textIv.len := by
  unfold OffHeap textIv textBase textLen; decide

/-- `_impure_ptr` is off the footprint and below the arena. -/
theorem impure_off_foot {H : List (Nat × Nat)} {x : Nat} (h1 : impurePtr ≤ x) (h2 : x < impurePtr + 8) :
    ¬ Foot H x := by
  have eS : heapStart = 0x80019d10 := rfl
  have eE : heapEnd = 0x87800000 := rfl
  unfold impurePtr at *
  rintro (hg | ⟨hs, _, _⟩)
  · unfold Global at hg; omega
  · omega

theorem ImpureAt.of_keep {m M : Mem} {W : Nat → Prop}
    (hk : Keep W m M) (hw : ∀ x, impurePtr ≤ x → x < impurePtr + 8 → ¬ W x) (h : ImpureAt m) : ImpureAt M :=
  fun i b hb => by
    have hi : i < 8 := by
      have := (List.getElem?_eq_some_iff.1 hb).1
      simpa [impureBytes] using this
    rw [hk _ (hw _ (by omega) (by omega))]; exact h i b hb

/-! ## The call context -/

/-- **What an allocating function needs of its caller** besides its operands:
the code, `_impure_ptr`, `gp`, and a 16-aligned stack of `F` bytes (its own
frame and the allocator's) above the arena and below 4 GiB. -/
structure ACtx (m : Mem) (v : Abi) (sp F : Nat) : Prop where
  img : Img m
  impure : ImpureAt m
  gp : v.gp = gpV
  sp_v : v.sp = BitVec.ofNat 64 sp
  sp_al : sp % 16 = 0
  sp_lo : heapEnd + F ≤ sp
  sp_hi : sp ≤ 0x100000000

/-- The allocator's context for a call from a frame `k` bytes below `sp`
(the callee's Abi `v'`: `sp - k`, our `gp`). -/
theorem ACtx.ctx {m M : Mem} {v v' : Abi} {sp F k F' : Nat} {ra : BitVec 64} (h : ACtx m v sp F)
    (hk : k % 16 = 0) (hF : F' + k ≤ F) (hsp : v'.sp = BitVec.ofNat 64 (sp - k)) (hgp : v'.gp = v.gp)
    (himg : Img M) (himp : ImpureAt M) (hra : ra.toNat % 4 = 0) : Ctx M v' (sp - k) F' ra :=
  have := h.sp_lo; have := h.sp_al
  { img := himg, impure := himp, gp := hgp.trans h.gp, sp_v := hsp
    sp_al := by omega, sp_lo := by omega, sp_hi := by have := h.sp_hi; omega, ra_al := hra }

/-- The stack of an `ACtx` is RAM off the arena. -/
theorem ACtx.ram {m : Mem} {v : Abi} {sp F : Nat} (h : ACtx m v sp F) : Ram (sp - F) F := by
  have := h.sp_lo; have := h.sp_hi
  have eE : heapEnd = 0x87800000 := rfl
  exact ⟨by omega, by omega, .inr (by unfold tohostAddr; omega)⟩

theorem ACtx.off {m : Mem} {v : Abi} {sp F : Nat} (h : ACtx m v sp F) : OffHeap (sp - F) F := by
  have := h.sp_lo; unfold OffHeap; omega

end Tom.Machine.Api.Heap
