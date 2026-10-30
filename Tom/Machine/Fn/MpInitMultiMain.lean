import Tom.Machine.Api.MpInitMulti
import Tom.Machine.Fn.MpInitMain
import Tom.Machine.Fn.MpClearMain
import Tom.Machine.Fn.MpClearMultiMain

/-!
# `mp_init_multi` on the machine: the whole function

The prologue spills the argument registers (`Fn/MpInitMulti.lean`); the loop
at `1428` is an induction over the arguments still to initialise (`loop`),
each round `mp_init` (`Fn.MpInit.init_correct`); on its failure the cleanup
loop at `144c` (`cloop`) clears the initialised prefix with `mp_clear`
(`Fn.MpClear.correct`). Both invariants share `Ours` (the argument slots, the
saved registers, the code, the frame), carried across a callee by `Ours.keep`:
every callee writes only `CW` (its stack, one struct, one block, the
footprint).
-/


namespace Tom.Machine.Fn.MpInitMulti

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api
open Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Api.Multi

/-- What a callee at depth 112 on the struct `p` may write: its stack, the
struct, `E` (inside the arena), the footprint for `K`. -/
def CW (sp p : Nat) (E : Nat → Prop) (K : List (Nat × Nat)) (x : Nat) : Prop :=
  (sp - 672 ≤ x ∧ x < sp - 112) ∨ (p ≤ x ∧ x < p + 24) ∨ E x ∨ Foot K x

/-- Our part of memory: the argument slots, the `va_list` pointer, the saved
registers, the code, `_impure_ptr`, the frame so far. -/
structure Ours (m : Mem) (v : Abi) (H : List (Nat × Nat)) (sp : Nat) (ra : BitVec 64) (xs : List Nat)
    (va : Nat) (M : Mem) : Prop where
  slots : ∀ j w, (args xs)[j]? = some w → 1 ≤ j → bytesT8 M (sp - 64 + 8 * j) = BitVec.ofNat 64 w
  va_v : bytesT8 M (sp - 112) = BitVec.ofNat 64 va
  ra_v : bytesT8 M (sp - 112 + 40) = ra
  s1_v : bytesT8 M (sp - 112 + 24) = v.s.s1
  s0_v : bytesT8 M (sp - 112 + 32) = v.s0
  s2_v : bytesT8 M (sp - 112 + 16) = v.s.s2
  img : Img M
  impure : ImpureAt M
  frame : Keep (MpInitMulti.W xs H sp) m M

section
variable {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp : Nat} {xs : List Nat}
  {ra : BitVec 64}

theorem args_len' (xs : List Nat) : (args xs).length = xs.length + 1 := by simp [args]

/-- `Ours` across a callee's `CW`. -/
theorem Ours.keep (hP : MpInitMulti.Pre m v H sp xs ra) {va : Nat} {M M' : Mem} (hO : Ours m v H sp ra xs va M)
    {p : Nat} {E : Nat → Prop} {K : List (Nat × Nat)} (hk : Keep (CW sp p E K) M M') (hp : p ∈ xs)
    (hE : ∀ x, E x → heapStart ≤ x ∧ x < heapEnd) (hEH : ∀ x, E x → Foot H x)
    (hK : ∀ x, Foot K x → Foot H x) : Ours m v H sp ra xs va M' := by
  have eE : heapEnd = 0x87800000 := rfl
  have eS : heapStart = 0x80019d10 := rfl
  have eL : allocLo = 0x800188a0 := rfl
  have eF : MpInitMulti.F = 672 := rfl
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi
  have hst := hP.st.stk p hp
  have hof := hP.st.off p hp
  have hco := hP.st.code p hp
  unfold Disj at hst hco; unfold OffHeap at hof
  rw [eF] at hst
  have wmiss : ∀ a, sp - 112 ≤ a → a < sp + argLen (xs.length + 1) → ¬ CW sp p E K a := by
    intro a h1 h2 hw
    rcases hw with h | h | h | h
    · omega
    · omega
    · have := hE a h; omega
    · exact OffHeap.off_foot (a := a) (n := 1) (.inr (by omega)) (Nat.le_refl _) (by omega) h
  refine { slots := fun j w hj h1 => ?_, va_v := ?_, ra_v := ?_, s1_v := ?_, s0_v := ?_, s2_v := ?_,
           img := ?_, impure := ?_, frame := ?_ }
  · have hlt : j < xs.length + 1 := by
      have := (List.getElem?_eq_some_iff.1 hj).1; rwa [args_len'] at this
    rw [hk.bytesT8 fun a h1' h2' => wmiss a (by omega) (by unfold argLen; omega)]; exact hO.slots j w hj h1
  · rw [hk.bytesT8 fun a h1 h2 => wmiss a (by omega) (by unfold argLen; omega)]; exact hO.va_v
  · rw [hk.bytesT8 fun a h1 h2 => wmiss a (by omega) (by unfold argLen; omega)]; exact hO.ra_v
  · rw [hk.bytesT8 fun a h1 h2 => wmiss a (by omega) (by unfold argLen; omega)]; exact hO.s1_v
  · rw [hk.bytesT8 fun a h1 h2 => wmiss a (by omega) (by unfold argLen; omega)]; exact hO.s0_v
  · rw [hk.bytesT8 fun a h1 h2 => wmiss a (by omega) (by unfold argLen; omega)]; exact hO.s2_v
  · refine hk.img (fun a h1 h2 hw => ?_) hO.img
    simp only [textBase, textLen] at h1 h2 hco
    rcases hw with h | h | h | h
    · omega
    · omega
    · have := hE a h; omega
    · exact (OffHeap.text (x := a) (by unfold textBase; omega) (by unfold textBase textLen; omega)).off_foot
        (Nat.le_refl _) (by omega) h
  · refine ImpureAt.of_keep hk (fun a h1 h2 hw => ?_) hO.impure
    unfold impurePtr at h1 h2
    rcases hw with h | h | h | h
    · omega
    · omega
    · have := hE a h; omega
    · exact impure_off_foot (by unfold impurePtr; omega) (by unfold impurePtr; omega) h
  · refine Keep.mono (Keep.trans hO.frame hk) fun a ha => ?_
    rcases ha with h | h
    · exact h
    · rcases h with h | h | h | h
      · exact .inl (by unfold Stk; have : MpInit.Finit = 560 := rfl; omega)
      · exact .inr (.inl ⟨p, hp, h⟩)
      · exact .inr (.inr (hEH a h))
      · exact .inr (.inr (hK a h))

/-- A struct of the arguments other than `p` misses `CW`. -/
theorem cw_struct (hP : MpInitMulti.Pre m v H sp xs ra) {p q : Nat} {E : Nat → Prop} {K : List (Nat × Nat)}
    (hq : q ∈ xs) (hd : Disj q 24 p 24) (hE : ∀ x, E x → heapStart ≤ x ∧ x < heapEnd) :
    ∀ x, q ≤ x → x < q + 24 → ¬ CW sp p E K x := by
  have eE : heapEnd = 0x87800000 := rfl
  have eS : heapStart = 0x80019d10 := rfl
  have eL : allocLo = 0x800188a0 := rfl
  have eF : MpInitMulti.F = 672 := rfl
  have hst := hP.st.stk q hq
  have hof := hP.st.off q hq
  unfold Disj at hst hd; unfold OffHeap at hof
  rw [eF] at hst
  have := hP.ctx.sp_lo
  intro x h1 h2 hw
  rcases hw with h | h | h | h
  · omega
  · omega
  · have := hE x h; omega
  · exact hP.st.off q hq |>.off_foot h1 h2 h

/-- A block of `K` apart from `E` misses `CW`. -/
theorem cw_blk (hP : MpInitMulti.Pre m v H sp xs ra) {M : Mem} {p : Nat} {E : Nat → Prop} {K : List (Nat × Nat)}
    (hK : Heap M K) {e : Nat × Nat} (he : e ∈ K) (hp : p ∈ xs) (hEe : ∀ x, InBlk e x → ¬ E x) :
    ∀ x, InBlk e x → ¬ CW sp p E K x := by
  have eE : heapEnd = 0x87800000 := rfl
  have eS : heapStart = 0x80019d10 := rfl
  have eL : allocLo = 0x800188a0 := rfl
  have hb := Fn.Alloc.Heap.blk hK he
  have hof := hP.st.off p hp
  unfold OffHeap at hof
  have := hP.ctx.sp_lo
  have eF : MpInitMulti.F = 672 := rfl
  intro x hx hw
  unfold InBlk at hx
  rcases hw with h | h | h | h
  · omega
  · omega
  · exact hEe x hx h
  · exact blk_off_foot hK he hx h

/-- `Ours` after a store to the `va_list` pointer. -/
theorem Ours.set_va (hP : MpInitMulti.Pre m v H sp xs ra) {va : Nat} {M : Mem} (hO : Ours m v H sp ra xs va M)
    (va' : Nat) : Ours m v H sp ra xs va' (writeLog M [(sp - 112, 8, BitVec.ofNat 64 va')]) := by
  have eF : MpInitMulti.F = 672 := rfl
  have hsl := hP.ctx.sp_lo
  have eE : heapEnd = 0x87800000 := rfl
  have hk : Keep (fun a => sp - 112 ≤ a ∧ a < sp - 104) M (writeLog M [(sp - 112, 8, BitVec.ofNat 64 va')]) :=
    fun a ha => writeLog_out _ _ _ ⟨by simp only; omega, trivial⟩
  exact
    { slots := fun j w hj h1 => by
        rw [hk.bytesT8 fun a h1' h2' hw => by omega]; exact hO.slots j w hj h1
      va_v := bytesT8_sd_self _ _ _
      ra_v := by rw [hk.bytesT8 fun a h1 h2 hw => by omega]; exact hO.ra_v
      s1_v := by rw [hk.bytesT8 fun a h1 h2 hw => by omega]; exact hO.s1_v
      s0_v := by rw [hk.bytesT8 fun a h1 h2 hw => by omega]; exact hO.s0_v
      s2_v := by rw [hk.bytesT8 fun a h1 h2 hw => by omega]; exact hO.s2_v
      img := hk.img (fun a h1 h2 hw => by unfold textBase textLen at h2; omega) hO.img
      impure := ImpureAt.of_keep hk (fun a h1 h2 hw => by unfold impurePtr at h2; omega) hO.impure
      frame := Keep.mono (Keep.trans hO.frame hk) fun a ha => ha.elim id fun h =>
        .inl (by have eF : MpInitMulti.F = 672 := rfl; simp only [Stk, eF]; omega) }

/-- `Ours` after the store to `sp - 104` (the failure path's `s1` spill). -/
theorem Ours.set104 (hP : MpInitMulti.Pre m v H sp xs ra) {va : Nat} {M : Mem} (hO : Ours m v H sp ra xs va M)
    (x : BitVec 64) : Ours m v H sp ra xs va (writeLog M [(sp - 104, 8, x)]) := by
  have hsl := hP.ctx.sp_lo
  have eE : heapEnd = 0x87800000 := rfl
  have hk : Keep (fun a => sp - 104 ≤ a ∧ a < sp - 96) M (writeLog M [(sp - 104, 8, x)]) :=
    fun a ha => writeLog_out _ _ _ ⟨by simp only; omega, trivial⟩
  exact
    { slots := fun j w hj h1 => by
        rw [hk.bytesT8 fun a h1' h2' hw => by omega]; exact hO.slots j w hj h1
      va_v := by rw [hk.bytesT8 fun a h1 h2 hw => by omega]; exact hO.va_v
      ra_v := by rw [hk.bytesT8 fun a h1 h2 hw => by omega]; exact hO.ra_v
      s1_v := by rw [hk.bytesT8 fun a h1 h2 hw => by omega]; exact hO.s1_v
      s0_v := by rw [hk.bytesT8 fun a h1 h2 hw => by omega]; exact hO.s0_v
      s2_v := by rw [hk.bytesT8 fun a h1 h2 hw => by omega]; exact hO.s2_v
      img := hk.img (fun a h1 h2 hw => by unfold textBase textLen at h2; omega) hO.img
      impure := ImpureAt.of_keep hk (fun a h1 h2 hw => by unfold impurePtr at h2; omega) hO.impure
      frame := Keep.mono (Keep.trans hO.frame hk) fun a ha => ha.elim id fun h =>
        .inl (by have eF : MpInitMulti.F = 672 := rfl; simp only [Stk, eF]; omega) }

/-- Two arguments at different positions have apart structs. -/
theorem st_apart (hP : MpInitMulti.Pre m v H sp xs ra) {i j : Nat} (hi : i < xs.length) (hj : j < xs.length)
    (hne : i ≠ j) : Disj xs[i] 24 xs[j] 24 := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact List.pairwise_iff_getElem.1 hP.st.pw i j hi hj h
  · exact Disj.symm (List.pairwise_iff_getElem.1 hP.st.pw j i hj hi h)

/-- The Abi `mp_clear` sees in the cleanup loop. -/
def cAbi (v : Abi) (sp b s p : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 112), s0 := BitVec.ofNat 64 b,
           s := { v.s with s1 := BitVec.ofNat 64 s, s2 := BitVec.ofNat 64 p } }

/-- The `mp_clear` call at `1450`, back at `1454`. -/
theorem clear_call (v : Abi) (outp : Array String) (sp b s p : Nat) (M : Mem)
    (hc : CodeAt M mpInitMultiBase mpInitMultiCode) :
    Triple (At 0x80001450#64 (callL sp b s p) M v.keepR2 outp)
      (At Fn.MpClear.entry (Api.MpClear.entryL 0x80001454#64 p) M (cAbi v sp b s p).keep outp) := by
  refine Triple.rmap (fun c h => ?_)
    (jal_at (pc := 0x80001450#64) (w := 0x3c9030ef#32) (imm := 0x3bc8#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 112)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 s),
        (18, BitVec.ofNat 64 p), (10, BitVec.ofNat 64 p)])
      (hc.word (a := (0x80001450#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [callL]) (by simp [keysG]) (by simp [Abi.keepR2, keysG]))
  have hpc : (0x80001450#64 : BitVec 64) + sign_extend (m := 64) (0x3bc8#21) = Fn.MpClear.entry := by decide
  have hra : Sail.BitVec.addInt (0x80001450#64 : BitVec 64) 4 = 0x80001454#64 := by decide
  rw [hpc, hra] at h
  exact h.reshape (by simp [Api.MpClear.entryL]) (by simp [cAbi, Abi.keep, Abi.keepR2, sKeepL])

/-- The Abi `mp_init` sees in the main loop. -/
def iAbi (v : Abi) (sp i p0 : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 112), s0 := BitVec.ofNat 64 i,
           s := { v.s with s1 := BitVec.ofNat 64 (sp - 56), s2 := BitVec.ofNat 64 p0 } }

/-- The `mp_init` call at `1428`, back at `142c`. -/
theorem init_call (v : Abi) (outp : Array String) (sp i p0 p : Nat) (M : Mem)
    (hc : CodeAt M mpInitMultiBase mpInitMultiCode) :
    Triple (At 0x80001428#64 (headL sp i p0 p) M v.keepR2 outp)
      (At Fn.MpInit.initEntry (Api.MpInit.initL 0x8000142c#64 p) M (iAbi v sp i p0).keep outp) := by
  refine Triple.rmap (fun c h => ?_)
    (jal_at (pc := 0x80001428#64) (w := 0xed5ff0ef#32) (imm := 0x1ffed4#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 112)), (8, BitVec.ofNat 64 i), (9, BitVec.ofNat 64 (sp - 56)),
        (18, BitVec.ofNat 64 p0), (10, BitVec.ofNat 64 p)])
      (hc.word (a := (0x80001428#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [headL]) (by simp [keysG]) (by simp [Abi.keepR2, keysG]))
  have hpc : (0x80001428#64 : BitVec 64) + sign_extend (m := 64) (0x1ffed4#21) = Fn.MpInit.initEntry := by decide
  have hra : Sail.BitVec.addInt (0x80001428#64 : BitVec 64) 4 = 0x8000142c#64 := by decide
  rw [hpc, hra] at h
  exact h.reshape (by simp [Api.MpInit.initL]) (by simp [iAbi, Abi.keep, Abi.keepR2, sKeepL])

theorem idx_of_mem {ys : List Arg} {n : Nat} (hys : ptrs ys = xs.take n) {y : Arg} (hy : y ∈ ys) :
    ∃ j, ∃ hj : j < xs.length, j < n ∧ y.1 = xs[j] := by
  have hm : y.1 ∈ xs.take n := hys ▸ List.mem_map_of_mem hy
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.1 hm
  rw [List.getElem_take] at he
  have := List.length_take_le' n xs
  exact ⟨j, by simp at hj; omega, by simp at hj; omega, he.symm⟩

theorem mem_of_idx {ys : List Arg} {n : Nat} (hys : ptrs ys = xs.take n) {j : Nat} (hj : j < xs.length)
    (hjn : j < n) : ∃ y ∈ ys, y.1 = xs[j] := by
  have hm : xs[j] ∈ ptrs ys := by
    rw [hys]; exact List.mem_iff_getElem.2 ⟨j, by simp; omega, by rw [List.getElem_take]⟩
  obtain ⟨y, hy, he⟩ := List.mem_map.1 hm
  exact ⟨y, hy, he⟩

theorem args_get {j : Nat} (hj : j < xs.length) : (args xs)[j]? = some xs[j] := by
  simp [args, List.getElem?_append_left hj]

theorem args_end : (args xs)[xs.length]? = some 0 := by simp [args]

theorem ptrs_get {ys : List Arg} {n : Nat} (hys : ptrs ys = xs.take n) {zs us : List Arg} {u : Arg}
    (he : zs ++ u :: us = ys) (hn : n ≤ xs.length) : ∃ h : zs.length < xs.length, u.1 = xs[zs.length] := by
  have hl : zs.length < n := by
    have h1 := congrArg List.length hys
    rw [← he, ptrs, List.length_map, List.length_append, List.length_cons, List.length_take] at h1
    omega
  refine ⟨by omega, ?_⟩
  have := congrArg (·[zs.length]?) hys
  simp only [← he, ptrs, List.map_append, List.map_cons] at this
  rw [List.getElem?_append_right (by simp), List.length_map, Nat.sub_self, List.getElem?_cons_zero,
    List.getElem?_take, if_pos hl, List.getElem?_eq_getElem (by omega)] at this
  exact Option.some.inj this

/-- `mp_clear`'s precondition for an argument `u` live in `us`. -/
theorem clear_pre (hP : MpInitMulti.Pre m v H sp xs ra) {va : Nat} {M : Mem} (hO : Ours m v H sp ra xs va M)
    {u : Arg} {us : List Arg} (hu : u.1 ∈ xs) (hr : MpAt M u.1 u.2.1 u.2.2) (hh : Heap M (blocks (u :: us) ++ H))
    (b s : Nat) :
    MpClear.Pre M (cAbi v sp b s u.1) (blocks us ++ H) (sp - 112) u.1 u.2.1 u.2.2 0x80001454#64 := by
  have eE : heapEnd = 0x87800000 := rfl
  have eS : heapStart = 0x80019d10 := rfl
  have eF : MpInitMulti.F = 672 := rfl
  have eC : MpClear.F = 544 := rfl
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi; have hsal := hP.ctx.sp_al
  have hby := Fn.Alloc.Heap.blk hh (e := digBlk u.2.1 u.2.2) (List.mem_append_left _ (List.mem_cons_self ..))
  simp only at hby
  have ho := hP.st.off u.1 hu
  unfold OffHeap at ho
  have eL : allocLo = 0x800188a0 := rfl
  have hlo : heapEnd + MpClear.F ≤ sp - 112 := by omega
  have hctx : ACtx M (cAbi v sp b s u.1) (sp - 112) MpClear.F :=
    ⟨hO.img, hO.impure, hP.ctx.gp, rfl, by omega, hlo, by omega⟩
  have hst := hP.st.stk u.1 hu
  have hco := hP.st.code u.1 hu
  have hlay : Sound (Un.lay MpClear.F (sp - 112) u.1 u.2.1 u.2.2) Un.isW := by
    intro r t h
    cases r <;> cases t <;> first
      | exact absurd h (by decide)
      | (simp only [Iv.Disj, Disj, Un.lay, textIv, textBase, textLen] at hst hco ⊢; omega)
  exact ⟨hr, hh, hP.st.ram u.1 hu, hP.st.al u.1 hu, hP.st.off u.1 hu, hctx, by decide, hlay⟩

/-- `mp_clear`'s frame as a `CW`. -/
theorem clear_cw {M M' : Mem} {u : Arg} {K : List (Nat × Nat)} (hs : 672 ≤ sp)
    (h : HFrm (Un.lay MpClear.F (sp - 112) u.1 u.2.1 u.2.2) Un.ws K M M') :
    Keep (CW sp u.1 (InBlk (digBlk u.2.1 u.2.2)) K) M M' := Keep.mono h fun a ha => by
  have eC : MpClear.F = 544 := rfl
  rcases ha with h | h
  · simp only [InAny, Un.ws, Iv.In, Un.lay, eC, or_false] at h
    rcases h with h | h | h
    · exact .inl ⟨by omega, by omega⟩
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

/-- The cleanup invariant: `zs` cleared again, `us` still live, `xs[n]` with `dp = NULL`. -/
structure CInv (m : Mem) (v : Abi) (H : List (Nat × Nat)) (sp : Nat) (ra : BitVec 64) (xs : List Nat) (n : Nat)
    (hn : n < xs.length) (zs us : List Arg) (M : Mem) : Prop where
  ours : ∃ va, Ours m v H sp ra xs va M
  done : ∀ z ∈ zs, MpAt M z.1 0 MpInt.cleared
  rest : ∀ u ∈ us, MpAt M u.1 u.2.1 u.2.2
  heap : Heap M (blocks us ++ H)
  dpk : bytesT8 M (xs[n] + 16) = 0#64

/-- **The cleanup loop**, from its head with `u` next. -/
theorem cloop (hP : MpInitMulti.Pre m v H sp xs ra) {n : Nat} (hn : n < xs.length) {ys : List Arg}
    (hys : ptrs ys = xs.take n) (hap : MpInitMulti.Apart ys H) :
    ∀ (us zs : List Arg) (u : Arg), zs ++ u :: us = ys → ∀ M, CInv m v H sp ra xs n hn zs (u :: us) M →
      Triple (At 0x8000144c#64 (clrL sp (sp - 56 + 8 * n) (sp - 56 + 8 * zs.length) u.1) M v.keepR2 outp)
        (MpInitMulti.Ret m v outp H sp xs ra)
  | us, zs, u, he, M, hI => by
    have hsf : SFacts sp :=
      have := hP.ctx.sp_lo; have := hP.ctx.sp_hi; have := hP.ctx.sp_al
      have eE : heapEnd = 0x87800000 := rfl
      { rs := ⟨by omega, by omega, .inr (by unfold tohostAddr; omega)⟩, sp_al := this, sp_ge := by omega
        code_off := by unfold mpInitMultiBase; omega }
    have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi
    have eE : heapEnd = 0x87800000 := rfl
    have eS : heapStart = 0x80019d10 := rfl
    have hsv := hP.ctx.sp_v
    obtain ⟨va, hO⟩ := hI.ours
    have hah := hP.args_hi; unfold argLen at hah
    have hlen : ys.length = n := by
      have h1 := congrArg List.length hys
      rw [ptrs, List.length_map, List.length_take] at h1; omega
    obtain ⟨hzl, hu1⟩ := ptrs_get hys he (by omega)
    have hzn : zs.length < n := by rw [← hlen, ← he]; simp
    have hux : u.1 ∈ xs := by rw [hu1]; exact List.getElem_mem _
    have huy : u ∈ ys := he ▸ List.mem_append_right _ (List.mem_cons_self ..)
    -- the structs of `ys` are pairwise apart
    have hpw : (ptrs ys).Pairwise fun p q => Disj p 24 q 24 := hys ▸ hP.st.pw.sublist (List.take_sublist n xs)
    rw [← he, ptrs_append] at hpw
    have hpw' := List.pairwise_append.1 hpw
    have hbpw := hap.pw
    rw [← he, blocks_append] at hbpw
    have hbpw' := (List.pairwise_append.1 hbpw).2.1
    have hbu := Fn.Alloc.Heap.blk hI.heap (e := digBlk u.2.1 u.2.2) (List.mem_append_left _ (List.mem_cons_self ..))
    simp only at hbu
    have hE : ∀ x, InBlk (digBlk u.2.1 u.2.2) x → heapStart ≤ x ∧ x < heapEnd := fun x hx => by
      unfold InBlk at hx; simp only at hx; omega
    have hEH : ∀ x, InBlk (digBlk u.2.1 u.2.2) x → Foot H x := fun x hx =>
      .inr ⟨(hE x hx).1, (hE x hx).2, fun e' he' => hap.off _ (List.mem_map_of_mem huy) e' he' x hx⟩
    refine Triple.seq (ca_step v outp sp _ _ u.1 M hO.img.mpInitMulti)
      (Triple.seq (clear_call v outp sp _ _ u.1 _ hO.img.mpInitMulti)
        (Triple.seq (Fn.MpClear.correct (clear_pre hP hO hux (hI.rest u (List.mem_cons_self ..)) hI.heap _ _)) ?_))
    intro c ⟨M', hA, hC⟩
    have hk := clear_cw (by omega) hC.frame
    have hO' := hO.keep hP hk hux hE hEH fun x hx => Foot.of_append hx
    have hA' : At 0x80001454#64 (cbackL sp (sp - 56 + 8 * n) (sp - 56 + 8 * zs.length)) M' v.keepR2 outp c :=
      hA.reshape (by simp [cbackL, cAbi, Abi.keep, sKeepL]) (by simp [cAbi, Abi.keep, Abi.keepR2, sKeepL])
    have hI' : CInv m v H sp ra xs n hn (zs ++ [u]) us M' :=
      { ours := ⟨va, hO'⟩
        done := fun z hz => by
          rcases List.mem_append.1 hz with hz | hz
          · refine hk.mpAt (hI.done z hz) (cw_struct hP (hP.st.pw |> fun _ => by
                obtain ⟨j, hj, -, hje⟩ := idx_of_mem hys (he ▸ List.mem_append_left _ hz); rw [hje]
                exact List.getElem_mem _)
              (hpw'.2.2 z.1 (List.mem_map_of_mem hz) u.1 (List.mem_cons_self ..)) hE) fun a h1 h2 => ?_
            simp [MpInt.cleared] at h2
          · simp only [List.mem_singleton] at hz; subst hz; exact hC.repr
        rest := fun w hw => by
          have hwy : w ∈ ys := he ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hw)
          obtain ⟨j, hj, -, hje⟩ := idx_of_mem hys hwy
          have hd : Disj w.1 24 u.1 24 := Disj.symm (List.rel_of_pairwise_cons hpw'.2.1 (List.mem_map_of_mem hw))
          have hdb : Disj u.2.1 (4 * u.2.2.alloc) w.2.1 (4 * w.2.2.alloc) :=
            List.rel_of_pairwise_cons hbpw' (List.mem_map_of_mem (f := fun x : Arg => digBlk x.2.1 x.2.2) hw)
          refine hk.mpAt (hI.rest w (List.mem_cons_of_mem _ hw))
            (cw_struct hP (by rw [hje]; exact List.getElem_mem _) hd hE) fun a h1 h2 => ?_
          exact cw_blk hP hC.heap (List.mem_append_left _ (List.mem_map_of_mem hw)) hux
            (fun x hx hx' => by unfold InBlk at hx hx'; unfold Disj at hdb; simp only at hx hx'; omega) a ⟨h1, h2⟩
        heap := hC.heap
        dpk := by
          rw [hk.bytesT8 fun a h1 h2 => cw_struct hP (List.getElem_mem _)
            (by rw [hu1]; exact st_apart hP hn hzl (by omega)) hE a (by omega) (by omega)]
          exact hI.dpk }
    cases us with
    | nil =>
      have hzn' : zs.length + 1 = n := by rw [← hlen, ← he]; simp
      have hO3 := hO'
      have hdone : ∀ i (h : i < n), MpAt M' (xs[i]'(by omega)) 0 MpInt.cleared := fun i h => by
        obtain ⟨y, hy, hye⟩ := mem_of_idx hys (by omega) h
        rw [← hye]; exact hI'.done y (he ▸ hy)
      refine Triple.seq (cc_step v outp sp _ _ M' hO'.img.mpInitMulti ⟨by omega, by omega,
          .inr (by unfold tohostAddr; omega)⟩ (by omega) (by omega))
        (Triple.rmap (fun c hA => ⟨_, _, hA.reshape (by simp [retL]) (by simp [retL, Abi.keep, Abi.keepR2, sKeepL, hsv]),
            .mem n hn hdone hI'.dpk (show Heap M' H by simpa [blocks] using hI'.heap) hO'.frame⟩)
          (fend_step ra v.s0 v.s.s1 v.s.s2 v outp sp M' hO'.img.mpInitMulti hP.ra_al hsf hO'.s0_v hO'.s2_v
            hO'.ra_v hO'.s1_v)) c hA'
    | cons u' us' =>
      have he' : (zs ++ [u]) ++ u' :: us' = ys := by rw [← he]; simp
      obtain ⟨hzl', hu1'⟩ := ptrs_get hys he' (by omega)
      have hzn' : zs.length + 1 < n := by rw [← hlen, ← he]; simp
      have hp := hO'.slots (zs.length + 1) u'.1 (by rw [hu1']; simp only [List.length_append, List.length_singleton] at hzl' ⊢; exact args_get hzl') (by omega)
      rw [show sp - 64 + 8 * (zs.length + 1) = sp - 56 + 8 * zs.length by omega] at hp
      exact Triple.seq (cb_step v outp sp _ _ u'.1 M' hO'.img.mpInitMulti ⟨by omega, by
          have := hP.args_hi; unfold argLen at this; omega, .inr (by unfold tohostAddr; omega)⟩ (by omega) (by omega)
          (by omega) hp)
        (by
          have := cloop hP hn hys hap us' (zs ++ [u]) u' he' (writeLog M' []) hI'
          simpa [Nat.mul_add, Nat.add_assoc] using this) c hA'

/-- The success invariant at the loop head: `ys` initialised. -/
structure Inv (m : Mem) (v : Abi) (H : List (Nat × Nat)) (sp : Nat) (ra : BitVec 64) (xs : List Nat)
    (ys : List Arg) (M : Mem) : Prop where
  ours : Ours m v H sp ra xs (sp - 56 + 8 * ys.length) M
  hp : ptrs ys = xs.take ys.length
  zero : ∀ y ∈ ys, y.2.2 = MpInt.zeroN defPrec
  live : ∀ y ∈ ys, MpAt M y.1 y.2.1 y.2.2
  heap : Heap M (blocks ys ++ H)
  apart : MpInitMulti.Apart ys H

/-- A store to our frame's low slots (`[sp - 112, sp - 96)`) misses the structs and the heap. -/
theorem lo_store (hP : MpInitMulti.Pre m v H sp xs ra) {M : Mem} {t : Nat} (ht : sp - 112 ≤ t ∧ t + 8 ≤ sp - 96)
    (x : BitVec 64) : Keep (fun a => sp - 112 ≤ a ∧ a < sp - 96) M (writeLog M [(t, 8, x)]) :=
  fun a ha => writeLog_out _ _ _ ⟨by simp only; omega, trivial⟩

theorem lo_struct (hP : MpInitMulti.Pre m v H sp xs ra) {q : Nat} (hq : q ∈ xs) :
    ∀ a, q ≤ a → a < q + 24 → ¬ (sp - 112 ≤ a ∧ a < sp - 96) := by
  have hst := hP.st.stk q hq
  have eF : MpInitMulti.F = 672 := rfl
  unfold Disj at hst; rw [eF] at hst
  have := hP.ctx.sp_lo; have eE : heapEnd = 0x87800000 := rfl
  intro a h1 h2 h; omega

theorem lo_heap (hP : MpInitMulti.Pre m v H sp xs ra) {K : List (Nat × Nat)} {a : Nat} (h : Foot K a ∨
    heapStart ≤ a ∧ a < heapEnd) : ¬ (sp - 112 ≤ a ∧ a < sp - 96) := by
  have := hP.ctx.sp_lo; have eE : heapEnd = 0x87800000 := rfl
  have eF : MpInitMulti.F = 672 := rfl
  have : a < heapEnd := by
    rcases h with (hg | ⟨_, h2, _⟩) | h
    · have := Global.lt hg; have eS : heapStart = 0x80019d10 := rfl; omega
    · exact h2
    · exact h.2
  omega

/-- The success invariant through a low-slot store. -/
theorem Inv.lo (hP : MpInitMulti.Pre m v H sp xs ra) {ys : List Arg} {M : Mem} {t : Nat}
    (ht : sp - 112 ≤ t ∧ t + 8 ≤ sp - 96) (x : BitVec 64)
    (hlive : ∀ y ∈ ys, y.1 ∈ xs ∧ MpAt M y.1 y.2.1 y.2.2) (hh : Heap M (blocks ys ++ H)) :
    (∀ y ∈ ys, MpAt (writeLog M [(t, 8, x)]) y.1 y.2.1 y.2.2) ∧ Heap (writeLog M [(t, 8, x)]) (blocks ys ++ H) := by
  have hk := lo_store hP ht x (M := M)
  refine ⟨fun y hy => hk.mpAt (hlive y hy).2 (lo_struct hP (hlive y hy).1) fun a h1 h2 => lo_heap hP (K := H)
    (.inr ?_), hh.frame fun a ha => hk a (lo_heap hP (.inl ha))⟩
  have := Fn.Alloc.Heap.blk hh (e := digBlk y.2.1 y.2.2) (List.mem_append_left _ (List.mem_map_of_mem hy))
  simp only at this; omega

/-- `mp_init`'s precondition at the loop head. -/
theorem init_pre (hP : MpInitMulti.Pre m v H sp xs ra) {va : Nat} {M : Mem} (hO : Ours m v H sp ra xs va M)
    {K : List (Nat × Nat)} (hK : Heap M K) {p : Nat} (hp : p ∈ xs) (i p0 : Nat) :
    Api.MpInit.Pre M (iAbi v sp i p0) K (sp - 112) p Api.MpInit.Finit 0x8000142c#64 := by
  have eE : heapEnd = 0x87800000 := rfl
  have eF : MpInitMulti.F = 672 := rfl
  have eI : Api.MpInit.Finit = 560 := rfl
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi; have hsal := hP.ctx.sp_al
  have hst := hP.st.stk p hp
  have hco := hP.st.code p hp
  have hlay : Sound (Api.MpInit.lay Api.MpInit.Finit (sp - 112) p) Api.MpInit.isW := by
    intro r t h
    cases r <;> cases t <;> first
      | exact absurd h (by decide)
      | (simp only [Iv.Disj, Disj, Api.MpInit.lay, textIv, textBase, textLen, eI] at hst hco ⊢; omega)
  exact ⟨hK, hP.st.ram p hp, hP.st.al p hp, hP.st.off p hp,
    ⟨hO.img, hO.impure, hP.ctx.gp, rfl, by omega, by omega, by omega⟩, by decide, hlay⟩

/-- `mp_init`'s frame as a `CW`. -/
theorem init_cw {M M' : Mem} {p : Nat} {K : List (Nat × Nat)} (hs : 672 ≤ sp)
    (h : HFrm (Api.MpInit.lay Api.MpInit.Finit (sp - 112) p) Api.MpInit.ws K M M') :
    Keep (CW sp p (fun _ => False) K) M M' := Keep.mono h fun a ha => by
  have eI : Api.MpInit.Finit = 560 := rfl
  rcases ha with h | h
  · simp only [InAny, Api.MpInit.ws, Iv.In, Api.MpInit.lay, eI, or_false] at h
    rcases h with h | h
    · exact .inl ⟨by omega, by omega⟩
    · exact .inr (.inl h)
  · exact .inr (.inr (.inr h))

theorem sfacts (hP : MpInitMulti.Pre m v H sp xs ra) : SFacts sp :=
  have := hP.ctx.sp_lo; have := hP.ctx.sp_hi; have := hP.ctx.sp_al
  have eE : heapEnd = 0x87800000 := rfl
  { rs := ⟨by omega, by omega, .inr (by unfold tohostAddr; omega)⟩, sp_al := this, sp_ge := by omega
    code_off := by unfold mpInitMultiBase; omega }

/-- **One round of the main loop**, the rounds after it as `cont`. -/
theorem step (hP : MpInitMulti.Pre m v H sp xs ra) (p0 : Nat) (hp0 : ∀ h : 0 < xs.length, p0 = xs[0])
    {ys : List Arg} {M : Mem} (hlt : ys.length < xs.length) (hI : Inv m v H sp ra xs ys M)
    (cont : ∀ (ys' : List Arg) (M' : Mem) (h : ys.length + 1 < xs.length), ys'.length = ys.length + 1 →
      Inv m v H sp ra xs ys' M' →
      Triple (At 0x80001428#64 (headL sp (ys.length + 1) p0 (xs[ys.length + 1]'h)) M' v.keepR2 outp)
        (MpInitMulti.Ret m v outp H sp xs ra)) :
    Triple (At 0x80001428#64 (headL sp ys.length p0 (xs[ys.length]'hlt)) M v.keepR2 outp)
      (MpInitMulti.Ret m v outp H sp xs ra) := by
  have hsf := sfacts hP
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi
  have eE : heapEnd = 0x87800000 := rfl
  have eS : heapStart = 0x80019d10 := rfl
  have hsv := hP.ctx.sp_v
  have hah := hP.args_hi; unfold argLen at hah
  have hlen31 := hP.len
  have hpx : xs[ys.length] ∈ xs := List.getElem_mem _
  have hO := hI.ours
  refine Triple.seq (init_call v outp sp ys.length p0 _ M hO.img.mpInitMulti)
    (Triple.seq (Fn.MpInit.init_correct (init_pre hP hO hI.heap hpx ys.length p0)) ?_)
  intro c ⟨r, M', hA, hpost⟩
  have hA' : At 0x8000142c#64 (backL sp ys.length p0 r) M' v.keepR2 outp c :=
    hA.reshape (by simp [backL, iAbi, Abi.keep, sKeepL]) (by simp [iAbi, Abi.keep, Abi.keepR2, sKeepL])
  -- the structs of `ys` against `xs[ys.length]`
  have hsy : ∀ y ∈ ys, y.1 ∈ xs ∧ Disj y.1 24 xs[ys.length] 24 := fun y hy => by
    obtain ⟨j, hj, hjn, hje⟩ := idx_of_mem hI.hp hy
    rw [hje]; exact ⟨List.getElem_mem _, st_apart hP hj hlt (by omega)⟩
  -- `mp_init`'s writes keep the earlier ones
  have live_keep : ∀ {E : Nat → Prop} {M2 : Mem}, Keep (CW sp xs[ys.length] E (blocks ys ++ H)) M M2 →
      (∀ x, E x → heapStart ≤ x ∧ x < heapEnd) → (∀ y ∈ ys, ∀ x, InBlk (digBlk y.2.1 y.2.2) x → ¬ E x) →
      ∀ y ∈ ys, MpAt M2 y.1 y.2.1 y.2.2 := fun hk hE hEe y hy =>
    hk.mpAt (hI.live y hy) (cw_struct hP (hsy y hy).1 (hsy y hy).2 hE) fun x h1 h2 =>
      cw_blk hP hI.heap (List.mem_append_left _ (List.mem_map_of_mem hy)) hpx (hEe y hy) x ⟨h1, h2⟩
  cases hpost with
  | @ok q fresh heap' live' frame' =>
    have hk := init_cw (by omega) frame'
    have hO' := hO.keep hP hk hpx (fun x h => h.elim) (fun x h => h.elim) fun x hx => Foot.of_append hx
    have hold := live_keep hk (fun x h => h.elim) fun _ _ _ _ h => h
    let y' : Arg := (xs[ys.length], q, MpInt.zeroN defPrec)
    have hblk' : blocks (ys ++ [y']) ++ H = blocks ys ++ (q, 4 * defPrec) :: H := by simp [blocks, y', digBlk, MpInt.zeroN]
    have hh2 : Heap M' (blocks (ys ++ [y']) ++ H) := by
      rw [hblk']; exact heap'.perm List.perm_middle.symm
    have hap' : MpInitMulti.Apart (ys ++ [y']) H :=
      { pw := by
          rw [blocks_append]
          refine List.pairwise_append.2 ⟨hI.apart.pw, by simp [blocks], fun e he e' he' => ?_⟩
          simp only [blocks, List.map_cons, List.map_nil, List.mem_singleton] at he'
          subst he'
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he
          refine Disj.symm (fresh.disj_blk (List.mem_append_left _ (List.mem_map_of_mem hy)) (by decide) ?_)
          simp [hI.zero y hy, MpInt.zeroN, defPrec]
        off := fun e he e' he' a ha => by
          rw [blocks_append] at he
          rcases List.mem_append.1 he with he | he
          · exact hI.apart.off e he e' he' a ha
          · simp only [blocks, List.map_cons, List.map_nil, List.mem_singleton] at he
            subst he
            exact fresh.disj e' (List.mem_append_right _ he') a ha }
    have hp' : ptrs (ys ++ [y']) = xs.take (ys ++ [y']).length := by
      rw [ptrs_append, hI.hp, List.length_append, List.length_singleton, List.take_add_one,
        List.getElem?_eq_getElem hlt]
      rfl
    have hz' : ∀ y ∈ ys ++ [y'], y.2.2 = MpInt.zeroN defPrec := fun y hy => by
      rcases List.mem_append.1 hy with hy | hy
      · exact hI.zero y hy
      · simp only [List.mem_singleton] at hy; subst hy; rfl
    have hl' : ∀ y ∈ ys ++ [y'], y.1 ∈ xs ∧ MpAt M' y.1 y.2.1 y.2.2 := fun y hy => by
      rcases List.mem_append.1 hy with hy | hy
      · exact ⟨(hsy y hy).1, hold y hy⟩
      · simp only [List.mem_singleton] at hy; subst hy; exact ⟨hpx, live'.repr⟩
    have hw := hO'.va_v
    obtain ⟨hlive2, hheap2⟩ := Inv.lo hP (t := sp - 112) (by omega)
      (BitVec.ofNat 64 (sp - 56 + 8 * ys.length + 8)) hl' hh2
    have hO2 := hO'.set_va hP (sp - 56 + 8 * ys.length + 8)
    by_cases hlast : ys.length + 1 < xs.length
    · have hpn := hO'.slots (ys.length + 1) _ (args_get hlast) (by omega)
      rw [show sp - 64 + 8 * (ys.length + 1) = sp - 56 + 8 * ys.length by omega] at hpn
      have hpr := hP.st.ram _ (List.getElem_mem hlast)
      have hI2 : Inv m v H sp ra xs (ys ++ [y'])
          (writeLog M' [(sp - 112, 8, BitVec.ofNat 64 (sp - 56 + 8 * ys.length + 8))]) :=
        { ours := by
            rw [show sp - 56 + 8 * (ys ++ [y']).length = sp - 56 + 8 * ys.length + 8 by simp; omega]; exact hO2
          hp := hp', zero := hz', live := hlive2, heap := hheap2, apart := hap' }
      exact Triple.seq (next_step v outp sp ys.length p0 (sp - 56 + 8 * ys.length) _ M' hO'.img.mpInitMulti hsf
          ⟨by omega, by omega, .inr (by unfold tohostAddr; omega)⟩ (by omega) (by omega) hw hpn
          (by have := hpr.hi_le; omega) (by have := hpr.lo_ge; omega))
        (cont _ _ hlast (by simp) hI2) c hA'
    · have hlast' : ys.length + 1 = xs.length := by omega
      have hpn := hO'.slots (ys.length + 1) 0 (by rw [hlast']; exact args_end) (by omega)
      rw [show sp - 64 + 8 * (ys.length + 1) = sp - 56 + 8 * ys.length by omega] at hpn
      have hpall : ptrs (ys ++ [y']) = xs := by
        rw [hp', List.length_append, List.length_singleton, hlast', List.take_length]
      exact Triple.seq (done_step v outp sp ys.length p0 (sp - 56 + 8 * ys.length) M' hO'.img.mpInitMulti hsf
          ⟨by omega, by omega, .inr (by unfold tohostAddr; omega)⟩ (by omega) (by omega) hw hpn)
        (Triple.rmap (fun c hA => ⟨0#64, _, hA.reshape (by simp [retL]) (by simp [retL, Abi.keep, Abi.keepR2, sKeepL,
            hsv]), .ok _ hpall hz' hlive2 hheap2 hap' hO2.frame⟩)
          (dend_step ra v.s0 v.s.s1 v.s.s2 v outp sp _ p0 _ hO2.img.mpInitMulti hP.ra_al hsf hO2.s0_v hO2.s2_v
            hO2.ra_v hO2.s1_v)) c hA'
  | mem heap' dp' frame' =>
    have hk := init_cw (by omega) frame'
    have hO' := hO.keep hP hk hpx (fun x h => h.elim) (fun x h => h.elim) fun x hx => Foot.of_append hx
    have hold := live_keep hk (fun x h => h.elim) fun _ _ _ _ h => h
    have hl' : ∀ y ∈ ys, y.1 ∈ xs ∧ MpAt M' y.1 y.2.1 y.2.2 := fun y hy => ⟨(hsy y hy).1, hold y hy⟩
    obtain ⟨hlive2, hheap2⟩ := Inv.lo hP (t := sp - 104) (by omega) (BitVec.ofNat 64 (sp - 56)) hl' heap'
    have hO2 := hO'.set104 hP (BitVec.ofNat 64 (sp - 56))
    have hdp2 : bytesT8 (writeLog M' [(sp - 104, 8, BitVec.ofNat 64 (sp - 56))]) (xs[ys.length] + 16) = 0#64 := by
      rw [(lo_store hP (M := M') (t := sp - 104) (by omega) (BitVec.ofNat 64 (sp - 56))).bytesT8 fun a h1 h2 =>
        lo_struct hP hpx a (by omega) (by omega)]
      exact dp'
    cases hys : ys with
    | nil =>
      subst hys
      exact Triple.seq (fail0_step v outp sp p0 M' hO'.img.mpInitMulti hsf)
        (Triple.rmap (fun c hA => ⟨_, _, hA.reshape (by simp [retL]) (by simp [retL, Abi.keep, Abi.keepR2, sKeepL,
            hsv]), .mem 0 hlt (fun i h => absurd h (Nat.not_lt_zero _)) hdp2 (by simpa [blocks, writeLog_nil] using hheap2)
            hO2.frame⟩)
          (fend_step ra v.s0 v.s.s1 v.s.s2 v outp sp _ hO2.img.mpInitMulti hP.ra_al hsf hO2.s0_v hO2.s2_v
            hO2.ra_v hO2.s1_v)) c hA'
    | cons u us =>
      subst hys
      have hu1 : u.1 = p0 := by
        obtain ⟨hh, h⟩ := ptrs_get (zs := []) (us := us) (u := u) hI.hp (by simp) (by omega)
        rw [h, hp0 (by omega)]; rfl
      have hcl := cloop (outp := outp) hP hlt hI.hp hI.apart us [] u (by simp) _
        { ours := ⟨_, hO2⟩, done := fun z hz => absurd hz List.not_mem_nil
          rest := hlive2, heap := hheap2, dpk := hdp2 }
      rw [hu1] at hcl
      exact Triple.seq (fail1_step v outp sp _ p0 M' hO'.img.mpInitMulti hsf (by simp) (by omega))
        (by simpa using hcl) c hA'

/-- **The main loop**, from its head with `i` initialised. -/
theorem loop (hP : MpInitMulti.Pre m v H sp xs ra) (p0 : Nat) (hp0 : ∀ h : 0 < xs.length, p0 = xs[0]) :
    ∀ (k i : Nat) (ys : List Arg) (M : Mem) (h : i < xs.length), ys.length = i → xs.length = i + k + 1 →
      Inv m v H sp ra xs ys M →
      Triple (At 0x80001428#64 (headL sp i p0 (xs[i]'h)) M v.keepR2 outp) (MpInitMulti.Ret m v outp H sp xs ra)
  | 0, i, ys, M, h, hl, hk, hI => by
    subst hl
    exact step hP p0 hp0 h hI fun ys' M' h' _ _ => absurd h' (by omega)
  | k + 1, i, ys, M, h, hl, hk, hI => by
    subst hl
    exact step hP p0 hp0 h hI fun ys' M' h' hl' hI' => loop hP p0 hp0 k _ ys' M' h' hl' (by omega) hI'

/-- **`mp_init_multi` on the machine.** -/
theorem correct : Api.MpInitMulti.Statement := by
  intro m v outp H sp xs ra hP c hA
  have hsf := sfacts hP
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi
  have eE : heapEnd = 0x87800000 := rfl
  have eS : heapStart = 0x80019d10 := rfl
  have eF : MpInitMulti.F = 672 := rfl
  have hsv := hP.ctx.sp_v
  -- the argument registers, at their values
  let r : Nat → BitVec 64 := fun i => (gprGet c.σ (10 + i)).getD 0
  have g : ∀ i, i ≤ 7 → gprGet c.σ (10 + i) = some (r i) := fun i hi =>
    MpClearMulti.eq_some_getD (hA.gprs (10 + i) (by omega) (by omega))
  have hr : ∀ i w, (args xs)[i]? = some w → i < 8 → r i = BitVec.ofNat 64 w := by
    intro i w hw hi
    obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 hw
    have hm := mem_argRegs 0 (args xs) i hlt (by omega)
    have := gholds_mem hA.regs (List.mem_cons_of_mem _ hm)
    rw [show 10 + 0 + i = 10 + i by omega, g i (by omega), he] at this
    exact Option.some.inj this
  have hk : GHolds c.σ (v.keep) := hA.keep
  have h1 : gprGet c.σ 1 = some ra := gholds_mem hA.regs (List.mem_cons_self ..)
  have h2 : gprGet c.σ 2 = some (BitVec.ofNat 64 sp) := by
    rw [← hsv]; exact gholds_mem hk (by simp [Abi.keep])
  have h8 : gprGet c.σ 8 = some v.s0 := gholds_mem hk (by simp [Abi.keep])
  have h9 : gprGet c.σ 9 = some v.s.s1 := gholds_mem hk (by simp [Abi.keep, sKeepL])
  have h18 : gprGet c.σ 18 = some v.s.s2 := gholds_mem hk (by simp [Abi.keep, sKeepL])
  have hA0 : At entry (entryL ra v.s0 v.s.s1 v.s.s2 sp r) m v.keepR2 outp c :=
    { hA with
      regs := ⟨h1, h2, h8, h9, h18, g 0 (by omega), g 1 (by omega), g 2 (by omega), g 3 (by omega),
        g 4 (by omega), g 5 (by omega), g 6 (by omega), g 7 (by omega), trivial⟩
      keep := gholds_of_mem hk (by simp [Abi.keep, Abi.keepR2, sKeepL]) }
  refine (Triple.seq (pro_step ra v.s0 v.s.s1 v.s.s2 v outp sp r m hP.ctx.img.mpInitMulti hsf) ?_) c hA0
  cases hxs : xs with
  | nil =>
    subst hxs
    have hr0 : r 0 = 0#64 := hr 0 0 (by simp [args]) (by omega)
    rw [hr0]
    have hout : Keep (fun x => ¬ (x < sp - 112 ∨ sp ≤ x)) m (writeLog m (proLog ra v.s.s1 sp r)) :=
      fun x hx => pro_out m ra v.s.s1 sp r (by omega) x (Classical.byContradiction hx)
    have hpost : MpInitMulti.Post m (writeLog m (proLog ra v.s.s1 sp r)) H sp [] 0#64 :=
      .ok [] rfl (fun y hy => absurd hy List.not_mem_nil) (fun y hy => absurd hy List.not_mem_nil)
        (hP.heap.frame fun x hx => hout x fun hw => hw (.inl (by
          have : x < heapEnd := by
            rcases hx with hg | ⟨_, h2, _⟩
            · have := Global.lt hg; omega
            · exact h2
          omega)))
        ⟨List.Pairwise.nil, fun e he => absurd he List.not_mem_nil⟩
        (Keep.mono hout fun x hx => .inl (by unfold Stk; rw [eF]; omega))
    exact Triple.rmap (fun c hA => by
        rw [writeLog_nil] at hA
        exact ⟨_, _, hA.reshape (by simp [retL]) (by simp [retL, Abi.keep, Abi.keepR2, sKeepL, hsv]), hpost⟩)
      (zero_step ra v.s0 v.s.s1 v.s.s2 v outp sp _ (hout.img (fun x h1 h2 hx => hx (.inl (by
          unfold textBase textLen at h2; omega))) hP.ctx.img).mpInitMulti hP.ra_al hsf
        (pro_ra m ra v.s.s1 sp r (by omega)) (pro_s1 m ra v.s.s1 sp r (by omega)))
  | cons x0 xs' =>
    subst hxs
    have hy := hP.st.ram x0 (List.mem_cons_self ..)
    have hr0 : r 0 = BitVec.ofNat 64 x0 := hr 0 x0 (by simp [args]) (by omega)
    rw [hr0]
    have hz : (BitVec.ofNat 64 x0 == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hy.hi_le; omega)] at h'
      have := hy.lo_ge; simp at h'; omega
    have e2 : writeLog (writeLog m (proLog ra v.s.s1 sp r)) (startLog v.s0 v.s.s2 sp) =
        writeLog m (allLog ra v.s0 v.s.s1 v.s.s2 sp r) := by rw [allLog, writeLog_append]
    have hout : Keep (fun x => ¬ (x < sp - 112 ∨ sp ≤ x)) m (writeLog m (allLog ra v.s0 v.s.s1 v.s.s2 sp r)) :=
      fun x hx => all_out m ra v.s0 v.s.s1 v.s.s2 sp r (by omega) x (Classical.byContradiction hx)
    have hO : Ours m v H sp ra (x0 :: xs') (sp - 56 + 8 * 0) (writeLog m (allLog ra v.s0 v.s.s1 v.s.s2 sp r)) :=
      { slots := fun j w hw h1 => by
          by_cases h7 : j ≤ 7
          · rw [slot_all m ra v.s0 v.s.s1 v.s.s2 sp r (by omega) j h1 h7]; exact hr j w hw (by omega)
          · obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 hw
            rw [hout.bytesT8 fun x h1 h2 hx => hx (.inr (by omega)),
              show sp - 64 + 8 * j = sp + 8 * (j - 8) by omega, hP.sargs j hlt (by omega), he]
        va_v := all_va m ra v.s0 v.s.s1 v.s.s2 sp r (by omega)
        ra_v := all_ra m ra v.s0 v.s.s1 v.s.s2 sp r (by omega)
        s1_v := all_s1 m ra v.s0 v.s.s1 v.s.s2 sp r (by omega)
        s0_v := all_s0 m ra v.s0 v.s.s1 v.s.s2 sp r (by omega)
        s2_v := all_s2 m ra v.s0 v.s.s1 v.s.s2 sp r (by omega)
        img := hout.img (fun x h1 h2 hx => hx (.inl (by unfold textBase textLen at h2; omega))) hP.ctx.img
        impure := ImpureAt.of_keep hout (fun x h1 h2 hx => hx (.inl (by unfold impurePtr at h2; omega)))
          hP.ctx.impure
        frame := Keep.mono hout fun x hx => .inl (by unfold Stk; rw [eF]; omega) }
    have hI : Inv m v H sp ra (x0 :: xs') [] (writeLog m (allLog ra v.s0 v.s.s1 v.s.s2 sp r)) :=
      { ours := hO, hp := rfl, zero := fun y hy => absurd hy List.not_mem_nil
        live := fun y hy => absurd hy List.not_mem_nil
        heap := hP.heap.frame fun x hx => hout x fun hw => hw (.inl (by
          have : x < heapEnd := by
            rcases hx with hg | ⟨_, h2, _⟩
            · have := Global.lt hg; omega
            · exact h2
          omega))
        apart := ⟨List.Pairwise.nil, fun e he => absurd he List.not_mem_nil⟩ }
    have hout0 : Keep (fun x => ¬ (x < sp - 112 ∨ sp ≤ x)) m (writeLog m (proLog ra v.s.s1 sp r)) :=
      fun x hx => pro_out m ra v.s.s1 sp r (by omega) x (Classical.byContradiction hx)
    have hstart := start_step ra v.s0 v.s.s2 v outp sp x0 _ ((hout0.img (fun x h1 h2 hx => hx (.inl (by
      unfold textBase textLen at h2; omega))) hP.ctx.img).mpInitMulti) hsf hz
    rw [e2] at hstart
    exact Triple.seq hstart (loop hP x0 (fun _ => rfl) xs'.length 0 [] _ (by simp) rfl (by simp) hI)

end

end Tom.Machine.Fn.MpInitMulti
