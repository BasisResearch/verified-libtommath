import Tom.Machine.Api.MpClearMulti
import Tom.Machine.Fn.MpClearMain

/-!
# `mp_clear_multi` on the machine: the whole function

The prologue spills the argument registers (`Fn/MpClearMulti.lean`); the loop
at `6cc` is an induction over the arguments still to clear (`loop`), each
round `mp_clear` (`Fn.MpClear.correct`) and the next argument's load. The
loop invariant `Inv` holds the cleared prefix, the live suffix with its heap,
the argument slots and the saved registers; `inv_preserve` carries it across one
`mp_clear` by `Keep` (`Api/Heap.lean`), the facts off its writes by the
`Structs` layout and the arena.
-/


namespace Tom.Machine.Fn.MpClearMulti

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api
open Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Api.Multi

/-- The Abi `mp_clear` sees: our frame's `sp`, `s0 = s`. -/
def clearAbi (v : Abi) (sp s : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 96), s0 := BitVec.ofNat 64 s }

/-- The `mp_clear` call at `6cc`, back at `6d0`. -/
theorem clear_call (v : Abi) (outp : Array String) (sp s p : Nat) (M : Mem)
    (hc : CodeAt M mpClearMultiBase mpClearMultiCode) :
    Triple (At 0x800006cc#64 (loopL sp s p) M v.keepR outp)
      (At Fn.MpClear.entry (Api.MpClear.entryL 0x800006d0#64 p) M (clearAbi v sp s).keep outp) := by
  refine Triple.rmap (fun c h => ?_)
    (jal_at (pc := 0x800006cc#64) (w := 0x14d040ef#32) (imm := 0x494c#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 96)), (8, BitVec.ofNat 64 s), (10, BitVec.ofNat 64 p)])
      (hc.word (a := (0x800006cc#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [loopL]) (by simp [keysG]) (by simp [Abi.keepR, keysG, sKeepL]))
  have hpc : (0x800006cc#64 : BitVec 64) + sign_extend (m := 64) (0x494c#21) = Fn.MpClear.entry := by decide
  have hra : Sail.BitVec.addInt (0x800006cc#64 : BitVec 64) 4 = 0x800006d0#64 := by decide
  rw [hpc, hra] at h
  exact h.reshape (by simp [Api.MpClear.entryL]) (by simp [clearAbi, Abi.keep, Abi.keepR, sKeepL])

theorem args_cons (zs ys : List Arg) (y : Arg) :
    (args (ptrs (zs ++ y :: ys)))[zs.length]? = some y.1 := by
  simp [args, ptrs, List.getElem?_append_right]

theorem args_last (xs : List Arg) : (args (ptrs xs))[xs.length]? = some 0 := by
  simp [args, ptrs, List.getElem?_append_right]

theorem args_len (xs : List Arg) : (args (ptrs xs)).length = xs.length + 1 := by simp [args, ptrs]

/-- The loop invariant: `zs` cleared, `ys` live, the slots and saved registers. -/
structure Inv (m : Mem) (v : Abi) (H : List (Nat × Nat)) (sp : Nat) (ra : BitVec 64) (xs zs ys : List Arg)
    (M : Mem) : Prop where
  done : ∀ x ∈ zs, MpAt M x.1 0 MpInt.cleared
  rest : ∀ x ∈ ys, MpAt M x.1 x.2.1 x.2.2
  heap : Heap M (blocks ys ++ H)
  slots : ∀ j w, (args (ptrs xs))[j]? = some w → 1 ≤ j → bytesT8 M (sp - 64 + 8 * j) = BitVec.ofNat 64 w
  ra_v : bytesT8 M (sp - 96 + 24) = ra
  s0_v : bytesT8 M (sp - 96 + 16) = v.s0
  img : Img M
  impure : ImpureAt M
  frame : Keep (MpClearMulti.W xs H sp) m M

section
variable {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp : Nat} {xs : List Arg}
  {ra : BitVec 64}

theorem sfacts (hP : MpClearMulti.Pre m v H sp xs ra) : SFacts sp :=
  have := hP.ctx.sp_lo; have := hP.ctx.sp_hi; have := hP.ctx.sp_al
  have eE : heapEnd = 0x87800000 := rfl
  have eD : depth = 512 := rfl
  { rs := ⟨by omega, by omega, .inr (by unfold tohostAddr; omega)⟩, sp_al := this, sp_ge := by omega
    code_off := by unfold mpClearMultiBase; omega }

/-- A struct of the arguments misses the stack window, the arena and the footprint. -/
theorem st_miss (hP : MpClearMulti.Pre m v H sp xs ra) {x : Arg} (hx : x ∈ xs) {K : List (Nat × Nat)}
    {a : Nat} (h1 : x.1 ≤ a) (h2 : a < x.1 + 24) :
    (a < sp - MpClearMulti.F ∨ sp + argLen (xs.length + 1) ≤ a) ∧ (a < heapStart ∨ heapEnd ≤ a) ∧
      ¬ Foot K a := by
  have hp : x.1 ∈ ptrs xs := List.mem_map_of_mem hx
  have hs := hP.st.stk x.1 hp
  have ho := hP.st.off x.1 hp
  have eE : heapEnd = 0x87800000 := rfl
  have eS : heapStart = 0x80019d10 := rfl
  have eL : allocLo = 0x800188a0 := rfl
  have := hP.ctx.sp_lo
  refine ⟨?_, ?_, ho.off_foot h1 h2⟩
  · unfold Disj at hs; omega
  · unfold OffHeap at ho; omega

/-- One `mp_clear` keeps the invariant. -/
theorem inv_preserve (hP : MpClearMulti.Pre m v H sp xs ra) {zs ys : List Arg} {y : Arg}
    (hxs : zs ++ y :: ys = xs) {M M' : Mem} (hI : Inv m v H sp ra xs zs (y :: ys) M)
    (hC : MpClear.Post M (blocks ys ++ H) (sp - 96) y.1 y.2.1 y.2.2 M') :
    Inv m v H sp ra xs (zs ++ [y]) ys M' := by
  have eE : heapEnd = 0x87800000 := rfl
  have eS : heapStart = 0x80019d10 := rfl
  have eL : allocLo = 0x800188a0 := rfl
  have eF : MpClearMulti.F = 640 := rfl
  have eC : MpClear.F = 544 := rfl
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi
  have hy : y ∈ xs := hxs ▸ List.mem_append_right _ (List.mem_cons_self ..)
  have hby := Fn.Alloc.Heap.blk hI.heap (e := digBlk y.2.1 y.2.2) (List.mem_append_left _ (List.mem_cons_self ..))
  simp only at hby
  -- what `mp_clear` writes
  let Wy : Nat → Prop := fun a => (sp - 640 ≤ a ∧ a < sp - 96) ∨ (y.1 ≤ a ∧ a < y.1 + 24) ∨
    InBlk (digBlk y.2.1 y.2.2) a ∨ Foot (blocks ys ++ H) a
  have hkW : Keep Wy M M' := Keep.mono hC.frame fun a ha => by
    rcases ha with h | h
    · simp only [InAny, Un.ws, Iv.In, Un.lay, eC, or_false] at h
      rcases h with h | h | h
      · exact .inl ⟨by omega, by omega⟩
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
  have hpw := hP.st.pw
  rw [← hxs, ptrs_append] at hpw
  have hpw' := List.pairwise_append.1 hpw
  have hbpw := hP.bpw
  rw [← hxs, blocks_append] at hbpw
  have hbpw' := (List.pairwise_append.1 hbpw).2.1
  -- a struct other than `y`'s misses `Wy`
  have smiss : ∀ x, x ∈ xs → Disj x.1 24 y.1 24 → ∀ a, x.1 ≤ a → a < x.1 + 24 → ¬ Wy a := by
    intro x hx hd a h1 h2 hw
    obtain ⟨hs, ha, hf⟩ := st_miss hP hx (K := blocks ys ++ H) h1 h2
    rcases hw with h | h | h | h
    · rw [eF] at hs; omega
    · unfold Disj at hd; omega
    · unfold InBlk at h; simp only at h; omega
    · exact hf h
  -- a slot of ours misses `Wy`
  have wmiss : ∀ a, sp - 88 ≤ a → a < sp + argLen (xs.length + 1) → ¬ Wy a := by
    intro a h1 h2 hw
    have hs := hP.st.stk y.1 (List.mem_map_of_mem hy)
    rcases hw with h | h | h | h
    · omega
    · unfold Disj at hs; rw [eF] at hs; omega
    · unfold InBlk at h; simp only at h; omega
    · exact OffHeap.off_foot (a := a) (n := 1) (.inr (by omega)) (Nat.le_refl _) (by omega) h
  refine { done := ?_, rest := ?_, heap := hC.heap, slots := ?_, ra_v := ?_, s0_v := ?_, img := ?_,
           impure := ?_, frame := ?_ }
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · refine hkW.mpAt (hI.done x hx) (smiss x (hxs ▸ List.mem_append_left _ hx)
        (hpw'.2.2 x.1 (List.mem_map_of_mem hx) y.1 (List.mem_cons_self ..))) fun a h1 h2 => ?_
      simp [MpInt.cleared] at h2
    · simp only [List.mem_singleton] at hx; subst hx; exact hC.repr
  · intro x hx
    have hxm : x ∈ xs := hxs ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hx)
    have hd : Disj x.1 24 y.1 24 :=
      Disj.symm (List.rel_of_pairwise_cons hpw'.2.1 (List.mem_map_of_mem hx))
    have hdb : Disj y.2.1 (4 * y.2.2.alloc) x.2.1 (4 * x.2.2.alloc) :=
      List.rel_of_pairwise_cons hbpw' (List.mem_map_of_mem (f := fun x : Arg => digBlk x.2.1 x.2.2) hx)
    have hbx := Fn.Alloc.Heap.blk hC.heap (e := digBlk x.2.1 x.2.2)
      (List.mem_append_left _ (List.mem_map_of_mem hx))
    simp only at hbx
    refine hkW.mpAt (hI.rest x (List.mem_cons_of_mem _ hx)) (smiss x hxm hd) fun a h1 h2 hw => ?_
    rcases hw with h | h | h | h
    · omega
    · have := st_miss hP hy (K := H) h.1 h.2; omega
    · unfold InBlk at h; unfold Disj at hdb; simp only at h; omega
    · exact blk_off_foot hC.heap (List.mem_append_left _ (List.mem_map_of_mem hx)) ⟨h1, h2⟩ h
  · intro j w hj h1
    have hlt : j < xs.length + 1 := by
      have := (List.getElem?_eq_some_iff.1 hj).1; rwa [args_len] at this
    rw [hkW.bytesT8 fun a h1' h2' => wmiss a (by omega) (by unfold argLen; omega)]
    exact hI.slots j w hj h1
  · rw [hkW.bytesT8 fun a h1 h2 => wmiss a (by omega) (by unfold argLen; omega)]; exact hI.ra_v
  · rw [hkW.bytesT8 fun a h1 h2 => wmiss a (by omega) (by unfold argLen; omega)]; exact hI.s0_v
  · refine hkW.img (fun a h1 h2 hw => ?_) hI.img
    have hc := hP.st.code y.1 (List.mem_map_of_mem hy)
    simp only [textBase, textLen] at h1 h2
    rcases hw with h | h | h | h
    · omega
    · unfold Disj textBase textLen at hc; omega
    · unfold InBlk at h; simp only at h; omega
    · exact (OffHeap.text (x := a) (by unfold textBase; omega) (by unfold textBase textLen; omega)).off_foot
        (Nat.le_refl _) (by omega) h
  · refine ImpureAt.of_keep hkW (fun a h1 h2 hw => ?_) hI.impure
    unfold impurePtr at h1 h2
    rcases hw with h | h | h | h
    · omega
    · have := st_miss hP hy (K := H) h.1 h.2; have := hP.st.off y.1 (List.mem_map_of_mem hy)
      unfold OffHeap at this; omega
    · unfold InBlk at h; simp only at h; omega
    · exact impure_off_foot (by unfold impurePtr; omega) (by unfold impurePtr; omega) h
  · refine Keep.mono (Keep.trans hI.frame hkW) fun a ha => ?_
    rcases ha with h | h
    · exact h
    · rcases h with h | h | h | h
      · exact .inl (by unfold Stk; rw [eF]; omega)
      · exact .inr (.inl ⟨y, hy, .inl h⟩)
      · exact .inr (.inl ⟨y, hy, .inr h⟩)
      · exact .inr (.inr (Foot.of_append h))

/-- `mp_clear`'s precondition for the argument `y` at the loop head. -/
theorem clear_pre (hP : MpClearMulti.Pre m v H sp xs ra) {zs ys : List Arg} {y : Arg}
    (hxs : zs ++ y :: ys = xs) {M : Mem} (hI : Inv m v H sp ra xs zs (y :: ys) M) (s : Nat) :
    MpClear.Pre M (clearAbi v sp s) (blocks ys ++ H) (sp - 96) y.1 y.2.1 y.2.2 0x800006d0#64 := by
  have eE : heapEnd = 0x87800000 := rfl
  have eS : heapStart = 0x80019d10 := rfl
  have eF : MpClearMulti.F = 640 := rfl
  have eC : MpClear.F = 544 := rfl
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi; have hsal := hP.ctx.sp_al
  have hy : y ∈ xs := hxs ▸ List.mem_append_right _ (List.mem_cons_self ..)
  have hp : y.1 ∈ ptrs xs := List.mem_map_of_mem hy
  have hby := Fn.Alloc.Heap.blk hI.heap (e := digBlk y.2.1 y.2.2) (List.mem_append_left _ (List.mem_cons_self ..))
  simp only at hby
  have ho := hP.st.off y.1 hp
  unfold OffHeap at ho
  have eL : allocLo = 0x800188a0 := rfl
  have hlo : heapEnd + MpClear.F ≤ sp - 96 := by omega
  have hal : (sp - 96) % 16 = 0 := by omega
  have hhi : sp - 96 ≤ 0x100000000 := by omega
  have hctx : ACtx M (clearAbi v sp s) (sp - 96) MpClear.F :=
    ⟨hI.img, hI.impure, hP.ctx.gp, rfl, hal, hlo, hhi⟩
  have hst := hP.st.stk y.1 hp
  have hco := hP.st.code y.1 hp
  have hlay : Sound (Un.lay MpClear.F (sp - 96) y.1 y.2.1 y.2.2) Un.isW := by
    intro r t h
    cases r <;> cases t <;> first
      | exact absurd h (by decide)
      | (simp only [Iv.Disj, Disj, Un.lay, textIv, textBase, textLen] at hst hco ⊢; omega)
  exact ⟨hI.rest y (List.mem_cons_self ..), hI.heap, hP.st.ram y.1 hp, hP.st.al y.1 hp, hP.st.off y.1 hp, hctx,
    by decide, hlay⟩

/-- **The loop**, from the head with `y` next and `ys` after it. -/
theorem loop (hP : MpClearMulti.Pre m v H sp xs ra) :
    ∀ (ys zs : List Arg) (y : Arg) (s : Nat), zs ++ y :: ys = xs → s = sp - 56 + 8 * zs.length →
      ∀ M, Inv m v H sp ra xs zs (y :: ys) M →
      Triple (At 0x800006cc#64 (loopL sp s y.1) M v.keepR outp) (MpClearMulti.Ret m v outp H sp xs ra)
  | ys, zs, y, s, hxs, hs, M, hI => by
    have hsf := sfacts hP
    have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi
    have eE : heapEnd = 0x87800000 := rfl
    have eF : MpClearMulti.F = 640 := rfl
    have hsv := hP.ctx.sp_v
    have hlen : zs.length + 1 ≤ xs.length := by rw [← hxs]; simp
    refine Triple.seq (clear_call v outp sp s y.1 M hI.img.mpClearMulti)
      (Triple.seq (Fn.MpClear.correct (clear_pre hP hxs hI s)) ?_)
    intro c ⟨M', hA, hC⟩
    have hI' := inv_preserve hP hxs hI hC
    have hA' : At 0x800006d0#64 (backL sp s) M' v.keepR outp c :=
      hA.reshape (by simp [backL, clearAbi, Abi.keep, sKeepL]) (by simp [clearAbi, Abi.keep, Abi.keepR, sKeepL])
    have hsl8 : s = sp - 64 + 8 * (zs.length + 1) := by omega
    have hram : Ram s 8 := ⟨by omega, by have := hP.args_hi; unfold argLen at this; omega,
      .inr (by unfold tohostAddr; omega)⟩
    cases ys with
    | nil =>
      have hx : zs ++ [y] = xs := hxs
      have h0 := hI'.slots (zs.length + 1) 0 (by rw [← hxs]; have := args_last (zs ++ [y]); simpa using this)
        (by omega)
      rw [← hsl8] at h0
      have hpost : MpClearMulti.Post m H sp xs M' :=
        ⟨fun x hx' => hI'.done x (hx ▸ hx'), by simpa [blocks] using hI'.heap, hI'.frame⟩
      refine Triple.rmap (fun c hA => ⟨_, hA.reshape (by simp [retL]) (by simp [retL, Abi.keep, Abi.keepR, sKeepL,
          hsv]), hpost⟩)
        (end_step ra v.s0 v outp sp s M' hI'.img.mpClearMulti hP.ra_al hsf hram h0 hI'.ra_v hI'.s0_v) c hA'
    | cons y' ys' =>
      have hx : (zs ++ [y]) ++ y' :: ys' = xs := by rw [← hxs]; simp
      have hy' : y' ∈ xs := hx ▸ List.mem_append_right _ (List.mem_cons_self ..)
      have hpr := hP.st.ram y'.1 (List.mem_map_of_mem hy')
      have hp' := hI'.slots (zs.length + 1) y'.1 (by rw [← hx]; simpa using args_cons (zs ++ [y]) ys' y')
        (by omega)
      rw [← hsl8] at hp'
      have hz : (BitVec.ofNat 64 y'.1 == 0#64) = false := by
        rw [beq_eq_false_iff_ne]; intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hpr.hi_le; omega)] at h'
        have := hpr.lo_ge; simp at h'; omega
      exact Triple.seq (next_step v outp sp s y'.1 M' hI'.img.mpClearMulti hram (by have := hram.hi_le; omega) hp' hz
          (by have := hpr.hi_le; omega) (by have := hpr.lo_ge; omega))
        (loop hP ys' (zs ++ [y]) y' (s + 8) hx (by simp; omega) _ hI') c hA'

end

theorem eq_some_getD {o : Option (BitVec 64)} (h : o.isSome) : o = some (o.getD 0) := by
  cases o <;> simp_all

/-- **`mp_clear_multi` on the machine.** -/
theorem correct : Api.MpClearMulti.Statement := by
  intro m v outp H sp xs ra hP c hA
  have hsf := sfacts hP
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi
  have eE : heapEnd = 0x87800000 := rfl
  have eS : heapStart = 0x80019d10 := rfl
  have eF : MpClearMulti.F = 640 := rfl
  have hsv := hP.ctx.sp_v
  -- the argument registers, at their values
  let r : Nat → BitVec 64 := fun i => (gprGet c.σ (10 + i)).getD 0
  have g : ∀ i, i ≤ 7 → gprGet c.σ (10 + i) = some (r i) := fun i hi =>
    eq_some_getD (hA.gprs (10 + i) (by omega) (by omega))
  have hr : ∀ i w, (args (ptrs xs))[i]? = some w → i < 8 → r i = BitVec.ofNat 64 w := by
    intro i w hw hi
    obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 hw
    have hm := mem_argRegs 0 (args (ptrs xs)) i hlt (by omega)
    have := gholds_mem hA.regs (List.mem_cons_of_mem _ hm)
    rw [show 10 + 0 + i = 10 + i by omega, g i (by omega), he] at this
    exact Option.some.inj this
  have hk : GHolds c.σ (v.keep) := hA.keep
  have h1 : gprGet c.σ 1 = some ra := gholds_mem hA.regs (List.mem_cons_self ..)
  have h2 : gprGet c.σ 2 = some (BitVec.ofNat 64 sp) := by
    rw [← hsv]; exact gholds_mem hk (by simp [Abi.keep])
  have h8 : gprGet c.σ 8 = some v.s0 := gholds_mem hk (by simp [Abi.keep])
  have hA0 : At entry (entryL ra v.s0 sp r) m v.keepR outp c :=
    { hA with
      regs := ⟨h1, h2, h8, g 0 (by omega), g 1 (by omega), g 2 (by omega), g 3 (by omega), g 4 (by omega),
        g 5 (by omega), g 6 (by omega), g 7 (by omega), trivial⟩
      keep := gholds_of_mem hk (by simp [Abi.keep, Abi.keepR, sKeepL]) }
  -- after the prologue
  have hout : Keep (fun x => ¬ (x < sp - 88 ∨ sp ≤ x)) m (writeLog m (proLog ra v.s0 sp r)) :=
    fun x hx => pro_out m ra v.s0 sp r x (Classical.byContradiction hx) (by omega)
  have hI : Inv m v H sp ra xs [] xs (writeLog m (proLog ra v.s0 sp r)) :=
    { done := fun x hx => by simp at hx
      rest := fun x hx => by
        have hb := Fn.Alloc.Heap.blk hP.heap (e := digBlk x.2.1 x.2.2)
          (List.mem_append_left _ (List.mem_map_of_mem hx))
        simp only at hb
        refine hout.mpAt (hP.live x hx) (fun a h1 h2 hw => ?_) (fun a h1 h2 hw => hw (.inl (by omega)))
        have := (st_miss hP hx (K := H) h1 h2).1; rw [eF] at this; omega
      heap := hP.heap.frame fun x hx => hout x fun hw => hw (.inl (by
        have : x < heapEnd := by
          rcases hx with hg | ⟨_, h2, _⟩
          · have := Global.lt hg; omega
          · exact h2
        omega))
      slots := fun j w hw h1 => by
        by_cases h7 : j ≤ 7
        · rw [slot_pro m ra v.s0 sp r (by omega) j h1 h7]; exact hr j w hw (by omega)
        · obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 hw
          rw [hout.bytesT8 fun x h1 h2 hx => hx (.inr (by omega)), show sp - 64 + 8 * j = sp + 8 * (j - 8) by omega,
            hP.sargs j hlt (by omega), he]
      ra_v := pro_ra m ra v.s0 sp r (by omega)
      s0_v := pro_s0 m ra v.s0 sp r (by omega)
      img := hout.img (fun x h1 h2 hx => hx (.inl (by unfold textBase textLen at h2; omega))) hP.ctx.img
      impure := ImpureAt.of_keep hout (fun x h1 h2 hx => hx (.inl (by unfold impurePtr at h2; omega)))
        hP.ctx.impure
      frame := Keep.mono hout fun x hx => .inl (by unfold Stk; rw [eF]; omega) }
  refine (Triple.seq (pro_step ra v.s0 v outp sp r m hP.ctx.img.mpClearMulti hsf) ?_) c hA0
  generalize writeLog m (proLog ra v.s0 sp r) = M1 at hI ⊢
  cases hxs : xs with
  | nil =>
    subst hxs
    have hr0 : r 0 = 0#64 := hr 0 0 (by simp [args, ptrs]) (by omega)
    rw [hr0]
    have hpost : MpClearMulti.Post m H sp [] (writeLog M1 []) :=
      ⟨fun x hx => absurd hx List.not_mem_nil, hI.heap, hI.frame⟩
    exact Triple.rmap (fun c hA => ⟨_, hA.reshape (by simp [retL]) (by simp [retL, Abi.keep, Abi.keepR, sKeepL,
        hsv]), hpost⟩)
      (zero_step ra v.s0 v outp sp _ hI.img.mpClearMulti hP.ra_al hsf hI.ra_v hI.s0_v)
  | cons y ys =>
    subst hxs
    have hy := hP.st.ram y.1 (List.mem_cons_self ..)
    have hr0 : r 0 = BitVec.ofNat 64 y.1 := hr 0 y.1 (by simp [args, ptrs]) (by omega)
    rw [hr0]
    have hz : (BitVec.ofNat 64 y.1 == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hy.hi_le; omega)] at h'
      have := hy.lo_ge; simp at h'; omega
    exact Triple.seq (nz_step ra v outp sp y.1 _ hI.img.mpClearMulti hz)
      (loop hP ys [] y (sp - 56) rfl (by simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]) _ hI)

end Tom.Machine.Fn.MpClearMulti
