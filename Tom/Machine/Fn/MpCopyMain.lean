import Tom.Machine.Api.MpCopy
import Tom.Machine.Api.StdLib

/-!
# `mp_copy` on the machine: the whole function

The segments of `Tom.Machine.Fn.MpCopy` over `Kit/Meet.lean`. Regions are
`Two`'s (`a` read, `b` written), the stack (32 bytes) all our own frame
(`Split`). After the prologue only `b`'s digits change: the copy loop
(`St.seqOvl`), the `memset` of `[a->used, b->used)` (`call_std memsetD`); the
two paths meet at `0850` with `b`'s digits re-abstracted (`St.setMp`), where
the epilogue stores `b`'s `used` and `sign` (`St.seqUS`).
-/


namespace Tom.Machine.Fn.MpCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api Tom.Machine.Std
open Tom.Machine.Api.Two (R isW)

/-- Our frame after the prologue. -/
abbrev m0Of (m : Mem) (ra s0 s1 : BitVec 64) (sp : Nat) : Mem := writeLog m (frameLog ra s0 s1 sp)

/-- The states after the prologue: `b`'s kinds as `b'`, our frame as stored. -/
abbrev Sb (m M : Mem) (ra s0 s1 : BitVec 64) (sp pa adp pb bdp : Nat) (a b b' : MpInt) : Prop :=
  St (Split.lay (Two.lay 32 sp pa adp pb bdp a b) .stk 32) (Split.wr isW) [none, some .stk, some .bS, some .bD]
    (Split.kind (Tom.Machine.Two.kind pa adp pb bdp a b') (m0Of m ra s0 s1 sp)) m M

/-- `b` with the digits `f`. -/
def withD (b : MpInt) (f : Nat → Nat) : MpInt := MpInt.ofDigits b.used b.alloc b.sign f

def σd : Dz → Option R
  | .D => some .bD
  | .code => some .code

theorem cd {sp pa adp pb bdp : Nat} {a b : MpInt} {W : List (Option R)} {κ : Option R → Kind} {m M : Mem}
    (h : St (Split.lay (Two.lay 32 sp pa adp pb bdp a b) .stk 32) (Split.wr isW) W κ m M)
    (hk : κ (some .code) = .code := by rfl) : CodeAt M mpCopyBase mpCopyCode := (h.img (some .code) hk).mpCopy

/-- **`mp_copy` on the machine** (distinct operands). -/
theorem correct : Api.MpCopy.Statement := by
  intro m v outp sp pa adp pb bdp a b ra s0 hP
  have h0 := St.two (f := 32) hP.ra_ hP.ga hP.rb hP.gb hP.rs hP.img hP.lay (by decide)
  have := hP.sp_ge; have := hP.sp_al; have hra := hP.ra_al; have hroom := hP.room
  have hua := hP.sa.used_le; have := hP.sa.alloc_lt; have hbu := hP.sb.used_le; have := hP.sb.alloc_lt
  have hne : pa ≠ pb := by have := hP.lay.disj (r := .aS) (s := .bS); simp only [Iv.Disj, Disj, Two.lay] at this; omega
  have hsg : a.sign < 2 := by have := hP.asign; simp only [Layout.mpZpos, Layout.mpNeg] at this; omega
  refine Triple.lmap (fun cf h => h.sub (L' := entry1 ra s0 v.s.s1 sp pa pb) (K' := v.keepR1) rfl rfl) ?_
  refine h0.seqW none rfl (p_step ra s0 v.s.s1 v outp sp pa pb a.used b.alloc m (cd h0) (by facts h0) hroom)
    fun M1 h1 => ?_
  -- from `0850`: the `used` and `sign` stores, the epilogue
  have fin : ∀ M, Sb m M ra s0 v.s.s1 sp pa adp pb bdp a b (withD b (copyDigits a b)) →
      Triple (At 0x80000850#64 (rL sp pa pb a.used) M v.keepR1 outp) (MpCopy.Ret m v outp sp pa adp pb bdp a b ra s0) :=
    fun M h => h.seqUS (some .bS) rfl (r_step ra s0 v.s.s1 v outp sp pa pb a.used a.sign M (cd h) (by facts h))
      (by omega) (by omega) fun M' h' cf hc => ⟨cf, Vsa.Machine.Steps.refl _, a.copyInto b, M', hc.sub rfl rfl,
        { repr := h'.mpAt (some .bS) (some .bD) rfl rfl, copy := CopyPost.copyInto hP.sb hP.room
          frame := h'.unsplit (by simp [Two.lay]) }⟩
  -- from `0834`: `memset` the digits `[a->used, b->used)`, if any
  have mid : ∀ M, St (Split.lay (Two.lay 32 sp pa adp pb bdp a b) .stk 32) (Split.wr isW)
      [none, some .stk, some .bS, some .bD] (Kind.set (Split.kind (Tom.Machine.Two.kind pa adp pb bdp a b)
        (m0Of m ra s0 v.s.s1 sp)) (some .bD) (.mpD bdp b.alloc (ovl (copyDigits a b) b.digit a.used))) m M →
      Triple (At 0x80000834#64 (jL ra sp pa pb bdp a.used a.used) M v.keepR1 outp)
        (MpCopy.Ret m v outp sp pa adp pb bdp a b ra s0) := fun M h => by
    by_cases hle : b.used ≤ a.used
    · refine St.seq0 (m0_step ra v outp sp pa pb bdp a.used b.used M (cd h) (by facts h) (by facts h) (by omega)
        (by omega) hle) ?_
      exact fin M ((h.setMp (some .bS) (some .bD) rfl rfl (withD b (copyDigits a b)) rfl rfl rfl rfl fun j hj => by
          simp only [withD, MpInt.ofDigits_digit, if_pos hj, ovl, copyDigits]
          by_cases h1 : j < a.used
          · simp [h1]
          · simp [h1, show ¬ j < b.used by omega]).congrK (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl))
    refine St.seq0 (m1_step ra v outp sp pa pb bdp a.used b.used M (cd h) (by facts h) (by facts h) (by omega)
      (by omega)) ?_
    refine call_std memsetD ⟨bdp, b.alloc, ovl (copyDigits a b) b.digit a.used, a.used, b.used, _⟩ σd h (cd h)
      0x35d080ef#32 0x08b5c#21 0x8000084c#64 ⟨by (try dsimp only); omega, by (try dsimp only); omega, rfl⟩
      fun _ M' _ h' => ?_
    refine St.seq0 (u_step v outp sp pa pb a.used M' (cd h') (by facts h') (by facts h') (by omega)) ?_
    exact fin M' ((h'.setMp (some .bS) (some .bD) rfl rfl (withD b (copyDigits a b)) rfl rfl rfl rfl fun j hj => by
        simp only [withD, MpInt.ofDigits_digit, if_pos hj, zfill, ovl, copyDigits]
        by_cases h1 : j < a.used
        · simp [h1, show ¬ a.used ≤ j by omega]
        · by_cases h2 : j < b.used
          · simp [h1, h2, show a.used ≤ j by omega]
          · simp [h1, h2]).congrK (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl))
  -- from `0808`: the copy loop, or none
  have h2 : St (Split.lay (Two.lay 32 sp pa adp pb bdp a b) .stk 32) (Split.wr isW) [none, some .stk, some .bS, some .bD]
      (Kind.set (Split.kind (Tom.Machine.Two.kind pa adp pb bdp a b) (m0Of m ra s0 v.s.s1 sp)) (some .bD)
        (.mpD bdp b.alloc (ovl (copyDigits a b) b.digit 0))) m M1 := by
    rw [ovl_zero]; exact h1.congrK (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl)
  rcases Nat.eq_zero_or_pos a.used with h0u | hpos
  · rw [h0u] at mid ⊢
    exact St.seq0 (e0_step ra v outp sp pa pb adp bdp b.alloc M1 (cd h1) (by facts h1)) (mid M1 h2)
  refine St.seq0 (e1_step ra v outp sp pa pb adp bdp a.used b.alloc M1 (cd h1) (by facts h1) hpos (by omega)) ?_
  have hx : ∀ i, a.digit i < 2 ^ 31 := fun i => Nat.lt_of_lt_of_le (hP.sa.digit_lt i) (by decide)
  refine Triple.lmap (fun cf hc => ⟨M1, h2, hc⟩) (Triple.countup_from (lo := 0) (n := a.used)
    (P := fun i cf => ∃ M, St (Split.lay (Two.lay 32 sp pa adp pb bdp a b) .stk 32) (Split.wr isW)
      [none, some .stk, some .bS, some .bD] (Kind.set (Split.kind (Tom.Machine.Two.kind pa adp pb bdp a b)
        (m0Of m ra s0 v.s.s1 sp)) (some .bD) (.mpD bdp b.alloc (ovl (copyDigits a b) b.digit i))) m M ∧
      At 0x80000818#64 (lL ra sp pa pb adp bdp a.used i) M v.keepR1 outp cf)
    (fun i _ hi cf ⟨M, h, hat⟩ => ?_) ?_ 0 (Nat.le_refl _) hpos)
  · have := hx i
    exact (h.seqOvl (some .bD) rfl (l_step ra v outp sp pa pb adp bdp a.used i _ M (cd h) (by facts h) hi)
      (by omega) (by omega) (by simp [copyDigits, show i < a.used by omega])
      fun M' h' cf' hc' => ⟨cf', Vsa.Machine.Steps.refl _, M', by rwa [Kind.set_set] at h', hc'⟩) cf hat
  intro cf ⟨M, h, hat⟩
  have := hx (a.used - 1)
  refine (h.seqOvl (some .bD) rfl (le_step ra v outp sp pa pb adp bdp a.used (a.used - 1) _ M (cd h) (by facts h)
    (by omega)) (by omega) (by omega) (by simp [copyDigits, show a.used - 1 < a.used by omega])
    fun M' h' => ?_) cf hat
  rw [Kind.set_set, show a.used - 1 + 1 = a.used by omega] at h'
  exact mid M' h'

/-- **`mp_copy(a, a)` on the machine.** -/
theorem alias_correct : Api.MpCopy.AliasStatement := by
  intro m v outp sp pa ra s0 hra himg
  refine Triple.lmap (fun cf h => h.reshape (L' := entry1 ra s0 v.s.s1 sp pa pa) (K' := v.keepR1)
    (by simp [entryL, entry1, Abi.keepR, sKeepL])
    (by simp [entryL, Abi.keepR1, Abi.keepR, sKeepL])) ?_
  exact Triple.rmap (fun cf h => h.reshape (by simp) (by simp [Abi.keepR, Abi.keepR1, sKeepL]))
    (a_step ra s0 v.s.s1 v outp sp pa m himg.mpCopy hra)

end Tom.Machine.Fn.MpCopy
