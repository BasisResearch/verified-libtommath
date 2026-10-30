import Tom.Machine.Fn.Div3
import Tom.Machine.Kit.Meet

/-!
# `s_mp_div_3`'s digit loop over `Kit/Meet.lean`

From the top digit down: at index `ix` the remainder carried in is
`ldR a.digit 3 u (ix + 1)` and the quotient's digits `[ix + 1, u)` are stored
(`qd u (ix + 1)`). One iteration is two or three of `Fn/Div3.lean`'s pieces and
one `St.seqD` into the quotient's digit array; the loop is an induction on the
index, its exit the continuation at `6744`.
-/


namespace Tom.Machine.Fn.Div3

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

/-- The quotient's digits stored from `i` up (of `u`). -/
def qd (da : Nat → Nat) (u i : Nat) : Nat → Nat := fun j => if i ≤ j ∧ j < u then Tom.ldQ da 3 u j else 0

theorem qd_step (da : Nat → Nat) (u ix : Nat) :
    (fun j => if j = ix then Tom.ldQ da 3 u ix else qd da u (ix + 1) j) = qd da u ix ∨ ¬ ix < u := by
  by_cases hi : ix < u
  · refine .inl (funext fun j => ?_)
    simp only [qd]
    by_cases hj : j = ix
    · subst hj; simp [hi]
    · rw [if_neg hj]; congr 1; apply propext; omega
  · exact .inr hi

theorem qd_set {da : Nat → Nat} {u ix : Nat} (hi : ix < u) :
    (fun j => if j = ix then Tom.ldQ da 3 u ix else qd da u (ix + 1) j) = qd da u ix :=
  (qd_step da u ix).resolve_right (by omega)

/-- One step's arithmetic: `W = w 2^28 + d`, the digit `W / 3`, the remainder `W % 3`. -/
theorem step_arith {da : Nat → Nat} {u ix : Nat} (hi : ix < u) :
    Tom.ldQ da 3 u ix = (Tom.ldR da 3 u (ix + 1) * 268435456 + da ix) / 3 ∧
      Tom.ldR da 3 u ix = (Tom.ldR da 3 u (ix + 1) * 268435456 + da ix) % 3 := by
  have e : Tom.radix = 268435456 := Tom.radix_eq
  refine ⟨by simp only [Tom.ldQ, e], by rw [Tom.ldR_step da 3 hi, e]⟩

/-- **One iteration to its store**: `W ≤ 2` to `66bc` (digit `0`), else the
estimate, the fix-up if needed, to `672c` with the digit `W / 3`, remainder `W % 3`. -/
theorem head {sp pa pc pd adp qdp w ix d : Nat} {M : Mem} {v : Abi} {outp : Array String}
    {Q : Vsa.Machine.Config → Prop} (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hf : LFacts M adp ix d) (hw : w < 3)
    (k1 : w * 268435456 + d ≤ 2 →
      Triple (At 0x800066bc#64 (cL sp pa pc pd adp qdp ix 0 (w * 268435456 + d)) M v.keepR2 outp) Q)
    (k2 : 2 < w * 268435456 + d → Triple (At 0x8000672c#64 (cL sp pa pc pd adp qdp ix ((w * 268435456 + d) / 3)
      ((w * 268435456 + d) % 3)) M v.keepR2 outp) Q) :
    Triple (At 0x800066d0#64 (lL sp pa pc pd adp qdp w ix) M v.keepR2 outp) Q := by
  have hd := hf.d_lt
  by_cases hW : w * 268435456 + d ≤ 2
  · exact St.seq0 (hl_step v outp sp pa pc pd adp qdp w ix d M hc hf hw hW) (k1 hW)
  refine St.seq0 (hh_step v outp sp pa pc pd adp qdp w ix d M hc hf hw (by omega)) ?_
  generalize hWd : w * 268435456 + d = W at hW k2
  have hWl : W < 805306368 := by omega
  have hb := est_bounds hWl
  by_cases hr : W - 3 * est W ≤ 2
  · exact St.seq0 (eo_step v outp sp pa pc pd adp qdp ix W M hc hWl hr) (k2 (by omega))
  refine St.seq0 (ef_step v outp sp pa pc pd adp qdp ix W M hc hWl (by omega)) ?_
  have e : W / 3 - 1 + 1 = W / 3 := by simp only [est] at hb hr; omega
  have := f_step v outp sp pa pc pd adp qdp ix (W / 3 - 1) (W % 3) M hc (by omega) (by omega)
  rw [e] at this
  exact St.seq0 this (k2 (by omega))

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind} {m : Mem}
  {v : Abi} {outp : Array String} {Q : Vsa.Machine.Config → Prop}

/-- The facts of one iteration, from the state. -/
structure LoopCtx (ρ : ι → Iv) (κ : ι → Kind) (rs rd rc : ι) (adp qdp n : Nat) (a : MpInt) : Prop where
  kd : κ rd = .mpD adp a.alloc a.digit
  kc : κ rc = .code
  ne_sd : rs ≠ rd
  ne_sc : rs ≠ rc
  dsc : (ρ rs).Disj (ρ rc)
  fit : Iv.Sub ⟨qdp, 4 * n⟩ (ρ rs)
  shape : a.Shape
  un : a.used ≤ n
  ua : a.used ≤ a.alloc
  ul : a.used < 2 ^ 31
  adp4 : 4 ≤ adp
  qdp4 : 4 ≤ qdp

theorem LoopCtx.set {rs rd rc : ι} {adp qdp n : Nat} {a : MpInt} (h : LoopCtx ρ κ rs rd rc adp qdp n a) (k : Kind) :
    LoopCtx ρ (Kind.set κ rs k) rs rd rc adp qdp n a :=
  { h with kd := by simp [Kind.set, Ne.symm h.ne_sd, h.kd], kc := by simp [Kind.set, Ne.symm h.ne_sc, h.kc] }

/-- An iteration's reads from the state. -/
theorem LoopCtx.facts {rs rd rc : ι} {adp qdp n : Nat} {a : MpInt} {f : Nat → Nat} {M : Mem}
    (h : St ρ isW W (Kind.set κ rs (.mpD qdp n f)) m M)
    (hx : LoopCtx ρ (Kind.set κ rs (.mpD qdp n f)) rs rd rc adp qdp n a) {ix : Nat} (hi : ix < a.used) :
    LFacts M adp ix (a.digit ix) ∧ QFacts qdp ix ∧ CodeAt M sMpDiv3Base sMpDiv3Code := by
  have dA := h.dig rd hx.kd
  have dQ := h.dig rs (dp := qdp) (n := n) (f := f) (by simp [Kind.set])
  have hu := hx.ua; have hn := hx.un
  have hcf := (h.wit rc).1; rw [hx.kc] at hcf
  have hd := hx.dsc; have hfit := hx.fit
  have e : sMpDiv3Base = 0x80006640 := rfl
  refine ⟨⟨Ram.sub dA.ram (by omega) (by omega), dA.arr ix (by omega),
    by have := hx.shape.digit_lt ix; rwa [Tom.radix_eq] at this⟩,
    ⟨Ram.sub dQ.ram (by omega) (by omega), dQ.al, ?_⟩, (h.img rc hx.kc).sMpDiv3⟩
  unfold Kind.Fits textIv textBase textLen at hcf
  unfold Iv.Disj Disj at hd; unfold Iv.Sub at hcf hfit; simp only at hcf hfit
  omega

/-- **The loop**: from the head at `ix` (digits above stored) to the exit with all stored. -/
theorem loop {rs rd rc : ι} {sp pa pc pd adp qdp n : Nat} {a : MpInt} (hw : isW rs = true) (hW : SubN [rs] W = true)
    (kexit : ∀ M, St ρ isW W (Kind.set κ rs (.mpD qdp n (qd a.digit a.used 0))) m M →
      Triple (At 0x80006744#64 (xL sp pa pc pd (Tom.ldR a.digit 3 a.used 0)) M v.keepR2 outp) Q) :
    ∀ ix, ix < a.used → ∀ M, St ρ isW W (Kind.set κ rs (.mpD qdp n (qd a.digit a.used (ix + 1)))) m M →
      LoopCtx ρ (Kind.set κ rs (.mpD qdp n (qd a.digit a.used (ix + 1)))) rs rd rc adp qdp n a →
      Triple (At 0x800066d0#64 (lL sp pa pc pd adp qdp (Tom.ldR a.digit 3 a.used (ix + 1)) ix) M v.keepR2 outp) Q := by
  intro ix
  induction ix with
  | zero =>
    intro hi M h hx
    obtain ⟨hf, hq, hc⟩ := hx.facts h hi
    obtain ⟨eq, er⟩ := step_arith (da := a.digit) hi
    have hk : Kind.set κ rs (.mpD qdp n (qd a.digit a.used (0 + 1))) rs = .mpD qdp n (qd a.digit a.used (0 + 1)) := by
      simp [Kind.set]
    have hr := Tom.ldR_lt a.digit (show 0 < 3 by decide) a.used (0 + 1)
    have hn := hx.un
    refine head hc hf hr (fun hW0 => ?_) (fun hW0 => ?_)
    · refine h.seqD rs hk (zx_step v outp sp pa pc pd adp qdp _ M hc hq) (by omega) (by decide) (fun M' h' => ?_) hw hW
      rw [Kind.set_set] at h'
      have := qd_set (da := a.digit) hi
      rw [eq, show (Tom.ldR a.digit 3 a.used (0 + 1) * 268435456 + a.digit 0) / 3 = 0 by omega] at this
      rw [this] at h'
      have e2 : Tom.ldR a.digit 3 a.used (0 + 1) * 268435456 + a.digit 0 = Tom.ldR a.digit 3 a.used 0 := by omega
      rw [e2]; exact kexit M' h'
    · have ht : (Tom.ldR a.digit 3 a.used (0 + 1) * 268435456 + a.digit 0) / 3 < 2 ^ 31 := by
        have := hf.d_lt; omega
      refine h.seqD rs hk (sx_step v outp sp pa pc pd adp qdp _ _ M hc hq ht) (by omega) (by omega)
        (fun M' h' => ?_) hw hW
      rw [Kind.set_set, ← eq, qd_set hi] at h'
      rw [← er]; exact kexit M' h'
  | succ k ih =>
    intro hi M h hx
    obtain ⟨hf, hq, hc⟩ := hx.facts h hi
    obtain ⟨eq, er⟩ := step_arith (da := a.digit) hi
    have hk : Kind.set κ rs (.mpD qdp n (qd a.digit a.used (k + 1 + 1))) rs =
        .mpD qdp n (qd a.digit a.used (k + 1 + 1)) := by simp [Kind.set]
    have hr := Tom.ldR_lt a.digit (show 0 < 3 by decide) a.used (k + 1 + 1)
    have hn := hx.un; have hul := hx.ul; have ha4 := hx.adp4
    refine head hc hf hr (fun hW0 => ?_) (fun hW0 => ?_)
    · refine h.seqD rs hk (zc_step v outp sp pa pc pd adp qdp k _ M hc hq (by omega) (by omega)) (by omega) (by decide)
        (fun M' h' => ?_) hw hW
      rw [Kind.set_set] at h'
      have := qd_set (da := a.digit) hi
      rw [eq, show (Tom.ldR a.digit 3 a.used (k + 1 + 1) * 268435456 + a.digit (k + 1)) / 3 = 0 by omega] at this
      rw [this] at h'
      have e2 : Tom.ldR a.digit 3 a.used (k + 1 + 1) * 268435456 + a.digit (k + 1) = Tom.ldR a.digit 3 a.used (k + 1) := by
        omega
      rw [e2]; exact ih (by omega) M' h'
        (by have := hx.set (.mpD qdp n (qd a.digit a.used (k + 1))); rwa [Kind.set_set] at this)
    · have ht : (Tom.ldR a.digit 3 a.used (k + 1 + 1) * 268435456 + a.digit (k + 1)) / 3 < 2 ^ 31 := by
        have := hf.d_lt; omega
      refine h.seqD rs hk (sc_step v outp sp pa pc pd adp qdp k _ _ M hc hq ht (by omega) (by omega)) (by omega)
        (by omega) (fun M' h' => ?_) hw hW
      rw [Kind.set_set, ← eq, qd_set hi] at h'
      rw [← er]; exact ih (by omega) M' h'
        (by have := hx.set (.mpD qdp n (qd a.digit a.used (k + 1))); rwa [Kind.set_set] at this)

end

end Tom.Machine.Fn.Div3
