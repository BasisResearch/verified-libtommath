import Tom.Machine.Api.MpRshd
import Tom.Machine.Api.StdLib

/-!
# `mp_rshd` on the machine: the whole function

The three branches of `Tom.Machine.Fn.MpRshd` over `Kit/Meet.lean`: `b = 0`
returns; `b ≥ used` tail-calls `mp_zero` (`tail_std`); otherwise the shift
loop (`St.seqOvl`: digit `x` takes `dp[x + b]`, still the old digit above the
index), the frame stores, `memset` of `[used - b, used)` (`call_std memsetD`)
and the `used` store (`St.seqU`). Regions are `Un`'s, the stack (32 bytes) all
our own frame (`Split`).
-/


namespace Tom.Machine.Fn.MpRshd

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api Tom.Machine.Std
open Tom.Machine.Api.Un (R isW)

/-- The digits the loop writes. -/
def gD (a : MpInt) (b j : Nat) : Nat := if j + b < a.used then a.digit (j + b) else 0

/-- The result. -/
def res (a : MpInt) (b : Nat) : MpInt := MpInt.ofDigits (a.used - b) a.alloc a.sign (rshdDigits a b)

theorem res_post {a : MpInt} {b : Nat} (ha : a.Shape) : RshdShift a b (res a b) :=
  { alloc := rfl, len := MpInt.ofDigits_len _ _ _ _, used := rfl, sign := rfl
    digit := fun i => by
      simp only [res, MpInt.ofDigits_digit]
      split
      · rfl
      · have := ha.used_le
        simp only [show ¬ i + b < a.used by omega, show ¬ i < a.used by omega, ite_false]
        exact (ha.high_zero i (by omega)).symm }

def σz : Ob → Option R
  | .S => some .aS
  | .D => some .aD
  | .code => some .code

def σd : Dz → Option R
  | .D => some .aD
  | .code => some .code

/-- The loop's states: `a`'s digits hold `ovl (gD a b) a.digit x`. -/
abbrev Sx (m M : Mem) (sp pa adp : Nat) (a : MpInt) (b x : Nat) : Prop :=
  St (Split.lay (Un.lay 32 sp pa adp a) .stk 32) (Split.wr isW) [none, some .stk, some .aS, some .aD]
    (Kind.set (Split.kind (Tom.Machine.Un.kind pa adp a) m) (some .aD) (.mpD adp a.alloc (ovl (gD a b) a.digit x))) m M

theorem cd {sp pa adp : Nat} {a : MpInt} {W : List (Option R)} {κ : Option R → Kind} {m M : Mem}
    (h : St (Split.lay (Un.lay 32 sp pa adp a) .stk 32) (Split.wr isW) W κ m M)
    (hk : κ (some .code) = .code := by rfl) : CodeAt M mpRshdBase mpRshdCode := (h.img (some .code) hk).mpRshd

/-- **`mp_rshd` on the machine.** -/
theorem correct : Api.MpRshd.Statement := by
  intro m v outp sp pa adp a b ra s0 hP
  have h0 := St.un (f := 32) hP.ra_ hP.ga hP.rs hP.img hP.lay (by decide)
  have hua := hP.sa.used_le; have := hP.sa.alloc_lt; have := hP.sp_ge; have := hP.sp_al; have := hP.ra_al
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · exact Triple.rmap (fun cf h => ⟨a, m, h, hP.ra_,
        ⟨fun _ => rfl, fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd h (Nat.lt_irrefl 0)⟩, Frm.refl _ _⟩)
      (n_step ra s0 v outp sp pa m (cd h0) hP.ra_al)
  by_cases hub : a.used ≤ b
  · refine St.seq0 (z_step ra s0 v outp sp pa adp a.used b m (cd h0) (by facts h0) hb hP.b_lt hub) ?_
    exact tail_std mpZero ⟨pa, adp, a⟩ σz (h0.forget none rfl) hP.sa hP.ra_al fun a' M cf hq h' hat =>
      ⟨a', M, hat, h'.mpAt (some .aS) (some .aD) rfl rfl,
        ⟨fun h => absurd h (by omega), fun _ _ => hq.1, fun _ h => absurd h (by omega)⟩, h'.unsplit (by simp [Un.lay])⟩
  have hlt : b < a.used := by omega
  refine St.seq0 (e_step ra s0 v outp sp pa adp a.used b m (cd h0) (by facts h0) hb hlt) ?_
  have h1 : Sx m m sp pa adp a b 0 := by
    rw [Sx, ovl_zero]; exact h0.congrK fun r => by unfold Kind.set; split <;> (try subst_vars) <;> rfl
  have hy : ∀ {M x}, Sx m M sp pa adp a b x → x + b < a.used →
      bytesT4 M (adp + 4 * (x + b)) = BitVec.ofNat 32 (a.digit (x + b)) ∧ a.digit (x + b) < 2 ^ 31 :=
    fun {M x} h hx => ⟨by have := (h.dig (some .aD) rfl).arr (x + b) (by omega); simpa [ovl, show ¬ x + b < x by omega] using this,
      Nat.lt_of_lt_of_le (hP.sa.digit_lt _) (by decide)⟩
  refine Triple.lmap (fun cf hc => ⟨m, h1, hc⟩) (Triple.countup_from (lo := 0) (n := a.used - b)
    (P := fun x cf => ∃ M, Sx m M sp pa adp a b x ∧ At 0x80001e3c#64 (hL ra s0 sp pa adp b x) M v.keepR outp cf)
    (fun x _ hx cf ⟨M, h, hat⟩ => ?_) ?_ 0 (Nat.le_refl _) (by omega))
  · obtain ⟨hy1, hy2⟩ := hy h (by omega)
    exact (h.seqOvl (some .aD) rfl (l_step ra s0 v outp sp pa adp a.used b x _ M (cd h) (by facts h) hlt hx)
      (by omega) (by omega) (by simp [gD, show x + b < a.used by omega])
      fun M' h' cf' hc' => ⟨cf', Vsa.Machine.Steps.refl _, M', by rwa [Kind.set_set] at h', hc'⟩) cf hat
  intro cf ⟨M, h, hat⟩
  obtain ⟨hy1, hy2⟩ := hy h (x := a.used - b - 1) (by omega)
  refine (h.seqOvl (some .aD) rfl (le_step ra s0 v outp sp pa adp a.used b (a.used - b - 1) _ M (cd h) (by facts h)
    hlt (by omega)) (by omega) (by omega) (by simp [gD, show a.used - b - 1 + b < a.used by omega])
    fun M1 h1 => ?_) cf hat
  rw [Kind.set_set, show a.used - b - 1 + 1 = a.used - b by omega] at h1
  refine h1.seqW none rfl (m_step ra s0 v outp sp pa adp a.used b M1 (cd h1) (by facts h1) hb hlt (by omega))
    fun M2 h2 => ?_
  refine call_std memsetD ⟨adp, a.alloc, ovl (gD a b) a.digit (a.used - b), a.used - b, a.used, b⟩ σd h2 (cd h2)
    0x528070ef#32 0x7528#21 0x80001e80#64 ⟨by (try dsimp only); omega, by (try dsimp only); omega,
      by (try dsimp only); omega⟩ fun _ M3 _ h3 => ?_
  refine h3.seqU (some .aS) rfl (r_step ra s0 v outp sp pa a.used b M3 (cd h3) (by facts h3)) (by omega)
    fun M4 h4 cf hc => ?_
  have h5 := h4.setMp (some .aS) (some .aD) rfl rfl (res a b) rfl rfl rfl rfl fun j hj => by
    simp only [res, MpInt.ofDigits_digit, if_pos hj, rshdDigits, zfill, ovl, gD]
    by_cases h1 : j < a.used - b
    · simp [h1, show j + b < a.used by omega, show ¬ a.used - b ≤ j by omega]
    · by_cases h2 : j < a.used
      · simp [h1, h2, show ¬ j + b < a.used by omega, show a.used - b ≤ j by omega]
      · simp [h1, h2, show ¬ j + b < a.used by omega]
  exact ⟨cf, Vsa.Machine.Steps.refl _, res a b, M4, hc, h5.mpAt (some .aS) (some .aD) rfl rfl,
    ⟨fun h => absurd h (by omega), fun _ h => absurd h (by omega), fun _ _ => res_post hP.sa⟩, h4.unsplit (by simp [Un.lay])⟩

end Tom.Machine.Fn.MpRshd
