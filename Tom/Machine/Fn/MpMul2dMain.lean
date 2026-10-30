import Tom.Machine.Api.Std
import Tom.Machine.Api.MpMul2d

/-!
# `mp_mul_2d` on the machine: the whole function

The segments of `Tom.Machine.Fn.MpMul2d` and the contracts of `mp_copy`,
`__divdi3`, `__moddi3`, `mp_lshd` and `mp_clamp` by `call_std`
(`Kit/Meet.lean`, `Api/Std.lean`). Regions as `mp_mod_2d`'s (`Two`'s, the
stack cut into our 48-byte frame and the callees' 32 below). The bit loop is
`St.seqOvl` over `c`'s digits; the paths meet at `183c` (`tail`, the state
re-abstracted by `St.congrK`).
-/


namespace Tom.Machine.Fn.MpMul2d

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api Tom.Machine.Std
open Tom.Machine.Api.Two (R isW)

/-! ## The value -/

/-- `a` shifted up by `D` digits. -/
def A (a : MpInt) (D j : Nat) : Nat := if D ≤ j then a.digit (j - D) else 0

/-- The carry into digit `j` of the bit loop over `f`. -/
def cr (d : Nat) (f : Nat → Nat) (j : Nat) : Nat := if j = 0 then 0 else shlHi d (f (j - 1))

/-- The bit loop's digit `j`. -/
def gl (d : Nat) (f : Nat → Nat) (j : Nat) : Nat := shlLo d (f j) + cr d f j

theorem shlHi_zero (d : Nat) : shlHi d 0 = 0 := by simp [shlHi]
theorem shlLo_zero (d : Nat) : shlLo d 0 = 0 := by simp [shlLo]

theorem mul2d_eq {a : MpInt} (b : Nat) : mul2dDigit a b = gl (b % 28) (A a (b / 28)) := by
  funext j
  have e : Layout.digitBits = 28 := rfl
  simp only [mul2dDigit, gl, cr, A, e]
  by_cases h1 : b / 28 ≤ j
  · by_cases h2 : b / 28 < j
    · simp [h1, h2, show j ≠ 0 by omega, show b / 28 ≤ j - 1 by omega, show j - 1 - b / 28 = j - b / 28 - 1 by omega]
    · by_cases h0 : j = 0
      · simp [h2, h0]; split <;> simp [shlLo_zero]
      · simp [h1, h2, h0, show ¬ b / 28 ≤ j - 1 by omega, shlHi_zero]
  · by_cases h0 : j = 0
    · simp [h1, h0, show ¬ b / 28 < j by omega, shlLo_zero]; split <;> simp [shlLo_zero]
    · simp [h1, h0, show ¬ b / 28 < j by omega, show ¬ b / 28 ≤ j - 1 by omega, shlLo_zero, shlHi_zero]

theorem A_lt {a : MpInt} (ha : a.Shape) (D j : Nat) : A a D j < radix := by
  unfold A; split
  · exact ha.digit_lt _
  · exact radix_pos

theorem gl_zero {f : Nat → Nat} (hf : ∀ j, f j < radix) : gl 0 f = f := by
  funext j; simp only [gl, cr, shlLo, shlHi, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (hf j)]
  split
  · rfl
  · simp [Nat.div_eq_of_lt (hf _)]

theorem copy_digit {a c c' : MpInt} (ha : a.Shape) (hc : c.Shape) (h : CopyPost a c c') : c'.digit = a.digit :=
  funext fun j => by
    rw [h.digit]; split
    · rfl
    · rw [ha.high_zero j (by omega)]; split
      · rfl
      · exact hc.high_zero j (by omega)

theorem lshd_digit {a c' c'' : MpInt} {D : Nat} (ha : a.Shape) (h : LshdPost c' D c'')
    (hd : c'.digit = a.digit) (hu : c'.used = a.used) : c''.digit = A a D := by
  funext j
  by_cases h0 : D = 0 ∨ c'.used = 0
  · rw [h.noop h0, hd]; simp only [A]
    rcases h0 with h0 | h0
    · subst h0; simp
    · rw [ha.high_zero j (by omega)]; split
      · exact (ha.high_zero _ (by omega)).symm
      · rfl
  · rw [(h.shift (by omega) (by omega)).digit, hd]; simp only [A]
    by_cases hj : j < D
    · rw [if_pos hj, if_neg (by omega)]
    · rw [if_neg hj, if_pos (show D ≤ j by omega)]; split
      · rfl
      · exact (ha.high_zero j (by omega)).trans (ha.high_zero _ (by omega)).symm

theorem lshd_used {a c' c'' : MpInt} {D : Nat} (h : LshdPost c' D c'') (hu : c'.used = a.used) :
    c''.used = if a.used = 0 then 0 else a.used + D := by
  by_cases h0 : D = 0 ∨ c'.used = 0
  · rw [h.noop h0, hu]; split
    · omega
    · rcases h0 with h0 | h0 <;> omega
  · rw [(h.shift (by omega) (by omega)).used, hu, if_neg (by omega)]

theorem clampUsed_ext {f : Nat → Nat} {n : Nat} : ∀ N, n ≤ N → (∀ j, n ≤ j → j < N → f j = 0) →
    clampUsed f N = clampUsed f n
  | 0, h, _ => by rw [show n = 0 by omega]
  | N + 1, h, hz => by
    rcases Nat.lt_or_eq_of_le h with h | h
    · simp only [clampUsed, hz N (by omega) (by omega), if_true]
      exact clampUsed_ext N (by omega) fun j h1 h2 => hz j h1 (by omega)
    · rw [h]

theorem mul2d_post {a c c₃ c₄ : MpInt} {b : Nat} (hcl : ClampPost c₃ c₄) (hlen : c₃.digits.length = c.alloc)
    (hal : c₃.alloc = c.alloc) (hsg : c₃.sign = a.sign) (hdig : c₃.digit = mul2dDigit a b)
    (hu : c₃.used ≤ a.used + b / 28 + 1) (hz : ∀ j, c₃.used ≤ j → j < a.used + b / 28 + 1 → mul2dDigit a b j = 0) :
    Mul2dPost a b c c₄ :=
  { alloc := by rw [hcl.alloc, hal]
    len := by rw [hcl.digits, hlen]
    digit := by rw [hcl.digit, hdig]
    used := by rw [hcl.used, hdig]; exact (clampUsed_ext (n := c₃.used) _ hu hz).symm
    sign := by rw [hcl.sign, hsg] }

/-- What `mp_clamp` is handed after the bit loop: `used` `u`, the model's digits. -/
def fin (a c₁ : MpInt) (b u : Nat) : MpInt := MpInt.ofDigits u c₁.alloc c₁.sign (mul2dDigit a b)

theorem fin_digit {a c c₁ : MpInt} {b u : Nat} (ha : a.Shape) (hal : c₁.alloc = c.alloc)
    (hroom : a.used + b / 28 + 1 ≤ c.alloc) : (fin a c₁ b u).digit = mul2dDigit a b := by
  funext j; simp only [fin, MpInt.ofDigits_digit]
  by_cases hj : j < c.alloc
  · rw [if_pos (by rw [hal]; exact hj)]
  · rw [if_neg (by rw [hal]; exact hj)]; exact (mul2dDigit_high ha b j (by simp only [Layout.digitBits]; omega)).symm

theorem fin_shape {a c c₁ : MpInt} {b u : Nat} (ha : a.Shape) (hc : c.Shape) (hal : c₁.alloc = c.alloc)
    (hroom : a.used + b / 28 + 1 ≤ c.alloc) (hu : u ≤ a.used + b / 28 + 1)
    (hz : ∀ j, u ≤ j → j < a.used + b / 28 + 1 → mul2dDigit a b j = 0) : (fin a c₁ b u).Shape :=
  { len := MpInt.ofDigits_len _ _ _ _
    used_le := by simp only [fin, MpInt.ofDigits, hal]; omega
    alloc_lt := by simp only [fin, MpInt.ofDigits, hal]; exact hc.alloc_lt
    digit_lt := fun i => by rw [fin_digit ha hal hroom]; exact mul2dDigit_lt ha b i
    high_zero := fun i hi => by
      rw [fin_digit ha hal hroom]
      simp only [fin, MpInt.ofDigits] at hi
      by_cases h : i < a.used + b / 28 + 1
      · exact hz i hi h
      · exact mul2dDigit_high ha b i (by simp only [Layout.digitBits]; omega) }

/-- The `mp_int` the bit loop starts from (after `mp_copy`, and `mp_lshd` when `b ≥ 28`). -/
structure Mid (a c c₁ : MpInt) (b : Nat) : Prop where
  dig : c₁.digit = A a (b / 28)
  used : c₁.used = if a.used = 0 then 0 else a.used + b / 28
  alloc : c₁.alloc = c.alloc
  sign : c₁.sign = a.sign
  len : c₁.digits.length = c.alloc

theorem Mid.shape {a c c₁ : MpInt} {b : Nat} (h : Mid a c c₁ b) (ha : a.Shape) (hc : c.Shape)
    (hroom : a.used + b / 28 + 1 ≤ c.alloc) : c₁.Shape :=
  { len := by rw [h.len, h.alloc]
    used_le := by rw [h.used, h.alloc]; split <;> omega
    alloc_lt := by rw [h.alloc]; exact hc.alloc_lt
    digit_lt := fun i => by rw [h.dig]; exact A_lt ha _ i
    high_zero := fun i hi => by
      rw [h.dig]; simp only [A]; split
      · rw [h.used] at hi; exact ha.high_zero _ (by split at hi <;> omega)
      · rfl }

theorem Mid.copy {a c c' : MpInt} {b : Nat} (ha : a.Shape) (hc : c.Shape) (h : CopyPost a c c') (hb : b < 28) :
    Mid a c c' b :=
  { dig := by rw [copy_digit ha hc h, show b / 28 = 0 by omega]; funext j; simp [A]
    used := by rw [h.used, show b / 28 = 0 by omega]; split <;> omega
    alloc := h.alloc, sign := h.sign, len := h.len }

theorem Mid.lshd {a c c' c'' : MpInt} {b : Nat} (ha : a.Shape) (hc : c.Shape) (h : CopyPost a c c')
    (hl : LshdPost c' (b / 28) c'') : Mid a c c'' b :=
  { dig := lshd_digit ha hl (copy_digit ha hc h) h.used
    used := lshd_used hl h.used
    alloc := by rw [hl.alloc', h.alloc]
    sign := by
      by_cases h0 : b / 28 = 0 ∨ c'.used = 0
      · rw [hl.noop h0, h.sign]
      · rw [(hl.shift (by omega) (by omega)).sign, h.sign]
    len := by
      by_cases h0 : b / 28 = 0 ∨ c'.used = 0
      · rw [hl.noop h0, h.len]
      · rw [(hl.shift (by omega) (by omega)).len, h.alloc] }

/-- No bit loop (`b % 28 = 0`, or `a` is zero): `c₁` is the result. -/
theorem Mid.post {a c c₁ c₄ : MpInt} {b : Nat} (h : Mid a c c₁ b) (ha : a.Shape) (hroom : a.used + b / 28 + 1 ≤ c.alloc)
    (h0 : b % 28 = 0 ∨ a.used = 0) (hcl : ClampPost c₁ c₄) : Mul2dPost a b c c₄ := by
  have hz : ∀ j, mul2dDigit a b j = A a (b / 28) j ∨ a.used = 0 := fun j => by
    rcases h0 with h0 | h0
    · left; rw [mul2d_eq, h0, gl_zero (A_lt ha _)]
    · right; exact h0
  have hdig : c₁.digit = mul2dDigit a b := by
    funext j; rw [h.dig]
    rcases hz j with e | e
    · exact e.symm
    · have hA0 : A a (b / 28) = fun _ => 0 := funext fun j => by
        simp only [A]; split
        · exact ha.high_zero _ (by omega)
        · rfl
      rw [mul2d_eq, hA0]; simp [gl, cr, shlLo_zero, shlHi_zero]
  refine mul2d_post hcl h.len h.alloc h.sign hdig (by rw [h.used]; split <;> omega) fun j hj1 hj2 => ?_
  rw [← hdig, h.dig]; simp only [A]; split
  · rw [h.used] at hj1; exact ha.high_zero _ (by split at hj1 <;> omega)
  · rfl


theorem A_hi {a : MpInt} (ha : a.Shape) {D j : Nat} (hj : a.used + D ≤ j) : A a D j = 0 := by
  simp only [A]; split
  · exact ha.high_zero _ (by omega)
  · rfl

theorem cr_lt {d : Nat} {f : Nat → Nat} (hf : ∀ j, f j < radix) (hd : d ≤ 28) (j : Nat) : cr d f j < 2 ^ d := by
  unfold cr; split
  · exact Nat.two_pow_pos _
  · exact shlHi_lt hd (hf _)

/-- The digits after the bit loop and the last carry `r` at `used`. -/
theorem fin_eq {a c c₁ : MpInt} {b : Nat} (ha : a.Shape) (hm : Mid a c c₁ b) (hu0 : a.used ≠ 0) (j : Nat) :
    mul2dDigit a b j = if j = c₁.used then shlHi (b % 28) (c₁.digit (c₁.used - 1))
      else ovl (gl (b % 28) c₁.digit) c₁.digit c₁.used j := by
  have hu : c₁.used = a.used + b / 28 := by rw [hm.used, if_neg hu0]
  rw [mul2d_eq, ← hm.dig]
  simp only [ovl]
  by_cases hj : j = c₁.used
  · subst hj; rw [if_pos rfl]
    simp only [gl, cr, hm.dig, A_hi ha (by omega : a.used + b / 28 ≤ c₁.used), shlLo_zero, Nat.zero_add,
      if_neg (show c₁.used ≠ 0 by omega)]
  · rw [if_neg hj]; split
    · rfl
    · simp only [gl, cr, hm.dig, A_hi ha (by omega : a.used + b / 28 ≤ j), shlLo_zero, Nat.zero_add,
        if_neg (show j ≠ 0 by omega), A_hi ha (by omega : a.used + b / 28 ≤ j - 1), shlHi_zero]

/-! ## The machine -/

def σz : Ob → Option R
  | .S => some .bS
  | .D => some .bD
  | .code => some .code

def σc : Cd → Option R := fun _ => some .code

def σl : Un.R → Option R
  | .stk => some .stk
  | .aS => some .bS
  | .aD => some .bD
  | .code => some .code

abbrev ρw (sp pa adp pc cdp : Nat) (a c : MpInt) := Split.lay (Two.lay 80 sp pa adp pc cdp a c) R.stk 48

abbrev Wr : List (Option R) := [none, some .stk, some .bS, some .bD]

/-- Our frame after the prologue. -/
abbrev m0 (m : Mem) (ra s0 s1 : BitVec 64) (sp : Nat) : Mem := writeLog (writeLog m (frameLog1 s0 s1 sp)) [(sp - 8, 8, ra)]

theorem cd {sp pa adp pc cdp : Nat} {a c : MpInt} {W : List (Option R)} {κ : Option R → Kind} {m M : Mem}
    (h : St (ρw sp pa adp pc cdp a c) (Split.wr isW) W κ m M)
    (hk : κ (some .code) = .code := by rfl) : CodeAt M mpMul2dBase mpMul2dCode := (h.img (some .code) hk).mpMul2d

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat} {c : MpInt}
  {ra s0 : BitVec 64}

/-- From `183c`: `mp_clamp(c)`, the epilogue. -/
theorem tail (hP : MpMul2d.Pre m sp pa adp pc cdp a b c ra) {M : Mem} {c₃ : MpInt}
    (h : St (ρw sp pa adp pc cdp a c) (Split.wr isW) Wr (Split.kind (Two.kind pa adp pc cdp a c₃) (m0 m ra s0 v.s.s1 sp)) m M)
    (hs : c₃.Shape) (hal : c₃.alloc = c.alloc) (hq : ∀ c₄, ClampPost c₃ c₄ → Mul2dPost a b c c₄) :
    Triple (At 0x8000183c#64 (kL sp pc b) M v.keepR1 outp) (MpMul2d.Ret m v outp sp pa adp pc cdp a b c ra s0) := by
  have := hP.sp_ge; have := hP.sp_al; have hra := hP.ra_al
  refine St.seq0 (k_step v outp sp pc b M (cd h)) ?_
  refine call_std clamp ⟨pc, cdp, c₃⟩ σz h (cd h) 0x798030ef#32 0x3798#21 0x80001844#64 hs fun c₄ M' hcl h' => ?_
  exact (Triple.rmap (fun cf hc => ⟨c₄, M', hc.sub rfl rfl, ⟨(h'.hdr (some .bS) rfl).mpAt (by
      rw [hcl.alloc, hcl.digit]; exact h'.dig (some .bD) rfl), hq c₄ hcl, h'.unsplit (by simp [Two.lay])⟩⟩)
    (e_step ra s0 v.s.s1 v outp sp pc b M' (cd h') (by facts h'))).pre

end


section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat} {c : MpInt}
  {ra s0 : BitVec 64}

/-- From `17c0` (`b % 28 ≠ 0`): the bit loop over `c₁`'s digits, the last carry, then `tail`. -/
theorem bit (hP : MpMul2d.Pre m sp pa adp pc cdp a b c ra) {M : Mem} {c₁ : MpInt} (hm : Mid a c c₁ b)
    (h : St (ρw sp pa adp pc cdp a c) (Split.wr isW) Wr (Split.kind (Two.kind pa adp pc cdp a c₁) (m0 m ra s0 v.s.s1 sp)) m M)
    (hd0 : b % 28 ≠ 0) :
    Triple (At 0x800017c0#64 (nL sp pc b (b % 28)) M v.keepR1 outp) (MpMul2d.Ret m v outp sp pa adp pc cdp a b c ra s0) := by
  have := hP.sp_ge; have hroom : a.used + b / 28 + 1 ≤ c.alloc := hP.room; have := hP.va.alloc_lt
  have := hP.sc.alloc_lt; have := hP.va.used_le; have hal := hm.alloc
  have hs1 := hm.shape hP.va.toShape hP.sc hroom
  have hd : b % 28 < 28 := Nat.mod_lt _ (by decide)
  by_cases hu0 : a.used = 0
  · have hu : c₁.used = 0 := by rw [hm.used, if_pos hu0]
    refine St.seq0 (u0_step v outp sp pc b (b % 28) cdp M (cd h) (by rw [← hu]; facts h)) ?_
    exact tail hP h hs1 hal fun c₄ hcl => hm.post hP.va.toShape hroom (Or.inr hu0) hcl
  have hu : c₁.used = a.used + b / 28 := by rw [hm.used, if_neg hu0]
  refine St.seq0 (i_step v outp sp pc b (b % 28) cdp c₁.used M (cd h) (by facts h) (by omega) (by omega) hd) ?_
  have h0 : St (ρw sp pa adp pc cdp a c) (Split.wr isW) Wr (Kind.set (Split.kind (Two.kind pa adp pc cdp a c₁)
      (m0 m ra s0 v.s.s1 sp)) (some .bD) (.mpD cdp c₁.alloc (ovl (gl (b % 28) c₁.digit) c₁.digit 0))) m M := by
    rw [ovl_zero]; exact h.congrK fun r => by unfold Kind.set; split <;> (try subst_vars) <;> rfl
  have hv : ∀ x, shlLo (b % 28) (c₁.digit x) + cr (b % 28) c₁.digit x < 2 ^ 32 := fun x =>
    Nat.lt_of_lt_of_le (shlLo_add_lt (by simp only [Layout.digitBits]; omega) (cr_lt hs1.digit_lt (by omega) x)) (by decide)
  refine Triple.lmap (fun cf hc => ⟨M, h0, hc.subL (by exact rfl)⟩) (Triple.countup_from (lo := 0) (n := c₁.used) (P := fun x cf => ∃ M', St (ρw sp pa adp pc cdp a c)
      (Split.wr isW) Wr (Kind.set (Split.kind (Two.kind pa adp pc cdp a c₁) (m0 m ra s0 v.s.s1 sp)) (some .bD)
        (.mpD cdp c₁.alloc (ovl (gl (b % 28) c₁.digit) c₁.digit x))) m M' ∧
      At 0x800017f4#64 (lpL sp pc b (b % 28) cdp x (cr (b % 28) c₁.digit x)) M' v.keepR1 outp cf)
    (fun x _ hx cf ⟨M', h', hat⟩ => ?_) ?_ 0 (Nat.le_refl _) (by omega))
  · have he : bytesT4 M' (cdp + 4 * x) = BitVec.ofNat 32 (c₁.digit x) := by
      have := (h'.dig (some .bD) rfl).arr x (by omega); simpa [ovl] using this
    have hel := hs1.digit_lt x
    refine (h'.seqOvl (some .bD) rfl (lp_step v outp sp pc b (b % 28) cdp c₁.used x (c₁.digit x) (cr (b % 28) c₁.digit x)
      M' (cd h') (by facts h') (by omega) hd (cr_lt hs1.digit_lt (by omega) x) hx) (by omega) (hv x) rfl
      fun M'' h'' cf' hc' => ⟨cf', Vsa.Machine.Steps.refl _, M'', by rwa [Kind.set_set] at h'', hc'.subL (by exact rfl)⟩) cf hat
  · intro cf ⟨M', h', hat⟩
    have he : bytesT4 M' (cdp + 4 * (c₁.used - 1)) = BitVec.ofNat 32 (c₁.digit (c₁.used - 1)) := by
      have := (h'.dig (some .bD) rfl).arr (c₁.used - 1) (by omega); simpa [ovl] using this
    have hel := hs1.digit_lt (c₁.used - 1)
    refine (h'.seqOvl (some .bD) rfl (lx_step v outp sp pc b (b % 28) cdp c₁.used (c₁.used - 1) (c₁.digit (c₁.used - 1))
      (cr (b % 28) c₁.digit (c₁.used - 1)) M' (cd h') (by facts h') (by omega) hd (cr_lt hs1.digit_lt (by omega) _)
      (by omega)) (by omega) (hv _) rfl fun M'' h'' => ?_) cf hat
    rw [Kind.set_set, show c₁.used - 1 + 1 = c₁.used by omega] at h''
    have hfe := fin_eq hP.va.toShape hm hu0
    by_cases hr : shlHi (b % 28) (c₁.digit (c₁.used - 1)) = 0
    · refine St.seq0 (cz_step v outp sp pc b cdp c₁.used M'' (cd h'')) ?_ (by rw [hr]; exact rfl)
      have h3 := (h''.setMp (some .bS) (some .bD) rfl rfl (fin a c₁ b c₁.used) rfl rfl rfl rfl fun j hj => by
          rw [fin_digit hP.va.toShape hal hroom, hfe j, hr]; split
          · subst_vars; simp [ovl, hm.dig, A_hi hP.va.toShape (by omega : a.used + b / 28 ≤ c₁.used)]
          · rfl).congrK (κ' := Split.kind (Two.kind pa adp pc cdp a (fin a c₁ b c₁.used)) (m0 m ra s0 v.s.s1 sp))
        (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl)
      have hz : ∀ j, c₁.used ≤ j → j < a.used + b / 28 + 1 → mul2dDigit a b j = 0 := fun j h1 h2 => by
        rw [hfe j, if_pos (by omega), hr]
      exact tail hP h3 (fin_shape hP.va.toShape hP.sc hal hroom (by omega) hz) (by simp only [fin, MpInt.ofDigits]; exact hal)
        fun c₄ hcl => mul2d_post hcl (by rw [fin, MpInt.ofDigits_len, hal]) (by simp only [fin, MpInt.ofDigits]; exact hal)
          (by simp only [fin, MpInt.ofDigits]; exact hm.sign) (fin_digit hP.va.toShape hal hroom)
          (by simp only [fin, MpInt.ofDigits]; omega) hz
    · refine h''.seqU (some .bS) rfl (cn1_step v outp sp pc b cdp c₁.used (shlHi (b % 28) (c₁.digit (c₁.used - 1))) M'' (cd h'') (by facts h'') (by omega)
        (by omega) (Nat.lt_of_lt_of_le (shlHi_lt (by simp only [Layout.digitBits]; omega) hel) (by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show b % 28 ≤ 64 by omega); omega))) (by omega)
        fun M3 h3 => ?_
      have hrl : shlHi (b % 28) (c₁.digit (c₁.used - 1)) < 2 ^ 32 :=
        Nat.lt_of_lt_of_le (shlHi_lt (by simp only [Layout.digitBits]; omega) hel)
          (Nat.pow_le_pow_right (by decide) (by omega))
      refine h3.seqD (some .bD) rfl (cn2_step v outp sp pc b cdp c₁.used (shlHi (b % 28) (c₁.digit (c₁.used - 1))) M3 (cd h3) (by facts h3)) (by omega) hrl
        fun M4 h4 => ?_
      have h5 := (h4.setMp (some .bS) (some .bD) rfl rfl (fin a c₁ b (c₁.used + 1)) rfl rfl rfl rfl fun j hj => by
          rw [fin_digit hP.va.toShape hal hroom, hfe j]).congrK
        (κ' := Split.kind (Two.kind pa adp pc cdp a (fin a c₁ b (c₁.used + 1))) (m0 m ra s0 v.s.s1 sp))
        (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl)
      have hz : ∀ j, c₁.used + 1 ≤ j → j < a.used + b / 28 + 1 → mul2dDigit a b j = 0 := fun j h1 h2 => by omega
      exact tail hP h5 (fin_shape hP.va.toShape hP.sc hal hroom (by omega) hz) (by simp only [fin, MpInt.ofDigits]; exact hal)
        fun c₄ hcl => mul2d_post hcl (by rw [fin, MpInt.ofDigits_len, hal]) (by simp only [fin, MpInt.ofDigits]; exact hal)
          (by simp only [fin, MpInt.ofDigits]; exact hm.sign) (fin_digit hP.va.toShape hal hroom)
          (by simp only [fin, MpInt.ofDigits]; omega) hz

end

/-- **`mp_mul_2d` on the machine** (distinct operands). -/
theorem correct : Api.MpMul2d.Statement := by
  intro m v outp sp pa adp pc cdp a b c ra s0 hP
  have h0 := St.two (f := 48) hP.ra_ hP.ga hP.rc hP.gc hP.rs hP.img hP.lay (by decide)
  have := hP.sp_ge; have := hP.sp_al; have hra := hP.ra_al; have hb := hP.b_lt
  have hroom : a.used + b / 28 + 1 ≤ c.alloc := hP.room
  have := hP.va.used_le; have := hP.va.alloc_lt; have := hP.sc.used_le; have := hP.sc.alloc_lt
  have hne : pa ≠ pc := by have := hP.lay.disj (r := .aS) (s := .bS); simp only [Iv.Disj, Disj, Two.lay] at this; omega
  have := hP.ga.st.hi_le; have := hP.gc.st.hi_le
  refine Triple.lmap (fun cf h => h.sub (L' := entry1 ra s0 v.s.s1 sp pa b pc) (K' := v.keepR1) rfl rfl) ?_
  refine h0.seqW none rfl (p1_step ra s0 v.s.s1 v outp sp pa b pc m (cd h0) (by facts h0) hb) fun M1 h1 => ?_
  refine h1.seqW none rfl (p2_step ra v outp sp pa b pc M1 (cd h1) (by facts h1) hne (by omega) (by omega))
    fun M2 h2 => ?_
  refine call_std mpCopy ⟨sp - 48, pa, adp, pc, cdp, a, c⟩ some h2 (cd h2) 0x864ff0ef#32 0x1ff064#21 0x80001780#64
    ⟨hP.va.toShape, hP.sc, hP.va.sign_ok, by (try dsimp only); omega, by (try dsimp only); omega,
      by (try dsimp only); omega⟩ fun c' M3 hq h3 => ?_
  have hcp : CopyPost a c c' := hq.1; have hu := hcp.used; have hal := hcp.alloc
  refine St.seq0 (d_step v outp sp pc b M3 (cd h3)) ?_
  refine call_std divdi3 ⟨b, 28⟩ σc h3 (cd h3) 0x619150ef#32 0x15e18#21 0x80001790#64
    (DivRes.of (by omega) (by decide) (by decide)) fun _ M4 _ h4 => ?_
  refine St.seq0 (g_step v outp sp pc b c'.used c'.alloc M4 (cd h4) (by facts h4) hb (by omega)) ?_
  by_cases hb28 : b < 28
  · refine St.seq0 (s_step v outp sp pc b (b / 28) M4 (cd h4) hb28) ?_
    refine call_std moddi3 ⟨b, 28⟩ σc h4 (cd h4) 0x675150ef#32 0x15e74#21 0x800017b8#64
      (DivRes.of (by omega) (by decide) (by decide)) fun _ M5 _ h5 => ?_
    have hm := Mid.copy hP.va.toShape hP.sc hcp hb28
    have h6 := h5.congrK (κ' := Split.kind (Two.kind pa adp pc cdp a c') (m0 m ra s0 v.s.s1 sp))
      (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl)
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · refine St.seq0 (sz_step v outp sp pc 0 M5 (cd h5)) ?_
      exact tail hP h6 (hm.shape hP.va.toShape hP.sc hroom) hal fun c₄ hcl => hm.post hP.va.toShape hroom (Or.inl rfl) hcl
    · refine St.seq0 (sn_step v outp sp pc b (b % 28) M5 (cd h5) (by omega) (Nat.mod_lt _ (by decide))) ?_
      exact bit hP hm h6 (by omega)
  refine St.seq0 (l_step v outp sp pc b (b / 28) M4 (cd h4) (by omega) hb) ?_
  refine call_std mpLshd ⟨sp - 48, pc, cdp, c', b / 28⟩ σl h4 (cd h4) 0xd55ff0ef#32 0x1ffd54#21 0x80001868#64
    ⟨hq.2, by (try dsimp only); omega, by (try dsimp only); omega, by (try dsimp only); omega,
      by (try dsimp only); omega⟩ fun c'' M5 hl h5 => ?_
  have hm := Mid.lshd (b := b) hP.va.toShape hP.sc hcp hl
  refine St.seq0 (l2_step v outp sp pc b M5 (cd h5)) ?_
  refine call_std moddi3 ⟨b, 28⟩ σc h5 (cd h5) 0x5b5150ef#32 0x15db4#21 0x80001878#64
    (DivRes.of (by omega) (by decide) (by decide)) fun _ M6 _ h6 => ?_
  have h7 := h6.congrK (κ' := Split.kind (Two.kind pa adp pc cdp a c'') (m0 m ra s0 v.s.s1 sp))
    (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl)
  by_cases hd0 : b % 28 = 0
  · refine St.seq0 (lz_step v outp sp pc b M6 (cd h6)) ?_
      (by rw [show BitVec.ofNat 64 0 = BitVec.ofNat 64 (b % 28) by rw [hd0]]; exact rfl)
    exact tail hP h7 (hm.shape hP.va.toShape hP.sc hroom) hm.alloc fun c₄ hcl =>
      hm.post hP.va.toShape hroom (Or.inl hd0) hcl
  · refine St.seq0 (ln_step v outp sp pc b (b % 28) M6 (cd h6) (by omega) (Nat.mod_lt _ (by decide))) ?_
    exact bit hP hm h7 hd0

end Tom.Machine.Fn.MpMul2d
