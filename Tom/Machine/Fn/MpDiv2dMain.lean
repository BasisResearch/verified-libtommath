import Tom.Machine.Api.Std
import Tom.Machine.Api.MpDiv2d
import Tom.Machine.Kit.MeetD

/-!
# `mp_div_2d(a, b, c, NULL)` on the machine: the whole function

The segments of `Tom.Machine.Fn.MpDiv2d` and the contracts of `mp_copy`
(`mpCopy`, or `mpCopyA` in place), `__divdi3`, `mp_rshd`, `__moddi3` and
`mp_clamp` by `call_std` (`Kit/Meet.lean`, `Api/Std.lean`). The regions are
`Two`'s (`correct`) or `Un`'s (`correct_inplace`), the stack cut into our
64-byte frame and the callees' 32 below (`Split`). The paths after the copy
(and `mp_rshd`) meet at `5278` (`bit`, with the `mp_int` as `Mid`); the bit
loop runs from the top digit down (`St.seqOvlD`, `Triple.countdown`); the
paths meet again at `52e0` (`tail`, with the result as `Fin`).
-/


namespace Tom.Machine.Fn.MpDiv2d

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api Tom.Machine.Std

/-! ## The value -/

theorem div2dDigit_zero (a : MpInt) : div2dDigit a 0 = a.digit := by
  funext j; simp [div2dDigit, Layout.digitBits, Nat.mod_one]

theorem div2d_hi {a : MpInt} (ha : a.Shape) {b j : Nat} (hj : a.used ≤ j + b / 28) : div2dDigit a b j = 0 := by
  simp only [div2dDigit, Layout.digitBits, ha.high_zero _ hj, ha.high_zero (j + b / 28 + 1) (by omega)]; simp

theorem copy_digit {a c c' : MpInt} (ha : a.Shape) (hc : c.Shape) (h : CopyPost a c c') : c'.digit = a.digit :=
  funext fun j => by
    rw [h.digit]; split
    · rfl
    · rw [ha.high_zero j (by omega)]; split
      · rfl
      · exact hc.high_zero j (by omega)

theorem copy_self {a : MpInt} (ha : a.Shape) : CopyPost a a a :=
  { alloc := rfl, len := ha.len, used := rfl, sign := rfl
    digit := fun i => by split <;> (try split) <;> first | rfl | omega }

/-- `b = 0`: the copy is the result. -/
theorem div2d_copy {a c c' : MpInt} (ha : a.Valid) (hc : c.Shape) (h : CopyPost a c c') : Div2dPost a 0 c c' :=
  { alloc := h.alloc, len := h.len, digit := by rw [copy_digit ha.toShape hc h, div2dDigit_zero]
    used := by rw [h.used, div2dDigit_zero, Nat.zero_div, Nat.sub_zero, ha.clampUsed_self]
    sign := by rw [h.sign, h.used]; split <;> first | exact ha.zero_pos ‹_› | rfl }

/-- The result handed to `mp_clamp`: `div2dDigit` from `a->used - D`. -/
structure Fin (a c c₃ : MpInt) (b : Nat) : Prop where
  alloc : c₃.alloc = c.alloc
  len : c₃.digits.length = c.alloc
  dig : c₃.digit = div2dDigit a b
  used : c₃.used = a.used - b / 28
  sign : c₃.used ≠ 0 → c₃.sign = a.sign

theorem Fin.shape {a c c₃ : MpInt} {b : Nat} (h : Fin a c c₃ b) (ha : a.Shape) (hc : c.Shape)
    (hroom : a.used ≤ c.alloc) : c₃.Shape :=
  { len := by rw [h.len, h.alloc]
    used_le := by rw [h.used, h.alloc]; omega
    alloc_lt := by rw [h.alloc]; exact hc.alloc_lt
    digit_lt := fun i => by
      rw [h.dig]
      have hd : b % 28 < 28 := Nat.mod_lt _ (by decide)
      exact (div2dDigit_c _ _ _ hd (ha.digit_lt _) (Nat.mod_lt _ (Nat.two_pow_pos _))).2
    high_zero := fun i hi => by rw [h.dig]; exact div2d_hi ha (by rw [h.used] at hi; omega) }

theorem Fin.post {a c c₃ c₄ : MpInt} {b : Nat} (h : Fin a c c₃ b) (hcl : ClampPost c₃ c₄) : Div2dPost a b c c₄ :=
  { alloc := by rw [hcl.alloc, h.alloc]
    len := by rw [hcl.digits, h.len]
    digit := by rw [hcl.digit, h.dig]
    used := by rw [hcl.used, h.dig, h.used]; rfl
    sign := by
      rw [hcl.sign]; split
      · rfl
      · exact h.sign fun h0 => by have := clampUsed_le c₃.digit c₃.used; rw [← hcl.used] at this; omega }

/-- After the copy (and `mp_rshd`): digit `j` is `a[j + D]`. -/
structure Mid (a c c₂ : MpInt) (b : Nat) : Prop where
  dig : ∀ j, c₂.digit j = a.digit (j + b / 28)
  used : c₂.used = a.used - b / 28
  alloc : c₂.alloc = c.alloc
  len : c₂.digits.length = c.alloc
  sign : c₂.used ≠ 0 → c₂.sign = a.sign

theorem Mid.copy {a c c' : MpInt} {b : Nat} (ha : a.Shape) (hc : c.Shape) (h : CopyPost a c c') (hb : b < 28) :
    Mid a c c' b :=
  { dig := fun j => by rw [copy_digit ha hc h, show b / 28 = 0 by omega]; rfl
    used := by rw [h.used, show b / 28 = 0 by omega]; rfl
    alloc := h.alloc, len := h.len, sign := fun _ => h.sign }

theorem Mid.rshd {a c c' c₂ : MpInt} {b : Nat} (ha : a.Shape) (hc : c.Shape) (h : CopyPost a c c')
    (hr : RshdPost c' (b / 28) c₂) : Mid a c c₂ b := by
  have hd := copy_digit ha hc h
  rcases Nat.eq_zero_or_pos (b / 28) with h0 | hk
  · rw [hr.noop h0]
    exact { dig := fun j => by rw [hd, h0]; rfl, used := by rw [h.used, h0]; rfl, alloc := h.alloc, len := h.len
            sign := fun _ => h.sign }
  by_cases hu : c'.used ≤ b / 28
  · have hz := hr.zero hk hu
    rw [h.used] at hu
    exact { dig := fun j => by rw [hz.digit, ha.high_zero _ (by omega)], used := by rw [hz.used]; omega
            alloc := by rw [hz.alloc, h.alloc], len := by rw [hz.len, h.alloc]
            sign := fun h' => absurd hz.used h' }
  · have hs := hr.shift hk (by omega)
    rw [h.used] at hu
    refine { dig := fun j => ?_, used := by rw [hs.used, h.used], alloc := by rw [hs.alloc, h.alloc]
             len := by rw [hs.len, h.alloc], sign := fun _ => by rw [hs.sign, h.sign] }
    rw [hs.digit, h.used, hd]
    split
    · rfl
    · split
      · exact (ha.high_zero _ (by omega)).symm
      · rw [ha.high_zero j (by omega), ha.high_zero _ (by omega)]

theorem Mid.shape {a c c₂ : MpInt} {b : Nat} (h : Mid a c c₂ b) (ha : a.Shape) (hc : c.Shape)
    (hroom : a.used ≤ c.alloc) : c₂.Shape :=
  { len := by rw [h.len, h.alloc]
    used_le := by rw [h.used, h.alloc]; omega
    alloc_lt := by rw [h.alloc]; exact hc.alloc_lt
    digit_lt := fun i => by rw [h.dig]; exact ha.digit_lt _
    high_zero := fun i hi => by rw [h.dig]; exact ha.high_zero _ (by rw [h.used] at hi; omega) }

/-- `b % 28 = 0`: no bit loop. -/
theorem Mid.fin_d0 {a c c₂ : MpInt} {b : Nat} (h : Mid a c c₂ b) (hd0 : b % 28 = 0) : Fin a c c₂ b :=
  { alloc := h.alloc, len := h.len, used := h.used, sign := h.sign
    dig := funext fun j => by simp [div2dDigit, Layout.digitBits, hd0, h.dig, Nat.mod_one] }

/-- `c->used = 0`: no bit loop. -/
theorem Mid.fin_u0 {a c c₂ : MpInt} {b : Nat} (h : Mid a c c₂ b) (ha : a.Shape) (hu0 : c₂.used = 0) :
    Fin a c c₂ b :=
  { alloc := h.alloc, len := h.len, used := h.used, sign := h.sign
    dig := funext fun j => by
      rw [h.dig, div2d_hi ha (by have := h.used; omega), ha.high_zero _ (by have := h.used; omega)] }

/-- The bit loop's digit `x`. -/
def gq (c₂ : MpInt) (d x : Nat) : Nat := c₂.digit x / 2 ^ d + c₂.digit (x + 1) % 2 ^ d * 2 ^ (28 - d)

theorem Mid.gq_eq {a c c₂ : MpInt} {b : Nat} (h : Mid a c c₂ b) (x : Nat) : gq c₂ (b % 28) x = div2dDigit a b x := by
  simp only [gq, div2dDigit, Layout.digitBits, h.dig, Nat.add_right_comm x 1]

/-- The result after the bit loop. -/
def fin (a c₂ : MpInt) (b : Nat) : MpInt := MpInt.ofDigits c₂.used c₂.alloc c₂.sign (div2dDigit a b)

theorem Mid.fin_loop {a c c₂ : MpInt} {b : Nat} (h : Mid a c c₂ b) (ha : a.Shape) (hroom : a.used ≤ c.alloc) :
    Fin a c (fin a c₂ b) b :=
  { alloc := h.alloc, len := by rw [fin, MpInt.ofDigits_len, h.alloc], used := h.used, sign := h.sign
    dig := funext fun j => by
      rw [fin, MpInt.ofDigits_digit]; split
      · rfl
      · exact (div2d_hi ha (by rw [h.alloc] at *; omega)).symm }

theorem Mid.fin_ovl {a c c₂ : MpInt} {b : Nat} (h : Mid a c c₂ b) (ha : a.Shape) (j : Nat) (hj : j < c₂.alloc) :
    (fin a c₂ b).digit j = ovlD (gq c₂ (b % 28)) c₂.digit 0 c₂.used j := by
  rw [fin, MpInt.ofDigits_digit, ite_cond_eq_true _ _ (eq_true hj), ovlD]
  split
  · exact (h.gq_eq j).symm
  · rw [h.dig, div2d_hi ha (by have := h.used; omega), ha.high_zero _ (by have := h.used; omega)]

theorem gq_lt (c₂ : MpInt) (hs : c₂.Shape) {d : Nat} (hd : d < 28) (x : Nat) : gq c₂ d x < 2 ^ 32 :=
  Nat.lt_trans (div2dDigit_c _ _ _ hd (hs.digit_lt _) (Nat.mod_lt _ (Nat.two_pow_pos _))).2 (by decide)

/-! ## The machine (distinct operands) -/

section Dist

open Tom.Machine.Api.Two (R isW)

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

abbrev ρw (sp pa adp pc cdp : Nat) (a c : MpInt) := Split.lay (Two.lay 96 sp pa adp pc cdp a c) R.stk 64

abbrev Wr : List (Option R) := [none, some .stk, some .bS, some .bD]

/-- Our frame after the prologue. -/
abbrev m0 (m : Mem) (ra s0 s1 s2 s3 : BitVec 64) (sp : Nat) : Mem :=
  writeLog (writeLog m (frameLog1 ra s0 s1 sp)) (frameLog2 s2 s3 sp)

theorem cd {sp pa adp pc cdp : Nat} {a c : MpInt} {W : List (Option R)} {κ : Option R → Kind} {m M : Mem}
    (h : St (ρw sp pa adp pc cdp a c) (Split.wr isW) W κ m M)
    (hk : κ (some .code) = .code := by rfl) : CodeAt M mpDiv2dBase mpDiv2dCode := (h.img (some .code) hk).mpDiv2d

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat} {c : MpInt}
  {ra s0 : BitVec 64}

/-- From `52e0`: `mp_clamp(c)`, the epilogue. -/
theorem tail (hP : MpDiv2d.Pre m sp pa adp pc cdp a b c ra) {M : Mem} {c₃ : MpInt}
    (h : St (ρw sp pa adp pc cdp a c) (Split.wr isW) Wr
      (Split.kind (Two.kind pa adp pc cdp a c₃) (m0 m ra s0 v.s.s1 v.s.s2 v.s.s3 sp)) m M)
    (hf : Fin a c c₃ b) :
    Triple (At 0x800052e0#64 (clL sp pa b pc) M (keepD v) outp) (MpDiv2d.Ret m v outp sp pa adp pc cdp a b c ra s0) := by
  have := hP.sp_ge; have := hP.sp_al; have hra := hP.ra_al; have hal := hf.alloc
  refine call_std clamp ⟨pc, cdp, c₃⟩ σz h (cd h) 0xcf9ff0ef#32 0x1ffcf8#21 0x800052e4#64
    (hf.shape hP.va.toShape hP.sc hP.room) fun c₄ M' hcl h' => ?_
  exact (Triple.rmap (fun cf hc => ⟨c₄, M', hc.sub rfl rfl, ⟨(h'.hdr (some .bS) rfl).mpAt (by
      rw [hcl.alloc, hcl.digit]; exact h'.dig (some .bD) rfl), hf.post hcl, h'.unsplit (by simp [Two.lay])⟩⟩)
    (e_step ra s0 v.s.s1 v.s.s2 v.s.s3 v outp sp M' (cd h') (by facts h'))).pre

/-- From `5278` (`dd = b % 28` returned): the bit loop over `c₂`'s digits, then `tail`. -/
theorem bit (hP : MpDiv2d.Pre m sp pa adp pc cdp a b c ra) {M : Mem} {c₂ : MpInt} (hm : Mid a c c₂ b)
    (h : St (ρw sp pa adp pc cdp a c) (Split.wr isW) Wr
      (Split.kind (Two.kind pa adp pc cdp a c₂) (m0 m ra s0 v.s.s1 v.s.s2 v.s.s3 sp)) m M) :
    Triple (At 0x80005278#64 (a0L sp pa b pc (BitVec.ofNat 64 (b % 28))) M (keepD v) outp)
      (MpDiv2d.Ret m v outp sp pa adp pc cdp a b c ra s0) := by
  have := hP.sp_ge; have hroom := hP.room; have := hP.va.used_le; have := hP.sc.alloc_lt
  have hs2 := hm.shape hP.va.toShape hP.sc hroom
  have hd : b % 28 < 28 := Nat.mod_lt _ (by decide)
  have hal := hm.alloc; have := hs2.used_le; have := hs2.alloc_lt
  by_cases hd0 : b % 28 = 0
  · refine St.seq0 (dz_step v outp sp pa b pc M (cd h)) (tail hP h (hm.fin_d0 hd0))
      (by rw [show BitVec.ofNat 64 0 = BitVec.ofNat 64 (b % 28) by rw [hd0]]; exact rfl)
  by_cases hu0 : c₂.used = 0
  · refine St.seq0 (uz_step v outp sp pa b pc (b % 28) cdp M (cd h) (by rw [← hu0]; facts h) (by omega) hd)
      (tail hP h (hm.fin_u0 hP.va.toShape hu0))
  refine St.seq0 (i_step v outp sp pa b pc (b % 28) cdp c₂.used M (cd h) (by facts h) (by omega) (by omega) hd) ?_
  have hz : c₂.digit c₂.used % 2 ^ (b % 28) = 0 := by rw [hs2.high_zero _ (Nat.le_refl _)]; simp
  have h0 : St (ρw sp pa adp pc cdp a c) (Split.wr isW) Wr (Kind.set (Split.kind (Two.kind pa adp pc cdp a c₂)
      (m0 m ra s0 v.s.s1 v.s.s2 v.s.s3 sp)) (some .bD)
        (.mpD cdp c₂.alloc (ovlD (gq c₂ (b % 28)) c₂.digit c₂.used c₂.used))) m M := by
    rw [ovlD_top]; exact h.congrK fun r => by unfold Kind.set; split <;> (try subst_vars) <;> rfl
  refine Triple.lmap (fun cf hc => ⟨M, Nat.pos_of_ne_zero hu0, Nat.le_refl _, h0, by rw [hz]; exact hc⟩)
    (Triple.countdown (P := fun k cf => ∃ M', 0 < k ∧ k ≤ c₂.used ∧ St (ρw sp pa adp pc cdp a c) (Split.wr isW) Wr
      (Kind.set (Split.kind (Two.kind pa adp pc cdp a c₂) (m0 m ra s0 v.s.s1 v.s.s2 v.s.s3 sp)) (some .bD)
        (.mpD cdp c₂.alloc (ovlD (gq c₂ (b % 28)) c₂.digit k c₂.used))) m M' ∧
      At 0x800052bc#64 (lpL sp pa b pc (b % 28) cdp (k - 1) (c₂.digit k % 2 ^ (b % 28))) M' (keepD v) outp cf)
    (fun k cf ⟨M', _, hk, h', hat⟩ => ?_) (fun cf ⟨_, h0, _⟩ => absurd h0 (Nat.lt_irrefl 0)) c₂.used)
  have he : bytesT4 M' (cdp + 4 * k) = BitVec.ofNat 32 (c₂.digit k) := by
    have := (h'.dig (some .bD) rfl).arr k (by omega); simpa [ovlD, show ¬ k + 1 ≤ k by omega] using this
  have hel := hs2.digit_lt k
  rw [Nat.add_sub_cancel] at hat
  rcases k with _ | j
  · refine Triple.rmap (fun _ hq => Or.inl hq) (h'.seqOvlD (some .bD) rfl (lx_step v outp sp pa b pc (b % 28) cdp
      (c₂.digit 0) (c₂.digit (0 + 1) % 2 ^ (b % 28)) M' (cd h') (by facts h') hd (Nat.mod_lt _ (Nat.two_pow_pos _)))
      (by omega) (by omega) (gq_lt c₂ hs2 hd 0) rfl fun M'' h'' => ?_) cf hat
    have h3 := (h''.setMp (some .bS) (some .bD) rfl rfl (fin a c₂ b) rfl rfl rfl rfl
      (hm.fin_ovl hP.va.toShape)).congrK
      (κ' := Split.kind (Two.kind pa adp pc cdp a (fin a c₂ b)) (m0 m ra s0 v.s.s1 v.s.s2 v.s.s3 sp))
      (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl)
    exact tail hP h3 (hm.fin_loop hP.va.toShape hroom)
  · exact (h'.seqOvlD (some .bD) rfl (lp_step v outp sp pa b pc (b % 28) cdp j (c₂.digit (j + 1))
      (c₂.digit (j + 1 + 1) % 2 ^ (b % 28)) M' (cd h') (by facts h') (by omega) hd (Nat.mod_lt _ (Nat.two_pow_pos _)))
      (by omega) (by omega) (gq_lt c₂ hs2 hd _) rfl
      (fun M'' h'' cf' hc' => ⟨cf', Vsa.Machine.Steps.refl _, Or.inr ⟨M'', by omega, by omega,
        by rwa [Kind.set_set] at h'', by rw [Nat.add_sub_cancel]; exact hc'⟩⟩)) cf hat

end

/-- **`mp_div_2d(a, b, c, NULL)` on the machine** (distinct operands). -/
theorem correct : Api.MpDiv2d.Statement := by
  intro m v outp sp pa adp pc cdp a b c ra s0 hP
  have h0 := St.two (f := 64) hP.ra_ hP.ga hP.rc hP.gc hP.rs hP.img hP.lay (by decide)
  have := hP.sp_ge; have := hP.sp_al; have hra := hP.ra_al; have hb := hP.b_lt; have hroom := hP.room
  have := hP.va.used_le; have := hP.va.alloc_lt; have := hP.sc.used_le; have := hP.sc.alloc_lt
  refine Triple.lmap (fun cf h => h.sub (L' := entry1 ra s0 v.s.s1 v.s.s2 v.s.s3 sp pa b pc) (K' := keepD v) rfl rfl) ?_
  rcases Nat.eq_zero_or_pos b with rfl | hb0
  · -- `b = 0`: `mp_copy(a, c)`
    refine h0.seqW none rfl (z_step ra s0 v.s.s1 v.s.s2 v.s.s3 v outp sp pa pc m (cd h0) (by facts h0)) fun M1 h1 => ?_
    refine call_std mpCopy ⟨sp - 64, pa, adp, pc, cdp, a, c⟩ (some : R → Option R) h1 (cd h1) 0xcb4fb0ef#32 0x1fb4b4#21 0x80005330#64
      ⟨hP.va.toShape, hP.sc, hP.va.sign_ok, hroom, by (try dsimp only); omega, by (try dsimp only); omega⟩
      fun c' M2 hq h2 => ?_
    exact (Triple.rmap (fun cf h => ⟨c', M2, h.sub rfl rfl, ⟨h2.mpAt (some .bS) (some .bD) rfl rfl,
      div2d_copy hP.va hP.sc hq.1, h2.unsplit (by simp [Two.lay])⟩⟩)
      (zr_step ra s0 v.s.s1 v.s.s2 v.s.s3 v outp sp pc M2 (cd h2) (by facts h2))).pre
  refine h0.seqW none rfl (p1_step ra s0 v.s.s1 v.s.s2 v.s.s3 v outp sp pa b pc m (cd h0) (by facts h0) hb0 hb)
    fun M1 h1 => ?_
  refine h1.seqW none rfl (p2_step s0 v.s.s2 v.s.s3 v outp sp pa b pc M1 (cd h1) (by facts h1)) fun M2 h2 => ?_
  refine call_std mpCopy ⟨sp - 64, pa, adp, pc, cdp, a, c⟩ (some : R → Option R) h2 (cd h2) 0xda4fb0ef#32 0x1fb5a4#21 0x80005240#64
    ⟨hP.va.toShape, hP.sc, hP.va.sign_ok, hroom, by (try dsimp only); omega, by (try dsimp only); omega⟩
    fun c' M3 hq h3 => ?_
  have hcp : CopyPost a c c' := hq.1; have hal := hcp.alloc
  by_cases hb28 : b < 28
  · refine St.seq0 (s_step v outp sp pa b pc M3 (cd h3) (by facts h3) hb28) ?_
    refine call_std moddi3 ⟨b, 28⟩ σc h3 (cd h3) 0x3b4120ef#32 0x123b4#21 0x80005278#64
      (DivRes.of (by omega) (by decide) (by decide)) fun _ M4 _ h4 => ?_
    exact (bit hP (Mid.copy hP.va.toShape hP.sc hcp hb28) (h4.congrK
      (κ' := Split.kind (Two.kind pa adp pc cdp a c') (m0 m ra s0 v.s.s1 v.s.s2 v.s.s3 sp))
      (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl))).pre
  refine St.seq0 (l_step v outp sp pa b pc M3 (cd h3) (by facts h3) (by omega) hb) ?_
  refine call_std divdi3 ⟨b, 28⟩ σc h3 (cd h3) 0x230120ef#32 0x12230#21 0x80005378#64
    (DivRes.of (by omega) (by decide) (by decide)) fun _ M4 _ h4 => ?_
  refine St.seq0 (r_step v outp sp pa b pc M4 (cd h4) hb) ?_
  refine call_std mpRshd ⟨sp - 64, pc, cdp, c', b / 28⟩ σl h4 (cd h4) 0xa9dfc0ef#32 0x1fca9c#21 0x80005384#64
    ⟨hq.2, by (try dsimp only); omega, by (try dsimp only); omega, by (try dsimp only); omega⟩
    fun c₂ M5 hr h5 => ?_
  refine St.seq0 (r2_step v outp sp pa b pc M5 (cd h5)) ?_
  refine call_std moddi3 ⟨b, 28⟩ σc h5 (cd h5) 0x3b4120ef#32 0x123b4#21 0x80005278#64
    (DivRes.of (by omega) (by decide) (by decide)) fun _ M6 _ h6 => ?_
  exact (bit hP (Mid.rshd hP.va.toShape hP.sc hcp hr) (h6.congrK
    (κ' := Split.kind (Two.kind pa adp pc cdp a c₂) (m0 m ra s0 v.s.s1 v.s.s2 v.s.s3 sp))
    (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl))).pre

end Dist

/-! ## The machine (in place: `mp_div_2d(a, b, a, NULL)`) -/

namespace I

open Tom.Machine.Api.Un (R isW)

def σz : Ob → Option R
  | .S => some .aS
  | .D => some .aD
  | .code => some .code

def σc : Cd → Option R := fun _ => some .code

abbrev ρw (sp pa adp : Nat) (a : MpInt) := Split.lay (Un.lay 96 sp pa adp a) R.stk 64

abbrev Wr : List (Option R) := [none, some .stk, some .aS, some .aD]

theorem cd {sp pa adp : Nat} {a : MpInt} {W : List (Option R)} {κ : Option R → Kind} {m M : Mem}
    (h : St (ρw sp pa adp a) (Split.wr isW) W κ m M)
    (hk : κ (some .code) = .code := by rfl) : CodeAt M mpDiv2dBase mpDiv2dCode := (h.img (some .code) hk).mpDiv2d

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {b : Nat} {ra s0 : BitVec 64}

/-- From `52e0`: `mp_clamp(c)`, the epilogue. -/
theorem tail (hP : MpDiv2d.PreI m sp pa adp a b ra) {M : Mem} {c₃ : MpInt}
    (h : St (ρw sp pa adp a) (Split.wr isW) Wr
      (Split.kind (Un.kind pa adp c₃) (m0 m ra s0 v.s.s1 v.s.s2 v.s.s3 sp)) m M)
    (hf : Fin a a c₃ b) :
    Triple (At 0x800052e0#64 (clL sp pa b pa) M (keepD v) outp) (MpDiv2d.RetI m v outp sp pa adp a b ra s0) := by
  have := hP.sp_ge; have := hP.sp_al; have hra := hP.ra_al; have hal := hf.alloc
  refine call_std clamp ⟨pa, adp, c₃⟩ σz h (cd h) 0xcf9ff0ef#32 0x1ffcf8#21 0x800052e4#64
    (hf.shape hP.va.toShape hP.va.toShape hP.va.used_le) fun c₄ M' hcl h' => ?_
  exact (Triple.rmap (fun cf hc => ⟨c₄, M', hc.sub rfl rfl, ⟨(h'.hdr (some .aS) rfl).mpAt (by
      rw [hcl.alloc, hcl.digit]; exact h'.dig (some .aD) rfl), hf.post hcl, h'.unsplit (by simp [Un.lay])⟩⟩)
    (e_step ra s0 v.s.s1 v.s.s2 v.s.s3 v outp sp M' (cd h') (by facts h'))).pre

/-- From `5278` (`dd = b % 28` returned): the bit loop over `c₂`'s digits, then `tail`. -/
theorem bit (hP : MpDiv2d.PreI m sp pa adp a b ra) {M : Mem} {c₂ : MpInt} (hm : Mid a a c₂ b)
    (h : St (ρw sp pa adp a) (Split.wr isW) Wr
      (Split.kind (Un.kind pa adp c₂) (m0 m ra s0 v.s.s1 v.s.s2 v.s.s3 sp)) m M) :
    Triple (At 0x80005278#64 (a0L sp pa b pa (BitVec.ofNat 64 (b % 28))) M (keepD v) outp)
      (MpDiv2d.RetI m v outp sp pa adp a b ra s0) := by
  have := hP.sp_ge; have hroom := hP.va.used_le; have := hP.va.used_le; have := hP.va.toShape.alloc_lt
  have hs2 := hm.shape hP.va.toShape hP.va.toShape hroom
  have hd : b % 28 < 28 := Nat.mod_lt _ (by decide)
  have hal := hm.alloc; have := hs2.used_le; have := hs2.alloc_lt
  by_cases hd0 : b % 28 = 0
  · refine St.seq0 (dz_step v outp sp pa b pa M (cd h)) (tail hP h (hm.fin_d0 hd0))
      (by rw [show BitVec.ofNat 64 0 = BitVec.ofNat 64 (b % 28) by rw [hd0]]; exact rfl)
  by_cases hu0 : c₂.used = 0
  · refine St.seq0 (uz_step v outp sp pa b pa (b % 28) adp M (cd h) (by rw [← hu0]; facts h) (by omega) hd)
      (tail hP h (hm.fin_u0 hP.va.toShape hu0))
  refine St.seq0 (i_step v outp sp pa b pa (b % 28) adp c₂.used M (cd h) (by facts h) (by omega) (by omega) hd) ?_
  have hz : c₂.digit c₂.used % 2 ^ (b % 28) = 0 := by rw [hs2.high_zero _ (Nat.le_refl _)]; simp
  have h0 : St (ρw sp pa adp a) (Split.wr isW) Wr (Kind.set (Split.kind (Un.kind pa adp c₂)
      (m0 m ra s0 v.s.s1 v.s.s2 v.s.s3 sp)) (some .aD)
        (.mpD adp c₂.alloc (ovlD (gq c₂ (b % 28)) c₂.digit c₂.used c₂.used))) m M := by
    rw [ovlD_top]; exact h.congrK fun r => by unfold Kind.set; split <;> (try subst_vars) <;> rfl
  refine Triple.lmap (fun cf hc => ⟨M, Nat.pos_of_ne_zero hu0, Nat.le_refl _, h0, by rw [hz]; exact hc⟩)
    (Triple.countdown (P := fun k cf => ∃ M', 0 < k ∧ k ≤ c₂.used ∧ St (ρw sp pa adp a) (Split.wr isW) Wr
      (Kind.set (Split.kind (Un.kind pa adp c₂) (m0 m ra s0 v.s.s1 v.s.s2 v.s.s3 sp)) (some .aD)
        (.mpD adp c₂.alloc (ovlD (gq c₂ (b % 28)) c₂.digit k c₂.used))) m M' ∧
      At 0x800052bc#64 (lpL sp pa b pa (b % 28) adp (k - 1) (c₂.digit k % 2 ^ (b % 28))) M' (keepD v) outp cf)
    (fun k cf ⟨M', _, hk, h', hat⟩ => ?_) (fun cf ⟨_, h0, _⟩ => absurd h0 (Nat.lt_irrefl 0)) c₂.used)
  have he : bytesT4 M' (adp + 4 * k) = BitVec.ofNat 32 (c₂.digit k) := by
    have := (h'.dig (some .aD) rfl).arr k (by omega); simpa [ovlD, show ¬ k + 1 ≤ k by omega] using this
  have hel := hs2.digit_lt k
  rw [Nat.add_sub_cancel] at hat
  rcases k with _ | j
  · refine Triple.rmap (fun _ hq => Or.inl hq) (h'.seqOvlD (some .aD) rfl (lx_step v outp sp pa b pa (b % 28) adp
      (c₂.digit 0) (c₂.digit (0 + 1) % 2 ^ (b % 28)) M' (cd h') (by facts h') hd (Nat.mod_lt _ (Nat.two_pow_pos _)))
      (by omega) (by omega) (gq_lt c₂ hs2 hd 0) rfl fun M'' h'' => ?_) cf hat
    have h3 := (h''.setMp (some .aS) (some .aD) rfl rfl (fin a c₂ b) rfl rfl rfl rfl
      (hm.fin_ovl hP.va.toShape)).congrK
      (κ' := Split.kind (Un.kind pa adp (fin a c₂ b)) (m0 m ra s0 v.s.s1 v.s.s2 v.s.s3 sp))
      (by intro r; rcases r with _ | ⟨_ | _ | _ | _⟩ <;> rfl)
    exact tail hP h3 (hm.fin_loop hP.va.toShape hroom)
  · exact (h'.seqOvlD (some .aD) rfl (lp_step v outp sp pa b pa (b % 28) adp j (c₂.digit (j + 1))
      (c₂.digit (j + 1 + 1) % 2 ^ (b % 28)) M' (cd h') (by facts h') (by omega) hd (Nat.mod_lt _ (Nat.two_pow_pos _)))
      (by omega) (by omega) (gq_lt c₂ hs2 hd _) rfl
      (fun M'' h'' cf' hc' => ⟨cf', Vsa.Machine.Steps.refl _, Or.inr ⟨M'', by omega, by omega,
        by rwa [Kind.set_set] at h'', by rw [Nat.add_sub_cancel]; exact hc'⟩⟩)) cf hat

end

end I

open Tom.Machine.Api.Un (R isW) in
/-- **`mp_div_2d(a, b, a, NULL)` on the machine** (in place). -/
theorem correct_inplace : Api.MpDiv2d.StatementInPlace := by
  intro m v outp sp pa adp a b ra s0 hP
  have h0 := St.un (f := 64) hP.ra_ hP.ga hP.rs hP.img hP.lay (by decide)
  have := hP.sp_ge; have := hP.sp_al; have hra := hP.ra_al; have hb := hP.b_lt
  have := hP.va.used_le; have := hP.va.alloc_lt
  have hcp := copy_self hP.va.toShape
  refine Triple.lmap (fun cf h => h.sub (L' := entry1 ra s0 v.s.s1 v.s.s2 v.s.s3 sp pa b pa) (K' := keepD v) rfl rfl) ?_
  rcases Nat.eq_zero_or_pos b with rfl | hb0
  · -- `b = 0`: `mp_copy(a, a)`
    refine h0.seqW none rfl (z_step ra s0 v.s.s1 v.s.s2 v.s.s3 v outp sp pa pa m (I.cd h0) (by facts h0))
      fun M1 h1 => ?_
    refine call_std mpCopyA ⟨sp - 64, pa⟩ I.σc h1 (I.cd h1) 0xcb4fb0ef#32 0x1fb4b4#21 0x80005330#64 trivial
      fun _ M2 _ h2 => ?_
    exact (Triple.rmap (fun cf h => ⟨a, M2, h.sub rfl rfl, ⟨h2.mpAt (some .aS) (some .aD) rfl rfl,
      div2d_copy hP.va hP.va.toShape hcp, h2.unsplit (by simp [Un.lay])⟩⟩)
      (zr_step ra s0 v.s.s1 v.s.s2 v.s.s3 v outp sp pa M2 (I.cd h2) (by facts h2))).pre
  refine h0.seqW none rfl (p1_step ra s0 v.s.s1 v.s.s2 v.s.s3 v outp sp pa b pa m (I.cd h0) (by facts h0) hb0 hb)
    fun M1 h1 => ?_
  refine h1.seqW none rfl (p2_step s0 v.s.s2 v.s.s3 v outp sp pa b pa M1 (I.cd h1) (by facts h1)) fun M2 h2 => ?_
  refine call_std mpCopyA ⟨sp - 64, pa⟩ I.σc h2 (I.cd h2) 0xda4fb0ef#32 0x1fb5a4#21 0x80005240#64 trivial
    fun _ M3 _ h3 => ?_
  by_cases hb28 : b < 28
  · refine St.seq0 (s_step v outp sp pa b pa M3 (I.cd h3) (by facts h3) hb28) ?_
    refine call_std moddi3 ⟨b, 28⟩ I.σc h3 (I.cd h3) 0x3b4120ef#32 0x123b4#21 0x80005278#64
      (DivRes.of (by omega) (by decide) (by decide)) fun _ M4 _ h4 => ?_
    exact (I.bit hP (Mid.copy hP.va.toShape hP.va.toShape hcp hb28) (h4.congrK
      (κ' := Split.kind (Un.kind pa adp a) (m0 m ra s0 v.s.s1 v.s.s2 v.s.s3 sp))
      (by intro r; rcases r with _ | ⟨_ | _ | _ | _⟩ <;> rfl))).pre
  refine St.seq0 (l_step v outp sp pa b pa M3 (I.cd h3) (by facts h3) (by omega) hb) ?_
  refine call_std divdi3 ⟨b, 28⟩ I.σc h3 (I.cd h3) 0x230120ef#32 0x12230#21 0x80005378#64
    (DivRes.of (by omega) (by decide) (by decide)) fun _ M4 _ h4 => ?_
  refine St.seq0 (r_step v outp sp pa b pa M4 (I.cd h4) hb) ?_
  refine call_std mpRshd ⟨sp - 64, pa, adp, a, b / 28⟩ (some : R → Option R) h4 (I.cd h4) 0xa9dfc0ef#32 0x1fca9c#21
    0x80005384#64 ⟨hP.va.toShape, by (try dsimp only); omega, by (try dsimp only); omega, by (try dsimp only); omega⟩
    fun c₂ M5 hr h5 => ?_
  refine St.seq0 (r2_step v outp sp pa b pa M5 (I.cd h5)) ?_
  refine call_std moddi3 ⟨b, 28⟩ I.σc h5 (I.cd h5) 0x3b4120ef#32 0x123b4#21 0x80005278#64
    (DivRes.of (by omega) (by decide) (by decide)) fun _ M6 _ h6 => ?_
  exact (I.bit hP (Mid.rshd hP.va.toShape hP.va.toShape hcp hr) (h6.congrK
    (κ' := Split.kind (Un.kind pa adp c₂) (m0 m ra s0 v.s.s1 v.s.s2 v.s.s3 sp))
    (by intro r; rcases r with _ | ⟨_ | _ | _ | _⟩ <;> rfl))).pre

end Tom.Machine.Fn.MpDiv2d
