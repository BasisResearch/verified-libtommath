import Tom.Machine.Api.StdNorm
import Tom.Machine.Api.MontNorm

/-!
# `mp_montgomery_calc_normalization` on the machine: the whole function

The segments of `Tom.Machine.Fn.MontNorm` and the contracts of `mp_count_bits`,
`__moddi3`, `mp_2expt`, `mp_set`, `mp_mul_2(a, a)`, `mp_cmp_mag` and
`s_mp_sub(a, b, a)` by `call_std` (`Kit/Meet.lean`, `Api/StdNorm.lean`). Regions are
`BinA`'s (`isWA`: `a` written, `b` read), the stack cut into our 64-byte frame and
the callees' 48 below (`Split`). Both starts (`mp_2expt`, `mp_set`) reach the loop
head `5930` with the frame saved; each pass (`body`) is `mp_mul_2`, `mp_cmp_mag` and,
unless `MP_LT`, `s_mp_sub`, carrying `NI` (the value after `j` passes of
`Mont.normLoop`); the loop is `Triple.countup_from` over the passes.
-/


namespace Tom.Machine.Fn.MontNorm

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api Tom.Machine.Std
open Tom.Machine.Api.BinA (R isWA)
open Tom.Mont

/-! ## The value -/

theorem normLoop_succ (b : Nat) : ∀ j x, normLoop b x (j + 1) = normStep b (normLoop b x j)
  | 0, _ => rfl
  | j + 1, x => by
    show normLoop b (normStep b x) (j + 1) = _
    rw [normLoop_succ b j (normStep b x)]; rfl

/-- The value after `j` passes. -/
structure NI (a b ai : MpInt) (j : Nat) : Prop where
  valid : ai.Valid
  mag : ai.mag = normLoop b.mag (2 ^ normE0 b) j
  sign : ai.sign = Layout.mpZpos
  alloc : ai.alloc = a.alloc
  lt : ai.mag < b.mag

theorem NI.room {a b ai : MpInt} {j : Nat} (h : NI a b ai j) (hb : b.Valid) (hroom : b.used + 1 ≤ a.alloc) :
    ai.used + 1 ≤ ai.alloc := by
  have := MpInt.used_le_of_mag_le hb.toShape h.valid (Nat.le_of_lt h.lt); rw [h.alloc]; omega

/-- `MP_LT` after the doubling: the pass keeps `2 ai`. -/
theorem NI.step_lt {a b ai a1 : MpInt} {j : Nat} (h : NI a b ai j) (hv : a1.Valid) (hm : a1.mag = 2 * ai.mag)
    (hs : a1.sign = ai.sign) (hal : a1.alloc = ai.alloc) (hlt : a1.mag < b.mag) : NI a b a1 (j + 1) :=
  { valid := hv, sign := by rw [hs, h.sign], alloc := by rw [hal, h.alloc], lt := hlt
    mag := by rw [normLoop_succ, ← h.mag, normStep, if_neg (by omega), hm] }

/-- Not `MP_LT`: the pass subtracts `b`. -/
theorem NI.step_ge {a b ai a1 a2 : MpInt} {j : Nat} (h : NI a b ai j) (hb : b.Valid) (hv : a1.Valid)
    (hm : a1.mag = 2 * ai.mag) (hs : a1.sign = ai.sign) (hal : a1.alloc = ai.alloc) (hge : b.mag ≤ a1.mag)
    (hsub : SSubPost a1 b a1 a2) : NI a b a2 (j + 1) := by
  have hsg : a1.sign = Layout.mpZpos := by rw [hs, h.sign]
  obtain ⟨hv2, hm2⟩ := SSubPost.spec hv.toShape hb.toShape hge hv.used_le hv.alloc_lt (Or.inl hsg) hsub
  exact { valid := hv2, alloc := by rw [hsub.alloc, hal, h.alloc], lt := by have := h.lt; omega
          sign := by rw [hsub.sign, hsg]; split <;> rfl
          mag := by rw [normLoop_succ, ← h.mag, normStep, if_pos (by omega), hm2, hm] }

theorem nbits_eq (q : Nat) : nbits q = bitLen q := rfl

/-! ## The machine -/

def σcb : Ob → Option R
  | .S => some .bS
  | .D => some .bD
  | .code => some .code

def σs : Ob → Option R
  | .S => some .aS
  | .D => some .aD
  | .code => some .code

def σc : Cd → Option R := fun _ => some .code

def σu : Un.R → Option R
  | .stk => some .stk
  | .aS => some .aS
  | .aD => some .aD
  | .code => some .code

def σab : Ab → Option R
  | .aS => some .aS
  | .aD => some .aD
  | .bS => some .bS
  | .bD => some .bD
  | .code => some .code

abbrev ρw (sp pa adp pb bdp : Nat) (a b : MpInt) := Split.lay (BinA.lay 112 sp pa adp pb bdp a b) R.stk 64

abbrev Wr : List (Option R) := [none, some .stk, some .aS, some .aD]

/-- Our frame after both saves. -/
abbrev m0 (m : Mem) (ra s0 : BitVec 64) (w : Sv) (sp : Nat) : Mem :=
  writeLog (writeLog m (frameLog1 ra s0 w sp)) (frameLog2 w sp)

theorem cd {sp pa adp pb bdp : Nat} {a b : MpInt} {W : List (Option R)} {κ : Option R → Kind} {m M : Mem}
    (h : St (ρw sp pa adp pb bdp a b) (Split.wr isWA) W κ m M)
    (hk : κ (some .code) = .code := by rfl) :
    CodeAt M mpMontgomeryCalcNormalizationBase mpMontgomeryCalcNormalizationCode :=
  (h.img (some .code) hk).mpMontgomeryCalcNormalization

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64}
  {w : Sv}

/-- One pass from the loop head (`5930`) to `596c`. -/
theorem body (hP : MontNorm.Pre m sp pa adp pb bdp a b ra) {M : Mem} {ai : MpInt} {j k : Nat} {s1 : BitVec 64}
    (hni : NI a b ai j)
    (h : St (ρw sp pa adp pb bdp a b) (Split.wr isWA) Wr (Split.kind (BinA.kind pa adp pb bdp ai b) (m0 m ra s0 w sp)) m M)
    {Q : Vsa.Machine.Config → Prop}
    (kont : ∀ a2 M', NI a b a2 (j + 1) → St (ρw sp pa adp pb bdp a b) (Split.wr isWA) Wr
      (Split.kind (BinA.kind pa adp pb bdp a2 b) (m0 m ra s0 w sp)) m M' →
      Triple (At 0x8000596c#64 (jnL sp pa pb k) M' (keepN v) outp) Q) :
    Triple (At 0x80005930#64 (hdL s1 sp pa pb k) M (keepN v) outp) Q := by
  have := hP.sp_ge; have := hP.sp_al; have hroom := hP.room; have hal := hni.alloc
  have hr := hni.room hP.vb hroom
  refine St.seq0 (l1_step s1 v outp sp pa pb k M (cd h)) ?_
  refine call_std mul2I ⟨sp - 64, pa, adp, ai⟩ σu h (cd h) 0x368000ef#32 0x368#21 0x8000593c#64
    ⟨hni.valid, hr, by (try dsimp only); omega, by (try dsimp only); omega⟩ fun a1 M1 hm h1 => ?_
  obtain ⟨hv1, hm1, _⟩ := Mul2Post.spec hni.valid hr hni.valid.alloc_lt hm
  have hal1 : a1.alloc = ai.alloc := hm.alloc
  refine St.seq0 (l2_step v outp sp pa pb k M1 (cd h1)) ?_
  refine call_std Std.cmpMagN ⟨pa, adp, pb, bdp, a1, b⟩ σab h1 (cd h1) 0xe19fa0ef#32 0x1fae18#21 0x80005950#64
    ⟨hv1, hP.vb⟩ fun _ M2 _ h2 => ?_
  have h2' := h2.congrK (κ' := Split.kind (BinA.kind pa adp pb bdp a1 b) (m0 m ra s0 w sp))
    (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl)
  have sub : ∀ c, c ≤ 1 → b.mag ≤ a1.mag →
      Triple (At 0x80005950#64 (crL sp pa pb k (BitVec.ofNat 64 c)) M2 (keepN v) outp) Q := fun c hc hge => by
    have hu := MpInt.used_le_of_mag_le hv1.toShape hP.vb hge
    refine St.seq0 (ge_step v outp sp pa pb k c M2 (cd h2') hc) ?_
    refine call_std sSubA ⟨sp - 64, pa, adp, pb, bdp, a1, b⟩ (some : R → Option R) h2' (cd h2') 0xc01fe0ef#32
      0x1fec00#21 0x80005968#64 ⟨hv1.toShape, hP.vb.toShape, Or.inl (by rw [hm.sign, hni.sign]), hu,
        by (try dsimp only); omega, by (try dsimp only); omega⟩ fun a2 M3 hs h3 => ?_
    refine St.seq0 (l4_step v outp sp pa pb k M3 (cd h3)) ?_
    exact kont a2 M3 (hni.step_ge hP.vb hv1 hm1 hm.sign hal1 hge hs) (h3.congrK
      (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl))
  rcases hc : compare a1.mag b.mag with _ | _ | _
  · have hlt : a1.mag < b.mag := Nat.compare_eq_lt.1 hc
    have e : Std.cmpMagN.rets ⟨pa, adp, pb, bdp, a1, b⟩ 0x80005950#64 = [(1, 0x80005950#64), (10, 18446744073709551615#64)] := by
      show [(1, _), (10, BitVec.ofInt 64 (ordCode (compare a1.mag b.mag)))] = _; rw [hc]; rfl
    rw [e]
    refine St.seq0 (lt_step v outp sp pa pb k M2 (cd h2')) ?_
    exact kont a1 M2 (hni.step_lt hv1 hm1 hm.sign hal1 hlt) h2'
  · have e : Std.cmpMagN.rets ⟨pa, adp, pb, bdp, a1, b⟩ 0x80005950#64 = [(1, 0x80005950#64), (10, BitVec.ofNat 64 0)] := by
      show [(1, _), (10, BitVec.ofInt 64 (ordCode (compare a1.mag b.mag)))] = _; rw [hc]; rfl
    rw [e]
    exact (sub 0 (by omega) (Nat.le_of_eq (Nat.compare_eq_eq.1 hc).symm)).pre
  · have e : Std.cmpMagN.rets ⟨pa, adp, pb, bdp, a1, b⟩ 0x80005950#64 = [(1, 0x80005950#64), (10, BitVec.ofNat 64 1)] := by
      show [(1, _), (10, BitVec.ofInt 64 (ordCode (compare a1.mag b.mag)))] = _; rw [hc]; rfl
    rw [e]
    exact (sub 1 (by omega) (Nat.le_of_lt (Nat.compare_eq_gt.1 hc))).pre

/-- The loop from the head with `x = k0 - 1`, `cnt = 29 - k0` passes. -/
theorem loop (hP : MontNorm.Pre m sp pa adp pb bdp a b ra) {M : Mem} {a1 : MpInt} {k0 cnt : Nat} {s1 : BitVec 64}
    (hk : k0 + cnt = 29) (hc : 1 ≤ cnt) (hni : NI a b a1 0) (hw : w = ⟨v.s.s1, v.s.s2, v.s.s3, v.s.s4, v.s.s5⟩)
    (h : St (ρw sp pa adp pb bdp a b) (Split.wr isWA) Wr (Split.kind (BinA.kind pa adp pb bdp a1 b) (m0 m ra s0 w sp)) m M) :
    Triple (At 0x80005930#64 (hdL s1 sp pa pb k0) M (keepN v) outp)
      (fun cf => ∃ a' M', At ra (ret1 ra s0 w sp) M' (keepN v) outp cf ∧ NI a b a' cnt ∧
        St (ρw sp pa adp pb bdp a b) (Split.wr isWA) Wr (Split.kind (BinA.kind pa adp pb bdp a' b) (m0 m ra s0 w sp)) m M') := by
  have := hP.sp_ge; have hra := hP.ra_al
  refine Triple.lmap (fun cf hc' => ⟨a1, M, s1, hni, h, by rw [Nat.add_zero]; exact hc'⟩) (Triple.countup_from (lo := 0) (n := cnt)
    (P := fun i cf => ∃ ai M' s1', NI a b ai i ∧ St (ρw sp pa adp pb bdp a b) (Split.wr isWA) Wr
      (Split.kind (BinA.kind pa adp pb bdp ai b) (m0 m ra s0 w sp)) m M' ∧
      At 0x80005930#64 (hdL s1' sp pa pb (k0 + i)) M' (keepN v) outp cf)
    (fun i _ hi cf ⟨ai, M', s1', hn, h', hat⟩ => ?_) ?_ 0 (Nat.le_refl _) (by omega))
  · exact body hP hn h' (fun a2 M'' hn' h'' => St.seq0 (n_step v outp sp pa pb (k0 + i) M'' (cd h'') (by omega))
      (fun cf' hc' => ⟨cf', Vsa.Machine.Steps.refl _, a2, M'', 0#64, hn', h'', by rw [← Nat.add_assoc]; exact hc'⟩)) cf hat
  · intro cf ⟨ai, M', s1', hn, h', hat⟩
    rw [show k0 + (cnt - 1) = 28 by omega] at hat
    refine body hP hn h' (fun a2 M'' hn' h'' => ?_) cf hat
    subst hw
    exact Triple.rmap (fun cf' hc' => ⟨a2, M'', hc', by rw [show cnt - 1 + 1 = cnt by omega] at hn'; exact hn', h''⟩)
      (x_step ra s0 ⟨v.s.s1, v.s.s2, v.s.s3, v.s.s4, v.s.s5⟩ v outp sp pa pb M'' (cd h'') (by facts h''))

end

/-- **`mp_montgomery_calc_normalization` on the machine.** -/
theorem correct : Api.MontNorm.Statement := by
  intro m v outp sp pa adp pb bdp a b ra s0 hP
  have h0 := St.binA (f := 64) hP.ra_ hP.ga hP.rb hP.gb hP.rs hP.img hP.lay (by decide)
  have := hP.sp_ge; have := hP.sp_al; have hra := hP.ra_al; have hroom := hP.room
  have hbits : 28 * b.used < 2 ^ 31 := hP.bits
  have := hP.vb.used_le; have := hP.sa.alloc_lt; have := hP.vb.alloc_lt
  have hcb := countBits_le hP.vb.toShape; simp only [Layout.digitBits] at hcb
  have hcs := countBits_spec hP.vb
  let w : Sv := ⟨v.s.s1, v.s.s2, v.s.s3, v.s.s4, v.s.s5⟩
  refine Triple.lmap (fun cf h => h.sub (L' := entry1 ra s0 w sp pa pb) (K' := keepN v) rfl rfl) ?_
  have fin : ∀ {k0 cnt M a1 s1}, k0 + cnt = 29 → 1 ≤ cnt → cnt = normCnt b → NI a b a1 0 →
      St (ρw sp pa adp pb bdp a b) (Split.wr isWA) Wr (Split.kind (BinA.kind pa adp pb bdp a1 b) (m0 m ra s0 w sp)) m M →
      Triple (At 0x80005930#64 (hdL s1 sp pa pb k0) M (keepN v) outp) (MontNorm.Ret m v outp sp pa adp pb bdp a b ra s0) :=
    fun hk hc hn hni h => Triple.rmap (fun cf ⟨a', M', hat, hn', h'⟩ => ⟨a', M', hat.sub rfl rfl,
      { repr := h'.mpAt (some .aS) (some .aD) rfl rfl, norm := ⟨hn'.valid, by rw [hn'.mag, hn], hn'.sign⟩
        alloc := hn'.alloc, frame := h'.unsplit (by simp [BinA.lay]) }⟩) (loop hP hk hc hni rfl h)
  refine h0.seqW none rfl (p_step ra s0 w v outp sp pa pb m (cd h0) (by facts h0)) fun M1 h1 => ?_
  refine call_std cntBits ⟨pb, bdp, b⟩ σcb h1 (cd h1) 0x819ff0ef#32 0x1ff818#21 0x800058dc#64 ⟨hP.vb, hP.bits⟩
    fun _ M2 _ h2 => ?_
  by_cases hu : 1 < b.used
  · refine St.seq0 (ua_step w v outp sp pa pb b.used (countBits b) M2 (cd h2) (by facts h2) hu) ?_
    refine call_std moddi3 ⟨countBits b, 28⟩ σc h2 (cd h2) 0x53d110ef#32 0x11d3c#21 0x800058f0#64
      (DivRes.of (by omega) (by decide) (by decide)) fun _ M3 _ h3 => ?_
    have hb28 : countBits b % 28 < 28 := Nat.mod_lt _ (by decide)
    refine St.seq0 (a2_step w v outp sp pa pb b.used (countBits b % 28) M3 (cd h3) hu hbits hb28) ?_
    have he : 28 * (b.used - 1) + countBits b % 28 - 1 = normE0 b := by
      simp only [normE0, if_pos hu, hcs, ← nbits_eq, Layout.digitBits, Nat.mul_comm 28]
    have hE := normE0_lt b hP.vb hP.odd hP.gt1
    refine call_std mp2expt ⟨sp - 64, pa, adp, a, 28 * (b.used - 1) + countBits b % 28 - 1⟩ σu h3 (cd h3)
      0x5c5010ef#32 0x1dc4#21 0x80005914#64 ⟨hP.sa, by (try dsimp only); omega,
        by (try dsimp only); simp only [Layout.digitBits]; omega, by (try dsimp only); omega,
        by (try dsimp only); omega⟩ fun a1 M4 he2 h4 => ?_
    obtain ⟨hv1, hm1, _⟩ := Expt2Post.spec (by simp only [Layout.digitBits]; omega) hP.sa.alloc_lt he2
    refine h4.seqW none rfl (a3_step w v outp sp pa pb (countBits b % 28) M4 (cd h4) (by facts h4) hb28)
      fun M5 h5 => ?_
    refine fin (k0 := countBits b % 28) (cnt := 29 - countBits b % 28) (by omega) (by omega) ?_ ⟨hv1, by rw [hm1, he]; rfl, he2.sign, he2.alloc, by rw [hm1, he]; exact hE⟩
      (h5.congrK (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl))
    simp only [normCnt, if_pos hu, Layout.digitBits]; rw [nbits_eq, ← hcs]
  · refine h2.seqW none rfl (ub_step w v outp sp pa pb b.used (countBits b) M2 (cd h2) (by facts h2) (by facts h2)
      (by omega)) fun M3 h3 => ?_
    refine call_std mpSet ⟨pa, adp, a, 1⟩ σs h3 (cd h3) 0xd04fc0ef#32 0x1fc504#21 0x800059b0#64
      ⟨hP.sa, by (try dsimp only); omega⟩ fun a1 M4 hs h4 => ?_
    obtain ⟨hv1, hm1, _⟩ := SetPost.spec hP.sa (by omega) (Nat.mod_lt _ radix_pos) hs
    have hE := normE0_lt b hP.vb hP.odd hP.gt1
    have h0e : normE0 b = 0 := by simp only [normE0, if_neg hu]
    refine St.seq0 (b2_step (BitVec.ofNat 64 b.used) v outp sp pa pb M4 (cd h4)) ?_
    refine fin (k0 := 1) (cnt := 28) (by omega) (by omega) (by simp only [normCnt, if_neg hu]; rfl)
      ⟨hv1, by rw [hm1, h0e]; rfl, hs.sign, hs.alloc, by rw [hm1]; rw [h0e] at hE; exact hE⟩
      (h4.congrK (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl))

end Tom.Machine.Fn.MontNorm
