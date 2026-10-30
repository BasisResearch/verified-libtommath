import Tom.Machine.Api.Div3
import Tom.Machine.Fn.Div3Loop

/-!
# `s_mp_div_3` on the machine: the whole function (over `Kit/MeetHeap.lean`)

Regions: the contract's (`Api.Div3.R`), the stack cut three times (`Split`):
our saved registers `fB = [sp - 32, sp)`, the temporary `q`'s struct
`qS = [sp - 56, sp - 32)`, the spill `fA = [sp - 80, sp - 56)` and the callees'
area below; plus the allocation site `nS` (`Site`: `Iv.nil` until
`mp_init_size` places `q`'s digits there). The heap checkpoint at the entry
(`HP.entry`); `mp_init_size` and `mp_clear` by `call_heap`, `mp_clamp` and
`mp_exch` by `call_std`; the digit loop `Fn/Div3Loop.lean`; the end by `HP.fin`.
-/


namespace Tom.Machine.Fn.Div3

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api Tom.Machine.Std Tom.Machine.Api.Alloc
open Tom.Machine.Api.Heap
open Tom.Machine.Api.Div3 (R P lay kind isW ws Res)

instance : Names R := ⟨[.stk, .aS, .aD, .cS, .cD, .dS, .code]⟩

abbrev Y := Option (Option (Option R))
abbrev X := Option Y

/-- The contract's layout with the stack cut into `fB`, `qS`, `fA` and the callees' area. -/
def ρ3 (p : P) : Y → Iv := Split.lay (Split.lay (Split.lay (lay p) .stk 32) (some .stk) 24) (some (some .stk)) 24
def w3 : Y → Bool := Split.wr (Split.wr (Split.wr isW))
def κ3 (p : P) (m : Mem) : Y → Kind := Split.kind (Split.kind (Split.kind (kind p) m) m) m

abbrev nS : X := none
abbrev nA : X := some none
abbrev nQ : X := some (some none)
abbrev nB : X := some (some (some none))
abbrev nR (r : R) : X := some (some (some (some r)))
abbrev WX : List X := [nS, nA, nQ, nB, nR .stk, nR .cS, nR .cD, nR .dS]

/-- The contract region a piece lies in. -/
def proj : Y → R
  | none | some none | some (some none) => .stk
  | some (some (some r)) => r

theorem cd {ρ : X → Iv} {W : List X} {κ : X → Kind} {m M : Mem} (h : St ρ (Site.wr w3) W κ m M)
    (hk : κ (nR .code) = .code := by rfl) : CodeAt M sMpDiv3Base sMpDiv3Code := (h.img (nR .code) hk).sMpDiv3

section Entry
variable {p : P}

theorem sub3 (hF : 656 ≤ p.sp) (y : Y) : (ρ3 p y).Sub (lay p (proj y)) := by
  have eF : Api.Div3.F = 656 := rfl
  rcases y with _ | _ | _ | r
  · simp [ρ3, Split.lay, lay, proj, Iv.Sub, eF]
  · simp [ρ3, Split.lay, lay, proj, Iv.Sub, eF]
  · simp [ρ3, Split.lay, lay, proj, Iv.Sub, eF]
  · cases r <;> simp [ρ3, Split.lay, lay, proj, Iv.Sub, eF] <;> omega

theorem pos3 (hres : Res p) (y : Y) : 0 < (ρ3 p y).len ∨ (ρ3 p y).base < heapStart ∨ heapEnd ≤ (ρ3 p y).base := by
  have eF : Api.Div3.F = 656 := rfl
  have := hres.apos; have := hres.cpos
  rcases y with _ | _ | _ | r
  · left; simp [ρ3, Split.lay, lay, eF]
  · left; simp [ρ3, Split.lay, lay, eF]
  · left; simp [ρ3, Split.lay, lay, eF]
  · cases r
    · left; simp [ρ3, Split.lay, lay, eF]
    · left; simp [ρ3, Split.lay, lay]
    · left; simp [ρ3, Split.lay, lay]; omega
    · left; simp [ρ3, Split.lay, lay]
    · left; simp [ρ3, Split.lay, lay]; omega
    · cases hd : p.hasD
      · right; left; simp [ρ3, Split.lay, lay, hd, Api.Div3.dI, Iv.nil]; decide
      · left; simp [ρ3, Split.lay, lay, hd, Api.Div3.dI]
    · left; simp [ρ3, Split.lay, lay, textIv, textLen]

end Entry

/-- The layout with the stack cut and the site. -/
abbrev ρX (p : P) : X → Iv := Site.lay (ρ3 p)
abbrev wX : X → Bool := Site.wr w3
abbrev κX (p : P) (m : Mem) : X → Kind := Site.kind (κ3 p m)

/-- The entry state and the heap checkpoint. -/
theorem entry_state {p : P} {m : Mem} (hres : Res p) (hS : Sound (lay p) isW) (hB : Bundle (lay p) (kind p) m)
    (hH : AHeap m (Api.Div3.hin p)) (hoff : ∀ r, Off (lay p r) (Api.Div3.hin p)) :
    St (ρX p) wX WX (κX p m) m m ∧
      HP (ρX p) wX (Api.Div3.hin p) (Api.Div3.hin p) (InAny (lay p) ws) m m := by
  have hF : 656 ≤ p.sp := by have := hres.stk.lo; have e : heapEnd = 0x87800000 := rfl; omega
  have eF : Api.Div3.F = 656 := rfl
  have h1 : 32 ≤ (lay p .stk).len := by simp [lay, eF]
  have h2 : 24 ≤ (Split.lay (lay p) .stk 32 (some .stk)).len := by simp [Split.lay, lay, eF]
  have h3 : 24 ≤ (Split.lay (Split.lay (lay p) .stk 32) (some .stk) 24 (some (some .stk))).len := by
    simp [Split.lay, lay, eF]
  have offY : ∀ y, Off (ρ3 p y) (Api.Div3.hin p) := fun y => (hoff (proj y)).sub (sub3 hF y) (pos3 hres y)
  have S3 : Sound (ρ3 p) w3 := Split.sound (Split.sound (Split.sound hS rfl h1) rfl h2) rfl h3
  have B3 : Bundle (ρ3 p) (κ3 p m) m := Split.bundle (Split.bundle (Split.bundle hB rfl h1) rfl h2) rfl h3
  refine ⟨⟨Site.sound S3 fun y => (offY y).lo, Site.bundle B3, Frm.refl _ _⟩, HP.entry hH ?_ ?_ ?_⟩
  · intro x; cases x with
    | none => exact Off.nil _
    | some y => exact offY y
  · intro x hx a ha
    cases x with
    | none => simp [Site.lay, Iv.nil, Iv.In] at ha; omega
    | some y =>
      have hs := sub3 hF y
      have ha' : (lay p (proj y)).In a := by unfold Iv.Sub Iv.In at *; simp only [Site.lay] at ha; omega
      rcases y with _ | _ | _ | r
      · exact InAny.of_mem (w := R.stk) (by decide) ha'
      · exact InAny.of_mem (w := R.stk) (by decide) ha'
      · exact InAny.of_mem (w := R.stk) (by decide) ha'
      · cases r <;> simp [wX, Site.wr, w3, Split.wr, isW] at hx <;>
          exact InAny.of_mem (by decide) ha'
  · intro x hx
    cases x with
    | none => exact Ram.nil
    | some y =>
      have hs := sub3 hF y
      have hstk : Ram (lay p .stk).base (lay p .stk).len := (hB .stk).2
      rcases y with _ | _ | _ | r
      · exact Ram.sub hstk hs.1 hs.2
      · exact Ram.sub hstk hs.1 hs.2
      · exact Ram.sub hstk hs.1 hs.2
      · cases r <;> simp [wX, Site.wr, w3, Split.wr, isW] at hx
        · exact Ram.sub hstk hs.1 hs.2
        · simpa [Site.lay, ρ3, Split.lay, lay, Layout.sizeofMpInt] using (Hdr.geom (hB .cS).2).st
        · simpa [Site.lay, ρ3, Split.lay, lay] using (show Dig m p.cdp p.c.alloc p.c.digit from (hB .cD).2).ram
        · simpa [Site.lay, ρ3, Split.lay, lay] using (show Ram (lay p .dS).base (lay p .dS).len from (hB .dS).2)

/-- The layout with the site at `sI` and `c`'s digits at `cI`. -/
def ρC (p : P) (sI cI : Iv) : X → Iv
  | none => sI
  | some (some (some (some .cD))) => cI
  | some y => ρ3 p y

/-- The kinds: own frame `fA`/`fB` as stored, `q`'s struct `kq`, the site `kS`,
`c`'s struct/digits `kcS`/`kcD`, `*d`'s `kdS`, the rest the contract's. -/
def κC (p : P) (fA fB : Mem) (kq kS kcS kcD kdS : Kind) : X → Kind
  | none => kS
  | some none => .frz fA
  | some (some none) => kq
  | some (some (some none)) => .frz fB
  | some (some (some (some .cS))) => kcS
  | some (some (some (some .cD))) => kcD
  | some (some (some (some .dS))) => kdS
  | some (some (some (some r))) => kind p r

/-- The quotient before `mp_clamp`. -/
def q1 (a : MpInt) : MpInt := MpInt.ofDigits a.used (initPrec a.used) a.sign (qd a.digit a.used 0)

theorem q1_shape {a : MpInt} (ha : a.Shape) : (q1 a).Shape :=
  { len := MpInt.ofDigits_len _ _ _ _
    used_le := by simp only [q1, MpInt.ofDigits, initPrec, minPrec_eq]; omega
    alloc_lt := by have := ha.used_le; have := ha.alloc_lt; simp only [q1, MpInt.ofDigits, initPrec, minPrec_eq]; omega
    digit_lt := fun i => by
      simp only [q1, MpInt.ofDigits_digit, qd]
      split
      · split
        · exact Tom.ldQ_lt _ (by decide) _ _ (ha.digit_lt _)
        · exact Tom.radix_pos
      · exact Tom.radix_pos
    high_zero := fun i hi => by
      simp only [q1, MpInt.ofDigits] at hi
      simp only [q1, MpInt.ofDigits_digit, qd]; split
      · rw [if_neg (by omega)]
      · rfl }

theorem q1_quot {a q2 : MpInt} (h : ClampPost (q1 a) q2) : Tom.Div3Quot a q2 := by
  have hd : (q1 a).digit = Tom.divDDigit a 3 := funext fun j => by
    simp only [q1, MpInt.ofDigits_digit, qd, Tom.divDDigit, initPrec, minPrec_eq]
    by_cases h1 : j < a.used
    · rw [if_pos (by omega), if_pos ⟨Nat.zero_le _, h1⟩, if_pos h1]
    · rw [if_neg (show ¬ (0 ≤ j ∧ j < a.used) by omega), if_neg h1]; split <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h.alloc]; simp [q1, MpInt.ofDigits, initPrec, minPrec_eq]
  · rw [h.digits]; simp [q1, MpInt.ofDigits_len, initPrec, minPrec_eq]
  · rw [h.digit, hd]
  · rw [h.used, hd]; rfl
  · rw [h.sign]; rfl

/-- The contract's post. -/
def PostD (p : P) (m : Mem) (v : Abi) (outp : Array String) (ra : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ x M, At ra (Api.Div3.rets p x ra) M v.keep outp cf ∧ Api.Div3.Q p x ∧
    HPost (lay p) ws .cD (Api.Div3.out p x) (Api.Div3.site' p x) (Api.Div3.hin p) (Api.Div3.hout p x) m M

def σC : Ob → X
  | .S => nQ
  | .D => nS
  | .code => nR .code

def σE : Two.R → X
  | .stk => nR .stk
  | .aS => nQ
  | .aD => nS
  | .bS => nR .cS
  | .bD => nR .cD
  | .code => nR .code

def σL : Un.R → X
  | .stk => nR .stk
  | .aS => nQ
  | .aD => nR .cD
  | .code => nR .code

def σI : Is → X
  | .stk => nR .stk
  | .aS => nQ
  | .site => nS
  | .code => nR .code

/-- **`s_mp_div_3` on the machine.** -/
theorem correct : Api.Div3.Statement := by
  intro p m v outp ra hra hres hS hB hH hoff c hc
  obtain ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ := p
  obtain ⟨vsp, gp, tp, s0, s⟩ := v
  have hsp := At.sp_eq hc (x := BitVec.ofNat 64 sp) rfl
  have hgp := At.gp_eq hc (x := gpV) rfl
  simp only at hsp hgp; subst hsp hgp
  revert c hc
  obtain ⟨h0, hp0⟩ := entry_state hres hS hB hH hoff
  have hst : StkRes sp Api.Div3.F := hres.stk
  have eF : Api.Div3.F = 656 := rfl
  have eE : heapEnd = 0x87800000 := rfl
  have := hst.lo; have := hst.al; have := hst.hi
  have hva : a.Valid := hres.va
  have hul := hva.alloc_lt; have huu := hva.used_le
  have hpa := hS .aS .stk (by decide)
  have hco := hS .stk .code (by decide)
  simp only [Iv.Disj, Disj, lay, eF, textIv] at hpa hco
  have eFs : MpInit.Fsize = 576 := rfl
  have hR80 : Ram (sp - 80) 80 := Ram.sub (hB .stk).2 (by simp only [lay, eF]; omega) (by simp only [lay, eF]; omega)
  refine Triple.lmap (fun cf h => h.sub (L' := entryL ra s0 s.s1 s.s2 sp pa pc pd)
    (K' := Abi.keepR2 ⟨BitVec.ofNat 64 sp, gpV, tp, s0, s⟩) rfl rfl) ?_
  have eB : sMpDiv3Base = 0x80006640 := rfl
  have hAs : Ram pa 24 := by simpa [Layout.sizeofMpInt] using (show Hdr m pa adp a from (hB .aS).2).geom.st
  have ff : ∀ M, Hdr M pa adp a → FFacts M sp pa a.used := fun M e =>
    { rs := hR80, sp_al := by omega, sp_ge := by omega, ra_ := hAs, ua_v := e.used, ua_lt := by omega
      code_off := by rw [eB]; omega, pa_off := by omega }
  refine h0.seqW nB rfl (p1_step ra s0 s.s1 s.s2 _ outp sp pa pc pd a.used m (cd h0) (ff m (h0.hdr (nR .aS) rfl)))
    fun M1 h1 => ?_
  refine h1.seqW nA rfl (p2_step ra s0 _ outp sp pa pc pd a.used M1 (cd h1) (ff M1 (h1.hdr (nR .aS) rfl)))
    fun M2 h2 => ?_
  have h2' := h2.forget nQ rfl
  have hir : IsRes ⟨sp - 80, sp - 56, a.used, Api.Div3.hin ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩⟩ :=
    { stk := ⟨by show (sp - 80) % 16 = 0; omega, by show heapEnd + MpInit.Fsize ≤ sp - 80; omega,
        by show sp - 80 ≤ 0x100000000; omega⟩
      size_lt := by show a.used < 2 ^ 31; omega, pa_al := by show (sp - 56) % 8 = 0; omega
      soff := by show OffHeap (sp - 56) 24; unfold OffHeap; omega }
  refine call_heap mpInitSize _ σI h2' hp0 (cd h2') 0xe31fa0ef#32 0x1fae30#21 0x8000666c#64 hir
    fun x M3 hq h3 hp3 => ?_
  -- the epilogue from `676c`, result `r`
  have epi : ∀ {ρ : X → Iv} {κ : X → Kind} {M0 M : Mem} (r : BitVec 64), St ρ wX WX κ M0 M →
      κ nB = .frz (writeLog m (frameLog ra s0 s.s1 s.s2 sp)) → κ (nR .code) = .code → Iv.Sub ⟨sp - 32, 32⟩ (ρ nB) →
      Triple (At 0x8000676c#64 (eL sp r) M (Abi.keepR2 ⟨BitVec.ofNat 64 sp, gpV, tp, s0, s⟩) outp)
        (fun cf => At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s.s1), (18, s.s2), (10, r)] M
          (Abi.keepR2 ⟨BitVec.ofNat 64 sp, gpV, tp, s0, s⟩) outp cf) := by
    intro ρ κ M0 M r h hk hkc hl
    have hfz : ∀ x, sp - 32 ≤ x → x + 8 ≤ sp → bytesT8 M x = bytesT8 (writeLog m (frameLog ra s0 s.s1 s.s2 sp)) x :=
      fun x h1 h2 => h.frz nB hk (Iv.Sub.trans (J := ⟨sp - 32, 32⟩) ⟨h1, by simp only; omega⟩ hl)
    exact e_step ra s0 s.s1 s.s2 r _ outp sp M (cd h hkc)
      { rs := hR80, sp_al := by omega, sp_ge := by omega, ra_al := hra
        ra_v := by rw [hfz _ (by omega) (by omega)]; rd_log
        s0_v := by rw [hfz _ (by omega) (by omega)]; rd_log
        s1_v := by rw [hfz _ (by omega) (by omega)]; rd_log
        s2_v := by rw [hfz _ (by omega) (by omega)]; rd_log }
  cases x with
  | none =>
    refine St.seq0 (m_step _ outp sp pa pc M3 (cd h3)) ?_
    refine Triple.rmap (fun cf hat => ?_) (epi _ h3 rfl rfl (by iv_omega))
    obtain ⟨hfr, hh⟩ := hp3.fin h3
    exact ⟨none, M3, hat.sub rfl rfl, trivial,
      { wit := fun r hr hrs => by
          cases r with
          | stk => exact ⟨trivial, (hB .stk).2⟩
          | cS => exact ⟨Iv.sub_self _, h3.hdr (nR .cS) rfl⟩
          | dS => exact ⟨trivial, (hB .dS).2⟩
          | cD => exact absurd rfl hrs
          | _ => simp [ws] at hr
        wsite := ⟨Iv.sub_self _, h3.dig (nR .cD) rfl⟩, place := .keep
        frame := hfr, heap := hh, foot := fun a h => .inl h, off := hoff .cD }⟩
  | some qdp =>
    have hf : Fresh (Api.Div3.hin ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩) qdp (4 * initPrec a.used) := hq
    have en : initPrec a.used = max 3 a.used := by simp [initPrec, minPrec_eq]
    have hq1a : (q1 a).alloc = initPrec a.used := rfl
    have hpc0 : 0x80000000 ≤ pc := (show Hdr m pc cdp cc from (hB .cS).2).geom.st.lo_ge
    have hqlo := hf.lo; have hqhi := hf.hi
    have hpc1 := (show Hdr m pc cdp cc from (hB .cS).2).geom.st.hi_le
    have eS : heapStart = 0x80019d10 := rfl
    have hp3c := hp3.congrL (ρ' := ρC ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ ⟨qdp, 4 * initPrec a.used⟩ (lay ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cD)) (by
      intro r; rcases r with _ | _ | _ | _ | r
      all_goals first | rfl | (cases r <;> rfl))
    -- from `674c`: `mp_clamp`, `mp_exch`, `mp_clear`, the epilogue
    have tail : ∀ M (dk : Kind), St (ρC ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ ⟨qdp, 4 * initPrec a.used⟩
          (lay ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cD)) wX WX
        (κC ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ (writeLog m [(sp - 72, 8, BitVec.ofNat 64 pd)])
          (writeLog m (frameLog ra s0 s.s1 s.s2 sp)) (.mpS (sp - 56) qdp (q1 a)) (.mpD qdp (q1 a).alloc (q1 a).digit)
          (kind ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cS) (kind ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cD) dk)
          M3 M →
        dk = Api.Div3.dK hasD pd (Api.Div3.rem a) →
        Triple (At 0x8000674c#64 (tL sp pa pc) M (Abi.keepR2 ⟨BitVec.ofNat 64 sp, gpV, tp, s0, s⟩) outp)
          (fun cf => ∃ x M, At ra (Api.Div3.rets ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ x ra) M
            (Abi.keep ⟨BitVec.ofNat 64 sp, gpV, tp, s0, s⟩) outp cf ∧ Api.Div3.Q ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ x ∧
            HPost (lay ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩) ws .cD (Api.Div3.out ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ x)
              (Api.Div3.site' ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ x) (Api.Div3.hin ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩)
              (Api.Div3.hout ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ x) m M) := by
      intro M dk h hdk
      refine St.seq0 (t_step _ outp sp pa pc M (cd h) (by omega) (by omega) (by omega)) ?_
      refine call_std clamp ⟨sp - 56, qdp, q1 a⟩ σC h (cd h) 0x885fe0ef#32 0x1fe884#21 0x80006758#64
        (q1_shape hva.toShape) fun q2 M4 hcl h4 => ?_
      have h4' := h4.congrK (κ' := κC ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ (writeLog m [(sp - 72, 8, BitVec.ofNat 64 pd)])
          (writeLog m (frameLog ra s0 s.s1 s.s2 sp)) (.mpS (sp - 56) qdp q2) (.mpD qdp q2.alloc q2.digit)
          (kind ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cS) (kind ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cD) dk) (by
        intro r; rcases r with _ | _ | _ | _ | r
        · show Kind.mpD qdp (q1 a).alloc (q1 a).digit = Kind.mpD qdp q2.alloc q2.digit; rw [hcl.alloc, hcl.digit]
        all_goals first | rfl | (cases r <;> rfl))
      have hq2a : q2.alloc = initPrec a.used := hcl.alloc
      have hsg : q2.sign < 2 ^ 31 := by
        rw [hcl.sign]; split
        · decide
        · have := hva.sign_ok; simp only [q1, MpInt.ofDigits]; unfold Layout.mpNeg Layout.mpZpos at *; omega
      refine St.seq0 (x_step _ outp sp pa pc M4 (cd h4') (by omega)) ?_
      refine call_std mpExch ⟨sp - 80, sp - 56, qdp, pc, cdp, q2, cc⟩ σE h4' (cd h4') 0xf00fa0ef#32 0x1fa700#21
        0x80006764#64 hsg fun _ M5 _ h5 => ?_
      refine St.seq0 (c_step _ outp sp pa pc M5 (cd h5) (by omega)) ?_
      have hpP := hp3c.perm (List.Perm.swap (digBlk cdp cc) (qdp, 4 * initPrec a.used) H)
      have eCl : MpClear.F = 544 := rfl
      have hcr : ClRes ⟨sp - 80, sp - 56, cdp, cc, (qdp, 4 * initPrec a.used) :: H⟩ :=
        { stk := ⟨by show (sp - 80) % 16 = 0; omega, by show heapEnd + MpClear.F ≤ sp - 80; omega,
            by show sp - 80 ≤ 0x100000000; omega⟩
          soff := by show OffHeap (sp - 56) 24; unfold OffHeap; omega, apos := hres.cpos }
      refine call_heap mpClear ⟨sp - 80, sp - 56, cdp, cc, (qdp, 4 * initPrec a.used) :: H⟩ σL h5 hpP (cd h5)
        0x8b1fe0ef#32 0x1fe8b0#21 0x8000676c#64 hcr fun _ M6 _ h6 hp6 => ?_
      refine Triple.rmap (fun cf hat => ?_) ((epi 0#64 h6 rfl rfl (by iv_omega)).pre)
      obtain ⟨hfr, hh⟩ := hp6.fin h6
      have hfq : Fresh (Api.Div3.hin ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩) qdp (4 * q2.alloc) := hq2a ▸ hf
      subst hdk
      refine ⟨some (qdp, q2), M6, hat.sub rfl rfl, q1_quot hcl,
        { wit := fun r hr hrs => ?_
          wsite := ⟨Iv.sub_self _, h6.dig nS rfl⟩
          place := .fresh hfq (by have := hres.apos; rw [hq2a]; unfold initPrec minPrec at *; simp only [Layout.digitBits] at *; omega)
          frame := hfr, heap := by rw [show Api.Div3.hout ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ (some (qdp, q2)) =
              (qdp, 4 * initPrec a.used) :: H by rw [← hq2a]; rfl]; exact hh
          foot := fun x hx => (foot_uncons (e := digBlk cdp cc) (Foot.of_cons hx)).imp id id
          off := by have := hp6.off nS; rw [← hq2a] at this; exact this }⟩
      cases r with
      | stk => exact ⟨trivial, (hB .stk).2⟩
      | cS => exact ⟨Iv.sub_self _, h6.hdr (nR .cS) rfl⟩
      | dS => exact h6.wit (nR .dS)
      | cD => exact absurd rfl hrs
      | _ => simp [ws] at hr
    -- at `674c` from either path: re-abstract `q` as `q1 a`
    have fin : ∀ M (q0 : MpInt) (f : Nat → Nat) (dk : Kind), St (ρC ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ ⟨qdp, 4 * initPrec a.used⟩ (lay ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cD)) wX WX
          (κC ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ (writeLog m [(sp - 72, 8, BitVec.ofNat 64 pd)]) (writeLog m (frameLog ra s0 s.s1 s.s2 sp)) (.mpS (sp - 56) qdp q0) (.mpD qdp (initPrec a.used) f) (kind ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cS) (kind ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cD) dk) M3 M →
        q0.used = a.used → q0.alloc = initPrec a.used → q0.sign = a.sign →
        (∀ j, j < initPrec a.used → (q1 a).digit j = f j) → dk = Api.Div3.dK hasD pd (Api.Div3.rem a) →
        Triple (At 0x8000674c#64 (tL sp pa pc) M (Abi.keepR2 ⟨BitVec.ofNat 64 sp, gpV, tp, s0, s⟩) outp)
          (PostD ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ m ⟨BitVec.ofNat 64 sp, gpV, tp, s0, s⟩ outp ra) :=
      fun M q0 f dk h hu hal hsg hfd hdk => tail M dk ((h.setMp nQ nS rfl rfl (q1 a) hu.symm hal.symm hsg.symm hal hfd).congrK
        (by intro r; rcases r with _ | _ | _ | _ | r
            all_goals first | rfl | (cases r <;> rfl))) hdk
    -- the state after `mp_init_size`, normalised
    have h3c := (h3.congrL (ρ' := (ρC ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ ⟨qdp, 4 * initPrec a.used⟩ (lay ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cD))) (by
        intro r; rcases r with _ | _ | _ | _ | r
        all_goals first | rfl | (cases r <;> rfl))).congrK
      (κ' := κC ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ (writeLog m [(sp - 72, 8, BitVec.ofNat 64 pd)]) (writeLog m (frameLog ra s0 s.s1 s.s2 sp)) (.mpS (sp - 56) qdp (MpInt.zeroN (initPrec a.used)))
        (.mpD qdp (initPrec a.used) (MpInt.zeroN (initPrec a.used)).digit) (kind ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cS) (kind ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cD) .ram) (by
        intro r; rcases r with _ | _ | _ | _ | r
        all_goals first | rfl | (cases r <;> rfl))
    -- the frame reads
    have hfA : bytesT8 M3 (sp - 72) = BitVec.ofNat 64 pd := by
      rw [h3c.frz nA rfl (by iv_omega)]; rd_log
    have hAS : Hdr M3 pa adp a := h3c.hdr (nR .aS) rfl
    have hsgl : a.sign < 2 ^ 31 := by have := hva.sign_ok; unfold Layout.mpNeg Layout.mpZpos at *; omega
    -- `*d`: the remainder's store, or none
    have dstep : ∀ M (w : Nat) (q0 : MpInt) (f : Nat → Nat), St (ρC ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ ⟨qdp, 4 * initPrec a.used⟩ (lay ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cD)) wX WX
          (κC ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ (writeLog m [(sp - 72, 8, BitVec.ofNat 64 pd)]) (writeLog m (frameLog ra s0 s.s1 s.s2 sp)) (.mpS (sp - 56) qdp q0) (.mpD qdp (initPrec a.used) f) (kind ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cS) (kind ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cD) .ram) M3 M →
        q0.used = a.used → q0.alloc = initPrec a.used → q0.sign = a.sign →
        (∀ j, j < initPrec a.used → (q1 a).digit j = f j) → w = Api.Div3.rem a →
        Triple (At 0x80006744#64 (xL sp pa pc pd w) M (Abi.keepR2 ⟨BitVec.ofNat 64 sp, gpV, tp, s0, s⟩) outp)
          (PostD ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ m ⟨BitVec.ofNat 64 sp, gpV, tp, s0, s⟩ outp ra) := by
      intro M w q0 f h hu hal hsg hfd hw
      revert h hw
      cases hasD with
      | false =>
        intro h hw
        have hp0 : pd = 0 := hres.dnull rfl
        subst hp0
        exact St.seq0 (d0_step _ outp sp pa pc w M (cd h)) (fin M q0 f .ram h hu hal hsg hfd rfl)
      | true =>
        intro h hw
        obtain ⟨hpd0, hpd4, hpdo⟩ := hres.dslot rfl
        have hdR : Ram pd 4 := (h.wit (nR .dS)).2
        have hdc := h.disj (nR .dS) (nR .code)
        simp [ρC, ρ3, Split.lay, lay, Api.Div3.dI, Iv.Disj, Disj, textIv, textBase, textLen] at hdc
        have hwl : w < 2 ^ 32 := by
          rw [hw]; show Tom.ldR a.digit 3 a.used 0 < 2 ^ 32
          have := Tom.ldR_lt a.digit (show 0 < 3 by decide) a.used 0; omega
        refine St.seqK h (nR .dS) (Api.Div3.dK true pd (Api.Div3.rem a))
          (d1_step _ outp sp pa pc pd w M (cd h) ⟨hdR, hpd4, by rw [eB]; omega⟩ hpd0)
          ⟨by show Iv.Sub ⟨pd, 4 * 1⟩ ⟨pd, 4⟩; simp only [Iv.Sub]; omega,
           { ram := by simpa using hdR, al := hpd4, arr := fun j hj => by
              rw [show j = 0 by omega, show pd + 4 * 0 = pd by omega, ← hw]; exact bytesT4_sw_self _ _ w hwl }⟩
          fun M' h' => fin M' q0 f _ (h'.congrK (by
            intro r; rcases r with _ | _ | _ | _ | r
            all_goals first | rfl | (cases r <;> rfl))) hu hal hsg hfd rfl
    have hun : a.used ≤ initPrec a.used := by rw [en]; omega
    have hco' : sp ≤ sMpDiv3Base ∨ sMpDiv3Base + 340 ≤ sp - 80 := by rw [eB]; omega
    by_cases hu0 : a.used = 0
    · -- `a->used = 0`: no loop, `*d = 0`
      have zf : ZFacts M3 sp pa a.sign pd :=
        { pa_off := by omega, rs := hR80, sp_al := by omega, sp_ge := by omega, ra_ := hAs
          ua_v := by rw [← hu0]; exact hAS.used, sg_v := hAS.sign, sg_lt := hsgl, pd_v := hfA, code_off := hco' }
      refine St.seqUS h3c nQ rfl (z_step _ outp sp pa pc pd a.sign M3 (cd h3c) zf) (by decide) (by omega)
        fun M4 h4 => ?_
      have hfd : ∀ j, j < initPrec a.used → (q1 a).digit j = (MpInt.zeroN (initPrec a.used)).digit j := fun j hj => by
        rw [MpInt.zeroN_digit]; simp [q1, MpInt.ofDigits_digit, qd, hu0]
      have hr0 : Api.Div3.rem a = 0 := by show Tom.ldR a.digit 3 a.used 0 = 0; rw [hu0]; exact Tom.ldR_top _ _ _
      revert h4
      cases hasD with
      | false =>
        intro h4
        have hp0 : pd = 0 := hres.dnull rfl
        subst hp0
        exact St.seq0 (z0_step _ outp sp pa pc M4 (cd h4)) (fin M4 { MpInt.zeroN (initPrec a.used) with used := 0, sign := a.sign } (MpInt.zeroN (initPrec a.used)).digit .ram (h4.congrK (by
            intro r; rcases r with _ | _ | _ | _ | r
            all_goals first | rfl | (cases r <;> rfl))) (by simp [hu0]) rfl rfl hfd rfl)
      | true =>
        intro h4
        obtain ⟨hpd0, hpd4, hpdo⟩ := hres.dslot rfl
        have hdR : Ram pd 4 := (h4.wit (nR .dS)).2
        have hdc := h4.disj (nR .dS) (nR .code)
        simp [ρC, ρ3, Split.lay, lay, Api.Div3.dI, Iv.Disj, Disj, textIv, textBase, textLen] at hdc
        refine St.seqK h4 (nR .dS) (Api.Div3.dK true pd (Api.Div3.rem a))
          (z1_step _ outp sp pa pc pd M4 (cd h4) ⟨hdR, hpd4, by rw [eB]; omega⟩ hpd0)
          ⟨by show Iv.Sub ⟨pd, 4 * 1⟩ ⟨pd, 4⟩; simp only [Iv.Sub]; omega,
           { ram := by simpa using hdR, al := hpd4, arr := fun j hj => by
              rw [show j = 0 by omega, show pd + 4 * 0 = pd by omega, hr0]; exact bytesT4_sw_self _ _ 0 (by decide) }⟩
          fun M' h' => fin M' { MpInt.zeroN (initPrec a.used) with used := 0, sign := a.sign } (MpInt.zeroN (initPrec a.used)).digit _ (h'.congrK (by
            intro r; rcases r with _ | _ | _ | _ | r
            all_goals first | rfl | (cases r <;> rfl))) (by simp [hu0]) rfl rfl hfd rfl
    · -- the loop
      have hf1 : HFacts M3 sp pa a.used a.sign pd :=
        { rs := hR80, sp_al := by omega, sp_ge := by omega, ra_ := hAs, ua_v := hAS.used, ua_lt := by omega
          sg_v := hAS.sign, sg_lt := hsgl, pd_v := hfA, code_off := hco', pa_off := by omega }
      refine St.seqUS h3c nQ rfl (s1_step _ outp sp pa pc pd a.used a.sign M3 (cd h3c) hf1 (by omega)) (by omega)
        (by omega) fun M4 h4 => ?_
      have hq4 := h4.hdr nQ rfl
      have hA4 : Hdr M4 pa adp a := h4.hdr (nR .aS) rfl
      have dA : Dig M4 adp a.alloc a.digit := h4.dig (nR .aD) rfl
      have hadp := dA.ram.lo_ge
      have pf : PFacts M4 sp pa adp qdp a.used :=
        { ra_ := hAs, rs := hR80, sp_ge := by omega, adp_v := hA4.dpv
          qdp_v := by rw [show sp - 40 = sp - 56 + 16 by omega]; exact hq4.dpv
          adp_ge := by omega, qdp_ge := by omega, ua_ge := by omega, ua_lt := by omega }
      refine St.seq0 (s2_step _ outp sp pa pc pd adp qdp a.used M4 (cd h4) pf) ?_
      have e0 : Tom.ldR a.digit 3 a.used (a.used - 1 + 1) = 0 := by
        rw [Nat.sub_add_cancel (by omega)]; exact Tom.ldR_top _ _ _
      have hl := loop (ρ := (ρC ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ ⟨qdp, 4 * initPrec a.used⟩ (lay ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cD))) (rs := nS) (rd := nR .aD) (rc := nR .code) (W := WX) (m := M3)
        (κ := κC ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ (writeLog m [(sp - 72, 8, BitVec.ofNat 64 pd)]) (writeLog m (frameLog ra s0 s.s1 s.s2 sp)) (.mpS (sp - 56) qdp { MpInt.zeroN (initPrec a.used) with used := a.used, sign := a.sign })
          .ram (kind ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cS) (kind ⟨sp, pa, adp, pc, cdp, hasD, pd, a, cc, H⟩ .cD) .ram)
        (sp := sp) (pa := pa) (pc := pc) (pd := pd) (adp := adp) (qdp := qdp) (n := initPrec a.used) (a := a)
        (v := ⟨BitVec.ofNat 64 sp, gpV, tp, s0, s⟩) (outp := outp) rfl (by decide)
        (fun M h => dstep M (Tom.ldR a.digit 3 a.used 0) { MpInt.zeroN (initPrec a.used) with used := a.used, sign := a.sign }
            (qd a.digit a.used 0) (h.congrK (by
            intro r; rcases r with _ | _ | _ | _ | r
            all_goals first | rfl | (cases r <;> rfl))) rfl rfl rfl
          (fun j hj => by simp [q1, MpInt.ofDigits_digit, hj]) rfl)
        (a.used - 1) (by omega) M4 (h4.congrK (by
            intro r; rcases r with _ | _ | _ | _ | r
            · show Kind.mpD qdp (initPrec a.used) (MpInt.zeroN (initPrec a.used)).digit = _
              show _ = Kind.mpD qdp (initPrec a.used) (qd a.digit a.used (a.used - 1 + 1))
              congr 1; funext j; rw [MpInt.zeroN_digit]; simp only [qd]; rw [if_neg (by omega)]
            all_goals first | rfl | (cases r <;> rfl)))
        { kd := rfl, kc := rfl, ne_sd := by decide, ne_sc := by decide
          dsc := h4.disj nS (nR .code), fit := Iv.sub_self _, shape := hva.toShape, un := hun
          ua := hva.used_le, ul := by omega, adp4 := by omega, qdp4 := by omega }
      rw [e0] at hl
      exact hl

end Tom.Machine.Fn.Div3

namespace Tom.Machine.Std

open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Div3

/-- `s_mp_div_3` as an allocating contract (for `mp_div_d`). -/
def sMpDiv3 : HContract where
  P := Api.Div3.P
  X := Option (Nat × MpInt)
  R := Api.Div3.R
  all := [.stk, .aS, .aD, .cS, .cD, .dS, .code]
  hall := Api.Div3.all
  entry := Fn.Div3.entry
  args := Api.Div3.args
  rets := Api.Div3.rets
  lay := Api.Div3.lay
  kind := Api.Div3.kind
  out := Api.Div3.out
  isW := Api.Div3.isW
  ws := Api.Div3.ws
  site := .cD
  site' := Api.Div3.site'
  hin := Api.Div3.hin
  hout := Api.Div3.hout
  Res := Api.Div3.Res
  Q := Api.Div3.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, c'⟩
    · cases r <;> simp_all [Api.Div3.out, Api.Div3.kind, Kind.isRam, Kind.indep]
    · cases r <;> simp_all [Api.Div3.out, Api.Div3.kind, Kind.isRam, Kind.indep]
      cases hd : p.hasD <;> simp_all [Api.Div3.dK, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.cpos
    cases r with
    | stk => exact .inl (show 0 < Api.Div3.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | cS => exact .inl (show 0 < 24 by decide)
    | cD => exact .inl (show 0 < 4 * p.c.alloc by omega)
    | dS =>
      show 0 < (Api.Div3.dI p.hasD p.pd).len ∨ (Api.Div3.dI p.hasD p.pd).base < heapStart ∨
        heapEnd ≤ (Api.Div3.dI p.hasD p.pd).base
      cases p.hasD
      · exact .inr (.inl (show 0x80000000 < heapStart by decide))
      · exact .inl (show 0 < 4 by decide)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.Div3.correct

end Tom.Machine.Std
