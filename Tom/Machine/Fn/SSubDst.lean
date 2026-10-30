import Tom.Machine.Fn.SSub
import Tom.Machine.Kit.Dst

/-!
# `s_mp_sub` on the machine: one assembly for every destination

The segment lemmas of `Tom.Machine.Fn.SSub` chained over the destination
kernel (`Tom/Machine/Kit/Dst.lean`), each operand a `Dst.Src`: one proof for
`s_mp_sub(a, b, c)` with `c` distinct from both (`SSubMain.lean`'s
`correct`), `s_mp_sub(a, b, a)` (`s_mp_sub(x, n, x)` in `mp_dr_reduce`,
`mp_montgomery_reduce`, …) and `s_mp_sub(a, b, b)` (`SSubAlias.lean`).

The prologue reads `a->dp`, `b->dp` after the `c->used` store in the same
block, past `c->used` (`Src.off_used`: their struct is `c`'s, or apart);
loop 1 reads `a->dp[i]`, `b->dp[i]` and loop 2 `a->dp[i]` before writing
`c->dp[i]` (`Src.read`). `olduse` is `c->used` at entry, which in the
aliased cases is `a->used = max` or `b->used ≤ max`, so `memset` clears
nothing there; the proof does not need to know.
-/


namespace Tom.Machine.Fn.SSub

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

/-! ## Segment variants: the array bounds as `≤` -/

/-- `l1t_step` with `cdp + 4 min ≤ 2^32`, `adp + 4 min ≤ 2^32`. -/
theorem l1t_step' (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx adp bdp u : Nat)
    (M : Mem) (hc : CodeAt M sMpSubBase sMpSubCode) (hmn : 1 ≤ mn) (hmn' : mn < 2 ^ 31)
    (hcd : cdp + 4 * mn ≤ 4294967296) (had : adp + 4 * mn ≤ 4294967296) :
    Triple (At 0x800045ec#64 (l1L ra sp pc cdp ou mn mx adp bdp mn u) M v.keepR outp)
      (At 0x80004608#64 (j2L ra sp pc cdp ou mn mx adp u) (writeLog M []) v.keepR outp) := by
  ssub_ctx
  seg_step ssubL1t 0x80004608#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 10, 12, 14, 29, 30, 28, 31, 16, 11, 17, 13] abiKeysR [l1L] [j2L] [] hc

/-- `b2_step` with `adp + 4 max ≤ 2^32`. -/
theorem b2_step' (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx adp u : Nat)
    (M : Mem) (hc : CodeAt M sMpSubBase sMpSubCode) (hlt : mn < mx) (hmx : mx < 2 ^ 31)
    (had : adp + 4 * mx ≤ 4294967296) :
    Triple (At 0x80004608#64 (j2L ra sp pc cdp ou mn mx adp u) M v.keepR outp)
      (At 0x80004628#64 (l2L ra sp pc cdp ou mn mx adp mn u) (writeLog M []) v.keepR outp) := by
  ssub_ctx
  seg_step ssubB2 0x80004628#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 29, 30, 13, 12, 14, 10] abiKeysR [j2L] [l2L] [] hc

/-- `l2t_step` with `cdp + 4 max ≤ 2^32`. -/
theorem l2t_step' (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx adp u : Nat)
    (M : Mem) (hc : CodeAt M sMpSubBase sMpSubCode) (hlt : mn < mx) (hmx : mx < 2 ^ 31)
    (hcd : cdp + 4 * mx ≤ 4294967296) :
    Triple (At 0x80004648#64 (l2L ra sp pc cdp ou mn mx adp mx u) M v.keepR outp)
      (At 0x80004660#64 (j3L ra sp pc cdp ou mx) (writeLog M []) v.keepR outp) := by
  ssub_ctx
  seg_step ssubL2t 0x80004660#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 29, 30, 12, 10, 16, 17, 11, 14, 13] abiKeysR [l2L] [j3L] [] hc

/-! ## The calls -/

/-- The callee-saved registers `memset`/`mp_clamp` see. -/
def calleeAbi (v : Abi) (sp pc : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 48), s0 := BitVec.ofNat 64 pc }

/-- `memset(c->dp + max, 0, 4 (olduse - max))` at `4674`, back at `4678`. -/
theorem memset_call (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mx : Nat) (M : Mem)
    (hc : CodeAt M sMpSubBase sMpSubCode) (hP : Memset.Pre M (cdp + 4 * mx) 0 (4 * (ou - mx))) :
    Triple (At 0x80004674#64 (msL ra sp pc cdp ou mx) M v.keepR outp)
      (fun c => ∃ M', At 0x80004678#64 (j4L sp pc) M' v.keepR outp c ∧
        Memset.Post M (cdp + 4 * mx) (4 * (ou - mx)) 0#8 M') := by
  refine Triple.seq (jal_at (pc := 0x80004674#64) (w := 0x531040ef#32) (imm := 0x04d30#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc),
        (10, BitVec.ofNat 64 (cdp + 4 * mx)), (11, 0#64), (12, BitVec.ofNat 64 (4 * (ou - mx)))])
      (hc.word (a := (0x80004674#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [msL]) (by simp [keysG]) (by simp [Abi.keepR, sKeepL, keysG])) ?_
  refine Triple.conseq (Memset.correct_zero 0x80004678#64 (calleeAbi v sp pc) outp M _ _ (by decide) hP)
    (fun c h => ?_) (fun c ⟨M', hat, hpost⟩ => ⟨M', hat.reshape ?_ ?_, hpost⟩)
  · have hpc : (0x80004674#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x04d30#21) = Memset.entry := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [Memset.entryL, Sail.BitVec.addInt]
    · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]
  · simp [j4L, Abi.keep, calleeAbi]
  · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]

/-- `mp_clamp(c)` at `467c`, back at `4680`. -/
theorem clamp_call (v : Abi) (outp : Array String) (sp pc cdp : Nat) (cm : MpInt) (M : Mem)
    (hc : CodeAt M sMpSubBase sMpSubCode) (hP : Clamp.Pre M pc cdp cm) :
    Triple (At 0x8000467c#64 [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc),
        (10, BitVec.ofNat 64 pc)] M v.keepR outp)
      (fun c => ∃ a' M', At 0x80004680#64 [(2, BitVec.ofNat 64 (sp - 48))] M' v.keepR outp c ∧
        Clamp.Post M pc cdp cm a' M') := by
  refine Triple.seq (jal_at (pc := 0x8000467c#64) (w := 0x15d000ef#32) (imm := 0x0095c#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pc)])
      (hc.word (a := (0x8000467c#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp) (by simp [keysG]) (by simp [Abi.keepR, sKeepL, keysG])) ?_
  refine Triple.conseq (Clamp.correct 0x80004680#64 (calleeAbi v sp pc) outp pc cdp cm M (by decide) hP)
    (fun c h => ?_) (fun c ⟨a', M', hat, hpost⟩ => ⟨a', M', hat.reshape ?_ ?_, hpost⟩)
  · have hpc : (0x8000467c#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x0095c#21) = Clamp.entry := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [Sail.BitVec.addInt]
    · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]
  · simp [Abi.keep, calleeAbi]
  · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]

/-! ## Borrows and the clamp input -/

theorem borrow_eq {x y u : Nat} (hx : x < 268435456) (hy : y < 268435456) (hu : u ≤ 1) :
    (x + 4294967296 - (y + u)) % 4294967296 / 2147483648 = if x < y + u then 1 else 0 := by
  split <;> omega

theorem borrow_eq0 {x y u : Nat} (hx : x < 268435456) (hu : u ≤ 1) (hy : y = 0) :
    (x + 4294967296 - u) % 4294967296 / 2147483648 = if x < y + u then 1 else 0 := by
  split <;> omega

/-- `c` as `s_mp_sub` hands it to `mp_clamp`: `used = a->used`, the difference digits. -/
def cMid (a b c : MpInt) : MpInt :=
  { used := a.used, alloc := c.alloc, sign := c.sign, digits := (List.range c.alloc).map (subDigits a b) }

theorem cMid_digit_eq {a b c : MpInt} (ha : a.Shape) (hroom : a.used ≤ c.alloc) :
    (cMid a b c).digit = subDigits a b := by
  funext i
  simp only [cMid, MpInt.digit, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < c.alloc
  · simp [h]
  · simp [h, subDigits_ge ha b (show a.used ≤ i by omega)]

end Tom.Machine.Fn.SSub

namespace Tom.Machine.Fn.SSub.AnyDst

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg
open Tom.Machine.Dst (K isW ws Src SrcAt)

/-- The kernel placement (stack frame of 48 bytes). -/
abbrev lay (sp pc cdp : Nat) (c : MpInt) : K → Iv := Tom.Machine.Dst.lay 48 sp pc cdp c ⟨sMpSubBase, 380⟩

/-- What `s_mp_sub(a, b, c)` needs, for any destination: `c` in memory, each
operand a `Src`, `b->used ≤ a->used`, `c` with room for `a->used` digits
(D5), the kernel's written regions apart from each other and the code. -/
structure Pre (m : Mem) (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt) (ra : BitVec 64) : Prop where
  rc : MpAt m pc cdp c
  srcA : Src (lay sp pc cdp c) m pc cdp c pa adp a
  srcB : Src (lay sp pc cdp c) m pc cdp c pb bdp b
  sa : a.Shape
  sb : b.Shape
  sc : c.Shape
  csign : c.sign = Layout.mpZpos ∨ c.sign = Layout.mpNeg
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  gc : MpGeom pc cdp c.alloc
  ge : b.used ≤ a.used
  room : a.used ≤ c.alloc
  rs : Ram (sp - 48) 48
  sp_al : sp % 16 = 0
  sp_ge : 48 ≤ sp
  ra_al : ra.toNat % 4 = 0
  code : CodeAt m sMpSubBase sMpSubCode
  code_ms : CodeAt m memsetBase memsetCode
  code_cl : CodeAt m mpClampBase mpClampCode
  lay : Sound (lay sp pc cdp c) isW

/-- What it leaves. -/
structure Post (m : Mem) (sp pc cdp : Nat) (a b c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  ssub : SSubPost a b c c'
  frame : Frm (lay sp pc cdp c) ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pc cdp : Nat) (a b c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pc cdp a b c c' M

/-! ## Snapshots and join points -/

/-- The memory after the prologue: the frame stores and `c->used := a->used`. -/
def m2Of (m : Mem) (ra s0 : BitVec 64) (sp pc ua : Nat) : Mem :=
  writeLog (writeLog m (frameLog ra s0 sp)) [(pc, 4, BitVec.ofNat 64 ua)]

/-- The join points: `c`'s digits hold `f`, nothing else changed since `m2Of`. -/
abbrev St (m : Mem) (v : Abi) (outp : Array String) (sp pc cdp : Nat) (a c : MpInt) (ra s0 : BitVec 64) :=
  ASt (lay sp pc cdp c) K.cD (m2Of m ra s0 sp pc a.used) cdp c.alloc v.keepR outp

/-- The facts of the snapshot `m2Of`. -/
structure Snap (ρ : K → Iv) (m M : Mem) (sp pc cdp : Nat) (c : MpInt) (ua : Nat) (ra s0 : BitVec 64) :
    Prop where
  fr : Frm ρ [.fr, .cS] m M
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  rc : MpAt M pc cdp { c with used := ua }

/-- The code, as at the entry. -/
structure RO (M : Mem) : Prop where
  code : CodeAt M sMpSubBase sMpSubCode
  code_ms : CodeAt M memsetBase memsetCode
  code_cl : CodeAt M mpClampBase mpClampCode

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat} {a b c : MpInt}
  {ra s0 : BitVec 64}

local notation "ρ" => lay sp pc cdp c

theorem RO.of (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) {M : Mem} (hF : Frm ρ ws m M) : RO M :=
  { code := hF.keep hP.lay (CodeAt.reads (r := K.code) (k := 95) rfl (Iv.sub_self _)) hP.code
    code_ms := hF.keep hP.lay (CodeAt.reads (r := K.ms) (k := 55) rfl (Iv.sub_self _)) hP.code_ms
    code_cl := hF.keep hP.lay (CodeAt.reads (r := K.cl) (k := 16) rfl (Iv.sub_self _)) hP.code_cl }

theorem f1 (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) : Frm ρ [.fr] m (writeLog m (frameLog ra s0 sp)) := by
  have := hP.sp_ge
  exact Frm.store (by simp only [LogIn, frameLog, Iv.Sub, lay, Tom.Machine.Dst.lay, and_true]; omega)

theorem snap (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Snap ρ m (m2Of m ra s0 sp pc a.used) sp pc cdp c a.used ra s0 := by
  have := hP.sp_ge; have := hP.sa.used_le; have := hP.sa.alloc_lt; have hS := hP.lay
  have hF := f1 (s0 := s0) hP
  have h2 : Frm ρ [.cS] (writeLog m (frameLog ra s0 sp)) (m2Of m ra s0 sp pc a.used) :=
    Frm.sw (Iv.sub_pre (by decide))
  have hs : Iv.Sub ⟨sp - 16, 8⟩ (ρ .fr) := by simp only [Iv.Sub, lay, Tom.Machine.Dst.lay]; omega
  have hr : Iv.Sub ⟨sp - 8, 8⟩ (ρ .fr) := by simp only [Iv.Sub, lay, Tom.Machine.Dst.lay]; omega
  have e : writeLog m (frameLog ra s0 sp) = writeLog (writeLog m [(sp - 16, 8, s0)]) [(sp - 8, 8, ra)] :=
    writeLog_append m [(sp - 16, 8, s0)] [(sp - 8, 8, ra)]
  have hs0 : bytesT8 (writeLog m (frameLog ra s0 sp)) (sp - 16) = s0 := by
    rw [e, bytesT8_sd_out _ _ _ _ (by omega)]; exact bytesT8_sd_self _ _ _
  have hra : bytesT8 (writeLog m (frameLog ra s0 sp)) (sp - 8) = ra := by rw [e]; exact bytesT8_sd_self _ _ _
  exact { fr := hF.trans h2
          ra_v := h2.keep hS (Reads.w8 hr) hra
          s0_v := h2.keep hS (Reads.w8 hs) hs0
          rc := (hF.keep hS (MpAt.reads (rs := K.cS) (rd := K.cD) (Iv.sub_self _) (Iv.sub_self _)) hP.rc).set_used
            hP.gc _ (by omega) }

theorem ro (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) {M : Mem} {f : Nat → Nat}
    (hI : ArrFrm ρ .cD (m2Of m ra s0 sp pc a.used) M cdp c.alloc f) : RO M :=
  RO.of hP ((snap hP).fr.trans hI.fr).mono

/-- The operands at a join point of the loops (index `i`). -/
theorem srcs (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) {M : Mem} {i : Nat} {g : Nat → Nat}
    (hI : ArrFrm ρ .cD (m2Of m ra s0 sp pc a.used) M cdp c.alloc (ovl g c.digit i)) :
    SrcAt M pa adp a i ∧ SrcAt M pb bdp b i :=
  have hsn := snap (s0 := s0) hP
  have hdp : bytesT8 (m2Of m ra s0 sp pc a.used) (pc + 16) = BitVec.ofNat 64 cdp := by
    simpa [Layout.offDp] using hsn.rc.dpv
  ⟨hP.srcA.read hP.lay hsn.fr hdp hI, hP.srcB.read hP.lay hsn.fr hdp hI⟩

theorem ramA (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) : Ram adp (4 * a.alloc) := by
  simpa [Layout.sizeofDigit] using hP.ga.ds

theorem ramB (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) : Ram bdp (4 * b.alloc) := by
  simpa [Layout.sizeofDigit] using hP.gb.ds

theorem ramC (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) : Ram cdp (4 * c.alloc) := by
  simpa [Layout.sizeofDigit] using hP.gc.ds

theorem cstore_of (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) {i : Nat} (hi : i < c.alloc) : CStore cdp i :=
  have hr := ramC hP
  { rc := ⟨by have := hr.lo_ge; omega, by have := hr.hi_le; omega, by have := hr.off; omega⟩
    al := hP.gc.ds_al
    code_off := hP.lay.sub (r := K.cD) (s := K.code) (Iv.sub_elem hi) (Iv.sub_self _) }

end

/-- A digit read from a `SrcAt`. -/
theorem dread {M : Mem} {p dp i : Nat} {x : MpInt} (h : SrcAt M p dp x i) (hs : x.Shape)
    (hg : Ram dp (4 * x.alloc)) (hi : i < x.alloc) : DRead M dp i (x.digit i) :=
  { r := ⟨by have := hg.lo_ge; omega, by have := hg.hi_le; omega, by have := hg.off; omega⟩
    v := h.dig i (Nat.le_refl _) hi
    lt := by have := hs.digit_lt i; simpa [radix, Layout.digitBits] using this }

/-! ## The loops -/

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat} {a b c : MpInt}
  {ra s0 : BitVec 64}

/-- One loop-1 segment (back edge to `45c0`, or the exit at `45ec`). -/
theorem l1_seg (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) (i : Nat) (hi : i < b.used) (pc' : BitVec 64)
    (hseg : ∀ M, CodeAt M sMpSubBase sMpSubCode → DRead M adp i (a.digit i) → DRead M bdp i (b.digit i) →
      CStore cdp i → Triple (At 0x800045c0#64 (l1L ra sp pc cdp c.used b.used a.used adp bdp i
        (subBorrowAt a b i)) M v.keepR outp)
      (At pc' (l1L ra sp pc cdp c.used b.used a.used adp bdp (i + 1)
          ((a.digit i + 4294967296 - (b.digit i + subBorrowAt a b i)) % 4294967296 / 2147483648))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64
          ((a.digit i + 268435456 - b.digit i - subBorrowAt a b i) % 268435456))]) v.keepR outp)) :
    Triple (St m v outp sp pc cdp a c ra s0 0x800045c0#64
        (l1L ra sp pc cdp c.used b.used a.used adp bdp i (subBorrowAt a b i)) (ovl (subDigits a b) c.digit i))
      (St m v outp sp pc cdp a c ra s0 pc'
        (l1L ra sp pc cdp c.used b.used a.used adp bdp (i + 1) (subBorrowAt a b (i + 1)))
        (ovl (subDigits a b) c.digit (i + 1))) := by
  have hua := hP.sa.used_le; have hub := hP.sb.used_le; have hge := hP.ge; have hroom := hP.room
  refine ASt.store (fun M hI => ?_) (by omega)
    (by rw [subDigits_lt_used hP.sa hP.sb (by omega), radix_eq]) (by omega)
  have hs := srcs hP hI
  have hx := dread hs.1 hP.sa (ramA hP) (by omega)
  have hy := dread hs.2 hP.sb (ramB hP) (by omega)
  have h := hseg M (ro hP hI).code hx hy (cstore_of hP (by omega))
  rwa [borrow_eq hx.lt hy.lt (subBorrowAt_le_one a b i)] at h

theorem loop1 (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) (h1 : 1 ≤ b.used) :
    ∀ i, i < b.used → Triple (St m v outp sp pc cdp a c ra s0 0x800045c0#64
        (l1L ra sp pc cdp c.used b.used a.used adp bdp i (subBorrowAt a b i)) (ovl (subDigits a b) c.digit i))
      (St m v outp sp pc cdp a c ra s0 0x80004608#64
        (j2L ra sp pc cdp c.used b.used a.used adp (subBorrowAt a b b.used))
        (ovl (subDigits a b) c.digit b.used)) := by
  have hua := hP.sa.used_le; have hub := hP.sb.used_le; have hge := hP.ge; have hroom := hP.room
  have hal := hP.sa.alloc_lt; have hrA := ramA hP; have hrC := ramC hP
  refine Triple.countup (fun i hi => l1_seg hP i (by omega) _ fun M hc hx hy hs =>
    l1_step ra v outp sp pc cdp c.used b.used a.used adp bdp i _ _ _ M hc hx hy hs
      (subBorrowAt_le_one a b i) hi (by have := hrA.hi_le; omega)) ?_
  have h := l1_seg (s0 := s0) hP (b.used - 1) (by omega) _ fun M hc hx hy hs =>
    l1e_step ra v outp sp pc cdp c.used b.used a.used adp bdp (b.used - 1) _ _ _ M hc hx hy hs
      (subBorrowAt_le_one a b _) (by omega) (by have := hrA.hi_le; omega)
  rw [show b.used - 1 + 1 = b.used by omega] at h
  exact Triple.seq h (ASt.seg fun M hI => l1t_step' ra v outp sp pc cdp c.used b.used a.used adp bdp _ M
    (ro hP hI).code h1 (by omega) (by have := hrC.hi_le; omega) (by have := hrA.hi_le; omega))

/-- One loop-2 segment (back edge to `4628`, or the exit at `4648`). -/
theorem l2_seg (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) (i : Nat) (h1 : b.used ≤ i) (hi : i < a.used)
    (pc' : BitVec 64)
    (hseg : ∀ M, CodeAt M sMpSubBase sMpSubCode → DRead M adp i (a.digit i) → CStore cdp i →
      Triple (At 0x80004628#64 (l2L ra sp pc cdp c.used b.used a.used adp i (subBorrowAt a b i)) M v.keepR outp)
      (At pc' (l2L ra sp pc cdp c.used b.used a.used adp (i + 1)
          ((a.digit i + 4294967296 - subBorrowAt a b i) % 4294967296 / 2147483648))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64
          ((a.digit i + 268435456 - subBorrowAt a b i) % 268435456))]) v.keepR outp)) :
    Triple (St m v outp sp pc cdp a c ra s0 0x80004628#64
        (l2L ra sp pc cdp c.used b.used a.used adp i (subBorrowAt a b i)) (ovl (subDigits a b) c.digit i))
      (St m v outp sp pc cdp a c ra s0 pc'
        (l2L ra sp pc cdp c.used b.used a.used adp (i + 1) (subBorrowAt a b (i + 1)))
        (ovl (subDigits a b) c.digit (i + 1))) := by
  have hua := hP.sa.used_le; have hroom := hP.room
  have hb0 := hP.sb.high_zero i h1
  refine ASt.store (fun M hI => ?_) (by omega)
    (by rw [subDigits_lt_used hP.sa hP.sb hi, radix_eq, hb0, Nat.sub_zero]) (by omega)
  have hx := dread (srcs hP hI).1 hP.sa (ramA hP) (by omega)
  have h := hseg M (ro hP hI).code hx (cstore_of hP (by omega))
  rwa [borrow_eq0 hx.lt (subBorrowAt_le_one a b i) hb0] at h

/-- From `4608` (after loop 1) to `4660`. -/
theorem phase2 (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Triple (St m v outp sp pc cdp a c ra s0 0x80004608#64
        (j2L ra sp pc cdp c.used b.used a.used adp (subBorrowAt a b b.used)) (ovl (subDigits a b) c.digit b.used))
      (St m v outp sp pc cdp a c ra s0 0x80004660#64 (j3L ra sp pc cdp c.used a.used)
        (ovl (subDigits a b) c.digit a.used)) := by
  have hua := hP.sa.used_le; have hge := hP.ge; have hroom := hP.room
  have hal := hP.sa.alloc_lt; have hrA := ramA hP; have hrC := ramC hP
  by_cases he : b.used = a.used
  · rw [he]
    exact ASt.seg fun M hI => b0_step ra v outp sp pc cdp c.used a.used a.used adp _ M (ro hP hI).code
      rfl (by omega)
  refine Triple.seq (ASt.seg fun M hI => b2_step' ra v outp sp pc cdp c.used b.used a.used adp _ M
    (ro hP hI).code (by omega) (by omega) (by have := hrA.hi_le; omega)) ?_
  refine Triple.countup_from (lo := b.used) (fun i h1 hi => l2_seg hP i h1 (by omega) _ fun M hc hx hs =>
    l2_step ra v outp sp pc cdp c.used b.used a.used adp i _ _ M hc hx hs (subBorrowAt_le_one a b i) hi
      (by have := hrA.hi_le; omega)) ?_ b.used (Nat.le_refl _) (by omega)
  have h := l2_seg (s0 := s0) hP (a.used - 1) (by omega) (by omega) _ fun M hc hx hs =>
    l2e_step ra v outp sp pc cdp c.used b.used a.used adp (a.used - 1) _ _ M hc hx hs
      (subBorrowAt_le_one a b _) (by omega) (by have := hrA.hi_le; omega)
  rw [show a.used - 1 + 1 = a.used by omega] at h
  exact Triple.seq h (ASt.seg fun M hI => l2t_step' ra v outp sp pc cdp c.used b.used a.used adp _ M
    (ro hP hI).code (by omega) (by omega) (by have := hrC.hi_le; omega))

/-! ## The phases -/

/-- From the entry to `4608` (loop 1 done, or skipped). -/
theorem phase1 (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Triple (At 0x80004564#64 (entryL ra s0 sp pa pb pc) m v.keepR outp)
      (St m v outp sp pc cdp a c ra s0 0x80004608#64
        (j2L ra sp pc cdp c.used b.used a.used adp (subBorrowAt a b b.used))
        (ovl (subDigits a b) c.digit b.used)) := by
  have hua := hP.sa.used_le; have hub := hP.sb.used_le; have hcu := hP.sc.used_le
  have hal := hP.sa.alloc_lt; have hbl := hP.sb.alloc_lt; have hcl := hP.sc.alloc_lt; have := hP.sp_ge
  have hS := hP.lay
  have hF1 := f1 (s0 := s0) hP
  have hro := RO.of hP hF1.mono
  have hc1 := hF1.keep hS (MpAt.reads (rs := K.cS) (rd := K.cD) (Iv.sub_self _) (Iv.sub_self _)) hP.rc
  have ha0 := hP.srcA.mp1 hS hP.rc (Frm.refl _ m)
  have hb0 := hP.srcB.mp1 hS hP.rc (Frm.refl _ m)
  have ha1 := hP.srcA.mp1 hS hP.rc hF1
  have hb1 := hP.srcB.mp1 hS hP.rc hF1
  have hbs := hP.srcB.off_fr hS; have hcd := hS.disj (r := K.fr) (s := K.code)
  have hcc := hS.disj (r := K.cS) (s := K.code)
  simp only [Iv.Disj, Disj, lay, Tom.Machine.Dst.lay] at hbs hcd hcc
  have hpf : ProFacts m sp pa pb pc a.used b.used c.alloc :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rb := by simpa [Layout.sizeofMpInt] using hP.gb.st
      rc := by simpa [Layout.sizeofMpInt] using hP.gc.st
      rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
      ua_v := by simpa [Layout.offUsed] using ha0.used
      ub_v := by simpa [Layout.offUsed] using hb0.used
      al_v := by simpa [Layout.offAlloc] using hP.rc.alloc
      ua_lt := by omega, ub_lt := by omega, al_lt := hcl
      s_b := by omega, code_off := by omega }
  have hcf : CFacts (writeLog m (frameLog ra s0 sp)) pa pc c.used adp cdp :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rc := by simpa [Layout.sizeofMpInt] using hP.gc.st
      pc_al := hP.gc.st_al
      ou_v := by simpa [Layout.offUsed] using hc1.used
      adp_v := by simpa [Layout.offDp] using ha1.dpv
      cdp_v := by simpa [Layout.offDp] using hc1.dpv
      ou_lt := by omega, c_a := hP.srcA.off_used, code_off := by omega }
  have hI0 : ArrFrm (lay sp pc cdp c) .cD (m2Of m ra s0 sp pc a.used)
      (m2Of m ra s0 sp pc a.used) cdp c.alloc (ovl (subDigits a b) c.digit 0) :=
    ArrFrm.init (Iv.sub_self _) (by rw [ovl_zero]; exact (snap hP).rc.arr)
  refine Triple.seq (p_step ra s0 v outp sp pa pb pc _ _ _ m hP.code hpf hP.room) ?_
  by_cases h0 : b.used = 0
  · rw [h0]
    exact Triple.rmap (fun cf h => ⟨_, hI0, h⟩)
      (e0_step ra v outp sp pa pb pc a.used c.used adp cdp _ hro.code hcf)
  refine Triple.seq ?_ (loop1 hP (by omega) 0 (by omega))
  have hb : BFacts (writeLog m (frameLog ra s0 sp)) pb pc bdp :=
    { rb := by simpa [Layout.sizeofMpInt] using hP.gb.st
      bdp_v := by simpa [Layout.offDp] using hb1.dpv
      c_b := hP.srcB.off_used }
  exact Triple.rmap (fun cf h => ⟨_, hI0, h⟩)
    (e1_step ra v outp sp pa pb pc a.used b.used c.used adp bdp cdp _ hro.code hcf hb (by omega) (by omega))

/-- From `4660` to `4678`: `memset` the digits from `a->used` to `olduse` if there are any. -/
theorem phase3 (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Triple (St m v outp sp pc cdp a c ra s0 0x80004660#64 (j3L ra sp pc cdp c.used a.used)
        (ovl (subDigits a b) c.digit a.used))
      (St m v outp sp pc cdp a c ra s0 0x80004678#64 (j4L sp pc) (subDigits a b)) := by
  intro cf ⟨M, hI, hat⟩
  have hroom := hP.room; have hcu := hP.sc.used_le; have hal := hP.sc.alloc_lt; have hua := hP.sa.used_le
  have hrC := ramC hP
  have hro := ro hP hI
  have h0 := (snap (s0 := s0) hP).rc.used
  simp only [Layout.offUsed, Nat.add_zero] at h0
  have ht : TailFacts M pc a.used c.used :=
    { rc := by simpa [Layout.sizeofMpInt] using hP.gc.st, pc_al := hP.gc.st_al
      used_v := hI.fr.keep hP.lay (Reads.w4 (r := K.cS) (Iv.sub_pre (by decide))) h0
      mx_lt := by omega, ou_lt := by omega }
  have hz : ∀ j, a.used ≤ j → subDigits a b j = 0 := fun j hj => subDigits_ge hP.sa b hj
  have hfin : ∀ k, c.used ≤ k → a.used ≤ k → ∀ j, j < c.alloc →
      ovl (subDigits a b) c.digit k j = subDigits a b j := fun k hk hk' j hj => by
      simp only [ovl]
      split
      · rfl
      · rw [hP.sc.high_zero j (by omega), hz j (by omega)]
  by_cases hou : c.used ≤ a.used
  · exact Triple.rmap (fun cf h => ⟨_, hI.congr (hfin _ hou (Nat.le_refl _)), h⟩)
      (c0_step ra v outp sp pc cdp c.used a.used M hro.code ht hou) cf hat
  have hms : Memset.Pre (writeLog M []) (cdp + 4 * a.used) 0 (4 * (c.used - a.used)) :=
    { byte := by decide, code := hro.code_ms
      ram := ⟨by have := hrC.lo_ge; omega, by have := hrC.hi_le; omega, by have := hrC.off; omega⟩
      code_off := by
        have : memsetCode.length = 55 := rfl
        rw [this]
        exact hP.lay.sub (r := K.cD) (s := K.ms) (I := ⟨cdp + 4 * a.used, 4 * (c.used - a.used)⟩)
          ⟨by simp [lay, Tom.Machine.Dst.lay], by simp only [lay, Tom.Machine.Dst.lay]; omega⟩ (Iv.sub_self _) }
  refine Triple.seq (c1_step ra v outp sp pc cdp c.used a.used M hro.code ht (by omega))
    (Triple.rmap ?_ (memset_call ra v outp sp pc cdp c.used a.used _ hro.code hms)) cf hat
  intro cf ⟨M', hat', hpost⟩
  exact ⟨M', (hI.fill (k := c.used) (by omega) hcu hpost.fill hpost.frame fun j h1 _ => hz j h1).congr
    (hfin _ (Nat.le_refl _) (by omega)), hat'⟩

/-- From `4678` to the return: `mp_clamp(c)` and the epilogue. -/
theorem phase4 (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Triple (St m v outp sp pc cdp a c ra s0 0x80004678#64 (j4L sp pc) (subDigits a b))
      (Ret m v outp sp pc cdp a b c ra s0) := by
  intro cf ⟨M, hI, hat⟩
  have hroom := hP.room; have hal := hP.sc.alloc_lt; have := hP.sp_ge; have hS := hP.lay
  have hsn := snap (s0 := s0) hP
  have hro := ro hP hI
  have hdig := cMid_digit_eq (b := b) (c := c) hP.sa hroom
  have hpre : Clamp.Pre M pc cdp (cMid a b c) :=
    { repr := hsn.rc.of_hdr (fun x h1 h2 => (Frm.on (r := K.cS) hS hI.fr) x ⟨h1, h2⟩)
        (by rw [hdig]; exact hI.arr) rfl rfl rfl
      shape := { len := by simp [cMid]
                 used_le := hroom
                 alloc_lt := hal
                 digit_lt := fun i => by rw [hdig]; exact subDigits_lt a b i
                 high_zero := fun i hi => by rw [hdig]; exact subDigits_ge hP.sa b hi }
      geom := hP.gc, code := hro.code_cl, code_off := hS.disj (r := K.cS) (s := K.cl) }
  refine Triple.seq (d_step v outp sp pc M hro.code)
    (Triple.seq (clamp_call v outp sp pc cdp _ M hro.code hpre) ?_) cf hat
  intro cf ⟨c', M', hat', hpost⟩
  have hF := hI.fr.trans (Frm.call (w := K.cS) hpost.frame (Iv.sub_pre (by decide)))
  have hr : Iv.Sub ⟨sp - 8, 8⟩ (lay sp pc cdp c .fr) := by simp only [Iv.Sub, lay, Tom.Machine.Dst.lay]; omega
  have hs : Iv.Sub ⟨sp - 16, 8⟩ (lay sp pc cdp c .fr) := by simp only [Iv.Sub, lay, Tom.Machine.Dst.lay]; omega
  have hff : FrameFacts M' ra s0 sp :=
    { rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge, ra_al := hP.ra_al
      ra_v := hF.keep hS (Reads.w8 hr) hsn.ra_v
      s0_v := hF.keep hS (Reads.w8 hs) hsn.s0_v }
  have hF' := hsn.fr.trans hF
  refine Triple.rmap (fun cf h => ⟨c', _, h, ?_⟩)
    (r_step ra s0 v outp sp M' (RO.of hP hF'.mono).code hff) cf hat'
  have hcp := hpost.clamp
  exact { repr := hpost.repr
          ssub := { alloc := hcp.alloc
                    len := by rw [hcp.digits]; simp [cMid]
                    digit := by rw [hcp.digit, hdig]
                    used := by rw [hcp.used, hdig]; rfl
                    sign := by rw [hcp.sign]; rfl }
          frame := hF'.mono }

end

/-- **`s_mp_sub` on the machine, for any destination.** -/
theorem correct {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat}
    {a b c : MpInt} {ra s0 : BitVec 64} (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Triple (At 0x80004564#64 (entryL ra s0 sp pa pb pc) m v.keepR outp)
      (Ret m v outp sp pc cdp a b c ra s0) :=
  Triple.seq (phase1 hP) (Triple.seq (phase2 hP) (Triple.seq (phase3 hP) (phase4 hP)))

end Tom.Machine.Fn.SSub.AnyDst
