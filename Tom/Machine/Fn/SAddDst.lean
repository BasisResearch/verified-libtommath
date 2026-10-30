import Tom.Machine.Fn.SAdd
import Tom.Machine.Kit.Dst

/-!
# `s_mp_add` on the machine: one assembly for every destination

The segment lemmas of `Tom.Machine.Fn.SAdd` chained over the destination
kernel (`Tom/Machine/Kit/Dst.lean`): the regions are the stack frame, `c`'s
struct and digits, and the three functions' code; each operand is a
`Dst.Src`, its own `mp_int` (`own`) or `c` itself (`self`). So one proof
covers `s_mp_add(a, b, c)` with `c` distinct from both (`SAddMain.lean`'s
`correct`), `s_mp_add(a, b, a)` and `s_mp_add(a, b, b)` (`SAddAlias.lean`).

It is the assembly of the distinct case with the operand reads abstracted:
`Src.read` gives a loop's read of an operand's digit `i` at a join point
(`ArrFrm` on `c`'s digits holding `ovl (addDigits a b) c.digit i`; in the
aliased case the array still holds the operand's digit `i`, since both
loops read index `i` before they write it), and the digit pointers after
the `c->used` store. The `olduse` test reads `c->used` as it was at entry,
so in the aliased cases (`olduse = a->used ≤ max`) the `memset` branch is
not taken; the proof does not need to know.
-/


namespace Tom.Machine.Fn.SAdd.AnyDst

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg
open Tom.Machine.Dst (K isW ws Src SrcAt)

/-! ## A segment variant: the operands' digit pointers without `c` apart -/

/-- The operands' digit pointers (their structs may be `c`'s). -/
structure OpFacts' (M : Mem) (pa pb adp bdp mn : Nat) : Prop where
  ra_ : Ram pa 24
  rb : Ram pb 24
  adp_v : bytesT8 M (pa + 16) = BitVec.ofNat 64 adp
  bdp_v : bytesT8 M (pb + 16) = BitVec.ofNat 64 bdp
  ra_d : Ram adp (4 * mn)
  rb_d : Ram bdp (4 * mn)

/-- `a1b_step` from `OpFacts'`. -/
theorem a1b_step' (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc xp mn mx ou cdp adp bdp : Nat)
    (M : Mem) (hc : CodeAt M sMpAddBase sMpAddCode) (hp : Ram pc 24)
    (hdp : bytesT8 M (pc + 16) = BitVec.ofNat 64 cdp) (ho : OpFacts' M pa pb adp bdp mn)
    (hmn : 1 ≤ mn) (hmn' : mn < 2 ^ 31) :
    Triple (At 0x800021e8#64 (jaL ra sp pa pb pc mn mx xp ou) M v.keepR outp)
      (At 0x80002218#64 (l1L ra sp pc cdp ou mn mx xp adp bdp 0 0) (writeLog M []) v.keepR outp) := by
  sadd_ctx
  seg_step saddA1b 0x80002218#64 [rd8 M (pc + 16), rd8 M (pa + 16), rd8 M (pb + 16)]
    [1, 2, 8, 14, 15, 28, 30, 31, 12] abiKeysR [jaL] [l1L] [hdp, ho.adp_v, ho.bdp_v] hc

/-! ## The kernel, the contract -/

/-- The kernel placement (stack frame of 64 bytes). -/
abbrev lay (sp pc cdp : Nat) (c : MpInt) : K → Iv := Tom.Machine.Dst.lay 64 sp pc cdp c ⟨sMpAddBase, 432⟩

/-- What `s_mp_add(a, b, c)` needs, for any destination: `c` in memory, each
operand a `Src` (its own `mp_int`, or `c`), `c` with room for `max + 1`
digits (D5), the kernel's written regions apart from each other and the code. -/
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
  room : max a.used b.used + 1 ≤ c.alloc
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  ra_al : ra.toNat % 4 = 0
  code : CodeAt m sMpAddBase sMpAddCode
  code_ms : CodeAt m memsetBase memsetCode
  code_cl : CodeAt m mpClampBase mpClampCode
  lay : Sound (lay sp pc cdp c) isW

/-- What it leaves: `c'` at `c`, `SAddPost a b c c'`, memory changed only in
the kernel's written regions. -/
structure Post (m : Mem) (sp pc cdp : Nat) (a b c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  sadd : SAddPost a b c c'
  frame : Frm (lay sp pc cdp c) ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pc cdp : Nat) (a b c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pc cdp a b c c' M

/-! ## Snapshots and join points -/

/-- The memory after the prologue's frame stores and `c->used := max + 1`. -/
def m2Of (m : Mem) (ra s0 : BitVec 64) (sp pc mx : Nat) : Mem :=
  writeLog (writeLog m (frameLog ra s0 sp)) [(pc, 4, BitVec.ofNat 64 (mx + 1))]

/-- The join points: `c`'s digits hold `f`, nothing else changed since `m2Of`. -/
abbrev St (m : Mem) (v : Abi) (outp : Array String) (sp pc cdp : Nat) (c : MpInt)
    (ra s0 : BitVec 64) (mx : Nat) :=
  ASt (lay sp pc cdp c) K.cD (m2Of m ra s0 sp pc mx) cdp c.alloc v.keepR outp

/-- The code, as at the entry. -/
structure RO (M : Mem) : Prop where
  code : CodeAt M sMpAddBase sMpAddCode
  code_ms : CodeAt M memsetBase memsetCode
  code_cl : CodeAt M mpClampBase mpClampCode

/-- The facts of the snapshot `m2Of`: the saved registers, `c` with `used := u`. -/
structure Snap (M : Mem) (sp pc cdp : Nat) (c : MpInt) (u : Nat) (ra s0 : BitVec 64) : Prop where
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  rc : MpAt M pc cdp { c with used := u }

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat} {a b c : MpInt}
  {ra s0 : BitVec 64}

local notation "ρ" => lay sp pc cdp c

theorem RO.of (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) {M : Mem} (hF : Frm ρ ws m M) : RO M :=
  { code := hF.keep hP.lay (CodeAt.reads (r := K.code) (k := 108) rfl (Iv.sub_self _)) hP.code
    code_ms := hF.keep hP.lay (CodeAt.reads (r := K.ms) (k := 55) rfl (Iv.sub_self _)) hP.code_ms
    code_cl := hF.keep hP.lay (CodeAt.reads (r := K.cl) (k := 16) rfl (Iv.sub_self _)) hP.code_cl }

theorem f1 (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) : Frm ρ [.fr] m (writeLog m (frameLog ra s0 sp)) := by
  have := hP.sp_ge
  exact Frm.store (by simp only [LogIn, frameLog, Iv.Sub, lay, Tom.Machine.Dst.lay, and_true]; omega)

theorem f2 (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) (mx : Nat) :
    Frm ρ [.fr, .cS] m (m2Of m ra s0 sp pc mx) :=
  (f1 hP).trans (Frm.sw (w := K.cS) (Iv.sub_pre (by decide)))

theorem snap (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) (mx : Nat) (hmx : mx + 1 < 2 ^ 32) :
    Snap (m2Of m ra s0 sp pc mx) sp pc cdp c (mx + 1) ra s0 := by
  have := hP.sp_ge; have hS := hP.lay
  have hF := f1 (s0 := s0) hP
  have h2 : Frm ρ [.cS] (writeLog m (frameLog ra s0 sp)) (m2Of m ra s0 sp pc mx) := Frm.sw (Iv.sub_pre (by decide))
  have hs : Iv.Sub ⟨sp - 16, 8⟩ (ρ .fr) := by simp only [Iv.Sub, lay, Tom.Machine.Dst.lay]; omega
  have hr : Iv.Sub ⟨sp - 8, 8⟩ (ρ .fr) := by simp only [Iv.Sub, lay, Tom.Machine.Dst.lay]; omega
  have e : writeLog m (frameLog ra s0 sp) = writeLog (writeLog m [(sp - 16, 8, s0)]) [(sp - 8, 8, ra)] :=
    writeLog_append m [(sp - 16, 8, s0)] [(sp - 8, 8, ra)]
  have hs0 : bytesT8 (writeLog m (frameLog ra s0 sp)) (sp - 16) = s0 := by
    rw [e, bytesT8_sd_out _ _ _ _ (by omega)]; exact bytesT8_sd_self _ _ _
  have hra : bytesT8 (writeLog m (frameLog ra s0 sp)) (sp - 8) = ra := by rw [e]; exact bytesT8_sd_self _ _ _
  exact { ra_v := h2.keep hS (Reads.w8 hr) hra
          s0_v := h2.keep hS (Reads.w8 hs) hs0
          rc := (hF.keep hS (MpAt.reads (rs := K.cS) (rd := K.cD) (Iv.sub_self _) (Iv.sub_self _)) hP.rc).set_used
            hP.gc _ hmx }

theorem ro (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) {M : Mem} {mx : Nat} {f : Nat → Nat}
    (hI : ArrFrm ρ .cD (m2Of m ra s0 sp pc mx) M cdp c.alloc f) : RO M :=
  RO.of hP ((f2 hP mx).trans hI.fr).mono

/-- `c`'s digit pointer after the prologue. -/
theorem dp2 (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) (mx : Nat) (hmx : mx + 1 < 2 ^ 32) :
    bytesT8 (m2Of m ra s0 sp pc mx) (pc + 16) = BitVec.ofNat 64 cdp := by
  simpa [Layout.offDp] using (snap (s0 := s0) hP mx hmx).rc.dpv

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

/-- The operands at a join point of the loops (index `i`). -/
theorem srcs (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) {M : Mem} {mx i : Nat} {g : Nat → Nat}
    (hmx : mx + 1 < 2 ^ 32) (hI : ArrFrm ρ .cD (m2Of m ra s0 sp pc mx) M cdp c.alloc (ovl g c.digit i)) :
    SrcAt M pa adp a i ∧ SrcAt M pb bdp b i :=
  ⟨hP.srcA.read hP.lay (f2 hP mx) (dp2 hP mx hmx) hI, hP.srcB.read hP.lay (f2 hP mx) (dp2 hP mx hmx) hI⟩

end

/-- A digit read from a `SrcAt`. -/
theorem dread {M : Mem} {p dp i : Nat} {x : MpInt} (h : SrcAt M p dp x i) (hs : x.Shape)
    (hg : Ram dp (4 * x.alloc)) (j : Nat) (hij : i ≤ j) (hj : j < x.alloc) : DRead M dp j (x.digit j) :=
  { r := ⟨by have := hg.lo_ge; omega, by have := hg.hi_le; omega, by have := hg.off; omega⟩
    v := h.dig j hij hj
    lt := by have := hs.digit_lt j; simpa [radix, Layout.digitBits] using this }

theorem carry_succ (a b : MpInt) (i : Nat) :
    (a.digit i + b.digit i + addCarryAt a b i) / 268435456 = addCarryAt a b (i + 1) := by
  rw [addCarryAt_succ, radix_eq]

/-- The operand with more digits (`x` of the C). -/
def xpOf (a b : MpInt) (pa pb : Nat) : Nat := if a.used ≤ b.used then pb else pa

/-- Its digit pointer. -/
def xdpOf (a b : MpInt) (adp bdp : Nat) : Nat := if a.used ≤ b.used then bdp else adp

/-- `c` as `s_mp_add` hands it to `mp_clamp`: `used = max + 1`, the sum digits. -/
def cMid (a b c : MpInt) : MpInt :=
  { used := max a.used b.used + 1, alloc := c.alloc, sign := c.sign,
    digits := (List.range c.alloc).map (addDigits a b) }

theorem cMid_digit_eq {a b c : MpInt} (ha : a.Shape) (hb : b.Shape)
    (hroom : max a.used b.used + 1 ≤ c.alloc) : (cMid a b c).digit = addDigits a b := by
  funext i
  simp only [cMid, MpInt.digit, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < c.alloc
  · simp [h]
  · simp [h, addDigits_high ha hb i (by omega)]

/-! ## The loops -/

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat} {a b c : MpInt}
  {ra s0 : BitVec 64}

/-- One loop-1 segment (back edge to `2218`, or the exit at `2244`). -/
theorem l1_seg (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) {mn mx xp : Nat} (hmn : mn = min a.used b.used)
    (hmx : mx = max a.used b.used) (i : Nat) (hi : i < mn) (pc' : BitVec 64)
    (hseg : ∀ M, CodeAt M sMpAddBase sMpAddCode → DRead M adp i (a.digit i) → DRead M bdp i (b.digit i) →
      CStore cdp i → Triple (At 0x80002218#64 (l1L ra sp pc cdp c.used mn mx xp adp bdp i
        (addCarryAt a b i)) M v.keepR outp)
      (At pc' (l1L ra sp pc cdp c.used mn mx xp adp bdp (i + 1)
          ((a.digit i + b.digit i + addCarryAt a b i) / 268435456))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64
          ((a.digit i + b.digit i + addCarryAt a b i) % 268435456))]) v.keepR outp)) :
    Triple (St m v outp sp pc cdp c ra s0 mx 0x80002218#64
        (l1L ra sp pc cdp c.used mn mx xp adp bdp i (addCarryAt a b i)) (ovl (addDigits a b) c.digit i))
      (St m v outp sp pc cdp c ra s0 mx pc'
        (l1L ra sp pc cdp c.used mn mx xp adp bdp (i + 1) (addCarryAt a b (i + 1)))
        (ovl (addDigits a b) c.digit (i + 1))) := by
  have hua := hP.sa.used_le; have hub := hP.sb.used_le; have hroom := hP.room; have hal := hP.sc.alloc_lt
  refine ASt.store (fun M hI => ?_) (by omega)
    (by rw [addDigits_lt_max hP.sa hP.sb (by omega), radix_eq]) (by omega)
  have hs := srcs hP (by omega) hI
  have hx := dread hs.1 hP.sa (ramA hP) i (Nat.le_refl _) (by omega)
  have hy := dread hs.2 hP.sb (ramB hP) i (Nat.le_refl _) (by omega)
  have h := hseg M (ro hP hI).code hx hy (cstore_of hP (by omega))
  rwa [carry_succ] at h

theorem loop1 (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) {mn mx xp : Nat} (hmn : mn = min a.used b.used)
    (hmx : mx = max a.used b.used) (h1 : 1 ≤ mn) :
    ∀ i, i < mn → Triple (St m v outp sp pc cdp c ra s0 mx 0x80002218#64
        (l1L ra sp pc cdp c.used mn mx xp adp bdp i (addCarryAt a b i)) (ovl (addDigits a b) c.digit i))
      (St m v outp sp pc cdp c ra s0 mx 0x8000225c#64
        (j2L ra sp pc cdp c.used mn mx xp mn (addCarryAt a b mn)) (ovl (addDigits a b) c.digit mn)) := by
  have hua := hP.sa.used_le; have hub := hP.sb.used_le; have hroom := hP.room
  have hal := hP.sc.alloc_lt; have hrA := ramA hP; have hrC := ramC hP
  refine Triple.countup (fun i hi => l1_seg hP hmn hmx i (by omega) _ fun M hc hx hy hs =>
    l1_step ra v outp sp pc cdp c.used mn mx xp adp bdp i _ _ _ M hc hx hy hs
      (addCarryAt_le_one hP.sa hP.sb i) hi (by have := hrA.hi_le; omega)) ?_
  have h := l1_seg (s0 := s0) hP hmn hmx (mn - 1) (by omega) _ fun M hc hx hy hs =>
    l1e_step ra v outp sp pc cdp c.used mn mx xp adp bdp (mn - 1) _ _ _ M hc hx hy hs
      (addCarryAt_le_one hP.sa hP.sb _) (by omega) (by have := hrA.hi_le; omega)
  rw [show mn - 1 + 1 = mn by omega] at h
  exact Triple.seq h (ASt.seg fun M hI => l1t_step ra v outp sp pc cdp c.used mn mx xp adp bdp _ M
    (ro hP hI).code h1 (by omega) (by have := hrC.hi_le; omega))

/-- From `21d4` (after the prologue) to `225c`. -/
theorem phase1b (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) {mn mx xp : Nat} (hmn : mn = min a.used b.used)
    (hmx : mx = max a.used b.used) :
    Triple (At 0x800021d4#64 (j1L ra sp pa pb pc mn mx xp) (writeLog m (frameLog ra s0 sp)) v.keepR outp)
      (St m v outp sp pc cdp c ra s0 mx 0x8000225c#64
        (j2L ra sp pc cdp c.used mn mx xp mn (addCarryAt a b mn)) (ovl (addDigits a b) c.digit mn)) := by
  have hua := hP.sa.used_le; have hub := hP.sb.used_le; have hroom := hP.room
  have hal := hP.sc.alloc_lt; have hcu := hP.sc.used_le; have hS := hP.lay
  have hF1 := f1 (s0 := s0) hP
  have hc1 := hF1.keep hS (MpAt.reads (rs := K.cS) (rd := K.cD) (Iv.sub_self _) (Iv.sub_self _)) hP.rc
  have hcf : CFacts (writeLog m (frameLog ra s0 sp)) pc c.alloc c.used cdp :=
    { rc := by simpa [Layout.sizeofMpInt] using hP.gc.st, pc_al := hP.gc.st_al
      al_v := by simpa [Layout.offAlloc] using hc1.alloc
      ou_v := by simpa [Layout.offUsed] using hc1.used
      dp_v := by simpa [Layout.offDp] using hc1.dpv
      al_lt := hal, ou_lt := by omega, code_off := hS.disj (r := K.cS) (s := K.code) }
  have hsn := snap (s0 := s0) hP mx (by omega)
  have hI0 : ArrFrm (lay sp pc cdp c) .cD (m2Of m ra s0 sp pc mx) (m2Of m ra s0 sp pc mx)
      cdp c.alloc (ovl (addDigits a b) c.digit 0) :=
    ArrFrm.init (Iv.sub_self _) (by rw [ovl_zero]; exact hsn.rc.arr)
  have hro := ro hP hI0
  have hdp := dp2 (s0 := s0) hP mx (by omega)
  have hrc : Ram pc 24 := by simpa [Layout.sizeofMpInt] using hP.gc.st
  refine Triple.seq (a_step ra v outp sp pa pb pc xp mn mx c.alloc c.used cdp _ (RO.of hP hF1.mono).code
    hcf (by omega)) ?_
  by_cases h0 : mn = 0
  · subst h0
    exact Triple.rmap (fun cf h => ⟨_, hI0, by rwa [writeLog_nil] at h⟩)
      (a0b_step ra v outp sp pa pb pc xp mx c.used cdp _ hro.code hrc hdp)
  have hrA := ramA hP; have hrB := ramB hP
  have hs := srcs hP (by omega) hI0
  have ho : OpFacts' (m2Of m ra s0 sp pc mx) pa pb adp bdp mn :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rb := by simpa [Layout.sizeofMpInt] using hP.gb.st
      adp_v := hs.1.dpv, bdp_v := hs.2.dpv
      ra_d := ⟨hrA.lo_ge, by have := hrA.hi_le; omega, by have := hrA.off; omega⟩
      rb_d := ⟨hrB.lo_ge, by have := hrB.hi_le; omega, by have := hrB.off; omega⟩ }
  refine Triple.seq ?_ (loop1 hP hmn hmx (by omega) 0 (by omega))
  exact Triple.rmap (fun cf h => ⟨_, hI0, by rwa [writeLog_nil] at h⟩)
    (a1b_step' ra v outp sp pa pb pc xp mn mx c.used cdp adp bdp _ hro.code hrc hdp ho (by omega) (by omega))

/-- From the entry to `225c`. -/
theorem phase1 (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Triple (At 0x8000219c#64 (entryL ra s0 sp pa pb pc) m v.keepR outp)
      (St m v outp sp pc cdp c ra s0 (max a.used b.used) 0x8000225c#64
        (j2L ra sp pc cdp c.used (min a.used b.used) (max a.used b.used) (xpOf a b pa pb) (min a.used b.used)
          (addCarryAt a b (min a.used b.used))) (ovl (addDigits a b) c.digit (min a.used b.used))) := by
  have hua := hP.sa.used_le; have hub := hP.sb.used_le
  have hal := hP.sa.alloc_lt; have hbl := hP.sb.alloc_lt; have := hP.sp_ge
  have hcd := hP.lay.disj (r := K.fr) (s := K.code)
  simp only [Iv.Disj, Disj, lay, Tom.Machine.Dst.lay] at hcd
  have ha0 := hP.srcA.mp1 hP.lay hP.rc (Frm.refl _ m)
  have hb0 := hP.srcB.mp1 hP.lay hP.rc (Frm.refl _ m)
  have hpf : ProFacts m sp pa pb a.used b.used :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rb := by simpa [Layout.sizeofMpInt] using hP.gb.st
      rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
      ua_v := by simpa [Layout.offUsed] using ha0.used
      ub_v := by simpa [Layout.offUsed] using hb0.used
      ua_lt := by omega
      ub_lt := by omega
      code_off := by omega }
  by_cases hle : a.used ≤ b.used
  · rw [show xpOf a b pa pb = pb by simp [xpOf, hle], Nat.min_eq_left hle, Nat.max_eq_right hle]
    exact Triple.seq (e0_step ra s0 v outp sp pa pb pc _ _ m hP.code hpf hle)
      (phase1b hP (Nat.min_eq_left hle).symm (Nat.max_eq_right hle).symm)
  · have hle' : b.used ≤ a.used := by omega
    rw [show xpOf a b pa pb = pa by simp [xpOf, hle], Nat.min_eq_right hle', Nat.max_eq_left hle']
    exact Triple.seq (e1_step ra s0 v outp sp pa pb pc _ _ m hP.code hpf (by omega))
      (phase1b hP (Nat.min_eq_right hle').symm (Nat.max_eq_left hle').symm)

/-- `x`'s digit `i` above `min`: the sum of both digits (the other is zero). -/
theorem dreadX (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) {M : Mem} (i : Nat)
    (hsa : SrcAt M pa adp a i) (hsb : SrcAt M pb bdp b i)
    (hi1 : min a.used b.used ≤ i) (hi2 : i < max a.used b.used) :
    DRead M (xdpOf a b adp bdp) i (a.digit i + b.digit i) := by
  have hua := hP.sa.used_le; have hub := hP.sb.used_le
  by_cases hle : a.used ≤ b.used
  · rw [hP.sa.high_zero i (by omega), Nat.zero_add, show xdpOf a b adp bdp = bdp by simp [xdpOf, hle]]
    exact dread hsb hP.sb (ramB hP) i (Nat.le_refl _) (by omega)
  · rw [hP.sb.high_zero i (by omega), Nat.add_zero, show xdpOf a b adp bdp = adp by simp [xdpOf, hle]]
    exact dread hsa hP.sa (ramA hP) i (Nat.le_refl _) (by omega)

/-- `x`'s struct and digit pointer. -/
theorem xfacts (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) {M : Mem} {i : Nat}
    (hsa : SrcAt M pa adp a i) (hsb : SrcAt M pb bdp b i) :
    XFacts M (xpOf a b pa pb) (xdpOf a b adp bdp) (max a.used b.used) := by
  have hua := hP.sa.used_le; have hub := hP.sb.used_le
  have hrA := ramA hP; have hrB := ramB hP
  by_cases hle : a.used ≤ b.used
  · simp only [xpOf, xdpOf, hle, if_true]
    exact { rx := by simpa [Layout.sizeofMpInt] using hP.gb.st
            xdp_v := hsb.dpv
            rx_d := ⟨hrB.lo_ge, by have := hrB.hi_le; omega, by have := hrB.off; omega⟩ }
  · simp only [xpOf, xdpOf, hle, if_false]
    exact { rx := by simpa [Layout.sizeofMpInt] using hP.ga.st
            xdp_v := hsa.dpv
            rx_d := ⟨hrA.lo_ge, by have := hrA.hi_le; omega, by have := hrA.off; omega⟩ }

/-- One loop-2 segment (back edge to `228c`, or the exit at `22ac`). -/
theorem l2_seg (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) (i : Nat) (h1 : min a.used b.used ≤ i)
    (hi : i < max a.used b.used) (pc' : BitVec 64)
    (hseg : ∀ M, CodeAt M sMpAddBase sMpAddCode → DRead M (xdpOf a b adp bdp) i (a.digit i + b.digit i) →
      CStore cdp i → Triple (At 0x8000228c#64 (l2L ra sp pc cdp c.used (min a.used b.used) (max a.used b.used)
        (xdpOf a b adp bdp) i (addCarryAt a b i)) M v.keepR outp)
      (At pc' (l2L ra sp pc cdp c.used (min a.used b.used) (max a.used b.used) (xdpOf a b adp bdp) (i + 1)
          ((a.digit i + b.digit i + addCarryAt a b i) / 268435456))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64
          ((a.digit i + b.digit i + addCarryAt a b i) % 268435456))]) v.keepR outp)) :
    Triple (St m v outp sp pc cdp c ra s0 (max a.used b.used) 0x8000228c#64
        (l2L ra sp pc cdp c.used (min a.used b.used) (max a.used b.used) (xdpOf a b adp bdp) i (addCarryAt a b i))
        (ovl (addDigits a b) c.digit i))
      (St m v outp sp pc cdp c ra s0 (max a.used b.used) pc'
        (l2L ra sp pc cdp c.used (min a.used b.used) (max a.used b.used) (xdpOf a b adp bdp) (i + 1)
          (addCarryAt a b (i + 1)))
        (ovl (addDigits a b) c.digit (i + 1))) := by
  have hroom := hP.room; have hal := hP.sc.alloc_lt
  refine ASt.store (fun M hI => ?_) (by omega)
    (by rw [addDigits_lt_max hP.sa hP.sb hi, radix_eq]) (by omega)
  have hs := srcs hP (by omega) hI
  have h := hseg M (ro hP hI).code (dreadX hP i hs.1 hs.2 h1 hi) (cstore_of hP (by omega))
  rwa [carry_succ] at h

/-- From `225c` to `22c4`. -/
theorem phase2 (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Triple (St m v outp sp pc cdp c ra s0 (max a.used b.used) 0x8000225c#64
        (j2L ra sp pc cdp c.used (min a.used b.used) (max a.used b.used) (xpOf a b pa pb) (min a.used b.used)
          (addCarryAt a b (min a.used b.used))) (ovl (addDigits a b) c.digit (min a.used b.used)))
      (St m v outp sp pc cdp c ra s0 (max a.used b.used) 0x800022c4#64
        (j3L ra sp pc cdp c.used (max a.used b.used) (addCarryAt a b (max a.used b.used)))
        (ovl (addDigits a b) c.digit (max a.used b.used))) := by
  have hua := hP.sa.used_le; have hub := hP.sb.used_le; have hroom := hP.room
  have hal := hP.sc.alloc_lt; have hrC := ramC hP
  by_cases he : min a.used b.used = max a.used b.used
  · rw [he]
    exact ASt.seg fun M hI => b0_step ra v outp sp pc cdp c.used _ _ _ _ M (ro hP hI).code rfl (by omega)
      (by have := hrC.hi_le; omega)
  have hlt : min a.used b.used < max a.used b.used := by omega
  refine Triple.seq (ASt.seg fun M hI => b2_step ra v outp sp pc cdp c.used _ _ _ (xdpOf a b adp bdp) _ M
    (ro hP hI).code (xfacts hP (srcs hP (by omega) hI).1 (srcs hP (by omega) hI).2) hlt (by omega)
    (by have := hrC.hi_le; omega)) ?_
  refine Triple.countup_from (lo := min a.used b.used) (fun i h1 hi => l2_seg hP i h1 (by omega) _
    fun M hc hx hs => l2_step ra v outp sp pc cdp c.used _ _ _ i _ _ M hc hx hs
      (addCarryAt_le_one hP.sa hP.sb i) hi (by have := hrC.hi_le; omega)) ?_ _ (Nat.le_refl _) hlt
  have h := l2_seg (s0 := s0) hP (max a.used b.used - 1) (by omega) (by omega) _ fun M hc hx hs =>
    l2e_step ra v outp sp pc cdp c.used _ _ _ (max a.used b.used - 1) _ _ M hc hx hs
      (addCarryAt_le_one hP.sa hP.sb _) (by omega) (by have := hrC.hi_le; omega)
  rw [show max a.used b.used - 1 + 1 = max a.used b.used by omega] at h
  exact Triple.seq h (ASt.seg fun M hI => l2t_step ra v outp sp pc cdp c.used _ _ _ _ M
    (ro hP hI).code hlt (by omega) (by have := hrC.hi_le; omega))

/-- The carry store's and the `olduse` test's facts. -/
theorem tail_of (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) {M : Mem} {f : Nat → Nat}
    (hI : ArrFrm (lay sp pc cdp c) .cD (m2Of m ra s0 sp pc (max a.used b.used)) M cdp c.alloc f) :
    TailFacts M pc cdp (max a.used b.used) := by
  have hroom := hP.room; have hal := hP.sc.alloc_lt
  have h0 := (snap (s0 := s0) hP (max a.used b.used) (by omega)).rc.used
  simp only [Layout.offUsed, Nat.add_zero] at h0
  exact { rc := by simpa [Layout.sizeofMpInt] using hP.gc.st, pc_al := hP.gc.st_al
          used_v := hI.fr.keep hP.lay (Reads.w4 (r := K.cS) (Iv.sub_pre (by decide))) h0
          st := cstore_of hP (by omega)
          disj := hP.lay.sub (r := K.cS) (s := K.cD) (Iv.sub_self _) (Iv.sub_elem (by omega))
          mx_lt := by omega }

/-- From `22c4` to `22e4`: store the carry; `memset` the digits from `max + 1`
to `olduse` if there are any. -/
theorem phase3 (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Triple (St m v outp sp pc cdp c ra s0 (max a.used b.used) 0x800022c4#64
        (j3L ra sp pc cdp c.used (max a.used b.used) (addCarryAt a b (max a.used b.used)))
        (ovl (addDigits a b) c.digit (max a.used b.used)))
      (St m v outp sp pc cdp c ra s0 (max a.used b.used) 0x800022e4#64 (j4L sp pc)
        (addDigits a b)) := by
  have hroom := hP.room; have hcu := hP.sc.used_le; have hal := hP.sc.alloc_lt; have hrC := ramC hP
  have hu := addCarryAt_le_one hP.sa hP.sb (max a.used b.used)
  have hz : ∀ j, max a.used b.used + 1 ≤ j → addDigits a b j = 0 := fun j hj => addDigits_high hP.sa hP.sb j hj
  have hfin : ∀ k, c.used ≤ k → max a.used b.used + 1 ≤ k → ∀ j, j < c.alloc →
      ovl (addDigits a b) c.digit k j = addDigits a b j := fun k hk hk' j hj => by
    simp only [ovl]
    split
    · rfl
    · rw [hP.sc.high_zero j (by omega), hz j (by omega)]
  have hst := fun pc' L' (h : ∀ M, CodeAt M sMpAddBase sMpAddCode → TailFacts M pc cdp (max a.used b.used) →
      Triple (At 0x800022c4#64 (j3L ra sp pc cdp c.used (max a.used b.used) (addCarryAt a b (max a.used b.used)))
        M v.keepR outp) (At pc' L' (writeLog M [(cdp + 4 * max a.used b.used, 4,
          BitVec.ofNat 64 (addCarryAt a b (max a.used b.used)))]) v.keepR outp)) =>
    ASt.store (m0 := m2Of m ra s0 sp pc (max a.used b.used)) (old := c.digit)
      (fun M hI => h M (ro hP hI).code (tail_of hP hI)) (by omega)
      (addDigits_max hP.sa hP.sb).symm (by omega)
  by_cases hou : c.used ≤ max a.used b.used + 1
  · exact Triple.rmap (fun cf ⟨M, hI, h⟩ => ⟨M, hI.congr (hfin _ hou (Nat.le_refl _)), h⟩)
      (hst _ _ fun M hc ht => c0_step ra v outp sp pc cdp c.used _ _ M hc ht hu hou)
  refine Triple.seq (hst _ _ fun M hc ht => c1_step ra v outp sp pc cdp c.used _ _ M hc ht hu (by omega)
    (by omega)) ?_
  intro cf ⟨M, hI, hat⟩
  have hro := ro hP hI
  have hms : Memset.Pre M (cdp + 4 * (max a.used b.used + 1)) 0 (4 * (c.used - (max a.used b.used + 1))) :=
    { byte := by decide, code := hro.code_ms
      ram := ⟨by have := hrC.lo_ge; omega, by have := hrC.hi_le; omega, by have := hrC.off; omega⟩
      code_off := by
        have : memsetCode.length = 55 := rfl
        rw [this]
        exact hP.lay.sub (r := K.cD) (s := K.ms)
          (I := ⟨cdp + 4 * (max a.used b.used + 1), 4 * (c.used - (max a.used b.used + 1))⟩)
          ⟨by simp [lay, Tom.Machine.Dst.lay], by simp only [lay, Tom.Machine.Dst.lay]; omega⟩ (Iv.sub_self _) }
  refine Triple.rmap ?_ (memset_call ra v outp sp pc cdp c.used _ M hro.code hms) cf hat
  intro cf ⟨M', hat', hpost⟩
  exact ⟨M', (hI.fill (k := c.used) (by omega) hcu hpost.fill hpost.frame fun j h1 _ => hz j h1).congr
    (hfin _ (Nat.le_refl _) (by omega)), hat'⟩

/-- From `22e4` to the return: `mp_clamp(c)` and the epilogue. -/
theorem phase4 (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Triple (St m v outp sp pc cdp c ra s0 (max a.used b.used) 0x800022e4#64 (j4L sp pc)
        (addDigits a b))
      (Ret m v outp sp pc cdp a b c ra s0) := by
  intro cf ⟨M, hI, hat⟩
  have hroom := hP.room; have hal := hP.sc.alloc_lt; have := hP.sp_ge; have hS := hP.lay
  have hsn := snap (s0 := s0) hP (max a.used b.used) (by omega)
  have hro := ro hP hI
  have hdig := cMid_digit_eq (c := c) hP.sa hP.sb hroom
  have hpre : Clamp.Pre M pc cdp (cMid a b c) :=
    { repr := hsn.rc.of_hdr (fun x h1 h2 => (Frm.on (r := K.cS) hS hI.fr) x ⟨h1, h2⟩)
        (by rw [hdig]; exact hI.arr) rfl rfl rfl
      shape := { len := by simp [cMid]
                 used_le := by simp only [cMid]; omega
                 alloc_lt := hal
                 digit_lt := fun i => by rw [hdig]; exact addDigits_lt hP.sa hP.sb i
                 high_zero := fun i hi => by
                   rw [hdig]; exact addDigits_high hP.sa hP.sb i (by simpa [cMid] using hi) }
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
  have hF' := (f2 (s0 := s0) hP (max a.used b.used)).trans hF
  refine Triple.rmap (fun cf h => ⟨c', _, h, ?_⟩)
    (r_step ra s0 v outp sp M' (RO.of hP hF'.mono).code hff) cf hat'
  have hcp := hpost.clamp
  exact { repr := hpost.repr
          sadd := { alloc := hcp.alloc
                    len := by rw [hcp.digits]; simp [cMid]
                    digit := by rw [hcp.digit, hdig]
                    used := by rw [hcp.used, hdig]; rfl
                    sign := by rw [hcp.sign]; rfl }
          frame := hF'.mono }

end

/-- **`s_mp_add` on the machine, for any destination.** From its entry with
`Pre` (each operand its own `mp_int` or `c` itself), the machine returns to
`ra` with `a0 = MP_OKAY`, `sp`, `s0` and the callee-saved registers
restored, `c'` at `c` with `SAddPost a b c c'`, and memory changed only in
the stack frame and `c`'s struct and digits. -/
theorem correct {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat}
    {a b c : MpInt} {ra s0 : BitVec 64} (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Triple (At 0x8000219c#64 (entryL ra s0 sp pa pb pc) m v.keepR outp)
      (Ret m v outp sp pc cdp a b c ra s0) :=
  Triple.seq (phase1 hP) (Triple.seq (phase2 hP) (Triple.seq (phase3 hP) (phase4 hP)))

end Tom.Machine.Fn.SAdd.AnyDst
