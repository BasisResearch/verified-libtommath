import Tom.Machine.Fn.MulD
import Tom.Machine.Kit.Frame
import Tom.Machine.Fn.Memset
import Tom.Machine.Fn.Clamp
import Tom.Spec.Mul

/-!
# `mp_mul_d` on the machine: the loop and the tail, for any placement

From the loop head to the return, over an in-place array state (`ASt`) on
`c`'s digits under any region names `ρ`, `wD` (`wD`'s interval is `c`'s digit
array). What the code reads is supplied by named hypotheses (`LoopH`,
`TailH`), so the same lemmas serve `mp_mul_d(a, b, c)` with distinct operands
(`Fn/MulDMain.lean`, regions `Api/Two.lean`) and `mp_mul_d(a, b, a)` in place
(regions `Api/Un.lean`), where `a`'s digit `i` is read from the array state
itself (`ovl … a.digit i` at `i`).

The row: digit `i` is `mulDDigit a b i`, the carry into it `W a b i =
combaW (mulDCol a b) i` (`Tom/Spec/Mul.lean`).
-/

namespace Tom.Machine.Fn.MulD

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api.Libgcc

/-- The carry into digit `i`. -/
abbrev W (a : MpInt) (b i : Nat) : Nat := combaW (mulDCol a b) i

theorem W_succ (a : MpInt) (b i : Nat) : (a.digit i * b + W a b i) / 268435456 = W a b (i + 1) := by
  simp only [W, combaW, mulDCol, radix_eq, Nat.add_comm]

theorem G_lt {a : MpInt} {b i : Nat} (hi : i < a.used) :
    (a.digit i * b + W a b i) % 268435456 = mulDDigit a b i := by
  simp only [mulDDigit, if_pos hi, combaD, mulDCol, W, radix_eq, Nat.add_comm]

theorem G_top (a : MpInt) (b : Nat) : W a b a.used = mulDDigit a b a.used := by
  simp [mulDDigit, W]

theorem G_high {a : MpInt} {b j : Nat} (hj : a.used < j) : mulDDigit a b j = 0 := by
  simp [mulDDigit, show ¬ j < a.used by omega, show j ≠ a.used by omega]

theorem prod_lt {x y : Nat} (hx : x < radix) (hy : y < radix) : x * y < 2 ^ 56 := by
  have := Nat.mul_lt_mul'' hx hy
  simp only [radix, Layout.digitBits] at this; omega

/-- The join points: `c`'s digits hold `f`, nothing else changed since `m0`. -/
abbrev St {ι : Type} (ρ : ι → Iv) (wD : ι) (m0 : Mem) (cdp al : Nat) (v : Abi) (outp : Array String) :=
  ASt ρ wD m0 cdp al (kMD v) outp

section loop
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {wD : ι} {m0 : Mem} {v : Abi} {outp : Array String}
  {sp pa b pc cdp ou adp al : Nat} {a : MpInt} {old : Nat → Nat}

/-- What the loop reads: `a`'s digit `i` at iteration `i` (`rd`), the code and
`a->used` in every array state (`ru`). -/
structure LoopH (ρ : ι → Iv) (wD : ι) (m0 : Mem) (pa adp cdp al : Nat) (a : MpInt) (b : Nat)
    (old : Nat → Nat) : Prop where
  sa : a.Shape
  hb : b < radix
  room : a.used + 1 ≤ al
  rd : ∀ M i, i < a.used → ArrFrm ρ wD m0 M cdp al (ovl (mulDDigit a b) old i) → DRead M adp i (a.digit i)
  ru : ∀ M f, ArrFrm ρ wD m0 M cdp al f → Img M ∧ UFacts M pa a.used
  st : ∀ i, i < al → SFacts cdp i

/-- One iteration: `a->dp[i] * b` by `__muldi3`, plus the carry; the low digit
into `c->dp[i]`; the last segment (back edge or exit) is `hlast`. -/
theorem iter (h : LoopH ρ wD m0 pa adp cdp al a b old) (i : Nat) (hi : i < a.used) (pc' : BitVec 64)
    (L' : GRegs)
    (hlast : ∀ M, Img M → UFacts M pa a.used →
      Triple (At 0x80001a94#64 (b1L sp pa b pc cdp ou adp i (W a b i) (a.digit i * b + W a b i)) M (kMD v) outp)
        (At pc' L' (writeLog M []) (kMD v) outp)) :
    Triple (St ρ wD m0 cdp al v outp 0x80001a74#64 (hL sp pa b pc cdp ou adp i (W a b i))
        (ovl (mulDDigit a b) old i))
      (St ρ wD m0 cdp al v outp pc' L' (ovl (mulDDigit a b) old (i + 1))) := by
  intro cf ⟨M, hA, hat⟩
  have hd := h.rd M i hi hA
  have ⟨himg, _⟩ := h.ru M _ hA
  have hW : W a b i < 268435456 := by
    have := mulD_W_lt h.sa h.hb i; simp only [radix, Layout.digitBits] at this; exact this
  have hp := prod_lt (h.sa.digit_lt i) h.hb
  have hroom := h.room
  have hA1 := hA.step (i := i) (v := (a.digit i * b + W a b i) % 268435456) (by omega) (by omega)
    (G_lt (b := b) hi)
  have ⟨himg1, hu1⟩ := h.ru _ _ hA1
  refine Triple.rmap (fun cf h => ⟨_, hA1, h⟩) ?_ cf hat
  refine Triple.seq (a_step v outp sp pa b pc cdp ou adp i _ _ M himg.mpMulD hd) ?_
  refine Triple.seq (muldi3_call (pc := 0x80001a80#64) (w := 0x2c1150ef#32) (imm := 0x015ac0#21)
    (Lk := kL sp pa b pc cdp ou adp i (W a b i))
    (L2 := bL sp pa b pc cdp ou adp i (W a b i) (a.digit i * b)) himg himg.mpMulD (by decide +kernel)
    (by decide) (by decide) (fun s h1 h2 h3 => decodeW s h1 h2 h3)
    ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide) (by decide)
    (fun p hp => hp) (by simp [aL, kL, keysG]) (by simp [kMD, keysG])
    (by unfold KeepOK; rw [show keysG (kL sp pa b pc cdp ou adp i (W a b i) ++ kMD v) =
          [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 3, 4, 25, 26, 27] from rfl]; decide)
    (fun p hp => List.mem_cons_of_mem _ (by rw [ofNat_mul_ofNat]; exact hp))) ?_
  refine Triple.seq (b1_step v outp sp pa b pc cdp ou adp i _ _ _ himg.mpMulD (h.st i (by omega))
    (by omega)) ?_
  exact hlast _ himg1 hu1

/-- **The digit loop**, from iteration `i` to the exit at `1ab4`. -/
theorem loop (h : LoopH ρ wD m0 pa adp cdp al a b old) (hua : 1 ≤ a.used) :
    ∀ i, i < a.used → Triple (St ρ wD m0 cdp al v outp 0x80001a74#64 (hL sp pa b pc cdp ou adp i (W a b i))
        (ovl (mulDDigit a b) old i))
      (St ρ wD m0 cdp al v outp 0x80001ab4#64 (eL sp pa b pc cdp ou (a.used - 1) (W a b a.used))
        (ovl (mulDDigit a b) old a.used)) := by
  have hal := h.sa.alloc_lt; have hul := h.sa.used_le
  refine Triple.countup (fun i hi => iter h i (by omega) _ _ fun M hc hu => ?_) ?_
  · have := b_step v outp sp pa b pc cdp ou adp i (W a b i) (a.digit i * b + W a b i) a.used M hc.mpMulD hu
      (by have : W a b i < 268435456 := by
            have := mulD_W_lt h.sa h.hb i; simp only [radix, Layout.digitBits] at this; exact this
          have := prod_lt (h.sa.digit_lt i) h.hb
          omega) hi
    rwa [W_succ] at this
  · have h1 := iter (sp := sp) (pc := pc) (ou := ou) (v := v) (outp := outp) h (a.used - 1) (by omega) _ _
      fun M hc hu => by
        have := be_step v outp sp pa b pc cdp ou adp (a.used - 1) (W a b (a.used - 1))
          (a.digit (a.used - 1) * b + W a b (a.used - 1)) a.used M hc.mpMulD hu
          (by have : W a b (a.used - 1) < 268435456 := by
                have := mulD_W_lt h.sa h.hb (a.used - 1); simp only [radix, Layout.digitBits] at this
                exact this
              have := prod_lt (h.sa.digit_lt (a.used - 1)) h.hb
              omega) (by omega)
        rwa [W_succ, show a.used - 1 + 1 = a.used by omega] at this
    rwa [show a.used - 1 + 1 = a.used by omega] at h1

end loop

/-! ## The calls after the loop -/

/-- The callee-saved registers `memset`/`mp_clamp` see (`dL`'s `s` registers). -/
def cAbi (v : Abi) (sp pa b pc cdp ou ua u : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 80), s0 := BitVec.ofNat 64 u,
           s := { v.s with s2 := BitVec.ofNat 64 (cdp + 4 * ua), s3 := BitVec.ofNat 64 pa,
                           s4 := BitVec.ofNat 64 b, s6 := BitVec.ofNat 64 pc, s8 := BitVec.ofNat 64 ou } }

/-- `memset(c->dp + a->used + 1, 0, 4 (olduse - a->used - 1))` at `1adc`, back at `1ae0`. -/
theorem memset_call (v : Abi) (outp : Array String) (sp pa b pc cdp ou ua u : Nat) (M : Mem)
    (hc : CodeAt M mpMulDBase mpMulDCode) (hP : Memset.Pre M (cdp + 4 * ua + 4) 0 (4 * (ou - (ua + 1)))) :
    Triple (At 0x80001adc#64 (msL v sp pa b pc cdp ou ua u) M (kMD v) outp)
      (fun c => ∃ M', At 0x80001ae0#64 (dL v sp pa b pc cdp ou ua u) M' (kMD v) outp c ∧
        Memset.Post M (cdp + 4 * ua + 4) (4 * (ou - (ua + 1))) 0#8 M') :=
  jal_call (pc := 0x80001adc#64) (w := 0x0c9070ef#32) (imm := 0x0078c8#21) (Larg := msL v sp pa b pc cdp ou ua u)
    (L0 := Memset.entryL 0x80001ae0#64 (cdp + 4 * ua + 4) 0#64 (4 * (ou - (ua + 1))))
    (K := (cAbi v sp pa b pc cdp ou ua u).keep)
    hc (by decide +kernel) (by decide) (by decide) (fun s h1 h2 h3 => decodeW s h1 h2 h3)
    ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide) (by decide) (fun p hp => hp)
    (by simp [msL, dL, keysG]) (by simp [kMD, keysG])
    (by simp [Memset.entryL, msL, Sail.BitVec.addInt])
    (by simp [Abi.keep, cAbi, sKeepL, msL, dL, kMD])
    (Triple.rmap (fun c ⟨M', hat, hpost⟩ => ⟨M', hat.reshape (by simp [dL, Abi.keep, cAbi, sKeepL])
        (by simp [kMD, Abi.keep, cAbi, sKeepL]), hpost⟩)
      (Memset.correct_zero 0x80001ae0#64 (cAbi v sp pa b pc cdp ou ua u) outp M _ _ (by decide) hP))

/-- `mp_clamp(c)` at `1af0`, back at `1af4`. -/
theorem clamp_call (v : Abi) (outp : Array String) (sp pa b pc cdp ou ua u : Nat) (cm : MpInt) (M : Mem)
    (hc : CodeAt M mpMulDBase mpMulDCode) (hP : Clamp.Pre M pc cdp cm) :
    Triple (At 0x80001af0#64 (clL v sp pa b pc cdp ou ua u) M (kMD v) outp)
      (fun c => ∃ a' M', At 0x80001af4#64 (fL v sp) M' (kMD v) outp c ∧ Clamp.Post M pc cdp cm a' M') :=
  jal_call (pc := 0x80001af0#64) (w := 0x4e8030ef#32) (imm := 0x0034e8#21) (Larg := clL v sp pa b pc cdp ou ua u)
    (L0 := [(1, 0x80001af4#64), (10, BitVec.ofNat 64 pc)])
    (K := (cAbi v sp pa b pc cdp ou ua u).keep)
    hc (by decide +kernel) (by decide) (by decide) (fun s h1 h2 h3 => decodeW s h1 h2 h3)
    ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide) (by decide) (fun p hp => hp)
    (by simp [clL, dL, keysG]) (by simp [kMD, keysG])
    (by simp [clL, Sail.BitVec.addInt])
    (by simp [Abi.keep, cAbi, sKeepL, clL, dL, kMD])
    (Triple.rmap (fun c ⟨a', M', hat, hpost⟩ => ⟨a', M', hat.reshape (by simp [fL, Abi.keep, cAbi, sKeepL])
        (by simp [kMD, Abi.keep, cAbi, sKeepL]), hpost⟩)
      (Clamp.correct 0x80001af4#64 (cAbi v sp pa b pc cdp ou ua u) outp pc cdp cm M (by decide) hP))

/-! ## After the loop -/

section tail
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {wD : ι} {m0 : Mem} {v : Abi} {outp : Array String}
  {sp pa b pc cdp ou : Nat} {a c0 : MpInt} {old : Nat → Nat} {ra s0 : BitVec 64}

/-- What the code after the loop reads, and where things are. `m0` is the
snapshot at the loop entry; `c0` is `c` there (`sign := a->sign`). -/
structure TailH (ρ : ι → Iv) (wD : ι) (m0 : Mem) (ra s0 : BitVec 64) (v : Abi) (sp pa pc cdp ou : Nat)
    (a : MpInt) (b : Nat) (c0 : MpInt) (old : Nat → Nat) : Prop where
  sa : a.Shape
  hb : b < radix
  hw : ρ wD = ⟨cdp, 4 * c0.alloc⟩
  room : a.used + 1 ≤ c0.alloc
  al_lt : c0.alloc < 2 ^ 31
  ou_le : ou ≤ c0.alloc
  old_hz : ∀ j, ou ≤ j → old j = 0
  rc0 : MpAt m0 pc cdp c0
  gc : MpGeom pc cdp c0.alloc
  csign : c0.sign = a.sign
  ua_v : bytesT4 m0 pa = BitVec.ofNat 32 a.used
  ra_ : Ram pa 4
  img : Img m0
  sv : EFacts m0 ra s0 v sp
  a_d : pa + 4 ≤ cdp ∨ cdp + 4 * c0.alloc ≤ pa
  k_d : sp ≤ cdp ∨ cdp + 4 * c0.alloc ≤ sp - 80
  k_c : sp ≤ pc ∨ pc + 24 ≤ sp - 80
  t_d : textBase + textLen ≤ cdp ∨ cdp + 4 * c0.alloc ≤ textBase
  t_c : textBase + textLen ≤ pc ∨ pc + 24 ≤ textBase

/-- Outside `c`'s digits, an array state agrees with the snapshot. -/
theorem _root_.Tom.Machine.ArrFrm.out {M : Mem} {al : Nat} {f : Nat → Nat} (hA : ArrFrm ρ wD m0 M cdp al f)
    (hw : ρ wD = ⟨cdp, 4 * al⟩) {x : Nat} (hx : x < cdp ∨ cdp + 4 * al ≤ x) : M[x]? = m0[x]? :=
  hA.fr x (by simp only [InAny, Iv.In, hw, or_false]; omega)

theorem img_of {m M : Mem} (h : Img m) (hs : ∀ x, textBase ≤ x → x < textBase + textLen → M[x]? = m[x]?) : Img M :=
  Img.of_text h hs

theorem TailH.imgA (h : TailH ρ wD m0 ra s0 v sp pa pc cdp ou a b c0 old) {M : Mem} {f : Nat → Nat}
    (hA : ArrFrm ρ wD m0 M cdp c0.alloc f) : Img M :=
  img_of h.img fun x h1 h2 => hA.out h.hw (by have := h.t_d; omega)

theorem TailH.uA (h : TailH ρ wD m0 ra s0 v sp pa pc cdp ou a b c0 old) {M : Mem} {f : Nat → Nat}
    (hA : ArrFrm ρ wD m0 M cdp c0.alloc f) : UFacts M pa a.used :=
  { ra_ := h.ra_, ua_lt := by have := h.sa.used_le; have := h.sa.alloc_lt; omega
    ua_v := by rw [bytesT4_congr fun x h1 h2 => hA.out h.hw (by have := h.a_d; omega)]; exact h.ua_v }

theorem TailH.ramD (h : TailH ρ wD m0 ra s0 v sp pa pc cdp ou a b c0 old) : Ram cdp (4 * c0.alloc) := by
  simpa [Layout.sizeofDigit] using h.gc.ds

theorem TailH.sF (h : TailH ρ wD m0 ra s0 v sp pa pc cdp ou a b c0 old) {i : Nat} (hi : i < c0.alloc) :
    SFacts cdp i :=
  have hr := h.ramD
  { rc := ⟨by have := hr.lo_ge; omega, by have := hr.hi_le; omega, by have := hr.off; omega⟩
    al := h.gc.ds_al
    code_off := by have := h.t_d; simp only [mpMulDBase, textBase, textLen] at *; omega }

/-- The loop's facts from the tail's, given `a`'s digit reads. -/
theorem TailH.loopH (h : TailH ρ wD m0 ra s0 v sp pa pc cdp ou a b c0 old) {adp : Nat}
    (hrd : ∀ M i, i < a.used → ArrFrm ρ wD m0 M cdp c0.alloc (ovl (mulDDigit a b) old i) →
      DRead M adp i (a.digit i)) : LoopH ρ wD m0 pa adp cdp c0.alloc a b old :=
  { sa := h.sa, hb := h.hb, room := h.room, rd := hrd
    ru := fun _ _ hA => ⟨h.imgA hA, h.uA hA⟩
    st := fun _ hi => h.sF hi }

/-- `mp_clamp`'s argument: `c0` with the row's digits and `used := a->used + 1`. -/
def cMid (a : MpInt) (b : Nat) (c0 : MpInt) : MpInt :=
  { c0 with used := a.used + 1, digits := (List.range c0.alloc).map (mulDDigit a b) }

theorem cMid_digit {a : MpInt} {b : Nat} {c0 : MpInt} (ha : a.Shape) (hroom : a.used + 1 ≤ c0.alloc) :
    (cMid a b c0).digit = mulDDigit a b := by
  funext i
  simp only [cMid, MpInt.digit, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < c0.alloc
  · simp [h]
  · simp [h, G_high (a := a) (b := b) (j := i) (by omega)]

/-- What `mp_mul_d`'s tail leaves: `c'` at `c`, `MulDPost`, memory as at `m0`
outside `c`'s digits and struct. -/
def RetC (m0 : Mem) (v : Abi) (outp : Array String) (sp pc cdp : Nat) (a : MpInt) (b : Nat) (c0 : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra (rL ra s0 v sp) M (kMD v) outp cf ∧ MpAt M pc cdp c' ∧ MulDPost a b c0 c' ∧
    ∀ x, (x < cdp ∨ cdp + 4 * c0.alloc ≤ x) → (x < pc ∨ pc + 24 ≤ x) → M[x]? = m0[x]?

/-- From the join `1ac4` to `1ae0`: the last carry, and `memset` up to `olduse`. -/
theorem tailJ (h : TailH ρ wD m0 ra s0 v sp pa pc cdp ou a b c0 old) :
    Triple (St ρ wD m0 cdp c0.alloc v outp 0x80001ac4#64 (jL v sp pa b pc cdp ou a.used (W a b a.used))
        (ovl (mulDDigit a b) old a.used))
      (St ρ wD m0 cdp c0.alloc v outp 0x80001ae0#64 (dL v sp pa b pc cdp ou a.used (W a b a.used))
        (mulDDigit a b)) := by
  have hroom := h.room; have hal := h.al_lt; have hou := h.ou_le
  have hW : W a b a.used < 268435456 := by
    have := mulD_W_lt h.sa h.hb a.used; simp only [radix, Layout.digitBits] at this; exact this
  have hJ : JFacts cdp a.used ou :=
    have hs := h.sF (i := a.used) (by omega)
    { rc := hs.rc, al := hs.al, code_off := hs.code_off, ua_lt := by omega, ou_lt := by omega }
  by_cases h0 : ou ≤ a.used + 1
  · refine Triple.rmap (fun cf ⟨M, hA, hat⟩ => ⟨M, hA.congr fun j hj => ?_, hat⟩)
      (ASt.store (fun M hA => j0_step v outp sp pa b pc cdp ou a.used _ M (h.imgA hA).mpMulD hJ h0)
        (by omega) (G_top a b) (by omega))
    simp only [ovl]; split
    · rfl
    · rw [h.old_hz j (by omega), G_high (by omega)]
  refine Triple.seq (ASt.store (fun M hA => j1_step v outp sp pa b pc cdp ou a.used _ M (h.imgA hA).mpMulD hJ
    (by omega)) (by omega) (G_top a b) (by omega)) ?_
  intro cf ⟨M, hA, hat⟩
  have hr := h.ramD
  have hms : Memset.Pre M (cdp + 4 * a.used + 4) 0 (4 * (ou - (a.used + 1))) :=
    { byte := by decide, code := (h.imgA hA).memset
      ram := ⟨by have := hr.lo_ge; omega, by have := hr.hi_le; omega, by have := hr.off; omega⟩
      code_off := by
        have : memsetCode.length = 55 := rfl
        rw [this]; have := h.t_d; simp only [memsetBase, textBase, textLen] at *; omega }
  refine Triple.rmap (fun cf ⟨M', hat', hpost⟩ => ⟨M', (hA.fill (k := ou) (by omega) hou
      (fun t ht => by
        have := hpost.fill t (by omega)
        rwa [show cdp + 4 * a.used + 4 + t = cdp + 4 * (a.used + 1) + t by omega] at this)
      (fun x hx => hpost.frame x (by omega)) (fun j h1 _ => G_high (by omega))).congr fun j hj => ?_, hat'⟩)
    (memset_call v outp sp pa b pc cdp ou a.used _ M (h.imgA hA).mpMulD hms) cf hat
  simp only [ovl]; split
  · rfl
  · rw [h.old_hz j (by omega), G_high (by omega)]

/-- From `1ae0` to the return: `c->used := a->used + 1`, `mp_clamp(c)`, the epilogue. -/
theorem tailD (h : TailH ρ wD m0 ra s0 v sp pa pc cdp ou a b c0 old) :
    Triple (St ρ wD m0 cdp c0.alloc v outp 0x80001ae0#64 (dL v sp pa b pc cdp ou a.used (W a b a.used))
        (mulDDigit a b))
      (RetC m0 v outp sp pc cdp a b c0 ra s0) := by
  intro cf ⟨M, hA, hat⟩
  have hroom := h.room; have hal := h.al_lt
  have hst := h.gc.st; have hk := h.k_c; have htc := h.t_c
  simp only [Layout.sizeofMpInt] at hst
  have hu := h.uA hA
  have hd : DFacts M pa pc a.used :=
    { ra_ := hu.ra_, rc := ⟨hst.lo_ge, by have := hst.hi_le; omega, by have := hst.off; omega⟩
      pc_al := h.gc.st_al, ua_v := hu.ua_v, ua_lt := by omega
      code_c := by simp only [mpMulDBase, textBase, textLen] at *; omega }
  have hdig := cMid_digit (b := b) h.sa hroom
  -- `c`'s struct is as at `m0`
  have hS : ∀ x, pc ≤ x → x < pc + 24 → M[x]? = m0[x]? := fun x h1 h2 =>
    hA.out h.hw (by have := h.gc.disj; simp only [Layout.sizeofMpInt, Layout.sizeofDigit] at this; omega)
  have hd0 : ArrAt M cdp c0.alloc ({ cMid a b c0 with used := c0.used } : MpInt).digit := by
    show ArrAt M cdp c0.alloc (cMid a b c0).digit
    rw [hdig]; exact hA.arr
  have hrc : MpAt M pc cdp { cMid a b c0 with used := c0.used } := h.rc0.of_hdr hS hd0 rfl rfl rfl
  have hpre : Clamp.Pre (writeLog M [(pc, 4, BitVec.ofNat 64 (a.used + 1))]) pc cdp (cMid a b c0) :=
    { repr := hrc.set_used h.gc _ (by omega)
      shape := { len := by simp [cMid]
                 used_le := hroom
                 alloc_lt := hal
                 digit_lt := fun i => by rw [hdig]; exact mulDDigit_lt h.sa h.hb i
                 high_zero := fun i hi => by rw [hdig]; exact G_high (by simp only [cMid] at hi; omega) }
      geom := h.gc
      code := (img_of (h.imgA hA) fun x h1 h2 => writeLog_out _ _ _ (by simp [OutL]; omega)).mpClamp
      code_off := by simp only [mpClampBase, textBase, textLen] at *; omega }
  refine Triple.seq (d_step v outp sp pa b pc cdp ou a.used _ M (h.imgA hA).mpMulD hd)
    (Triple.seq (clamp_call v outp sp pa b pc cdp ou a.used _ _ _
      (img_of (h.imgA hA) fun x h1 h2 => writeLog_out _ _ _ (by simp [OutL]; omega)).mpMulD hpre) ?_) cf hat
  intro cf ⟨c', M', hat', hpost⟩
  -- memory off `c`'s digits and struct is as at `m0`
  have hfr : ∀ x, (x < cdp ∨ cdp + 4 * c0.alloc ≤ x) → (x < pc ∨ pc + 24 ≤ x) → M'[x]? = m0[x]? :=
    fun x h1 h2 => by
      rw [hpost.frame x (by omega), writeLog_out _ _ _ (by simp [OutL]; omega)]
      exact hA.out h.hw h1
  have hkd := h.k_d
  have hrd : ∀ k, sp - 80 ≤ k → k + 8 ≤ sp → bytesT8 M' k = bytesT8 m0 k := fun k h1 h2 =>
    bytesT8_congr fun x h3 h4 => hfr x (by omega) (by omega)
  have hsv := h.sv
  have := hsv.sp_ge
  have hef : EFacts M' ra s0 v sp :=
    { rs := hsv.rs, sp_al := hsv.sp_al, sp_ge := hsv.sp_ge, ra_al := hsv.ra_al
      s0_v := by rw [hrd _ (by omega) (by omega)]; exact hsv.s0_v
      s2_v := by rw [hrd _ (by omega) (by omega)]; exact hsv.s2_v
      s8_v := by rw [hrd _ (by omega) (by omega)]; exact hsv.s8_v
      ra_v := by rw [hrd _ (by omega) (by omega)]; exact hsv.ra_v
      s3_v := by rw [hrd _ (by omega) (by omega)]; exact hsv.s3_v
      s4_v := by rw [hrd _ (by omega) (by omega)]; exact hsv.s4_v
      s6_v := by rw [hrd _ (by omega) (by omega)]; exact hsv.s6_v }
  have himg' : Img M' := img_of h.img fun x h1 h2 => hfr x (by have := h.t_d; omega) (by omega)
  refine Triple.rmap (fun cf hat'' => ⟨c', _, hat'', hpost.repr, ?_, hfr⟩) (e_step ra s0 v outp sp M' himg'.mpMulD hef) cf hat'
  have hcp := hpost.clamp
  exact { alloc := hcp.alloc
          len := by rw [hcp.digits]; simp [cMid]
          digit := by rw [hcp.digit, hdig]
          used := by rw [hcp.used, hdig]; rfl
          sign := by rw [hcp.sign]; simp only [cMid, h.csign] }

/-- **The tail**: from the join to the return. -/
theorem tail (h : TailH ρ wD m0 ra s0 v sp pa pc cdp ou a b c0 old) :
    Triple (St ρ wD m0 cdp c0.alloc v outp 0x80001ac4#64 (jL v sp pa b pc cdp ou a.used (W a b a.used))
        (ovl (mulDDigit a b) old a.used))
      (RetC m0 v outp sp pc cdp a b c0 ra s0) :=
  Triple.seq (tailJ h) (tailD h)

end tail

theorem CFacts.of_agree {M M' : Mem} {v : Abi} {sp : Nat} (h : CFacts M v sp)
    (hs : ∀ x, sp - 80 ≤ x → x < sp → M'[x]? = M[x]?) : CFacts M' v sp :=
  have := h.sp_ge
  have hr : ∀ k, sp - 80 ≤ k → k + 8 ≤ sp → bytesT8 M' k = bytesT8 M k := fun k h1 h2 =>
    bytesT8_congr fun x h3 h4 => hs x (by omega) (by omega)
  { rs := h.rs, sp_al := h.sp_al, sp_ge := h.sp_ge
    s1_v := (hr _ (by omega) (by omega)).trans h.s1_v
    s5_v := (hr _ (by omega) (by omega)).trans h.s5_v
    s7_v := (hr _ (by omega) (by omega)).trans h.s7_v }

/-! ## The prologue -/

/-- The memories after the prologue's stores. -/
def m1Of (m : Mem) (ra : BitVec 64) (v : Abi) (sp : Nat) : Mem := writeLog m (log1 ra v sp)
def m2Of (m : Mem) (ra s0 : BitVec 64) (v : Abi) (sp : Nat) : Mem := writeLog (m1Of m ra v sp) (log2 s0 v sp)
def m3Of (m : Mem) (ra s0 : BitVec 64) (v : Abi) (sp pc sa : Nat) : Mem :=
  writeLog (m2Of m ra s0 v sp) [(pc + 8, 4, BitVec.ofNat 64 sa)]
def m4Of (m : Mem) (ra s0 : BitVec 64) (v : Abi) (sp pc sa : Nat) : Mem := writeLog (m3Of m ra s0 v sp pc sa) (log3 v sp)
def m5Of (m : Mem) (ra s0 : BitVec 64) (v : Abi) (sp pc sa : Nat) : Mem := writeLog (m4Of m ra s0 v sp pc sa) (log4 v sp)

/-- What the prologue reads, on the memories it reads them from. -/
structure ProH (m : Mem) (ra s0 : BitVec 64) (v : Abi) (sp pa adp pc cdp ou : Nat) (a : MpInt) (b al : Nat) :
    Prop where
  c1 : CodeAt m mpMulDBase mpMulDCode
  c2 : CodeAt (m1Of m ra v sp) mpMulDBase mpMulDCode
  c3 : CodeAt (m2Of m ra s0 v sp) mpMulDBase mpMulDCode
  c4 : CodeAt (m3Of m ra s0 v sp pc a.sign) mpMulDBase mpMulDCode
  c5 : CodeAt (m4Of m ra s0 v sp pc a.sign) mpMulDBase mpMulDCode
  p1 : P1Facts m sp pa pc a.used al
  k : KFacts sp
  p2 : P2Facts (m2Of m ra s0 v sp) pa pc a.sign ou cdp
  p3 : P3Facts (m4Of m ra s0 v sp pc a.sign) pa adp
  hb : b < 2 ^ 32

section pro
variable {m : Mem} {ra s0 : BitVec 64} {v : Abi} {outp : Array String} {sp pa adp pc cdp ou b al : Nat}
  {a : MpInt}

/-- `a->used = 0`: to the join. -/
theorem pro_z (h : ProH m ra s0 v sp pa adp pc cdp ou a b al) (h0 : a.used = 0) :
    Triple (At 0x800019fc#64 (entL ra s0 v sp pa b pc) m (kMD v) outp)
      (At 0x80001ac4#64 (jL v sp pa b pc cdp ou 0 0) (m3Of m ra s0 v sp pc a.sign) (kMD v) outp) := by
  have hp1 := h.p1
  rw [h0] at hp1
  exact Triple.seq (p1_step ra s0 v outp sp pa b pc 0 al m h.c1 hp1)
    (Triple.seq (p2_step ra s0 v outp sp pa b pc 0 _ h.c2 h.k)
      (p2z_step ra s0 v outp sp pa b pc a.sign ou cdp _ h.c3 h.p2))

/-- `a->used > 0`: to the loop head. -/
theorem pro_p (h : ProH m ra s0 v sp pa adp pc cdp ou a b al) (h0 : 0 < a.used) :
    Triple (At 0x800019fc#64 (entL ra s0 v sp pa b pc) m (kMD v) outp)
      (At 0x80001a74#64 (hL sp pa b pc cdp ou adp 0 0) (m5Of m ra s0 v sp pc a.sign) (kMD v) outp) :=
  Triple.seq (p1_step ra s0 v outp sp pa b pc a.used al m h.c1 h.p1)
    (Triple.seq (p2_step ra s0 v outp sp pa b pc a.used _ h.c2 h.k)
      (Triple.seq (p2b_step ra s0 v outp sp pa b pc a.used a.sign ou cdp _ h.c3 h.p2 h0 h.p1.ua_lt)
        (Triple.seq (p3_step ra v outp sp pa b pc a.used cdp ou _ h.c4 h.k)
          (p3b_step ra v outp sp pa b pc a.used cdp ou adp _ h.c5 h.k h.p3 h.hb))))

end pro

/-- The whole log of the stores before the loop. -/
def proLog (ra s0 : BitVec 64) (v : Abi) (sp pc sa : Nat) : List WEntry :=
  log1 ra v sp ++ log2 s0 v sp ++ [(pc + 8, 4, BitVec.ofNat 64 sa)] ++ log3 v sp ++ log4 v sp

theorem m5Of_eq (m : Mem) (ra s0 : BitVec 64) (v : Abi) (sp pc sa : Nat) :
    m5Of m ra s0 v sp pc sa = writeLog m (proLog ra s0 v sp pc sa) := by
  simp only [m5Of, m4Of, m3Of, m2Of, m1Of, proLog, writeLog_append]

theorem m3Of_eq (m : Mem) (ra s0 : BitVec 64) (v : Abi) (sp pc sa : Nat) :
    m3Of m ra s0 v sp pc sa = writeLog m (log1 ra v sp ++ log2 s0 v sp ++ [(pc + 8, 4, BitVec.ofNat 64 sa)]) := by
  simp only [m3Of, m2Of, m1Of, writeLog_append]

/-- The saved registers, read back from the snapshot. -/
theorem efacts5 {m : Mem} {ra s0 : BitVec 64} {v : Abi} {sp pc sa : Nat} (hk : KFacts sp)
    (hra : ra.toNat % 4 = 0) (hc : sp ≤ pc ∨ pc + 24 ≤ sp - 80) :
    EFacts (m5Of m ra s0 v sp pc sa) ra s0 v sp := by
  have := hk.sp_ge
  rw [m5Of_eq]
  exact { rs := hk.rs, sp_al := hk.sp_al, sp_ge := hk.sp_ge, ra_al := hra
          s3_v := bytesT8_log _ _ 0 _ _ rfl (by simp [proLog, log1, log2, log3, log4, OutLRange]; omega)
          s4_v := bytesT8_log _ _ 1 _ _ rfl (by simp [proLog, log1, log2, log3, log4, OutLRange]; omega)
          s6_v := bytesT8_log _ _ 2 _ _ rfl (by simp [proLog, log1, log2, log3, log4, OutLRange]; omega)
          ra_v := bytesT8_log _ _ 3 _ _ rfl (by simp [proLog, log1, log2, log3, log4, OutLRange]; omega)
          s0_v := bytesT8_log _ _ 4 _ _ rfl (by simp [proLog, log1, log2, log3, log4, OutLRange]; omega)
          s2_v := bytesT8_log _ _ 5 _ _ rfl (by simp [proLog, log1, log2, log3, log4, OutLRange]; omega)
          s8_v := bytesT8_log _ _ 6 _ _ rfl (by simp [proLog, log1, log2, log3, log4, OutLRange]; omega) }

theorem cfacts5 {m : Mem} {ra s0 : BitVec 64} {v : Abi} {sp pc sa : Nat} (hk : KFacts sp) :
    CFacts (m5Of m ra s0 v sp pc sa) v sp := by
  have := hk.sp_ge
  rw [m5Of_eq]
  exact { rs := hk.rs, sp_al := hk.sp_al, sp_ge := hk.sp_ge
          s7_v := bytesT8_log _ _ 8 _ _ rfl (by simp [proLog, log1, log2, log3, log4, OutLRange]; omega)
          s5_v := bytesT8_log _ _ 9 _ _ rfl (by simp [proLog, log1, log2, log3, log4, OutLRange]; omega)
          s1_v := bytesT8_log _ _ 10 _ _ rfl (by simp [proLog, log1, log2, log3, log4, OutLRange]) }

theorem efacts3 {m : Mem} {ra s0 : BitVec 64} {v : Abi} {sp pc sa : Nat} (hk : KFacts sp)
    (hra : ra.toNat % 4 = 0) (hc : sp ≤ pc ∨ pc + 24 ≤ sp - 80) :
    EFacts (m3Of m ra s0 v sp pc sa) ra s0 v sp := by
  have := hk.sp_ge
  rw [m3Of_eq]
  exact { rs := hk.rs, sp_al := hk.sp_al, sp_ge := hk.sp_ge, ra_al := hra
          s3_v := bytesT8_log _ _ 0 _ _ rfl (by simp [log1, log2, OutLRange]; omega)
          s4_v := bytesT8_log _ _ 1 _ _ rfl (by simp [log1, log2, OutLRange]; omega)
          s6_v := bytesT8_log _ _ 2 _ _ rfl (by simp [log1, log2, OutLRange]; omega)
          ra_v := bytesT8_log _ _ 3 _ _ rfl (by simp [log1, log2, OutLRange]; omega)
          s0_v := bytesT8_log _ _ 4 _ _ rfl (by simp [log1, log2, OutLRange]; omega)
          s2_v := bytesT8_log _ _ 5 _ _ rfl (by simp [log1, log2, OutLRange]; omega)
          s8_v := bytesT8_log _ _ 6 _ _ rfl (by simp [log1, log2, OutLRange]; omega) }

/-! ## The whole function, for any placement -/

section whole
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {wD : ι} {m : Mem} {v : Abi} {outp : Array String}
  {sp pa adp b pc cdp ou : Nat} {a c0 : MpInt} {old : Nat → Nat} {ra s0 : BitVec 64}

/-- **`mp_mul_d` from the entry**, given the prologue's facts, the tail's facts
on both snapshots (`a->used = 0`: after `m3Of`; otherwise after `m5Of`), the
array at the snapshot, and `a`'s digit reads. -/
theorem whole (hpro : ProH m ra s0 v sp pa adp pc cdp ou a b c0.alloc)
    (hz : a.used = 0 → TailH ρ wD (m3Of m ra s0 v sp pc a.sign) ra s0 v sp pa pc cdp ou a b c0 old ∧
      ArrAt (m3Of m ra s0 v sp pc a.sign) cdp c0.alloc old)
    (hp : 0 < a.used → TailH ρ wD (m5Of m ra s0 v sp pc a.sign) ra s0 v sp pa pc cdp ou a b c0 old ∧
      ArrAt (m5Of m ra s0 v sp pc a.sign) cdp c0.alloc old ∧
      (∀ M i, i < a.used → ArrFrm ρ wD (m5Of m ra s0 v sp pc a.sign) M cdp c0.alloc (ovl (mulDDigit a b) old i) →
        DRead M adp i (a.digit i))) :
    Triple (At 0x800019fc#64 (entL ra s0 v sp pa b pc) m (kMD v) outp)
      (fun cf => (a.used = 0 ∧ RetC (m3Of m ra s0 v sp pc a.sign) v outp sp pc cdp a b c0 ra s0 cf) ∨
        (0 < a.used ∧ RetC (m5Of m ra s0 v sp pc a.sign) v outp sp pc cdp a b c0 ra s0 cf)) := by
  by_cases h0 : a.used = 0
  · have ⟨ht, harr⟩ := hz h0
    have hA : ArrFrm ρ wD (m3Of m ra s0 v sp pc a.sign) (m3Of m ra s0 v sp pc a.sign) cdp c0.alloc
        (ovl (mulDDigit a b) old a.used) :=
      ArrFrm.init (by rw [ht.hw]; exact Iv.sub_self _) (by rw [h0, ovl_zero]; exact harr)
    refine Triple.rmap (fun cf h => Or.inl ⟨h0, h⟩) (Triple.seq ?_ (tail ht))
    refine Triple.rmap (fun cf h => ⟨_, hA, h⟩) ?_
    have e1 : W a b a.used = 0 := by rw [h0]; rfl
    rw [e1, h0]
    exact pro_z hpro h0
  · have ⟨ht, harr, hrd⟩ := hp (by omega)
    have hA : ArrFrm ρ wD (m5Of m ra s0 v sp pc a.sign) (m5Of m ra s0 v sp pc a.sign) cdp c0.alloc
        (ovl (mulDDigit a b) old 0) :=
      ArrFrm.init (by rw [ht.hw]; exact Iv.sub_self _) (by rw [ovl_zero]; exact harr)
    have hk := hpro.k
    have hcf : ∀ M f, ArrFrm ρ wD (m5Of m ra s0 v sp pc a.sign) M cdp c0.alloc f → CFacts M v sp :=
      fun M f hA' => (cfacts5 (m := m) (ra := ra) (s0 := s0) (v := v) (pc := pc) (sa := a.sign) hk).of_agree
        fun x h1 h2 => hA'.out ht.hw (by have := ht.k_d; omega)
    have hua := ht.sa.used_le; have hal := ht.al_lt; have hroom := ht.room
    refine Triple.rmap (fun cf h => Or.inr ⟨by omega, h⟩) (Triple.seq ?_ (tail ht))
    refine Triple.seq (Triple.rmap (fun cf h => ⟨_, hA, h⟩) (pro_p (outp := outp) hpro (by omega)))
      (Triple.seq (loop (ht.loopH hrd) (by omega) 0 (by omega)) ?_)
    refine ASt.seg fun M hA' => ?_
    have := c_step v outp sp pa b pc cdp ou (a.used - 1) (W a b a.used) M (ht.imgA hA').mpMulD (hcf M _ hA')
      (by omega)
    rwa [show a.used - 1 + 1 = a.used by omega] at this

end whole

end Tom.Machine.Fn.MulD
