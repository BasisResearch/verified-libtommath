import Tom.Machine.Fn.MpAddStmt
import Tom.Machine.Fn.SAddMain
import Tom.Machine.Fn.SSubMain

/-!
# `mp_add` on the machine: the whole function

The segments of `Tom.Machine.Fn.MpAdd` and the contracts of `s_mp_add`,
`s_mp_sub` and `mp_cmp_mag` chained into `correct_Statement`, with the frame
bookkeeping in named regions (`Tom/Machine/Kit/Frame.lean`): the closed
regions `R`, placed by `lay`, the written ones (`fr`, `cS`, `cD`) disjoint
from every other by `sound` (once, from `Pre.lay`). Every read-only fact
(the six functions' code, `a`, `b`) stays a fact about the entry memory and
is pulled by `Frm.keep`; each callee's frame clause becomes a `Frm` by
`Frm.ofClause` and composes with ours by `Frm.trans`. The tail calls'
results are collected as `RetQ` (`Out`) and turned into `AddPost` branch by
branch.
-/


namespace Tom.Machine.Fn.MpAdd

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

/-! ## Regions -/

/-- `mp_add`'s regions: its stack frame, the three structs and digit arrays,
the six functions' code. -/
inductive R | fr | cS | cD | aS | aD | bS | bD | add | cm | sa | ss | ms | cl
  deriving DecidableEq

/-- The regions it (and its callees) write. -/
def isW : R → Bool
  | .fr | .cS | .cD => true
  | _ => false

/-- Their placement. -/
def lay (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt) : R → Iv
  | .fr => ⟨sp - 64, 64⟩
  | .cS => ⟨pc, 24⟩
  | .cD => ⟨cdp, 4 * c.alloc⟩
  | .aS => ⟨pa, 24⟩
  | .aD => ⟨adp, 4 * a.alloc⟩
  | .bS => ⟨pb, 24⟩
  | .bD => ⟨bdp, 4 * b.alloc⟩
  | .add => ⟨mpAddBase, 144⟩
  | .cm => ⟨mpCmpMagBase, 124⟩
  | .sa => ⟨sMpAddBase, 432⟩
  | .ss => ⟨sMpSubBase, 380⟩
  | .ms => ⟨memsetBase, 220⟩
  | .cl => ⟨mpClampBase, 64⟩

/-- What stays as at the entry. -/
structure RO (M : Mem) (pa adp pb bdp : Nat) (a b : MpInt) : Prop where
  code : CodeAt M mpAddBase mpAddCode
  code_cm : CodeAt M mpCmpMagBase mpCmpMagCode
  code_sa : CodeAt M sMpAddBase sMpAddCode
  code_ss : CodeAt M sMpSubBase sMpSubCode
  code_ms : CodeAt M memsetBase memsetCode
  code_cl : CodeAt M mpClampBase mpClampCode
  ra_ : MpAt M pa adp a
  rb : MpAt M pb bdp b

/-- What a tail call leaves: `c'` at `c`, `Q`, memory changed only in `InW`. -/
structure Out (m M : Mem) (sp pc cdp : Nat) (c c' : MpInt) (Q : Prop) : Prop where
  repr : MpAt M pc cdp c'
  q : Q
  frame : ∀ x, ¬ InW sp pc cdp c.alloc x → M[x]? = m[x]?

/-- The return state with the result described by `Q`. -/
def RetQ (m : Mem) (v : Abi) (outp : Array String) (sp pc cdp : Nat) (c : MpInt) (ra s0 : BitVec 64)
    (Q : MpInt → Prop) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Out m M sp pc cdp c c' (Q c')

theorem RetQ.ret {m : Mem} {v : Abi} {outp : Array String} {sp pc cdp : Nat} {a b c : MpInt}
    {ra s0 : BitVec 64} {Q : MpInt → Prop} (h : ∀ c', Q c' → AddPost a b c c') :
    ∀ cf, RetQ m v outp sp pc cdp c ra s0 Q cf → Ret m v outp sp pc cdp a b c ra s0 cf
  | _, ⟨c', M, hat, ho⟩ => ⟨c', M, hat, ⟨ho.repr, h c' ho.q, ho.frame⟩⟩

/-! ## The callee layouts from ours -/

theorem shrink {sp x n : Nat} (hs : 64 ≤ sp) (h : Disj (sp - 64) 64 x n) : Disj (sp - 48) 48 x n := by
  unfold Disj at *; omega

section
variable {sp pa adp aal pb bdp bal pc cdp cal : Nat}

theorem Lay.swap (L : Lay sp pa adp aal pb bdp bal pc cdp cal) : Lay sp pb bdp bal pa adp aal pc cdp cal :=
  ⟨L.s_cs, L.s_cd, L.s_bs, L.s_bd, L.s_as, L.s_ad, L.s_add, L.s_cm, L.s_sa, L.s_ss, L.s_ms, L.s_cl,
   L.cs_bs, L.cs_bd, L.cs_as, L.cs_ad, L.cs_add, L.cs_cm, L.cs_sa, L.cs_ss, L.cs_ms, L.cs_cl,
   L.cd_bs, L.cd_bd, L.cd_as, L.cd_ad, L.cd_add, L.cd_cm, L.cd_sa, L.cd_ss, L.cd_ms, L.cd_cl⟩

theorem Lay.sadd (L : Lay sp pa adp aal pb bdp bal pc cdp cal) : SAdd.Lay sp pa adp aal pb bdp bal pc cdp cal :=
  ⟨L.s_cs, L.s_cd, L.s_as, L.s_ad, L.s_bs, L.s_bd, L.s_sa, L.s_ms, L.s_cl,
   L.cs_as, L.cs_ad, L.cs_bs, L.cs_bd, L.cs_sa, L.cs_ms, L.cs_cl,
   L.cd_as, L.cd_ad, L.cd_bs, L.cd_bd, L.cd_sa, L.cd_ms, L.cd_cl⟩

theorem Lay.ssub (L : Lay sp pa adp aal pb bdp bal pc cdp cal) (hs : 64 ≤ sp) :
    SSub.Lay sp pa adp aal pb bdp bal pc cdp cal :=
  ⟨shrink hs L.s_cs, shrink hs L.s_cd, shrink hs L.s_as, shrink hs L.s_ad, shrink hs L.s_bs,
   shrink hs L.s_bd, shrink hs L.s_ss, shrink hs L.s_ms, shrink hs L.s_cl,
   L.cs_as, L.cs_ad, L.cs_bs, L.cs_bd, L.cs_ss, L.cs_ms, L.cs_cl,
   L.cd_as, L.cd_ad, L.cd_bs, L.cd_bd, L.cd_ss, L.cd_ms, L.cd_cl⟩

end

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat} {a b c : MpInt}
  {ra s0 : BitVec 64}

theorem Pre.swap (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) : Pre m sp pb bdp pa adp pc cdp b a c ra :=
  { hP with ra_ := hP.rb, rb := hP.ra_, va := hP.vb, vb := hP.va, ga := hP.gb, gb := hP.ga
            room := by rw [Nat.max_comm]; exact hP.room
            lay := hP.lay.swap }

/-- **Disjointness, once**: from `Pre.lay` and `c`'s geometry. -/
theorem sound (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Sound (lay sp pa adp pb bdp pc cdp a b c) isW := by
  have hg : Disj pc 24 cdp (4 * c.alloc) := hP.gc.disj
  have L := hP.lay
  cases L
  sound_cases

theorem RO.of (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) (hS : Sound (lay sp pa adp pb bdp pc cdp a b c) isW)
    {M : Mem} (hF : Frm (lay sp pa adp pb bdp pc cdp a b c) [.fr, .cS, .cD] m M) : RO M pa adp pb bdp a b :=
  { code := hF.keep hS (CodeAt.reads (r := R.add) (k := 36) rfl (Iv.sub_self _)) hP.code
    code_cm := hF.keep hS (CodeAt.reads (r := R.cm) (k := 31) rfl (Iv.sub_self _)) hP.code_cm
    code_sa := hF.keep hS (CodeAt.reads (r := R.sa) (k := 108) rfl (Iv.sub_self _)) hP.code_sa
    code_ss := hF.keep hS (CodeAt.reads (r := R.ss) (k := 95) rfl (Iv.sub_self _)) hP.code_ss
    code_ms := hF.keep hS (CodeAt.reads (r := R.ms) (k := 55) rfl (Iv.sub_self _)) hP.code_ms
    code_cl := hF.keep hS (CodeAt.reads (r := R.cl) (k := 16) rfl (Iv.sub_self _)) hP.code_cl
    ra_ := hF.keep hS (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_
    rb := hF.keep hS (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _)) hP.rb }

/-- `c->sign` lies in `c`'s struct. -/
theorem sub_sign : Iv.Sub ⟨pc + 8, 4⟩ (lay sp pa adp pb bdp pc cdp a b c .cS) := by
  simp only [Iv.Sub, lay]; omega

/-- The written ranges are the written regions. -/
theorem any_of_inW {x : Nat} (h : InW sp pc cdp c.alloc x) :
    InAny (lay sp pa adp pb bdp pc cdp a b c) [.fr, .cS, .cD] x := by
  simp only [InW, InAny, Iv.In, lay, or_false] at h ⊢; omega

theorem inW_of_any {x : Nat} (hs : 64 ≤ sp) (h : InAny (lay sp pa adp pb bdp pc cdp a b c) [.fr, .cS, .cD] x) :
    InW sp pc cdp c.alloc x := by
  simp only [InW, InAny, Iv.In, lay, or_false] at h ⊢; omega

theorem any_of_ssub {x : Nat} (hs : 64 ≤ sp) (h : SSub.InW sp pc cdp c.alloc x) :
    InAny (lay sp pa adp pb bdp pc cdp a b c) [.fr, .cS, .cD] x := by
  simp only [SSub.InW, InAny, Iv.In, lay, or_false] at h ⊢; omega

/-- The sign loads. -/
theorem sfacts (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) : SFacts m pa pb a.sign b.sign :=
  have ha := hP.va.sign_ok; have hb := hP.vb.sign_ok
  { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
    rb := by simpa [Layout.sizeofMpInt] using hP.gb.st
    sa_v := by simpa [Layout.offSign] using hP.ra_.sign
    sb_v := by simpa [Layout.offSign] using hP.rb.sign
    sa_lt := by simp only [Layout.mpZpos, Layout.mpNeg] at ha; omega
    sb_lt := by simp only [Layout.mpZpos, Layout.mpNeg] at hb; omega }

theorem csign (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) (hS : Sound (lay sp pa adp pb bdp pc cdp a b c) isW) :
    CSign pc :=
  have h := hS.disj (r := R.cS) (s := R.add)
  { rc := by simpa [Layout.sizeofMpInt] using hP.gc.st, pc_al := hP.gc.st_al
    code_off := by simp only [Iv.Disj, Disj, lay] at h; omega }

/-- `c` with the sign `s` stored. -/
theorem shape_sign (hc : c.Shape) (s : Nat) : (c.withSign s).Shape :=
  ⟨hc.len, hc.used_le, hc.alloc_lt, hc.digit_lt, hc.high_zero⟩

end

/-! ## The calls -/

/-- The callee-saved registers `mp_cmp_mag` sees: this frame's `sp`, `s0 = a`, `s1 = b`. -/
def cmpAbi (v : Abi) (sp pa pb : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 64), s0 := BitVec.ofNat 64 pa, s := { v.s with s1 := BitVec.ofNat 64 pb } }

/-- `mp_cmp_mag(a, b)` at `0638`, back at `063c`. -/
theorem cmp_call (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (M : Mem) (hc : CodeAt M mpAddBase mpAddCode) (hP : CmpMag.Pre M pa adp pb bdp a b) :
    Triple (At 0x80000638#64 (callL ra sp pa pb) M v.keepR1 outp)
      (At 0x8000063c#64 (retL sp pa pb (BitVec.ofInt 64 (ordCode (compare a.mag b.mag)))) M v.keepR1 outp) := by
  refine Triple.seq (jal_at (pc := 0x80000638#64) (w := 0x12c000ef#32) (imm := 0x0012c#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb),
        (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)])
      (hc.word (a := (0x80000638#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [callL]) (by simp [keysG]) (by simp [Abi.keepR1, keysG])) ?_
  refine Triple.dimap (fun c h => ?_) (fun c h => h.reshape ?_ ?_)
    (CmpMag.correct 0x8000063c#64 (cmpAbi v sp pa pb) outp pa adp pb bdp a b M (by decide) hP)
  · have hpc : (0x80000638#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x0012c#21) = CmpMag.entry := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [CmpMag.entryL, Sail.BitVec.addInt]
    · simp [Abi.keep, Abi.keepR1, cmpAbi, sKeepL]
  · simp [retL, CmpMag.retL, Abi.keep, cmpAbi, sKeepL]
  · simp [Abi.keep, Abi.keepR1, cmpAbi, sKeepL]

/-! ## The branches -/

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat} {a b c : MpInt}
  {ra s0 : BitVec 64}

/-- Same signs: `c->sign := a->sign`, then `s_mp_add(a, b, c)`; its frame is ours. -/
theorem same (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) (hS : Sound (lay sp pa adp pb bdp pc cdp a b c) isW)
    (he : a.sign = b.sign) :
    Triple (At 0x80000608#64 (entry1 ra s0 v.s.s1 sp pa pb pc) m v.keepR1 outp)
      (RetQ m v outp sp pc cdp c ra s0 (SAddPost a b (c.withSign a.sign))) := by
  have hsf := sfacts hP; have := hP.sp_ge
  have hF : Frm (lay sp pa adp pb bdp pc cdp a b c) [.cS] m (writeLog m [(pc + 8, 4, BitVec.ofNat 64 a.sign)]) :=
    Frm.sw sub_sign
  have hro := RO.of hP hS hF.mono
  have hpre : SAdd.Pre (writeLog m [(pc + 8, 4, BitVec.ofNat 64 a.sign)]) sp pa adp pb bdp pc cdp a b
      (c.withSign a.sign) ra :=
    { ra_ := hro.ra_, rb := hro.rb, rc := hP.rc.set_sign hP.gc a.sign (Nat.lt_trans hsf.sa_lt (by decide))
      sa := hP.va.toShape, sb := hP.vb.toShape, sc := shape_sign hP.sc _, csign := hP.va.sign_ok
      ga := hP.ga, gb := hP.gb, gc := hP.gc, room := hP.room, rs := hP.rs, sp_al := hP.sp_al
      sp_ge := hP.sp_ge, ra_al := hP.ra_al, code := hro.code_sa, code_ms := hro.code_ms
      code_cl := hro.code_cl, lay := hP.lay.sadd }
  refine Triple.seq (s_step ra s0 v.s.s1 v outp sp pa pb pc _ _ m (RO.of hP hS (Frm.refl _ m)).code hsf (csign hP hS) he)
    (Triple.dimap (fun cf h => ?_)
      (fun cf ⟨c', M, hat, hpost⟩ => ⟨c', M, hat, hpost.repr, hpost.sadd,
        ((hF.trans (Frm.ofClause hpost.frame fun x h => any_of_inW h)).mono).clause
          fun x h => inW_of_any (by omega) h⟩)
      (SAdd.correct hpre))
  exact h.reshape (by simp [SAdd.entryL, entry1, Abi.keepR1])
    (by simp [entry1, Abi.keepR1, Abi.keepR, sKeepL])

/-- After the comparison: `c->sign := a->sign`, then `s_mp_sub(a, b, c)`; its
frame `[sp - 48, sp)` is inside ours. -/
theorem tail (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) (hS : Sound (lay sp pa adp pb bdp pc cdp a b c) isW)
    {M : Mem} (hF : Frm (lay sp pa adp pb bdp pc cdp a b c) [.fr] m M) (hge : b.used ≤ a.used) :
    Triple (At 0x80004564#64 (entry1 ra s0 v.s.s1 sp pa pb pc) (writeLog M [(pc + 8, 4, BitVec.ofNat 64 a.sign)])
        v.keepR1 outp)
      (RetQ m v outp sp pc cdp c ra s0 (SSubPost a b (c.withSign a.sign))) := by
  have hsf := sfacts hP; have := hP.sp_ge; have hroom := hP.room
  have hF3 := hF.trans (Frm.sw (w := R.cS) (v := BitVec.ofNat 64 a.sign) sub_sign)
  have hro := RO.of hP hS hF3.mono
  have hc := (hF.keep hS (MpAt.reads (rs := R.cS) (rd := R.cD) (Iv.sub_self _) (Iv.sub_self _)) hP.rc).set_sign
    hP.gc a.sign (Nat.lt_trans hsf.sa_lt (by decide))
  have hrs := hP.rs
  have hpre : SSub.Pre (writeLog M [(pc + 8, 4, BitVec.ofNat 64 a.sign)]) sp pa adp pb bdp pc cdp a b
      (c.withSign a.sign) ra :=
    { ra_ := hro.ra_, rb := hro.rb, rc := hc
      sa := hP.va.toShape, sb := hP.vb.toShape, sc := shape_sign hP.sc _, csign := hP.va.sign_ok
      ga := hP.ga, gb := hP.gb, gc := hP.gc, ge := hge, room := by simp only [MpInt.withSign_alloc]; omega
      rs := ⟨by have := hrs.lo_ge; omega, by have := hrs.hi_le; omega, by have := hrs.off; omega⟩
      sp_al := hP.sp_al, sp_ge := by omega, ra_al := hP.ra_al, code := hro.code_ss
      code_ms := hro.code_ms, code_cl := hro.code_cl, lay := hP.lay.ssub hP.sp_ge }
  refine Triple.dimap (fun cf h => ?_)
    (fun cf ⟨c', M', hat, hpost⟩ => ⟨c', M', hat, hpost.repr, hpost.ssub,
      ((hF3.trans (Frm.ofClause hpost.frame fun x h => any_of_ssub (by omega) h)).mono).clause
        fun x h => inW_of_any (by omega) h⟩)
    (SSub.correct hpre)
  exact h.reshape (by simp [SSub.entryL, entry1, Abi.keepR1])
    (by simp [entry1, Abi.keepR1, Abi.keepR, sKeepL])

theorem ne_lt : ∀ o : Ordering, o ≠ .lt → (BitVec.ofInt 64 (ordCode o) == 0xffffffffffffffff#64) = false
  | .lt, h => absurd rfl h
  | .eq, _ => by decide
  | .gt, _ => by decide

/-- Different signs: the frame, `mp_cmp_mag(a, b)`, then `s_mp_sub` the right way round. -/
theorem diff (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) (hS : Sound (lay sp pa adp pb bdp pc cdp a b c) isW)
    (hne : a.sign ≠ b.sign) :
    Triple (At 0x80000608#64 (entry1 ra s0 v.s.s1 sp pa pb pc) m v.keepR1 outp)
      (Ret m v outp sp pc cdp a b c ra s0) := by
  have hsf := sfacts hP; have := hP.sp_ge
  have hfa := hS.disj (r := R.fr) (s := R.add)
  simp only [Iv.Disj, Disj, lay] at hfa
  have hff : FFacts sp := { rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge, code_off := by omega }
  have hF1 : Frm (lay sp pa adp pb bdp pc cdp a b c) [.fr] m (writeLog m (frameLog1 s0 v.s.s1 sp a.sign b.sign)) :=
    Frm.store (by simp only [LogIn, frameLog1, Iv.Sub, lay, and_true]; omega)
  have hF2 : Frm (lay sp pa adp pb bdp pc cdp a b c) [.fr] m
      (writeLog (writeLog m (frameLog1 s0 v.s.s1 sp a.sign b.sign)) (frameLog2 ra sp pc)) :=
    (hF1.trans (Frm.store (w := R.fr) (by simp only [LogIn, frameLog2, Iv.Sub, lay, and_true]; omega))).mono
  have hrf : RFacts (writeLog (writeLog m (frameLog1 s0 v.s.s1 sp a.sign b.sign)) (frameLog2 ra sp pc))
      ra s0 v.s.s1 sp pc a.sign b.sign := by
    rw [← writeLog_append]
    exact { rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
            s0_v := bytesT8_log _ _ 0 _ _ rfl (by simp [frameLog1, frameLog2, OutLRange]; omega)
            s1_v := bytesT8_log _ _ 1 _ _ rfl (by simp [frameLog1, frameLog2, OutLRange]; omega)
            sb_v := bytesT8_log _ _ 2 _ _ rfl (by simp [frameLog1, frameLog2, OutLRange]; omega)
            sa_v := bytesT8_log _ _ 3 _ _ rfl (by simp [frameLog1, frameLog2, OutLRange]; omega)
            pc_v := bytesT8_log _ _ 4 _ _ rfl (by simp [frameLog1, frameLog2, OutLRange]; omega)
            ra_v := bytesT8_log _ _ 5 _ _ rfl (by simp [frameLog1, frameLog2, OutLRange]) }
  have hFs : Frm (lay sp pb bdp pa adp pc cdp b a c) [.fr] m
      (writeLog (writeLog m (frameLog1 s0 v.s.s1 sp a.sign b.sign)) (frameLog2 ra sp pc)) := hF2
  refine Triple.seq (d1_step ra s0 v.s.s1 v outp sp pa pb pc _ _ m (RO.of hP hS (Frm.refl _ m)).code hsf hff hne)
    (Triple.seq (d2_step ra s0 v.s.s1 v outp sp pa pb pc _ _ _ (RO.of hP hS hF1.mono).code hff) ?_)
  generalize writeLog (writeLog m (frameLog1 s0 v.s.s1 sp a.sign b.sign)) (frameLog2 ra sp pc) = M2
    at hF2 hFs hrf ⊢
  have hro := RO.of hP hS hF2.mono
  have hcmp : CmpMag.Pre M2 pa adp pb bdp a b :=
    { ra := hro.ra_, rb := hro.rb, va := hP.va, vb := hP.vb, ga := hP.ga, gb := hP.gb, code := hro.code_cm }
  refine Triple.seq (cmp_call ra v outp sp pa adp pb bdp a b M2 hro.code hcmp) ?_
  rw [← cmpMag_eq hP.va hP.vb]
  by_cases hlt : cmpMag a b = .lt
  · rw [hlt, show BitVec.ofInt 64 (ordCode .lt) = 0xffffffffffffffff#64 by decide]
    have hle : a.mag ≤ b.mag := by
      rw [cmpMag_eq hP.va hP.vb] at hlt; exact Nat.le_of_lt (Nat.compare_eq_lt.1 hlt)
    exact Triple.seq (bl_step ra s0 v.s.s1 v outp sp pa pb pc _ _ M2 hro.code hrf)
      (Triple.seq (l_step ra s0 v.s.s1 v outp sp pa pb pc _ _ M2 hro.code hrf (csign hP hS))
        (Triple.rmap (RetQ.ret fun c' q => ⟨fun h => absurd h hne, fun _ _ => q, fun _ h => absurd hlt h⟩)
          (tail hP.swap (sound hP.swap) hFs (MpInt.used_le_of_mag_le hP.vb.toShape hP.va hle))))
  · have hle : b.mag ≤ a.mag := by
      rw [cmpMag_eq hP.va hP.vb] at hlt; exact Nat.le_of_not_lt fun h => hlt (Nat.compare_eq_lt.2 h)
    exact Triple.seq (b_step ra s0 v.s.s1 v outp sp pa pb pc _ _ _ M2 hro.code hrf (ne_lt _ hlt))
      (Triple.seq (g_step ra s0 v.s.s1 v outp sp pa pb pc _ _ M2 hro.code hrf (csign hP hS))
        (Triple.rmap (RetQ.ret fun c' q => ⟨fun h => absurd h hne, fun _ h => absurd h hlt, fun _ _ => q⟩)
          (tail hP hS hF2 (MpInt.used_le_of_mag_le hP.va.toShape hP.vb hle))))

end

/-- **`mp_add` on the machine** (H2). -/
theorem correct : correct_Statement := by
  intro m v outp sp pa adp pb bdp pc cdp a b c ra s0 hP
  have hS := sound hP
  refine Triple.lmap (fun cf h => h.reshape (L' := entry1 ra s0 v.s.s1 sp pa pb pc) (K' := v.keepR1)
    (by simp [SSub.entryL, entry1, Abi.keepR, sKeepL])
    (by simp [SSub.entryL, Abi.keepR1, Abi.keepR, sKeepL])) ?_
  by_cases he : a.sign = b.sign
  · exact Triple.rmap (RetQ.ret fun c' q => ⟨fun _ => q, fun h => absurd he h, fun h => absurd he h⟩)
      (same hP hS he)
  · exact diff hP hS he

end Tom.Machine.Fn.MpAdd
