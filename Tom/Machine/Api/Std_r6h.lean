import Tom.Machine.Api.StdNorm
import Tom.Machine.Api.StdR5
import Tom.Spec.MpSqrStep
import Tom.Machine.Api.SqrFast
import Tom.Machine.Fn.SqrFastMain
import Tom.Machine.Api.KSqr
import Tom.Machine.Api.ToomSqr
import Tom.Machine.Api.MpAddH
import Tom.Machine.Api.MpLshdH
import Tom.Machine.Api.SAdd
import Tom.Machine.Api.MpAddAlias
import Tom.Machine.Fn.MpAddAlias

/-!
# Callee contracts of the squaring group

* `sqrFast`, `sqrFastA`: `s_mp_sqr_fast(a, b)` and `s_mp_sqr_fast(a, a)` (`Fn.SqrFast.correct`,
  `correct_inplace`), regions `Two`/`Un` (stack 2208), D5 (`2 a->used ≤ b->alloc`).
* `sqrB`, `sqrAB`: `mp_sqr(a, b)` (`Api/MpSqr.lean`), `mp_sqr(a, a)` for a caller holding the
  induction hypothesis `SqrBelow n` (`Api/SqrRec.lean`) with `a->used < n`: the residue is
  `MpSqr.Res`, the bound and the hypothesis, and `spec` is the hypothesis.
* `ksqr`, `ksqrA`, `toomSqr`, `toomSqrA`: the algorithms; the residue carries the algorithm's
  Statement (a named premise, discharged when the group closes: `Fn.MulGroupB.sqrCorrect`).

The parameters are the contracts' `P` fields, flat (the generator's anonymous constructor).
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap
open Tom.Machine.Api.SqrRec

/-! ## `s_mp_sqr_fast(a, b)`, `s_mp_sqr_fast(a, a)` -/

structure SqrFastRes (p : TwoP) : Prop where
  sa : p.a.Shape
  sb : p.b.Shape
  warr : 2 * p.a.used + 1 < 512
  room : 2 * p.a.used ≤ p.b.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 2208 ≤ p.sp

def sqrFast : Contract where
  P := TwoP
  X := MpInt
  R := Two.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Two.all
  entry := SqrFast.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Two.lay 2208 p.sp p.pa p.adp p.pb p.bdp p.a p.b
  kind := fun ⟨_, pa, adp, pb, bdp, a, b⟩ => Tom.Machine.Two.kind pa adp pb bdp a b
  out := fun ⟨_, pa, adp, pb, bdp, a, _⟩ x => Tom.Machine.Two.kind pa adp pb bdp a x
  isW := Two.isW
  ws := Two.ws
  Res := SqrFastRes
  Q p x := SqrFastPost p.a p.b x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpb, qbdp, qa, qb⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : SqrFast.Pre m qsp qpa qadp qpb qbdp qa qb ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2
        sa := hres.sa, sb := hres.sb, ga := Hdr.geom (hB .aS).2, gb := Hdr.geom (hB .bS).2
        warr := hres.warr, room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al
        sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, b', M, hat, hpost⟩ :=
      Fn.SqrFast.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, b', M, hat.sub rfl rfl, hpost.sqr, ?_, hpost.frame⟩
    have hal := hpost.sqr.alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact hB.keep hS hpost.frame Two.R.aS
    · exact hB.keep hS hpost.frame Two.R.aD
    · exact witS hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Two.R.code

structure SqrFastARes (p : UnP) : Prop where
  sa : p.a.Shape
  warr : 2 * p.a.used + 1 < 512
  room : 2 * p.a.used ≤ p.a.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 2208 ≤ p.sp

def sqrFastA : Contract where
  P := UnP
  X := MpInt
  R := Un.R
  all := [.stk, .aS, .aD, .code]
  hall := Un.all
  entry := SqrFast.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pa)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Un.lay 2208 p.sp p.pa p.adp p.a
  kind := fun ⟨_, pa, adp, a⟩ => Tom.Machine.Un.kind pa adp a
  out := fun ⟨_, pa, adp, _⟩ x => Tom.Machine.Un.kind pa adp x
  isW := Un.isW
  ws := Un.ws
  Res := SqrFastARes
  Q p x := SqrFastPost p.a p.a x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qa⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : SqrFast.PreI m qsp qpa qadp qa ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, sa := hres.sa, ga := Hdr.geom (hB .aS).2
        warr := hres.warr, room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al
        sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, a', M, hat, hpost⟩ :=
      Fn.SqrFast.correct_inplace (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, a', M, hat.sub rfl rfl, hpost.sqr, ?_, hpost.frame⟩
    have hal := hpost.sqr.alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Un.R.code

/-! ## `mp_sqr` below a bound -/

theorem mpSqr_pos (p : MpSqr.P) (ha : 0 < p.a.alloc) (hb : 0 < p.b.alloc) (F : Nat) (hF : 0 < F)
    (lay : MpSqr.R → Iv) (hl : ∀ r, r ≠ .stk → lay r = MpSqr.lay p r) (hs : (lay .stk).len = F) (r : MpSqr.R) :
    0 < (lay r).len ∨ (lay r).base < heapStart ∨ heapEnd ≤ (lay r).base := by
  left
  cases r with
  | stk => rw [hs]; exact hF
  | code => rw [hl _ (by decide)]; exact (show 0 < textLen by decide)
  | aD => rw [hl _ (by decide)]; show 0 < 4 * p.a.alloc; omega
  | bD => rw [hl _ (by decide)]; show 0 < 4 * p.b.alloc; omega
  | _ => rw [hl _ (by decide)]; simp [MpSqr.lay]

theorem mpSqrA_pos (p : MpSqrA.P) (ha : 0 < p.a.alloc) (F : Nat) (hF : 0 < F)
    (lay : MpSqrA.R → Iv) (hl : ∀ r, r ≠ .stk → lay r = MpSqrA.lay p r) (hs : (lay .stk).len = F) (r : MpSqrA.R) :
    0 < (lay r).len ∨ (lay r).base < heapStart ∨ heapEnd ≤ (lay r).base := by
  left
  cases r with
  | stk => rw [hs]; exact hF
  | code => rw [hl _ (by decide)]; exact (show 0 < textLen by decide)
  | aD => rw [hl _ (by decide)]; show 0 < 4 * p.a.alloc; omega
  | _ => rw [hl _ (by decide)]; simp [MpSqrA.lay]

structure SqrBP where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt
  H : List (Nat × Nat)
  n : Nat

def SqrBP.toP (p : SqrBP) : MpSqr.P := ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩

/-- `mp_sqr`'s residue, the bound and the hypothesis. -/
structure SqrBRes (p : SqrBP) : Prop where
  res : MpSqr.Res p.toP
  lt : p.a.used < p.n
  ih : SqrBelow p.n

def sqrB : HContract where
  P := SqrBP
  X := MpSqr.X
  R := MpSqr.R
  all := [.stk, .aS, .aD, .bS, .bD, .ks, .ts, .km, .tm, .code]
  hall := MpSqr.all
  entry := MpSqr.entry
  args p := MpSqr.args p.toP
  rets p := MpSqr.rets p.toP
  lay p := MpSqr.lay p.toP
  kind p := MpSqr.kind p.toP
  out p := MpSqr.out p.toP
  isW := MpSqr.isW
  ws := MpSqr.ws
  site := .bD
  site' p := MpSqr.site' p.toP
  hin p := MpSqr.hin p.toP
  hout p := MpSqr.hout p.toP
  Res := SqrBRes
  Q p := MpSqr.Q p.toP
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _ | simp [Kind.Fits, MpSqr.kind, MpSqr.lay, Iv.Sub]
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpSqr.out, MpSqr.kind, MpSqr.ws, Kind.isRam, Kind.indep]
  pos p h r := mpSqr_pos p.toP h.res.apos h.res.bpos _ (show 0 < MpSqr.Fs _ by unfold MpSqr.Fs; omega) _
    (fun r hr => rfl) rfl r
  spec := fun hra hres => hres.ih.sqr hres.lt hra hres.res

structure SqrABP where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt
  H : List (Nat × Nat)
  n : Nat

def SqrABP.toP (p : SqrABP) : MpSqrA.P := ⟨p.sp, p.pa, p.adp, p.a, p.H⟩

structure SqrABRes (p : SqrABP) : Prop where
  res : MpSqrA.Res p.toP
  lt : p.a.used < p.n
  ih : SqrBelow p.n

def sqrAB : HContract where
  P := SqrABP
  X := MpSqr.X
  R := MpSqrA.R
  all := [.stk, .aS, .aD, .ks, .ts, .km, .tm, .code]
  hall := MpSqrA.all
  entry := MpSqr.entry
  args p := MpSqrA.args p.toP
  rets p := MpSqrA.rets p.toP
  lay p := MpSqrA.lay p.toP
  kind p := MpSqrA.kind p.toP
  out p := MpSqrA.out p.toP
  isW := MpSqrA.isW
  ws := MpSqrA.ws
  site := .aD
  site' p := MpSqrA.site' p.toP
  hin p := MpSqrA.hin p.toP
  hout p := MpSqrA.hout p.toP
  Res := SqrABRes
  Q p := MpSqrA.Q p.toP
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _ | simp [Kind.Fits, MpSqrA.kind, MpSqrA.lay, Iv.Sub]
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpSqrA.out, MpSqrA.kind, MpSqrA.ws, Kind.isRam, Kind.indep]
  pos p h r := mpSqrA_pos p.toP h.res.apos _ (show 0 < MpSqr.Fs _ by unfold MpSqr.Fs; omega) _
    (fun r hr => rfl) rfl r
  spec := fun hra hres => hres.ih.sqrA hres.lt hra hres.res

/-! ## The algorithms, from their Statements -/

/-- An algorithm's residue and its Statement (a named premise, discharged by the group's closure: it
travels in the residue, so the contract is a constant the generator can name). -/
structure SqrAlgRes (entry : BitVec 64) (Rs : MpSqr.P → Prop) (p : MpSqr.P) : Prop where
  res : Rs p
  stmt : ∀ p, SqrAlg.SpecR entry Rs p

structure SqrAlgResA (entry : BitVec 64) (Rs : MpSqrA.P → Prop) (p : MpSqrA.P) : Prop where
  res : Rs p
  stmt : ∀ p, SqrAlg.SpecRA entry Rs p

/-- An algorithm (`b` distinct) as an allocating contract. -/
def sqrAlg (entry : BitVec 64) (Rs : MpSqr.P → Prop) (hpos : ∀ p, Rs p → SqrAlg.Base p) : HContract where
  P := MpSqr.P
  X := MpSqr.X
  R := MpSqr.R
  all := [.stk, .aS, .aD, .bS, .bD, .ks, .ts, .km, .tm, .code]
  hall := MpSqr.all
  entry := entry
  args := MpSqr.args
  rets := MpSqr.rets
  lay := SqrAlg.lay
  kind := MpSqr.kind
  out := MpSqr.out
  isW := MpSqr.isW
  ws := MpSqr.ws
  site := .bD
  site' := MpSqr.site'
  hin := MpSqr.hin
  hout := MpSqr.hout
  Res := SqrAlgRes entry Rs
  Q := SqrAlg.Q
  fits p r := by
    cases r <;> first | trivial | exact Iv.sub_self _ | simp [Kind.Fits, MpSqr.kind, SqrAlg.lay, MpSqr.lay, Iv.Sub]
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpSqr.out, MpSqr.kind, MpSqr.ws, Kind.isRam, Kind.indep]
  pos p hr r := mpSqr_pos p (hpos p hr.res).apos (hpos p hr.res).bpos _ (show 0 < SqrAlg.Fa _ by unfold SqrAlg.Fa; omega)
    _ (fun r hr => by cases r <;> first | rfl | exact absurd rfl hr) rfl r
  spec := fun hra hres => hres.stmt _ hra hres.res

/-- An algorithm in place (`b = a`). -/
def sqrAlgA (entry : BitVec 64) (Rs : MpSqrA.P → Prop) (hpos : ∀ p, Rs p → SqrAlg.BaseA p) : HContract where
  P := MpSqrA.P
  X := MpSqr.X
  R := MpSqrA.R
  all := [.stk, .aS, .aD, .ks, .ts, .km, .tm, .code]
  hall := MpSqrA.all
  entry := entry
  args := MpSqrA.args
  rets := MpSqrA.rets
  lay := SqrAlg.layA
  kind := MpSqrA.kind
  out := MpSqrA.out
  isW := MpSqrA.isW
  ws := MpSqrA.ws
  site := .aD
  site' := MpSqrA.site'
  hin := MpSqrA.hin
  hout := MpSqrA.hout
  Res := SqrAlgResA entry Rs
  Q := SqrAlg.QA
  fits p r := by
    cases r <;> first | trivial | exact Iv.sub_self _ | simp [Kind.Fits, MpSqrA.kind, SqrAlg.layA, MpSqrA.lay, Iv.Sub]
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpSqrA.out, MpSqrA.kind, MpSqrA.ws, Kind.isRam, Kind.indep]
  pos p hr r := mpSqrA_pos p (hpos p hr.res).apos _ (show 0 < SqrAlg.Fa _ by unfold SqrAlg.Fa; omega)
    _ (fun r hr => by cases r <;> first | rfl | exact absurd rfl hr) rfl r
  spec := fun hra hres => hres.stmt _ hra hres.res

def ksqr : HContract := sqrAlg KSqr.entry KSqr.Res (fun _ r => r.toBase)
def ksqrA : HContract := sqrAlgA KSqr.entry KSqr.ResA (fun _ r => r.toBaseA)
def toomSqr : HContract := sqrAlg ToomSqr.entry ToomSqr.Res (fun _ r => r.toBase)
def toomSqrA : HContract := sqrAlgA ToomSqr.entry ToomSqr.ResA (fun _ r => r.toBaseA)

/-! ## Karatsuba's other callees: `s_mp_add(a, b, c)`, `mp_add(a, b, b)` (D5) -/

/-- `s_mp_add(a, b, c)`, `c` distinct (`Api.SAdd.correct`), regions `Bin` (stack 64). -/
structure SAddDRes (p : FastP) : Prop where
  sa : p.a.Shape
  sb : p.b.Shape
  sc : p.c.Shape
  csign : p.c.sign = Layout.mpZpos ∨ p.c.sign = Layout.mpNeg
  room : max p.a.used p.b.used + 1 ≤ p.c.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 64 ≤ p.sp

/-- The parameters as `FastP`'s (`dg` unused). -/
def sAddD : Contract where
  P := FastP
  X := MpInt
  R := Bin.R
  all := [.stk, .cS, .cD, .aS, .aD, .bS, .bD, .code]
  hall := Bin.all
  entry := SAdd.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
    (12, BitVec.ofNat 64 p.pc)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Bin.lay 64 p.sp p.pa p.adp p.pb p.bdp p.pc p.cdp p.a p.b p.c
  kind := fun ⟨_, pa, adp, pb, bdp, pc, cdp, _, a, b, c⟩ => binKind pa adp pb bdp pc cdp a b c
  out := fun ⟨_, pa, adp, pb, bdp, pc, cdp, _, a, b, _⟩ x => binKind pa adp pb bdp pc cdp a b x
  isW := Bin.isW
  ws := Bin.ws
  Res := SAddDRes
  Q p x := SAddPost p.a p.b p.c x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [binKind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [binKind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpb, qbdp, qpc, qcdp, qdg, qa, qb, qc⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : SAdd.Pre m qsp qpa qadp qpb qbdp qpc qcdp qa qb qc ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2
        rc := Hdr.mpAt (hB .cS).2 (hB .cD).2, sa := hres.sa, sb := hres.sb, sc := hres.sc
        csign := hres.csign, ga := Hdr.geom (hB .aS).2, gb := Hdr.geom (hB .bS).2, gc := Hdr.geom (hB .cS).2
        room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al
        sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, x, M, hat, hpost⟩ :=
      SAdd.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, x, M, hat.sub rfl rfl, hpost.sadd, ?_, hpost.frame⟩
    have hal := hpost.sadd.alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.repr (Hdr.geom (hB .cS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .cS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Bin.R.aS
    · exact hB.keep hS hpost.frame Bin.R.aD
    · exact hB.keep hS hpost.frame Bin.R.bS
    · exact hB.keep hS hpost.frame Bin.R.bD
    · exact hB.keep hS hpost.frame Bin.R.code

structure AddCBRes (p : TwoP) : Prop where
  va : p.a.Valid
  vb : p.b.Valid
  room : max p.a.used p.b.used + 1 ≤ p.b.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 64 ≤ p.sp

/-- `mp_add(a, b, b)` (`Fn.MpAdd.correctCB`), regions `BinA` with `b` written (stack 64). -/
def mpAddCB : Contract where
  P := TwoP
  X := MpInt
  R := BinA.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := BinA.all
  entry := MpAddAlias.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
    (12, BitVec.ofNat 64 p.pb)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := BinA.lay 64 p.sp p.pa p.adp p.pb p.bdp p.a p.b
  kind := fun ⟨_, pa, adp, pb, bdp, a, b⟩ => BinA.kind pa adp pb bdp a b
  out := fun ⟨_, pa, adp, pb, bdp, a, _⟩ x => BinA.kind pa adp pb bdp a x
  isW := BinA.isWB
  ws := BinA.wsB
  Res := AddCBRes
  Q p x := AddPost p.a p.b p.b x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [BinA.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [BinA.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpb, qbdp, qa, qb⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MpAddAlias.PreCB m qsp qpa qadp qpb qbdp qa qb ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2
        ga := Hdr.geom (hB .aS).2, gb := Hdr.geom (hB .bS).2, rs := (hB .stk).2, sp_al := hres.sp_al
        sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2, va := hres.va, vb := hres.vb
        room := hres.room, lay := hS }
    obtain ⟨c', hs, b', M, hat, hpost⟩ :=
      Fn.MpAdd.correctCB (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, b', M, hat.sub rfl rfl, hpost.add, ?_, hpost.frame⟩
    have hal : b'.alloc = qb.alloc := addPost_alloc hpost.add
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact hB.keep hS hpost.frame BinA.R.aS
    · exact hB.keep hS hpost.frame BinA.R.aD
    · exact witS hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame BinA.R.code

/-! ## The growing callees (named premises: the Statement travels in the residue) -/

structure AddHRes (p : MpAddH.P) : Prop where
  res : MpAddH.Res p
  stmt : MpAddH.Statement

def mpAddH : HContract where
  P := MpAddH.P
  X := MpSqr.X
  R := Bin.R
  all := [.stk, .cS, .cD, .aS, .aD, .bS, .bD, .code]
  hall := Bin.all
  entry := MpAddH.entry
  args := MpAddH.args
  rets := MpAddH.rets
  lay := MpAddH.lay
  kind := MpAddH.kind
  out := MpAddH.out
  isW := Bin.isW
  ws := Bin.ws
  site := .cD
  site' := MpAddH.site'
  hin := MpAddH.hin
  hout := MpAddH.hout
  Res := AddHRes
  Q := MpAddH.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpAddH.out, MpAddH.kind, Bin.ws, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.res.apos; have := h.res.bpos; have := h.res.cpos
    left
    cases r with
    | code => exact (show 0 < textLen by decide)
    | stk => exact (show 0 < 608 by decide)
    | cS | aS | bS => exact (show 0 < 24 by decide)
    | cD => exact (show 0 < 4 * p.c.alloc by omega)
    | aD => exact (show 0 < 4 * p.a.alloc by omega)
    | bD => exact (show 0 < 4 * p.b.alloc by omega)
  spec := fun hra hres => hres.stmt hra hres.res

structure LshdHRes (p : MpLshdH.P) : Prop where
  res : MpLshdH.Res p
  stmt : MpLshdH.Statement

def mpLshdH : HContract where
  P := MpLshdH.P
  X := MpSqr.X
  R := Un.R
  all := [.stk, .aS, .aD, .code]
  hall := Un.all
  entry := MpLshdH.entry
  args := MpLshdH.args
  rets := MpLshdH.rets
  lay := MpLshdH.lay
  kind := MpLshdH.kind
  out := MpLshdH.out
  isW := Un.isW
  ws := Un.ws
  site := .aD
  site' := MpLshdH.site'
  hin := MpLshdH.hin
  hout := MpLshdH.hout
  Res := LshdHRes
  Q := MpLshdH.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpLshdH.out, MpLshdH.kind, Un.ws, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.res.apos
    left
    cases r with
    | code => exact (show 0 < textLen by decide)
    | stk => exact (show 0 < 576 by decide)
    | aS => exact (show 0 < 24 by decide)
    | aD => exact (show 0 < 4 * p.a.alloc by omega)
  spec := fun hra hres => hres.stmt hra hres.res

end Tom.Machine.Std
