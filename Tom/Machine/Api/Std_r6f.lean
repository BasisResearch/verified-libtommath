import Tom.Machine.Api.StdR5
import Tom.Machine.Api.CmpS
import Tom.Machine.Api.MpSubAlias
import Tom.Machine.Api.MpAddAlias
import Tom.Machine.Api.Libgcc
import Tom.Machine.Fn.CmpSMain
import Tom.Machine.Fn.MpSubAlias
import Tom.Machine.Fn.MpAddAlias
import Tom.Machine.Fn.MpSubAddS
import Tom.Machine.Fn.Libgcc

/-!
# The callee contracts (for `mp_div`)

Each a proved statement re-read as `Api/Std.lean`'s are (the Pre from the region bundle and a
scalar residue `Res`, the Post as the written regions' new witnesses):

* `mpCmpC`: `mp_cmp(a, b)` (`Api/CmpS.lean`), read only: `a0 = ordCode (cmpS a b)`.
* `mpSubS`: `mp_sub(a, b, a)` with equal signs (`MpSubAddS.StatementS`), regions `BinA` (stack
  64), room `max(used) ≤ a->alloc` (the `s_mp_sub` branches only; D5).
* `mpAddD`: `mp_add(a, b, a)` with different signs (`MpSubAddS.StatementD`), likewise.
* `mulDC`: `mp_mul_d(a, b, c)`, `c` distinct (`MulD.Statement`), regions `Two` (stack 80), room (D5).
* `udivdi3`: `__hidden___udivdi3(n, d)` (`Libgcc.Udivdi3.Statement`): `a0 = n / d`, `a1 = n % d`.

`mp_div`'s other callees have instances already (`cmpMag`, `mpCopy`, `mpZero`, `mpInitSize`,
`mpInit`, `mpInitCopy`, `mpClear`, `mpLshd`, `mpRshd`, `clamp`, `mpExch`, `moddi3`, `cntBits`,
`mulDA`; `Std_r6c.div2dG` for `mp_div_2d(a, b, a, NULL)`), but for `mp_mul_2d(a, b, a)` in place
(no machine proof: `Api/MpMul2d.lean` excludes `a == c`) and the growing variants.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api

/-! ## `mp_cmp(a, b)`: read only -/

def mpCmpC : Contract where
  P := CmP
  X := Unit
  R := Cm
  all := [.aS, .aD, .bS, .bD, .code]
  hall r := by cases r <;> simp
  entry := CmpS.entry
  args p := [(10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]
  rets p ra := [(1, ra), (10, BitVec.ofInt 64 (ordCode (cmpS p.a p.b)))]
  lay := Cm.lay
  kind := Cm.kind
  out p _ := Cm.kind p
  isW _ := false
  ws := []
  Res p := p.a.Valid ∧ p.b.Valid
  Q _ _ := True
  fits p r := by cases r <;> exact Iv.sub_self _
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB
    obtain ⟨qa, qadp, qb, qbdp, a, b⟩ := p
    have hpre : CmpS.Pre m qa qadp qb qbdp a b ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2, va := hres.1, vb := hres.2
        ga := Hdr.geom (hB .aS).2, gb := Hdr.geom (hB .bS).2, ra_al := hra, img := (hB .code).2 }
    exact Triple.rmap (fun cf hc => ⟨(), m, hc, trivial, hB, Frm.refl _ _⟩)
      (Fn.CmpS.correct (v := v) (outp := outp) hpre)

/-! ## In place: `mp_sub(a, b, a)`, `mp_add(a, b, a)` -/

/-- `mp_sub` keeps the destination's `alloc` (every branch is a `s_mp_add`/`s_mp_sub` with room). -/
theorem subPost_alloc {a b c c' : MpInt} (h : SubPost a b c c') : c'.alloc = c.alloc := by
  by_cases hs : a.sign = b.sign
  · by_cases hc : Tom.cmpMag a b = .lt
    · exact (h.lt hs hc).alloc
    · exact (h.ge hs hc).alloc
  · exact (h.diff hs).alloc

/-- `mp_add` keeps the destination's `alloc`. -/
theorem addPost_alloc {a b c c' : MpInt} (h : AddPost a b c c') : c'.alloc = c.alloc := by
  by_cases hs : a.sign = b.sign
  · exact (h.same hs).alloc
  · by_cases hc : Tom.cmpMag a b = .lt
    · exact (h.lt hs hc).alloc
    · exact (h.ge hs hc).alloc

structure SubSRes (p : TwoP) : Prop where
  va : p.a.Valid
  vb : p.b.Valid
  same : p.a.sign = p.b.sign
  room : max p.a.used p.b.used ≤ p.a.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 64 ≤ p.sp

structure AddDRes (p : TwoP) : Prop where
  va : p.a.Valid
  vb : p.b.Valid
  diff : p.a.sign ≠ p.b.sign
  room : max p.a.used p.b.used ≤ p.a.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 64 ≤ p.sp

/-- `mp_sub(a, b, a)`, same signs (`MpSubAddS.StatementS`). -/
def mpSubS : Contract where
  P := TwoP
  X := MpInt
  R := BinA.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := BinA.all
  entry := MpSubAlias.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
    (12, BitVec.ofNat 64 p.pa)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := BinA.lay 64 p.sp p.pa p.adp p.pb p.bdp p.a p.b
  kind := fun ⟨_, pa, adp, pb, bdp, a, b⟩ => Tom.Machine.BinA.kind pa adp pb bdp a b
  out := fun ⟨_, pa, adp, pb, bdp, _, b⟩ x => Tom.Machine.BinA.kind pa adp pb bdp x b
  isW := BinA.isWA
  ws := BinA.wsA
  Res := SubSRes
  Q p x := SubPost p.a p.b p.a x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.BinA.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.BinA.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpb, qbdp, qa, qb⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MpSubAddS.PreS m qsp qpa qadp qpb qbdp qa qb ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2
        ga := Hdr.geom (hB .aS).2, gb := Hdr.geom (hB .bS).2, rs := (hB .stk).2, sp_al := hres.sp_al
        sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2, va := hres.va, vb := hres.vb
        same := hres.same, room := hres.room, lay := hS }
    obtain ⟨c', hs, a', M, hat, hpost⟩ :=
      Fn.MpSubAddS.correctS (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, a', M, hat.sub rfl rfl, hpost.sub, ?_, hpost.frame⟩
    have hal := subPost_alloc hpost.sub
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame BinA.R.bS
    · exact hB.keep hS hpost.frame BinA.R.bD
    · exact hB.keep hS hpost.frame BinA.R.code

/-- `mp_add(a, b, a)`, different signs (`MpSubAddS.StatementD`). -/
def mpAddD : Contract where
  P := TwoP
  X := MpInt
  R := BinA.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := BinA.all
  entry := MpAddAlias.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
    (12, BitVec.ofNat 64 p.pa)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := BinA.lay 64 p.sp p.pa p.adp p.pb p.bdp p.a p.b
  kind := fun ⟨_, pa, adp, pb, bdp, a, b⟩ => Tom.Machine.BinA.kind pa adp pb bdp a b
  out := fun ⟨_, pa, adp, pb, bdp, _, b⟩ x => Tom.Machine.BinA.kind pa adp pb bdp x b
  isW := BinA.isWA
  ws := BinA.wsA
  Res := AddDRes
  Q p x := AddPost p.a p.b p.a x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.BinA.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.BinA.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpb, qbdp, qa, qb⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MpSubAddS.PreD m qsp qpa qadp qpb qbdp qa qb ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2
        ga := Hdr.geom (hB .aS).2, gb := Hdr.geom (hB .bS).2, rs := (hB .stk).2, sp_al := hres.sp_al
        sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2, va := hres.va, vb := hres.vb
        diff := hres.diff, room := hres.room, lay := hS }
    obtain ⟨c', hs, a', M, hat, hpost⟩ :=
      Fn.MpSubAddS.correctD (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, a', M, hat.sub rfl rfl, hpost.add, ?_, hpost.frame⟩
    have hal := addPost_alloc hpost.add
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame BinA.R.bS
    · exact hB.keep hS hpost.frame BinA.R.bD
    · exact hB.keep hS hpost.frame BinA.R.code

/-! ## `mp_mul_d(a, b, c)`, `c` distinct -/

structure MulDP where
  sp : Nat
  pa : Nat
  adp : Nat
  pc : Nat
  cdp : Nat
  a : MpInt
  b : Nat
  c : MpInt

structure MulDCRes (p : MulDP) : Prop where
  sa : p.a.Shape
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  sc : p.c.Shape
  hb : p.b < radix
  room : p.a.used + 1 ≤ p.c.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 80 ≤ p.sp

/-- `mp_mul_d(a, b, c)`. -/
def mulDC : Contract where
  P := MulDP
  X := MpInt
  R := Two.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Two.all
  entry := MulD.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.b),
    (12, BitVec.ofNat 64 p.pc)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Two.lay 80 p.sp p.pa p.adp p.pc p.cdp p.a p.c
  kind := fun ⟨_, pa, adp, pc, cdp, a, _, c⟩ => Tom.Machine.Two.kind pa adp pc cdp a c
  out := fun ⟨_, pa, adp, pc, cdp, a, _, _⟩ x => Tom.Machine.Two.kind pa adp pc cdp a x
  isW := Two.isW
  ws := Two.ws
  Res := MulDCRes
  Q p x := MulDPost p.a p.b p.c x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpc, qcdp, qa, qb, qc⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MulD.Pre m qsp qpa qadp qpc qcdp qa qb qc ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rc := Hdr.mpAt (hB .bS).2 (hB .bD).2, sa := hres.sa
        asign := hres.asign, sc := hres.sc, hb := hres.hb, ga := Hdr.geom (hB .aS).2
        gc := Hdr.geom (hB .bS).2, room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al
        sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, x, M, hat, hpost⟩ :=
      Fn.MulD.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, x, M, hat.sub rfl rfl, hpost.muld, ?_, hpost.frame⟩
    have hal := hpost.muld.alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact hB.keep hS hpost.frame Two.R.aS
    · exact hB.keep hS hpost.frame Two.R.aD
    · exact witS hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Two.R.code

/-! ## `__hidden___udivdi3(n, d)` -/

theorem udiv_ofNatF (n d : Nat) (hn : n < 2 ^ 64) (hd : d < 2 ^ 64) :
    BitVec.ofNat 64 n / BitVec.ofNat 64 d = BitVec.ofNat 64 (n / d) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]

theorem umod_ofNatF (n d : Nat) (hn : n < 2 ^ 64) (hd : d < 2 ^ 64) :
    BitVec.ofNat 64 n % BitVec.ofNat 64 d = BitVec.ofNat 64 (n % d) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hn)]

structure UDivResF (p : DivP) : Prop where
  n_lt : p.n < 2 ^ 64
  d_pos : 0 < p.d
  d_lt : p.d < 2 ^ 64

/-- `__hidden___udivdi3(n, d)` (`mp_div`'s step 3.1). -/
def udivdi3F : Contract where
  P := DivP
  X := Unit
  R := Cd
  all := [.code]
  hall r := by cases r; simp
  entry := Libgcc.udivdi3Entry
  args p := [(10, BitVec.ofNat 64 p.n), (11, BitVec.ofNat 64 p.d)]
  rets p ra := [(1, ra), (10, BitVec.ofNat 64 (p.n / p.d)), (11, BitVec.ofNat 64 (p.n % p.d))]
  lay _ _ := textIv
  kind _ _ := .code
  out _ _ _ := .code
  isW _ := false
  ws := []
  Res := UDivResF
  Q _ _ := True
  fits _ _ := Iv.sub_self _
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB
    have hd : BitVec.ofNat 64 p.d ≠ 0#64 := fun h => by
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hres.d_lt] at this
      exact absurd this (Nat.ne_of_gt hres.d_pos)
    have h := Fn.Libgcc.Udivdi3.correct (v := v) (outp := outp) (ra := ra) (n := BitVec.ofNat 64 p.n)
      (d := BitVec.ofNat 64 p.d) (hB .code).2 hra hd
    rw [udiv_ofNatF _ _ hres.n_lt hres.d_lt, umod_ofNatF _ _ hres.n_lt hres.d_lt] at h
    exact Triple.rmap (fun cf hc => ⟨(), m, hc, trivial, hB, Frm.refl _ _⟩) h

end Tom.Machine.Std
