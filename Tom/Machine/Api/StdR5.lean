import Tom.Machine.Api.Std
import Tom.Machine.Api.MulD
import Tom.Machine.Api.AddD
import Tom.Machine.Api.MulFast
import Tom.Machine.Api.SAddAlias
import Tom.Machine.Fn.MulDMain
import Tom.Machine.Fn.AddDPosI
import Tom.Machine.Fn.MulFastMain
import Tom.Machine.Fn.SAddAlias
import Tom.Machine.Kit.MeetD

/-!
# Standard contracts as `Contract` records: `mp_mul_d(a, b, a)`,
`mp_add_d(a, b, a)` for `a ≥ 0`, `s_mp_mul_digs_fast(a, b, c, digs)`, `s_mp_add(a, b, a)`

The callees of `mp_read_radix`, `mp_reduce_2k` and `s_mp_mul_digs`,
each its proved statement re-read as `Api/Std.lean`'s are: the Pre from the region bundle and a
scalar residue `Res`, the Post as the written regions' new witnesses.

* `mulDA`: `MulD.StatementInPlace` (`Fn.MulD.correct_inplace`), regions `Un` (stack 80).
  General in the struct's placement, so it also serves `mp_mul_d(&q, d, &q)` with `q` in a
  caller's frame (the caller gives `q`'s struct and digits their own regions).
* `addDA`: `AddD.StatementInPlacePos` at `F = 64` (`Fn.AddD.correct_inplace_pos`), regions `Un`.
* `mulFast`: `MulFast.Statement` (`Fn.MulFast.correct`), regions `Bin` (stack 2192); a plain
  `Contract`, so `tail_std` takes it (`s_mp_mul_digs`'s tail call at `42c4`).
* `sAddCA`: `SAddAlias.StatementCA` (`Fn.SAdd.correctCA`), regions `BinA` (stack 64).
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api

/-! ## One operand and a digit, in place: `mp_mul_d(a, b, a)`, `mp_add_d(a, b, a)` -/

structure DigP where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt
  b : Nat

structure MulDARes (p : DigP) : Prop where
  sa : p.a.Shape
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  hb : p.b < radix
  room : p.a.used + 1 ≤ p.a.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 80 ≤ p.sp

/-- `mp_mul_d(a, b, a)`. -/
def mulDA : Contract where
  P := DigP
  X := MpInt
  R := Un.R
  all := [.stk, .aS, .aD, .code]
  hall := Un.all
  entry := MulD.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.b),
    (12, BitVec.ofNat 64 p.pa)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Un.lay 80 p.sp p.pa p.adp p.a
  kind := fun ⟨_, pa, adp, a, _⟩ => Tom.Machine.Un.kind pa adp a
  out := fun ⟨_, pa, adp, _, _⟩ x => Tom.Machine.Un.kind pa adp x
  isW := Un.isW
  ws := Un.ws
  Res := MulDARes
  Q p x := MulDPost p.a p.b p.a x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qa, qb⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MulD.PreI m qsp qpa qadp qa qb ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, sa := hres.sa, asign := hres.asign, hb := hres.hb
        ga := Hdr.geom (hB .aS).2, room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al
        sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, a', M, hat, hpost⟩ :=
      Fn.MulD.correct_inplace (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, a', M, hat.sub rfl rfl, hpost.muld, ?_, hpost.frame⟩
    have hal := hpost.muld.alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Un.R.code

structure AddDARes (p : DigP) : Prop where
  va : p.a.Valid
  pos : p.a.sign = Layout.mpZpos
  hb : p.b < radix
  room : p.a.used + 1 ≤ p.a.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 64 ≤ p.sp

/-- `mp_add_d(a, b, a)` for `a ≥ 0` (stack 64: the branch that does not call `mp_sub_d`). -/
def addDA : Contract where
  P := DigP
  X := MpInt
  R := Un.R
  all := [.stk, .aS, .aD, .code]
  hall := Un.all
  entry := AddD.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.b),
    (12, BitVec.ofNat 64 p.pa)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Un.lay 64 p.sp p.pa p.adp p.a
  kind := fun ⟨_, pa, adp, a, _⟩ => Tom.Machine.Un.kind pa adp a
  out := fun ⟨_, pa, adp, _, _⟩ x => Tom.Machine.Un.kind pa adp x
  isW := Un.isW
  ws := Un.ws
  Res := AddDARes
  Q p x := AddDPost p.a p.b p.a x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qa, qb⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : AddD.PreI 64 m qsp qpa qadp qa qb ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, va := hres.va, hb := hres.hb
        ga := Hdr.geom (hB .aS).2, room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al
        sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, a', M, hat, hpost⟩ :=
      Fn.AddD.correct_inplace_pos (F := 64) (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp)
        (Nat.le_refl _) hpre hres.pos c (hc.sub rfl rfl)
    refine ⟨c', hs, a', M, hat.sub rfl rfl, hpost.addd, ?_, hpost.frame⟩
    have hal := (hpost.addd.pos hres.pos).alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Un.R.code

/-! ## Three operands: `s_mp_mul_digs_fast(a, b, c, digs)` (also as a tail call) -/

/-- `Api/Bin.lean`'s regions' kinds: `a`, `b` read, `c` the destination. -/
def binKind (pa adp pb bdp pc cdp : Nat) (a b c : MpInt) : Bin.R → Kind
  | .stk => .ram
  | .cS => .mpS pc cdp c
  | .cD => .mpD cdp c.alloc c.digit
  | .aS => .mpS pa adp a
  | .aD => .mpD adp a.alloc a.digit
  | .bS => .mpS pb bdp b
  | .bD => .mpD bdp b.alloc b.digit
  | .code => .code

structure FastP where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  pc : Nat
  cdp : Nat
  dg : Nat
  a : MpInt
  b : MpInt
  c : MpInt

structure FastRes (p : FastP) : Prop where
  sa : p.a.ShapeU
  sb : p.b.ShapeU
  sc : p.c.Shape
  cond : MulFast.Cond p.a p.b p.dg
  room : p.dg ≤ p.c.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 2192 ≤ p.sp

/-- `s_mp_mul_digs_fast(a, b, c, digs)`, `c` distinct from `a`, `b` (which may coincide). -/
def mulFast : Contract where
  P := FastP
  X := MpInt
  R := Bin.R
  all := [.stk, .cS, .cD, .aS, .aD, .bS, .bD, .code]
  hall := Bin.all
  entry := MulFast.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
    (12, BitVec.ofNat 64 p.pc), (13, BitVec.ofNat 64 p.dg)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Bin.lay 2192 p.sp p.pa p.adp p.pb p.bdp p.pc p.cdp p.a p.b p.c
  kind := fun ⟨_, pa, adp, pb, bdp, pc, cdp, _, a, b, c⟩ => binKind pa adp pb bdp pc cdp a b c
  out := fun ⟨_, pa, adp, pb, bdp, pc, cdp, _, a, b, _⟩ x => binKind pa adp pb bdp pc cdp a b x
  isW := Bin.isW
  ws := Bin.ws
  Res := FastRes
  Q p x := MulFastPost p.a p.b p.c x p.dg
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [binKind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [binKind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpb, qbdp, qpc, qcdp, qdg, qa, qb, qc⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MulFast.Pre m qsp qpa qadp qpb qbdp qpc qcdp qdg qa qb qc ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2
        rc := Hdr.mpAt (hB .cS).2 (hB .cD).2, sa := hres.sa, sb := hres.sb, sc := hres.sc
        ga := Hdr.geom (hB .aS).2, gb := Hdr.geom (hB .bS).2, gc := Hdr.geom (hB .cS).2
        cond := hres.cond, room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al
        sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, x, M, hat, hpost⟩ :=
      Fn.MulFast.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, x, M, hat.sub rfl rfl, hpost.fast, ?_, hpost.frame⟩
    have hal := hpost.fast.alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.repr (Hdr.geom (hB .cS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .cS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Bin.R.aS
    · exact hB.keep hS hpost.frame Bin.R.aD
    · exact hB.keep hS hpost.frame Bin.R.bS
    · exact hB.keep hS hpost.frame Bin.R.bD
    · exact hB.keep hS hpost.frame Bin.R.code

/-! ## `s_mp_add(a, b, a)` (in place, `c = a`) -/

structure AddARes (p : TwoP) : Prop where
  sa : p.a.Shape
  sb : p.b.Shape
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  room : max p.a.used p.b.used + 1 ≤ p.a.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 64 ≤ p.sp

def sAddCA : Contract where
  P := TwoP
  X := MpInt
  R := BinA.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := BinA.all
  entry := SAddAlias.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
    (12, BitVec.ofNat 64 p.pa)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := BinA.lay 64 p.sp p.pa p.adp p.pb p.bdp p.a p.b
  kind := fun ⟨_, pa, adp, pb, bdp, a, b⟩ => Tom.Machine.BinA.kind pa adp pb bdp a b
  out := fun ⟨_, pa, adp, pb, bdp, _, b⟩ x => Tom.Machine.BinA.kind pa adp pb bdp x b
  isW := BinA.isWA
  ws := BinA.wsA
  Res := AddARes
  Q p x := SAddPost p.a p.b p.a x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.BinA.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.BinA.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpb, qbdp, qa, qb⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : SAddAlias.PreCA m qsp qpa qadp qpb qbdp qa qb ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2
        ga := Hdr.geom (hB .aS).2, gb := Hdr.geom (hB .bS).2, rs := (hB .stk).2, sp_al := hres.sp_al
        sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2, sa := hres.sa, sb := hres.sb
        asign := hres.asign, room := hres.room, lay := hS }
    obtain ⟨c', hs, a', M, hat, hpost⟩ :=
      Fn.SAdd.correctCA (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, a', M, hat.sub rfl rfl, hpost.sadd, ?_, hpost.frame⟩
    have hal := hpost.sadd.alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame BinA.R.bS
    · exact hB.keep hS hpost.frame BinA.R.bD
    · exact hB.keep hS hpost.frame BinA.R.code

end Tom.Machine.Std
