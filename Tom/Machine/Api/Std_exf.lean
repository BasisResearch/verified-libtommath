import Tom.Machine.Api.Std_r6d
import Tom.Machine.Api.Std_r10aM
import Tom.Machine.Api.DrReduce
import Tom.Machine.Api.DrSetup
import Tom.Machine.Api.MpMontSetup
import Tom.Machine.Api.MontNorm
import Tom.Machine.Api.Reduce2kSetup
import Tom.Machine.Api.MpReduce2k
import Tom.Machine.Fn.DrReduceMain
import Tom.Machine.Fn.DrSetupMain
import Tom.Machine.Fn.MpMontSetupMain
import Tom.Machine.Fn.MontNormMain
import Tom.Machine.Fn.Reduce2kSetupMainG
import Tom.Machine.Fn.MpReduce2kMainG
import Tom.Machine.Fn.MpMulmodMainG
import Tom.Machine.Kit.Placed

/-!
# Callee contracts of `s_mp_exptmod_fast`

The callees whose proofs are stated in the older Pre/Post form (or as allocating `Statement`s
without a callee record), as `Contract`/`HContract` records:

* `montSetupC`: `mp_montgomery_setup(n, &rho)` on an odd `n` (`MP_OKAY`, `*rho = setupRho n->dp[0]`),
  `*rho` a one-word cell written as the one-digit array `rho`;
* `drSetupC`: `mp_dr_setup(a, &d)`, `*d := drSetupDigit a`;
* `montNormC`: `mp_montgomery_calc_normalization(a, b)` (`a` written, `alloc` kept);
* `drRedC`: `mp_dr_reduce(x, n, k)` (as `montRedF`: Two's `a` read, `b` written);
* `red2kSetupH`: `mp_reduce_2k_setup(a, &d)` (`Fn.Reduce2kSetupG5.correct`);
* `mpReduce2kH`: `mp_reduce_2k(a, n, d)` (`Fn.MpReduce2kG5.correct`);
* `mpMulmodH`: `mp_mulmod(a, b, c, d)` (`Fn.MpMulmodG5.correct`, its `mul` premise in the residue).
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Mont

/-- A one-word cell written with `v` (`< 2^32`): the one-digit array `fun _ => v`. -/
theorem cellDig {M : Mem} {pd v : Nat} (hr : Ram pd 4) (hal : pd % 4 = 0) (_hv : v < 2 ^ 32)
    (hb : bytesT4 M pd = BitVec.ofNat 32 v) : Dig M pd 1 (fun _ => v) :=
  ⟨by simpa using hr, hal, fun j hj => by
    have : j = 0 := by omega
    subst this; simpa using hb⟩

/-! ## `mp_montgomery_setup(n, &rho)` -/

structure MSetP where
  sp : Nat
  pn : Nat
  ndp : Nat
  prho : Nat
  n : MpInt

structure MSetRes (p : MSetP) : Prop where
  sn : p.n.Shape
  npos : 0 < p.n.alloc
  odd : p.n.digit 0 % 2 = 1
  al : p.prho % 4 = 0
  sp_al : p.sp % 16 = 0
  sp_ge : 48 ≤ p.sp

def MSetP.kind (p : MSetP) : MpMontSetup.R → Kind
  | .nS => .mpS p.pn p.ndp p.n
  | .nD => .mpD p.ndp p.n.alloc p.n.digit
  | .code => .code
  | _ => .ram

def MSetP.out (p : MSetP) (x : Nat) : MpMontSetup.R → Kind
  | .rho => .mpD p.prho 1 (fun _ => x)
  | r => p.kind r

def montSetupC : Contract where
  P := MSetP
  X := Nat
  R := MpMontSetup.R
  all := [.stk, .nS, .nD, .rho, .code]
  hall r := by cases r <;> simp
  entry := Fn.MpMontSetup.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pn), (11, BitVec.ofNat 64 p.prho)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := MpMontSetup.lay p.sp p.pn p.ndp p.prho p.n
  kind := MSetP.kind
  out := MSetP.out
  isW := MpMontSetup.isW
  ws := MpMontSetup.ws
  Res := MSetRes
  Q p x := x = setupRho (p.n.digit 0)
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases r <;> simp_all [MSetP.out, MSetP.kind, Kind.isRam]
  out_ind p x r _ h := by cases r <;> simp_all [MSetP.out, MSetP.kind, Kind.isRam, Kind.indep]
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpn, qndp, qprho, qn⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MpMontSetup.Pre m ⟨_, gp, tp, s0, s⟩ qsp qpn qndp qprho qn ra :=
      { repr := Hdr.mpAt (hB .nS).2 (hB .nD).2, shape := hres.sn, apos := hres.npos, gn := Hdr.geom (hB .nS).2
        rr := (hB .rho).2, r_al := hres.al, rs := (hB .stk).2, sp_al := hres.sp_al, sp_ge := hres.sp_ge
        sp_v := rfl, ra_al := hra, img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, ret, rho, M, hat, hpost⟩ := Fn.MpMontSetup.correct (outp := outp) hpre c (hc.sub rfl rfl)
    obtain ⟨hret, hrho⟩ := hpost.setup.odd hres.odd
    subst hret
    have hlt : rho < 2 ^ 32 := by
      rw [hrho]; exact Nat.lt_of_lt_of_le (setupRho_lt _) (by decide)
    refine ⟨c', hs, rho, M, hat.sub rfl rfl, hrho, ?_, hpost.frame⟩
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact hB.keep hS hpost.frame MpMontSetup.R.nS
    · exact hB.keep hS hpost.frame MpMontSetup.R.nD
    · exact ⟨Iv.sub_self _, cellDig (hB .rho).2 hres.al hlt hpost.rho_v⟩
    · exact hB.keep hS hpost.frame MpMontSetup.R.code

/-! ## `mp_dr_setup(a, &d)` -/

structure DSetP where
  pa : Nat
  adp : Nat
  pd : Nat
  a : MpInt

def DSetP.kind (p : DSetP) : DrSetup.R → Kind
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .code => .code
  | .dW => .ram

def DSetP.out (p : DSetP) : DrSetup.R → Kind
  | .dW => .mpD p.pd 1 (fun _ => drSetupDigit p.a)
  | r => p.kind r

def drSetupC : Contract where
  P := DSetP
  X := Unit
  R := DrSetup.R
  all := [.dW, .aS, .aD, .code]
  hall r := by cases r <;> simp
  entry := DrSetup.entry
  args p := [(10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pd)]
  rets _ ra := [(1, ra)]
  lay p := DrSetup.lay p.pd p.pa p.adp p.a
  kind := DSetP.kind
  out p _ := DSetP.out p
  isW := DrSetup.isW
  ws := [.dW]
  Res p := p.a.Shape ∧ 1 ≤ p.a.alloc ∧ p.pd % 4 = 0
  Q _ _ := True
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases r <;> simp_all [DSetP.out, Kind.isRam]
  out_ind p x r _ h := by cases r <;> simp_all [DSetP.out, Kind.isRam, Kind.indep]
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qpa, qadp, qpd, qa⟩ := p
    have hpre : DrSetup.Pre m qpa qadp qpd qa ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, sa := hres.1, ga := Hdr.geom (hB .aS).2, alloc_pos := hres.2.1
        rd := (hB .dW).2, pd_al := hres.2.2, ra_al := hra, img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, M, hat, hpost⟩ := Fn.DrSetup.correct (v := v) (outp := outp) hpre c (hc.sub rfl rfl)
    have hlt : drSetupDigit qa < 2 ^ 32 := by
      unfold drSetupDigit; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide)
    refine ⟨c', hs, (), M, hat.sub rfl rfl, trivial, ?_, hpost.frame⟩
    intro r; cases r
    · exact ⟨Iv.sub_self _, cellDig (hB .dW).2 hres.2.2 hlt hpost.res⟩
    · exact hB.keep hS hpost.frame DrSetup.R.aS
    · exact hB.keep hS hpost.frame DrSetup.R.aD
    · exact hB.keep hS hpost.frame DrSetup.R.code

/-! ## `mp_montgomery_calc_normalization(a, b)` -/

structure NormRes (p : TwoP) : Prop where
  sa : p.a.Shape
  vb : p.b.Valid
  odd : p.b.mag % 2 = 1
  gt1 : 1 < p.b.mag
  bits : Layout.digitBits * p.b.used < 2 ^ 31
  room : p.b.used + 1 ≤ p.a.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 112 ≤ p.sp

def montNormC : Contract where
  P := TwoP
  X := MpInt
  R := BinA.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := BinA.all
  entry := MontNorm.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]
  rets p ra := [(1, ra), (10, 0#64)]
  lay p := BinA.lay 112 p.sp p.pa p.adp p.pb p.bdp p.a p.b
  kind p := Tom.Machine.BinA.kind p.pa p.adp p.pb p.bdp p.a p.b
  out p x := Tom.Machine.BinA.kind p.pa p.adp p.pb p.bdp x p.b
  isW := BinA.isWA
  ws := BinA.wsA
  Res := NormRes
  Q p x := NormPost p.b x ∧ x.alloc = p.a.alloc
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases r <;> simp_all [Tom.Machine.BinA.kind, Kind.isRam]
  out_ind p x r _ h := by cases r <;> simp_all [Tom.Machine.BinA.kind, Kind.isRam, Kind.indep]
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpb, qbdp, qa, qb⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MontNorm.Pre m qsp qpa qadp qpb qbdp qa qb ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2, sa := hres.sa, vb := hres.vb
        ga := Hdr.geom (hB .aS).2, gb := Hdr.geom (hB .bS).2, odd := hres.odd, gt1 := hres.gt1, bits := hres.bits
        room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al, sp_ge := hres.sp_ge, ra_al := hra
        img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, a', M, hat, hpost⟩ :=
      Fn.MontNorm.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, a', M, hat.sub rfl rfl, ⟨hpost.norm, hpost.alloc⟩, ?_, hpost.frame⟩
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.repr (Hdr.geom (hB .aS).2) hpost.alloc (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .aS).2) hpost.alloc (Iv.sub_self _)
    · exact hB.keep hS hpost.frame BinA.R.bS
    · exact hB.keep hS hpost.frame BinA.R.bD
    · exact hB.keep hS hpost.frame BinA.R.code

/-! ## `mp_dr_reduce(x, n, k)` -/

structure DrRedRes (p : RedFP) : Prop where
  vx : p.x.Valid
  vn : p.n.Valid
  n_pos : 0 < p.n.mag
  k_lt : p.rho < radix
  x_lt : p.x.mag < radix ^ (2 * p.n.used)
  room : 2 * p.n.used ≤ p.x.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 176 ≤ p.sp

def drRedC : Contract where
  P := RedFP
  X := MpInt
  R := Two.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Two.all
  entry := DrReduce.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.px), (11, BitVec.ofNat 64 p.pn),
    (12, BitVec.ofNat 64 p.rho)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Two.lay 176 p.sp p.pn p.ndp p.px p.xdp p.n p.x
  kind := fun ⟨_, px, xdp, pn, ndp, x, n, _⟩ => Tom.Machine.Two.kind pn ndp px xdp n x
  out := fun ⟨_, px, xdp, pn, ndp, _, n, _⟩ x' => Tom.Machine.Two.kind pn ndp px xdp n x'
  isW := Two.isW
  ws := Two.ws
  Res := DrRedRes
  Q p x' := Reduce.DrReducePost p.x p.n p.rho x' ∧ x'.alloc = p.x.alloc
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpx, qxdp, qpn, qndp, qx, qn, qrho⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : DrReduce.Pre m qsp qpx qxdp qpn qndp qx qn qrho ra :=
      { rx := Hdr.mpAt (hB .bS).2 (hB .bD).2, rn := Hdr.mpAt (hB .aS).2 (hB .aD).2, vx := hres.vx
        vn := hres.vn, gx := Hdr.geom (hB .bS).2, gn := Hdr.geom (hB .aS).2, n_pos := hres.n_pos
        k_lt := hres.k_lt, x_lt := hres.x_lt, room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al
        sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, x', M, hat, hpost⟩ :=
      Fn.DrReduce.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, x', M, hat.sub rfl rfl, ⟨hpost.dr, hpost.alloc⟩, ?_, hpost.frame⟩
    have hal := hpost.alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact hB.keep hS hpost.frame Two.R.aS
    · exact hB.keep hS hpost.frame Two.R.aD
    · exact witS hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Two.R.code

/-! ## `mp_reduce_2k_setup(a, &d)`, `mp_reduce_2k(a, n, d)`, `mp_mulmod(a, b, c, d)` -/

def red2kSetupH : HContract where
  P := Reduce2kSetup.P
  X := Option Nat
  R := Reduce2kSetup.R
  all := [.stk, .aS, .aD, .dD, .code]
  hall := Reduce2kSetup.all
  entry := Reduce2kSetup.entry
  args := Reduce2kSetup.args
  rets := Reduce2kSetup.rets
  lay := Reduce2kSetup.lay
  kind := Reduce2kSetup.kind
  out := Reduce2kSetup.out
  isW := Reduce2kSetup.isW
  ws := Reduce2kSetup.ws
  site := .dD
  site' p _ := Reduce2kSetup.lay p .dD
  hin := Reduce2kSetup.hin
  hout p _ := Reduce2kSetup.hin p
  Res := Reduce2kSetup.Res
  Q := Reduce2kSetup.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | _ <;> cases r <;> simp_all [Reduce2kSetup.out, Reduce2kSetup.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos
    cases r with
    | stk => exact .inl (show 0 < Reduce2kSetup.F by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | dD => exact .inl (show 0 < 4 * 1 by decide)
    | code => exact .inl (show 0 < textLen by decide)
    | aS => exact .inl (show 0 < 24 by decide)
  spec := Fn.Reduce2kSetupG5.correct

def mpReduce2kH : HContract where
  P := MpReduce2k.P
  X := Option MpInt
  R := MpReduce2k.R
  all := [.stk, .aS, .aD, .nS, .nD, .code]
  hall := MpReduce2k.all
  entry := MpReduce2k.entry
  args := MpReduce2k.args
  rets := MpReduce2k.rets
  lay := MpReduce2k.lay
  kind := MpReduce2k.kind
  out := MpReduce2k.out
  isW := MpReduce2k.isW
  ws := MpReduce2k.ws
  site := .aD
  site' := MpReduce2k.site'
  hin := MpReduce2k.hin
  hout := MpReduce2k.hout
  Res := MpReduce2k.Res
  Q := MpReduce2k.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | _ <;> cases r <;> simp_all [MpReduce2k.out, MpReduce2k.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.aroom; have := Tom.Machine.MpInt.alloc_pos_of_mag h.vn h.npos
    cases r with
    | stk => exact .inl (show 0 < MpReduce2k.F by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | nD => exact .inl (show 0 < 4 * p.n.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | aS | nS => exact .inl (show 0 < 24 by decide)
  spec := Fn.MpReduce2kG5.correct

def mpMulmodH : HContract where
  P := MpMulmod.P
  X := MpMulmod.Out
  R := MpMulmod.R
  all := [.stk, .aS, .aD, .bS, .bD, .cS, .cD, .dS, .dD, .kc, .tc, .code]
  hall := MpMulmod.all
  entry := MpMulmod.entry
  args := MpMulmod.args
  rets := MpMulmod.rets
  lay := MpMulmod.lay
  kind := MpMulmod.kind
  out := MpMulmod.out
  isW := MpMulmod.isW
  ws := MpMulmod.ws
  site := .dD
  site' := MpMulmod.site'
  hin := MpMulmod.hin
  hout := MpMulmod.hout
  Res := MpMulmod.Res
  Q := MpMulmod.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _ | simp [Kind.Fits, MpMulmod.kind, MpMulmod.lay, Iv.Sub]
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | _ <;> cases r <;> simp_all [MpMulmod.out, MpMulmod.kind, MpMulmod.ws, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bpos; have := h.dpos; have := h.vc.used_le
    have := h.c0
    cases r with
    | stk => exact .inl (by simp only [MpMulmod.lay]; omega)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | cD => exact .inl (show 0 < 4 * p.c.alloc by omega)
    | dD => exact .inl (show 0 < 4 * p.d.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (by simp [MpMulmod.lay])
  spec := Fn.MpMulmodG5.correct

/-! ## A plain contract as an allocating one (the heap unchanged, the site written in place) -/

/-- **A plain contract's run with the heap**: its post as `HPost` with the site kept in place and the
same blocks (`HPost.inplace`): a caller whose written regions are not all in its own frame's written
list (a table entry) calls it by `call_heap`. -/
theorem Contract.hspec (C : Contract) (site : C.R) (p : C.P) {H : List (Nat × Nat)} {m : Mem} {v : Abi}
    {outp : Array String} {ra : BitVec 64} (hra : ra.toNat % 4 = 0) (hres : C.Res p)
    (hS : Sound (C.lay p) C.isW) (hB : Bundle (C.lay p) (C.kind p) m) (hH : AHeap m H)
    (hoff : ∀ r, Off (C.lay p r) H) :
    Triple (At C.entry ((1, ra) :: C.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (C.rets p ra) M v.keep outp cf ∧ C.Q p x ∧
        HPost (C.lay p) C.ws site (C.out p x) (C.lay p site) H H m M) :=
  Triple.rmap (fun _ ⟨x, M, hat, hq, hb, hF⟩ =>
    ⟨x, M, hat, hq, HPost.inplace (ws := C.ws) ⟨hS, hb, hF⟩ hH hoff rfl rfl (fun r _ _ => hb r) (hb site)⟩)
    (C.spec hra hres hS hB)

/-- `mp_copy(a, b)` with the heap (`b`'s digits the site, kept in place). -/
structure CopyHP where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt
  H : List (Nat × Nat)

def CopyHP.toP (p : CopyHP) : TwoP := ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b⟩

def mpCopyH : HContract where
  P := CopyHP
  X := MpInt
  R := Two.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Two.all
  entry := MpCopy.entry
  args p := mpCopy.args p.toP
  rets p _ ra := mpCopy.rets p.toP ra
  lay p := mpCopy.lay p.toP
  kind p := mpCopy.kind p.toP
  out p := mpCopy.out p.toP
  isW := Two.isW
  ws := Two.ws
  site := .bD
  site' p _ := mpCopy.lay p.toP .bD
  hin p := p.H
  hout p _ := p.H
  Res p := CopyRes p.toP ∧ 0 < p.a.alloc ∧ 0 < p.b.alloc
  Q p := mpCopy.Q p.toP
  fits p r := mpCopy.fits p.toP r
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr _ h := mpCopy.out_ind p.toP x r hr h
  pos p h r := by
    have := h.2.1; have := h.2.2; have := h.1.sp_ge
    cases r with
    | stk => exact .inl (show 0 < 32 by decide)
    | aS | bS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec hra hres hS hB hH hoff := Contract.hspec mpCopy .bD _ hra hres.1 hS hB hH hoff

end Tom.Machine.Std
