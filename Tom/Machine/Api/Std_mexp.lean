import Tom.Machine.Api.StdNorm
import Tom.Machine.Api.Reduce2kL
import Tom.Machine.Api.DrIsModulus
import Tom.Machine.Api.Reduce2k
import Tom.Machine.Fn.Reduce2kLMain
import Tom.Machine.Fn.DrIsModulusMain
import Tom.Machine.Fn.Reduce2kMain
import Tom.Machine.Api.MpExptmod
import Tom.Machine.Api.Std_inv

/-!
# `mp_exptmod`'s three modulus predicates as `Contract` records

`mp_reduce_is_2k_l(P)`, `mp_dr_is_modulus(P)` (nothing written, no stack: `Ob`'s regions, as
`Std.cntBits`) and `mp_reduce_is_2k(P)` (a 16-byte frame: `Un`'s regions, written `stk` only), each
returning its frozen contract's value in `a0`; `mp_exptmod`'s allocating callees: the two
workers as tail calls over `mp_exptmod`'s own layout (`sExptFastT`, `sExptT`: the residue says
the reservations agree), `mp_invmod` (`mpInvmodH`) and the recursive call on a nonnegative
exponent (`mpExptmodNNH`), their statements carried in the residues.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api

/-- `mp_reduce_is_2k_l(a)`: `a0 = isReduce2kL a`. -/
def reduceIs2kLc : Contract where
  P := ObP
  X := Unit
  R := Ob
  all := [.S, .D, .code]
  hall := Ob.all
  entry := Reduce2kL.entry
  args p := [(10, BitVec.ofNat 64 p.p)]
  rets p ra := [(1, ra), (10, BitVec.ofNat 64 (isReduce2kL p.a))]
  lay p := Ob.lay p.p p.dp p.a.alloc
  kind := fun ⟨p, dp, a⟩ => Ob.kind p dp a
  out := fun ⟨p, dp, a⟩ _ => Ob.kind p dp a
  isW _ := false
  ws := []
  Res p := p.a.Shape
  Q _ _ := True
  fits p r := by cases p; cases r <;> exact Iv.sub_self _
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB
    obtain ⟨qp, qdp, qa⟩ := p
    exact Triple.rmap (fun cf hc => ⟨(), m, hc, trivial, hB, Frm.refl _ _⟩) (Fn.Reduce2kL.correct (v := v)
      (outp := outp) { ra_ := Hdr.mpAt (hB .S).2 (hB .D).2, sa := hres, ga := Hdr.geom (hB .S).2,
                       ra_al := hra, img := (hB .code).2 })

/-- `mp_dr_is_modulus(a)`: `a0 = 1` for a DR modulus, else `0`. -/
def drIsModc : Contract where
  P := ObP
  X := Unit
  R := Ob
  all := [.S, .D, .code]
  hall := Ob.all
  entry := DrIsModulus.entry
  args p := [(10, BitVec.ofNat 64 p.p)]
  rets p ra := [(1, ra), (10, BitVec.ofNat 64 (if IsDrModulus p.a then 1 else 0))]
  lay p := Ob.lay p.p p.dp p.a.alloc
  kind := fun ⟨p, dp, a⟩ => Ob.kind p dp a
  out := fun ⟨p, dp, a⟩ _ => Ob.kind p dp a
  isW _ := false
  ws := []
  Res p := p.a.Shape
  Q _ _ := True
  fits p r := by cases p; cases r <;> exact Iv.sub_self _
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB
    obtain ⟨qp, qdp, qa⟩ := p
    exact Triple.rmap (fun cf hc => ⟨(), m, hc, trivial, hB, Frm.refl _ _⟩) (Fn.DrIsModulus.correct (v := v)
      (outp := outp) { ra_ := Hdr.mpAt (hB .S).2 (hB .D).2, sa := hres, ga := Hdr.geom (hB .S).2,
                       ra_al := hra, img := (hB .code).2 })

structure Is2kP where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt

structure Is2kRes (p : Is2kP) : Prop where
  va : p.a.Valid
  bits : Layout.digitBits * p.a.used < 2 ^ 31
  sp_al : p.sp % 16 = 0
  sp_ge : 16 ≤ p.sp

/-- `mp_reduce_is_2k(a)`: `a0 = isReduce2k a`, its 16-byte frame written. -/
def reduceIs2kc : Contract where
  P := Is2kP
  X := Unit
  R := Un.R
  all := [.stk, .aS, .aD, .code]
  hall := Un.all
  entry := Reduce2k.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa)]
  rets p ra := [(1, ra), (10, BitVec.ofNat 64 (isReduce2k p.a))]
  lay p := Un.lay 16 p.sp p.pa p.adp p.a
  kind := fun ⟨_, pa, adp, a⟩ => Tom.Machine.Un.kind pa adp a
  out := fun ⟨_, pa, adp, a⟩ _ => Tom.Machine.Un.kind pa adp a
  isW := Un.isR
  ws := Un.wsR
  Res := Is2kRes
  Q _ _ := True
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qa⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : Reduce2k.Pre m qsp qpa qadp qa ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, va := hres.va, ga := Hdr.geom (hB .aS).2, bits := hres.bits
        rs := (hB .stk).2, sp_al := hres.sp_al, sp_ge := hres.sp_ge, ra_al := hra
        img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, M, hat, hfr⟩ :=
      Fn.Reduce2k.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, (), M, hat.sub rfl rfl, trivial, ?_, hfr⟩
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact hB.keep hS hfr Un.R.aS
    · exact hB.keep hS hfr Un.R.aD
    · exact hB.keep hS hfr Un.R.code

/-! ## `mp_exptmod`'s allocating callees -/

section
open Tom.Machine.Api.Exptmod (P R lay kind out isW ws site' hin hout rets Base Out)

theorem Exptmod.pos {F : Nat} {p : Exptmod.P} (h : Base F p) (hF : 0 < F) (r : Exptmod.R) :
    0 < (lay F p r).len ∨ (lay F p r).base < heapStart ∨ heapEnd ≤ (lay F p r).base := by
  have := h.gpos; have := h.xpos; have := h.npos; have := h.ypos
  left
  cases r with
  | code => exact (show 0 < textLen by decide)
  | stk => exact hF
  | gS | xS | nS | yS => exact (show 0 < 24 by decide)
  | gD => exact (show 0 < 4 * p.g.alloc by omega)
  | xD => exact (show 0 < 4 * p.x.alloc by omega)
  | nD => exact (show 0 < 4 * p.n.alloc by omega)
  | yD => exact (show 0 < 4 * p.y.alloc by omega)
  | ks | ts | kc | tc => exact (show 0 < 4 by decide)

theorem Exptmod.out_ind (p : Exptmod.P) (x : Out) (r : Exptmod.R) (h : (out p x r).isRam = false) :
    (out p x r).indep = true := by
  cases x <;> cases r <;> simp_all [Exptmod.out, Exptmod.kind, Kind.isRam, Kind.indep]

theorem Exptmod.fits (F : Nat) (p : Exptmod.P) (r : Exptmod.R) : (kind p r).Fits (lay F p r) := by
  cases r <;> first | trivial | exact Iv.sub_self _

/-- A worker's tail call: its run over `mp_exptmod`'s reservation, equal to its own. -/
structure WorkRes (Fw : Exptmod.P → Nat) (Res : Exptmod.P → Prop) (St : Prop) (p : Exptmod.P) : Prop where
  res : Res p
  stmt : St
  eqF : MpExptmod.F p = Fw p

theorem WorkRes.base {Fw : Exptmod.P → Nat} {Res : Exptmod.P → Prop} {St : Prop} {p : Exptmod.P}
    (h : WorkRes Fw Res St p) (hb : Res p → Base (Fw p) p) (hF : 0 < Fw p) (r : Exptmod.R) :
    0 < (lay (MpExptmod.F p) p r).len ∨ (lay (MpExptmod.F p) p r).base < heapStart ∨
      heapEnd ≤ (lay (MpExptmod.F p) p r).base := by
  rw [h.eqF]; exact Exptmod.pos (hb h.res) hF r

/-- `s_mp_exptmod_fast` called by `j` from `mp_exptmod`. -/
def sExptFastT : HContract where
  P := Exptmod.P
  X := Out
  R := Exptmod.R
  all := [.stk, .gS, .gD, .xS, .xD, .nS, .nD, .yS, .yD, .ks, .ts, .kc, .tc, .code]
  hall := Exptmod.all
  entry := SMpExptmodFast.entry
  args := Exptmod.args
  rets := rets
  lay p := lay (MpExptmod.F p) p
  kind := kind
  out := out
  isW := isW
  ws := ws
  site := .yD
  site' p := site' (MpExptmod.F p) p
  hin := hin
  hout := hout
  Res := WorkRes SMpExptmodFast.F SMpExptmodFast.Res SMpExptmodFast.Statement
  Q := SMpExptmodFast.Q
  fits p r := Exptmod.fits _ p r
  site_ws := by decide
  site_w := rfl
  out_ind p x r _ _ h := Exptmod.out_ind p x r h
  pos p h := h.base (fun h' => h'.toBase) (by show 0 < SMpExptmodFast.Ff p.g p.n; unfold SMpExptmodFast.Ff; omega)
  spec := by
    intro p m v outp ra hra hres
    rw [hres.eqF]; exact hres.stmt hra hres.res

/-- `s_mp_exptmod` called by `j` from `mp_exptmod`. -/
def sExptT : HContract where
  P := Exptmod.P
  X := Out
  R := Exptmod.R
  all := [.stk, .gS, .gD, .xS, .xD, .nS, .nD, .yS, .yD, .ks, .ts, .kc, .tc, .code]
  hall := Exptmod.all
  entry := SMpExptmod.entry
  args := Exptmod.args
  rets := rets
  lay p := lay (MpExptmod.F p) p
  kind := kind
  out := out
  isW := isW
  ws := ws
  site := .yD
  site' p := site' (MpExptmod.F p) p
  hin := hin
  hout := hout
  Res := WorkRes SMpExptmod.F SMpExptmod.Res SMpExptmod.Statement
  Q := SMpExptmod.Q
  fits p r := Exptmod.fits _ p r
  site_ws := by decide
  site_w := rfl
  out_ind p x r _ _ h := Exptmod.out_ind p x r h
  pos p h := h.base (fun h' => h'.toBase) (by show 0 < SMpExptmod.Fs p.g p.n; unfold SMpExptmod.Fs; omega)
  spec := by
    intro p m v outp ra hra hres
    rw [hres.eqF]; exact hres.stmt hra hres.res

structure InvRes (p : Invmod.P) : Prop where
  res : Invmod.BaseG p
  stmt : MpInvmodG.Statement

/-- `mp_invmod(a, b, c)` as an allocating contract (`b` of any size). -/
def mpInvmodH : HContract where
  P := Invmod.P
  X := Invmod.Out
  R := Invmod.R
  all := [.stk, .aS, .aD, .bS, .bD, .cS, .cD, .code]
  hall := Invmod.all
  entry := MpInvmod.entry
  args := Invmod.args
  rets := Invmod.rets
  lay := Invmod.lay
  kind := Invmod.kind
  out := Invmod.out
  isW := Invmod.isW
  ws := Invmod.ws
  site := .cD
  site' := Invmod.site'
  hin := Invmod.hin
  hout := Invmod.hout
  Res := InvRes
  Q p x := MpInvmod.Q p x ∧ ∀ q c', x = .ok q c' → 0 < c'.alloc
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r _ _ h := Invmod.out_ind p x r h
  pos p h := Invmod.pos h.res
  spec := by
    intro p m v outp ra hra hres hS hB hH hoff
    exact Triple.rmap (fun _ ⟨x, M, hat, hq, hpo⟩ => ⟨x, M, hat, ⟨hq, fun q c' hx => by
      subst hx; exact Off.pos_blk hpo.off hpo.heap.heap (List.mem_cons_self ..)⟩, hpo⟩)
      (hres.stmt hra hres.res hS hB hH hoff)

structure NNRes (p : Exptmod.P) : Prop where
  res : MpExptmod.Res p
  xs : p.x.sign ≠ Layout.mpNeg
  stmt : MpExptmod.StatementNN

/-- The recursive `mp_exptmod(&tmpG, &tmpX, P, Y)` on a nonnegative exponent. -/
def mpExptmodNNH : HContract where
  P := Exptmod.P
  X := Out
  R := Exptmod.R
  all := [.stk, .gS, .gD, .xS, .xD, .nS, .nD, .yS, .yD, .ks, .ts, .kc, .tc, .code]
  hall := Exptmod.all
  entry := MpExptmod.entry
  args := MpExptmod.args
  rets := rets
  lay p := lay (MpExptmod.F p) p
  kind := kind
  out := out
  isW := isW
  ws := ws
  site := .yD
  site' p := site' (MpExptmod.F p) p
  hin := hin
  hout := hout
  Res := NNRes
  Q p x := MpExptmod.Q p x ∧ ∀ q y', x = .ok q y' → 0 < y'.alloc
  fits p r := Exptmod.fits _ p r
  site_ws := by decide
  site_w := rfl
  out_ind p x r _ _ h := Exptmod.out_ind p x r h
  pos p h := Exptmod.pos h.res.toBase (by rw [MpExptmod.F_nn h.xs]; have := MpExptmod.frame_le_Fd p; omega)
  spec := by
    intro p m v outp ra hra hres hS hB hH hoff
    exact Triple.rmap (fun _ ⟨x, M, hat, hq, hpo⟩ => ⟨x, M, hat, ⟨hq, fun q y' hx => by
      subst hx; exact Off.pos_blk hpo.off hpo.heap.heap (List.mem_cons_self ..)⟩, hpo⟩)
      (hres.stmt hra ⟨hres.res, hres.xs⟩ hS hB hH hoff)

end

/-! ## `mp_exptmod`'s residues for its tail calls -/

theorem _root_.Tom.Machine.Api.Exptmod.Base.restk {F F' : Nat} {p : Exptmod.P} (h : Api.Exptmod.Base F p)
    (hF : F = F') (md : Nat) (hmd : md < 2 ^ 31) : Api.Exptmod.Base F' { p with mode := md } :=
  { h with stk := hF ▸ h.stk, mode := hmd }

/-- `s_mp_exptmod_fast(…, md)` with `md = dr`, the dispatch's (`P` odd or `dr != 0`). -/
theorem MpExptmod.fastRes {p : Exptmod.P} {md : Nat} (hres : MpExptmod.ResOf p) (hxs : p.x.sign ≠ Layout.mpNeg)
    (hf : MpExptmod.IsFast p.n) (hmd : MpExptmodStep.drC p.n = md) :
    WorkRes SMpExptmodFast.F SMpExptmodFast.Res SMpExptmodFast.Statement { p with mode := md } := by
  have eF : MpExptmod.F p = SMpExptmodFast.F p := by rw [MpExptmod.F_nn hxs, MpExptmod.Fd_fast hf]
  have ha := hres.arith
  have hmd2 : md ≤ 2 := by
    rw [← hmd]; unfold MpExptmodStep.drC; split
    · omega
    · split <;> omega
  refine ⟨⟨hres.toBase.restk eF md (by omega), ?_⟩, hres.fast, eF⟩
  refine ⟨ha.gt1, ha.bits, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · dsimp only at e; subst e
    rcases hf.2 with ho | hd
    · exact (MpExptmodStep.odd_iff hres.vn.toShape).1 ho
    · exact absurd hmd hd
  · dsimp only at e; subst e
    have hdr : IsDrModulus p.n := by
      unfold MpExptmodStep.drC at hmd; split at hmd
      · assumption
      · split at hmd <;> omega
    exact absurd (isReduce2kL_of_dr hdr) hf.1
  · dsimp only at e
    have h2 : isReduce2k p.n = 1 := by
      unfold MpExptmodStep.drC at hmd; split at hmd
      · omega
      · split at hmd
        · assumption
        · omega
    exact ha.r2k h2

/-- `s_mp_exptmod(…, md)` (`md = 1` for a `2^k-L` modulus, `0` for Barrett). -/
theorem MpExptmod.slowRes {p : Exptmod.P} {md : Nat} (hres : MpExptmod.ResOf p) (hxs : p.x.sign ≠ Layout.mpNeg)
    (hf : ¬ MpExptmod.IsFast p.n) (hmd : md < 2) :
    WorkRes SMpExptmod.F SMpExptmod.Res SMpExptmod.Statement { p with mode := md } := by
  have eF : MpExptmod.F p = SMpExptmod.F p := by rw [MpExptmod.F_nn hxs, MpExptmod.Fd_slow hf]
  have ha := hres.arith
  exact ⟨⟨hres.toBase.restk eF md (by omega), ⟨by show 0 < p.n.mag; have := ha.gt1; omega,
    ha.bits, hmd⟩⟩, hres.slow, eF⟩


/-- `mp_invmod(G, P, &tmpG)`'s success on the modulus `P > 1`: a valid inverse below `P`. -/
theorem MpExptmod.inv_ok {a b c c' : MpInt} (hb : b.Valid) (hbs : b.sign ≠ Layout.mpNeg) (hb1 : 1 < b.mag)
    (ha : a.Valid) (h : InvmodPost a b c c' Layout.mpOkay) : c'.Valid ∧ c'.used ≤ b.used := by
  have hbv : b.val = b.mag := MpInt.val_of_pos hbs
  have hlt : c'.Valid ∧ c'.mag < b.mag := by
    by_cases hg : Nat.gcd (invmodRem a b) b.mag = 1
    · by_cases hs : 0 ≤ a.val ∨ b.mag % 2 = 0
      · obtain ⟨_, hv, h0, h1, _⟩ := h.spec_ok ha (by omega) hg hs
        refine ⟨hv, ?_⟩
        have : c'.val = c'.mag := MpInt.val_of_pos (MpInt.sign_ne_neg_of_nonneg hv h0)
        omega
      · have hneg : a.val < 0 := by omega
        obtain ⟨_, hv, h0, h1, _⟩ := h.spec_neg_odd ha (by omega) hg hneg (by omega)
        refine ⟨hv, ?_⟩
        have hn := MpInt.sign_neg_of_neg h1
        have : c'.val = -(c'.mag : Int) := by unfold MpInt.val; simp [hn]
        omega
    · exact absurd (h.spec_err (.inr (.inr hg))).1 (by decide)
  exact ⟨hlt.1, Ledger.used_le_of_lt hlt.1 (Nat.lt_of_lt_of_le hlt.2 (Nat.le_of_lt (MpInt.mag_lt hb.toShape)))⟩

/-- `mp_abs(X, &tmpX)`'s result (growing the fresh `tmpX`) is nonempty. -/
theorem MpExptmod.abs_pos {X tX : MpInt} (hX : X.Shape) (ha : AbsPost X (copyIn X (MpInt.zeroN defPrec)) tX) :
    0 < tX.alloc := by
  rw [ha.alloc]
  exact Nat.lt_of_lt_of_le (show 0 < (MpInt.zeroN defPrec).alloc by decide)
    (copyIn_grown (MpInt.zeroN_valid (by decide)).toShape (Nat.lt_of_le_of_lt hX.used_le hX.alloc_lt)).alloc

/-- The recursive call `mp_exptmod(&tmpG, &tmpX, P, Y)`'s residue (`tmpG` the inverse, `tmpX = |X|`, their
structs in the frame, their blocks live). -/
theorem MpExptmod.innerRes {p : Exptmod.P} (hres : MpExptmod.ResOf p) (hX : p.x.sign = Layout.mpNeg)
    {q qX : Nat} {Gi tX : MpInt} {H' : List (Nat × Nat)}
    (hvG : Gi.Valid) (hGu : Gi.used ≤ p.n.used) (hGa : 0 < Gi.alloc)
    (ha : AbsPost p.x (copyIn p.x (MpInt.zeroN defPrec)) tX)
    (hgb : Api.Heap.digBlk q Gi ∈ H') (hnb : Api.Heap.digBlk p.ndp p.n ∈ H') :
    NNRes ⟨p.sp - 96, p.sp - 96, q, p.sp - 72, qX, p.pn, p.ndp, p.py, p.ydp, Gi, tX, p.n, p.y, 0, H'⟩ := by
  have ar := hres.arith
  have hab := AbsPost.spec hres.vx
    (copyIn_grown (MpInt.zeroN_valid (by decide)).toShape (Nat.lt_of_le_of_lt hres.vx.used_le hres.vx.alloc_lt)).shape
    (copyIn_room _ _) ha
  have hts : tX.sign ≠ Layout.mpNeg := by rw [ha.sign]; decide
  have hF : MpExptmod.F p = 96 + MpExptmod.Fn p.n := MpExptmod.F_neg hX
  have hF' : MpExptmod.F ⟨p.sp - 96, p.sp - 96, q, p.sp - 72, qX, p.pn, p.ndp, p.py, p.ydp, Gi, tX, p.n, p.y, 0, H'⟩
      ≤ MpExptmod.Fn p.n := by
    rw [MpExptmod.F_nn hts]; exact MpExptmod.Fd_le_Fn hGu
  have hst := hres.stk
  have hlo := hst.lo; have := hst.al; have := hst.hi
  rw [hF] at hlo
  have eE : Api.Alloc.heapEnd = 0x87800000 := rfl
  have hxu := ha.used
  refine ⟨⟨{ stk := ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩, vg := hvG, vx := hab.1, vn := hres.vn, sy := hres.sy,
              nz := hres.nz, xbits := ?_, nbits := hres.nbits, gu := ?_, mode := by show 0 < 2 ^ 31; decide,
              gpos := hGa, xpos := ?_, npos := hres.npos, ypos := hres.ypos,
              goff := by unfold Api.Heap.OffHeap; dsimp only; omega, xoff := by unfold Api.Heap.OffHeap; dsimp only; omega, noff := hres.noff,
              yoff := hres.yoff, gblk := hgb, nblk := hnb },
           ⟨ar.gt1, ar.bits, ar.r2k⟩⟩, hts, hres.nn hX⟩
  · show Layout.digitBits * tX.used < 2 ^ 31; rw [hxu]; exact hres.xbits
  · show Gi.used + p.n.used + 3 < 2 ^ 30; have : 28 * (2 * p.n.used + 1) < 2 ^ 31 := ar.bits; omega
  · exact MpExptmod.abs_pos hres.vx.toShape ha

/-- `mp_invmod(G, P, &tmpG)`'s errors into the fresh `tmpG` (`MpInt.zeroN n`): `MP_MEM` or `MP_VAL` (an
inverse is never `0`, so `tmpG` unchanged is never a success). -/
theorem MpExptmod.inv_err {a b : MpInt} {n : Nat} {r : Int} (hbs : b.sign ≠ Layout.mpNeg) (hb1 : 1 < b.mag)
    (ha : a.Valid) (h : r = Layout.mpMem ∨ InvmodPost a b (MpInt.zeroN n) (MpInt.zeroN n) r) :
    r = Layout.mpMem ∨ r = Layout.mpVal := by
  rcases h with h | h
  · exact .inl h
  · have hbv : b.val = b.mag := MpInt.val_of_pos hbs
    have hz : (MpInt.zeroN n).val = 0 := by simp [MpInt.val, MpInt.zeroN, MpInt.mag, natUpTo]
    by_cases hg : Nat.gcd (invmodRem a b) b.mag = 1
    · by_cases hs : 0 ≤ a.val ∨ b.mag % 2 = 0
      · obtain ⟨_, _, _, _, h4⟩ := h.spec_ok ha (by omega) hg hs
        rw [hz, Int.mul_zero, Int.zero_emod] at h4; omega
      · obtain ⟨_, _, _, h3, _⟩ := h.spec_neg_odd ha (by omega) hg (by omega) (by omega)
        rw [hz] at h3; omega
    · exact .inr (h.spec_err (.inr (.inr hg))).1

/-- The recursive call's reservation inside the negative path's (`Fn`). -/
theorem MpExptmod.innerF {p : Exptmod.P} {q qX : Nat} {Gi tX : MpInt} {H' : List (Nat × Nat)}
    (hts : tX.sign ≠ Layout.mpNeg) (hGu : Gi.used ≤ p.n.used) :
    MpExptmod.F ⟨p.sp - 96, p.sp - 96, q, p.sp - 72, qX, p.pn, p.ndp, p.py, p.ydp, Gi, tX, p.n, p.y, 0, H'⟩
      ≤ MpExptmod.Fn p.n := by
  rw [MpExptmod.F_nn hts]; exact MpExptmod.Fd_le_Fn hGu

end Tom.Machine.Std
