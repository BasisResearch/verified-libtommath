import Tom.Machine.Api.Std
import Tom.Machine.Api.MpDiv2d
import Tom.Machine.Fn.MpDiv2dMain
import Tom.Machine.Fn.Libgcc

/-!
# Standard contracts as `Contract` records: `__udivdi3`, `mp_div_2d(a, k, b, NULL)`

The callees of `mp_div_d` that had no instance: `__hidden___udivdi3` (`Fn.Libgcc.Udivdi3`,
the relocated sibling proof; quotient in `a0`, remainder in `a1`) and `mp_div_2d` with
`d = NULL` and distinct operands (`Fn.MpDiv2d.correct`, its 96-byte stack).
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api

/-! ## `__udivdi3(n, d)` -/

theorem udiv_ofNat (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x / BitVec.ofNat 64 y = BitVec.ofNat 64 (x / y) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_udiv, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    Nat.mod_eq_of_lt (show x / y < 2 ^ 64 from Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

theorem umod_ofNat (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x % BitVec.ofNat 64 y = BitVec.ofNat 64 (x % y) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_umod, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    Nat.mod_eq_of_lt (show x % y < 2 ^ 64 from Nat.lt_of_le_of_lt (Nat.mod_le _ _) hx)]

structure UDivRes (p : DivP) : Prop where
  n_lt : p.n < 2 ^ 64
  d_pos : 0 < p.d
  d_lt : p.d < 2 ^ 64

def udivdi3 : Contract where
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
  Res := UDivRes
  Q _ _ := True
  fits _ _ := Iv.sub_self _
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB
    have hd : BitVec.ofNat 64 p.d ≠ 0#64 := fun h => by
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hres.d_lt] at this
      have := hres.d_pos; omega
    have h := Fn.Libgcc.Udivdi3.correct (v := v) (outp := outp) (n := BitVec.ofNat 64 p.n)
      (d := BitVec.ofNat 64 p.d) (hB .code).2 hra hd
    rw [udiv_ofNat _ _ hres.n_lt hres.d_lt, umod_ofNat _ _ hres.n_lt hres.d_lt] at h
    exact Triple.rmap (fun cf hc => ⟨(), m, hc, trivial, hB, Frm.refl _ _⟩) h

/-! ## `mp_div_2d(a, k, b, NULL)`, distinct operands -/

structure Div2dP where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  k : Nat
  b : MpInt

structure Div2dRes (p : Div2dP) : Prop where
  va : p.a.Valid
  sb : p.b.Shape
  k_lt : p.k < 2 ^ 31
  room : p.a.used ≤ p.b.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 96 ≤ p.sp

def mpDiv2d : Contract where
  P := Div2dP
  X := MpInt
  R := Two.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Two.all
  entry := MpDiv2d.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.k),
    (12, BitVec.ofNat 64 p.pb), (13, 0#64)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Two.lay 96 p.sp p.pa p.adp p.pb p.bdp p.a p.b
  kind := fun ⟨_, pa, adp, pb, bdp, a, _, b⟩ => Tom.Machine.Two.kind pa adp pb bdp a b
  out := fun ⟨_, pa, adp, pb, bdp, a, _, _⟩ x => Tom.Machine.Two.kind pa adp pb bdp a x
  isW := Two.isW
  ws := Two.ws
  Res := Div2dRes
  Q p x := Div2dPost p.a p.k p.b x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpb, qbdp, qa, qk, qb⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MpDiv2d.Pre m qsp qpa qadp qpb qbdp qa qk qb ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rc := Hdr.mpAt (hB .bS).2 (hB .bD).2, va := hres.va, sc := hres.sb
        ga := Hdr.geom (hB .aS).2, gc := Hdr.geom (hB .bS).2, b_lt := hres.k_lt, room := hres.room
        rs := (hB .stk).2, sp_al := hres.sp_al, sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2
        lay := hS }
    obtain ⟨c', hs, b', M, hat, hpost⟩ :=
      Fn.MpDiv2d.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, b', M, hat.sub rfl rfl, hpost.div, ?_, hpost.frame⟩
    have hbl : b'.alloc = qb.alloc := ClampedTo.alloc hpost.div
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact hB.keep hS hpost.frame Two.R.aS
    · exact hB.keep hS hpost.frame Two.R.aD
    · exact witS hpost.repr (Hdr.geom (hB .bS).2) hbl (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .bS).2) hbl (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Two.R.code

end Tom.Machine.Std
