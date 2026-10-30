import Tom.Machine.Api.Std_r6b
import Tom.Machine.Api.MpDiv2dR
import Tom.Machine.Fn.MpDiv2dRMainG

/-!
# Standard contracts as `Contract` records: `mp_div_2d(a, k, b, a)`

The callee of `mp_reduce_2k` (`mp_div_2d(a, p, &q, a)`). Apart from `Api/Std_r6b.lean`
because `Fn/MpDiv2dRMainG.lean` imports that file (its callee `mp_mod_2d(a, b, a)`).
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api

/-! ## `mp_div_2d(a, k, b, a)`: quotient in `b`, remainder in `a` -/

structure Div2dRP where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  k : Nat
  b : MpInt

structure Div2dRRes (p : Div2dRP) : Prop where
  va : p.a.Valid
  sb : p.b.Shape
  k_pos : 0 < p.k
  k_lt : p.k < 2 ^ 31
  bits : Layout.digitBits * p.a.used < 2 ^ 31
  room : p.a.used ≤ p.b.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 112 ≤ p.sp

def div2dR : Contract where
  P := Div2dRP
  X := MpInt × MpInt
  R := Two.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Two.all
  entry := MpDiv2dR.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.k),
    (12, BitVec.ofNat 64 p.pb), (13, BitVec.ofNat 64 p.pa)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Two.lay 112 p.sp p.pa p.adp p.pb p.bdp p.a p.b
  kind := fun ⟨_, pa, adp, pb, bdp, a, _, b⟩ => Tom.Machine.Two.kind pa adp pb bdp a b
  out := fun ⟨_, pa, adp, pb, bdp, _, _, _⟩ x => Tom.Machine.Two.kind pa adp pb bdp x.1 x.2
  isW := Two.isW2
  ws := Two.ws2
  Res := Div2dRRes
  Q p x := Mod2dPost p.a p.k p.a x.1 ∧ Div2dPost p.a p.k p.b x.2
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpb, qbdp, qa, qk, qb⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MpDiv2dR.Pre m qsp qpa qadp qpb qbdp qa qk qb ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rc := Hdr.mpAt (hB .bS).2 (hB .bD).2, va := hres.va, sc := hres.sb
        ga := Hdr.geom (hB .aS).2, gc := Hdr.geom (hB .bS).2, b_pos := hres.k_pos, b_lt := hres.k_lt
        bits := hres.bits, room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al, sp_ge := hres.sp_ge
        ra_al := hra, img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, a', b', M, hat, hpost⟩ :=
      Fn.MpDiv2dRG5.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, (a', b'), M, hat.sub rfl rfl, ⟨hpost.mod, hpost.div⟩, ?_, hpost.frame⟩
    have hal : a'.alloc = qa.alloc := ClampedTo.alloc hpost.mod
    have hbl : b'.alloc = qb.alloc := ClampedTo.alloc hpost.div
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.reprA (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact witD hpost.reprA (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact witS hpost.reprC (Hdr.geom (hB .bS).2) hbl (Iv.sub_self _)
    · exact witD hpost.reprC (Hdr.geom (hB .bS).2) hbl (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Two.R.code

end Tom.Machine.Std
