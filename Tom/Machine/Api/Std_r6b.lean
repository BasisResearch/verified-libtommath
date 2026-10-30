import Tom.Machine.Api.Std
import Tom.Machine.Api.MpMod2dI
import Tom.Machine.Fn.MpMod2dIMainG

/-!
# Standard contracts as `Contract` records: `mp_mod_2d(a, b, a)`

On top of `Api/Std.lean`; the callee of `mp_div_2d(a, b, c, a)` (`Api/MpDiv2dR.lean`, whose
own instance is in `Api/Std_r6bD.lean`: its assembly imports this file).
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api

/-! ## `mp_mod_2d(a, b, a)` (in place) -/

structure Mod2dIP where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt
  b : Nat

structure Mod2dIRes (p : Mod2dIP) : Prop where
  va : p.a.Valid
  b_pos : 0 < p.b
  b_lt : p.b < 2 ^ 31
  bits : Layout.digitBits * p.a.used < 2 ^ 31
  sp_al : p.sp % 16 = 0
  sp_ge : 48 ≤ p.sp

def mod2dI : Contract where
  P := Mod2dIP
  X := MpInt
  R := Un.R
  all := [.stk, .aS, .aD, .code]
  hall := Un.all
  entry := MpMod2dI.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.b),
    (12, BitVec.ofNat 64 p.pa)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Un.lay 48 p.sp p.pa p.adp p.a
  kind := fun ⟨_, pa, adp, a, _⟩ => Tom.Machine.Un.kind pa adp a
  out := fun ⟨_, pa, adp, _, _⟩ x => Tom.Machine.Un.kind pa adp x
  isW := Un.isW
  ws := Un.ws
  Res := Mod2dIRes
  Q p x := Mod2dPost p.a p.b p.a x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qa, qb⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MpMod2dI.Pre m qsp qpa qadp qa qb ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, va := hres.va, ga := Hdr.geom (hB .aS).2, b_pos := hres.b_pos
        b_lt := hres.b_lt, bits := hres.bits, rs := (hB .stk).2, sp_al := hres.sp_al, sp_ge := hres.sp_ge
        ra_al := hra, img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, a', M, hat, hpost⟩ :=
      Fn.MpMod2dIG5.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, a', M, hat.sub rfl rfl, hpost.mod, ?_, hpost.frame⟩
    have hal : a'.alloc = qa.alloc := ClampedTo.alloc hpost.mod
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Un.R.code

end Tom.Machine.Std
