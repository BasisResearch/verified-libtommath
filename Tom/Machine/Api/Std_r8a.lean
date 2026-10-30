import Tom.Machine.Api.Std_r6f
import Tom.Machine.Api.Std_r6c
import Tom.Machine.Api.Std_grow6
import Tom.Machine.Fn.CmpMag
import Tom.Machine.Api.StdNorm

/-!
# The callee contracts (for `mp_div`'s assembly)

* `cmpMagS`: `mp_cmp_mag(a, b)` of two shaped integers (`Fn/CmpMag.lean` `correctS`), `a0` the structural
  comparison `cmpMag a b` as a `Nat` pin (`ordNG`): step 3.2 compares `t1` with the unclamped
  three-digit `t2`.
* `mpCmpG`: `mp_cmp(a, b)` (`Std.mpCmpC`) with `a0` as a `Nat` pin.
* `HContract.wp`: an allocating contract whose `Q` also carries the site's placement
  (`HContract.after` consumes the callee's `HPost.place`; a caller that must place the
  re-placed block itself later, as `mp_div` does with `x`'s digits, needs it through `Q`).
  `mpMul2dIP := mpMul2dI.wp`, `mpLshdGP := mpLshdG.wp`, `mulDGP := mulDG.wp`.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `mp_cmp_mag(a, b)` of shaped integers: `a0 = ordNG (cmpMag a b)`. -/
def cmpMagS : Contract where
  P := CmP
  X := Unit
  R := Cm
  all := [.aS, .aD, .bS, .bD, .code]
  hall r := by cases r <;> simp
  entry := Fn.CmpMag.entry
  args p := [(10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]
  rets p ra := [(1, ra), (10, BitVec.ofNat 64 (ordNG (Tom.cmpMag p.a p.b)))]
  lay := Cm.lay
  kind := Cm.kind
  out p _ := Cm.kind p
  isW _ := false
  ws := []
  Res p := p.a.Shape ∧ p.b.Shape
  Q _ _ := True
  fits p r := by cases r <;> exact Iv.sub_self _
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB
    obtain ⟨qa, qadp, qb, qbdp, a, b⟩ := p
    have hpre : Fn.CmpMag.PreS m qa qadp qb qbdp a b :=
      { ra := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2, sa := hres.1, sb := hres.2
        ga := Hdr.geom (hB .aS).2, gb := Hdr.geom (hB .bS).2, code := (hB .code).2.mpCmpMag }
    have h := Fn.CmpMag.correctS ra v outp qa qadp qb qbdp a b m hra hpre
    simp only [Fn.CmpMag.res, ofInt_ordCodeG] at h
    exact Triple.rmap (fun cf hc => ⟨(), m, hc, trivial, hB, Frm.refl _ _⟩) h

/-- `mp_cmp(a, b)` with `a0 = ordNG (cmpS a b)`. -/
def mpCmpG : Contract where
  P := CmP
  X := Unit
  R := Cm
  all := [.aS, .aD, .bS, .bD, .code]
  hall r := by cases r <;> simp
  entry := CmpS.entry
  args p := [(10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]
  rets p ra := [(1, ra), (10, BitVec.ofNat 64 (ordNG (cmpS p.a p.b)))]
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
    have h := Std.mpCmpC.spec (p := p) (v := v) (outp := outp) hra hres hS hB
    simpa only [Std.mpCmpC, ofInt_ordCodeG] using h

/-- An allocating contract whose `Q` also says where the site went. -/
def _root_.Tom.Machine.HContract.wp (C : HContract) : HContract :=
  { C with
    Q := fun p x => C.Q p x ∧ Place (C.hin p) (C.lay p C.site) (C.site' p x)
    spec := by
      intro p m v outp ra hra hres hS hB hH hoff
      exact Triple.rmap (fun _ ⟨x, M, hat, hq, hpo⟩ => ⟨x, M, hat, ⟨hq, hpo.place⟩, hpo⟩)
        (C.spec hra hres hS hB hH hoff) }

/-- `mp_mul_2d(a, b, a)`, growing `a`, with the placement of `a`'s digits. -/
def mpMul2dIP : HContract := mpMul2dI.wp

/-- `mp_lshd(a, k)` growing `a`, with the placement of `a`'s digits in `Q`. -/
def mpLshdGP : HContract := mpLshdG.wp

/-- `mp_mul_d(a, b, c)` growing `c`, with the placement of `c`'s digits in `Q`. -/
def mulDGP : HContract := mulDG.wp

end Tom.Machine.Std
