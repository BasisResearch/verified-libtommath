import Tom.Machine.Api.MpMulG
import Tom.Spec.MpMulStep
import Tom.Machine.Kit.ResFrom

/-!
# `mp_mul`'s assembly: the Pre, the callees' parameters and residues, the exits' `Q`

Helpers of the generated `Fn/MpMulMainG.lean` (`experiments/asm/mmul.asm.json`): the
contract's Pre as one structure (`MPre`), the callees' parameter records (`subP`: the
algorithms at `sp - 32`; `digsP`: `s_mp_mul_digs(_fast)` with `digs = a->used + b->used + 1`),
their residues from `mp_mul`'s, and `mp_mul`'s `Q` from each callee's (`Tom/Spec/MpMulStep.lean`).
-/

namespace Tom.Machine.Fn.MpMulG5K

open Tom.Machine Tom.Machine.Api Tom.Machine.Std Tom.Machine.Api.Alloc Tom.Machine.Api.Heap
open Tom.Machine.Api.MpMul (P μ)

/-- `mp_mul`'s Pre (the Statement's hypotheses). -/
structure MPre (p : P) (m : Mem) (ra : BitVec 64) : Prop where
  ra4 : ra.toNat % 4 = 0
  res : Api.MpMulG.Res p
  lay : Sound (MpMul.lay p) MpMul.isW
  bund : Bundle (MpMul.lay p) (MpMul.kind p) m
  heap : AHeap m (MpMul.hin p)
  off : ∀ r, Off (MpMul.lay p r) (MpMul.hin p)

/-- The algorithms' parameters: `mp_mul`'s, at `sp - 32`. -/
def subP (p : P) : P := { p with sp := p.sp - 32 }

/-- `s_mp_mul_digs(_fast)(a, b, c, a->used + b->used + 1)` at `sp - 32`. -/
def digsP (p : P) : SMpMulDigs.P :=
  ⟨p.sp - 32, p.pa, p.adp, p.pb, p.bdp, p.pc, p.cdp, p.a.used + p.b.used + 1, p.a, p.b, p.c, p.H⟩

/-- A hypothesis hidden from `cfacts`' context scan (a callee's `Q`: its placement and footprint
are only needed at the exit, and scanning them after `s_mp_mul_digs` exhausts the heartbeats). -/
@[irreducible] def Hide (P : Prop) : Prop := P

theorem Hide.mk {P : Prop} (h : P) : Hide P := by unfold Hide; exact h
theorem Hide.get {P : Prop} (h : Hide P) : P := by unfold Hide at h; exact h

/-- `s_mp_mul_digs(_fast)`'s regions in `mp_mul`'s. -/
def embR : SMpMulDigs.R → MpMul.R
  | .stk => .stk | .aS => .aS | .aD => .aD | .bS => .bS | .bD => .bD | .cS => .cS | .cD => .cD | .code => .code

variable {p : P}

theorem algBase (h : Api.MpMulG.Res p) : MulAlg.Base (subP p) := by
  res_from [MpMul.F, MpMul.Fm, μ, subP, MulAlg.F] h

theorem kres (h : Api.MpMulG.Res p) (h1 : 80 ≤ min p.a.used p.b.used)
    (h2 : max p.a.used p.b.used < 2 * min p.a.used p.b.used) : AlgRes KMul.entry KMul.Res (subP p) :=
  ⟨algBase h, { toBase := algBase h, kmin := h1, kbal := h2, ih := h.ih }, h.gaps.kmul⟩

theorem bres (h : Api.MpMulG.Res p) (h1 : 80 ≤ min p.a.used p.b.used) (h2 : 80 ≤ max p.a.used p.b.used / 2)
    (h3 : 2 * min p.a.used p.b.used ≤ max p.a.used p.b.used) : AlgRes BalMul.entry BalMul.Res (subP p) :=
  ⟨algBase h, { toBase := algBase h, bmin := h1, bhalf := h2, bratio := h3, ih := h.ih }, h.gaps.bal⟩

theorem tres (h : Api.MpMulG.Res p) (h1 : 350 ≤ min p.a.used p.b.used)
    (h2 : max p.a.used p.b.used < 2 * min p.a.used p.b.used) : AlgRes ToomMul.entry ToomMul.Res (subP p) :=
  ⟨algBase h, { toBase := algBase h, tmin := h1, tbal := h2, ih := h.ih }, h.gaps.toom⟩

theorem dres (h : Api.MpMulG.Res p) (hf : ¬ (p.a.used + p.b.used + 1 < 512 ∧ min p.a.used p.b.used ≤ 256)) :
    SMpMulDigs.Res (digsP p) := by
  have hs := h.stk
  have := hs.al; have := hs.lo; have := hs.hi; have := h.uab
  simp only [MpMul.F, MpMul.Fm, μ] at *
  exact { stk := ⟨by simp only [digsP, SMpMulDigs.F]; omega, by simp only [digsP, SMpMulDigs.F]; omega, by simp only [digsP, SMpMulDigs.F]; omega⟩
          sa := h.va.toShapeU, sb := h.vb.toShapeU, sc := h.sc, csign := h.csign
          dg_lt := by simp only [digsP]; omega, uab := by simp only [digsP]; omega
          room := fun hF => absurd ⟨hF.1, by have := hF.2; simp only [digsP] at this; omega⟩ hf
          apos := h.apos, bpos := h.bpos, cpos := h.cpos, aoff := h.aoff, boff := h.boff, coff := h.coff }

theorem fres (h : Api.MpMulG.Res p) (hf : p.a.used + p.b.used + 1 < 512) (hm : min p.a.used p.b.used ≤ 256) :
    FastHRes (digsP p) := by
  have := h.va.toShapeU; have := h.vb.toShapeU
  refine ⟨?_, h.gaps.fast⟩; res_from [MpMul.F, MpMul.Fm, μ, digsP] h

/-! ## `mp_mul`'s `Q` after the sign store -/

theorem post_alg (h : Api.MpMulG.Res p) {ok : Bool} {c1 : MpInt} (hq : MulAlg.Out (subP p) ok c1) :
    MpMul.Out p ok (withSign p.a p.b c1) :=
  { shape := withSign_shape hq.shape, sign := withSign_sign _ _ _, pos := hq.pos
    post := fun hk => mul_post h.va.toU h.vb.toU hq.shape (hq.valid hk).top (hq.mag hk) }

theorem post_fast (h : Api.MpMulG.Res p) {ok : Bool} {c1 : MpInt} (hq : MulFastH.Out (digsP p) ok c1) :
    MpMul.Out p ok (withSign p.a p.b c1) :=
  { shape := withSign_shape hq.shape, sign := withSign_sign _ _ _, pos := hq.pos
    post := fun hk => mul_post h.va.toU h.vb.toU hq.shape (hq.top hk)
      (by rw [hq.mag hk]; exact mag_full h.va.toShapeU h.vb.toShapeU) }

theorem post_digs (h : Api.MpMulG.Res p) {q : Nat} {c1 : MpInt} (hq : SMpMulDigs.Digs (digsP p) q c1) :
    MpMul.Out p true (withSign p.a p.b c1) :=
  { shape := withSign_shape hq.valid.toShape, sign := withSign_sign _ _ _
    pos := by have := hq.valid.used_le; rcases Nat.eq_zero_or_pos c1.alloc with h0 | h0
              · exact absurd h0 (by
                  by_cases hF : SMpMulDigs.Fast (digsP p).a (digsP p).b (digsP p).digs
                  · have := (hq.fast hF).2.alloc; rw [this]; exact Nat.pos_iff_ne_zero.1 h.cpos
                  · rw [(hq.slow hF).1]; unfold initPrec minPrec; simp only [Layout.digitBits]; omega)
              · exact h0
    post := fun _ => mul_post h.va.toU h.vb.toU hq.valid.toShape hq.valid.top
      (by rw [hq.mag]; exact mag_full h.va.toShapeU h.vb.toShapeU) }

theorem post_none (h : Api.MpMulG.Res p) : MpMul.Out p false (withSign p.a p.b p.c) :=
  { shape := withSign_shape h.sc, sign := withSign_sign _ _ _, pos := h.cpos, post := fun hk => absurd hk (by decide) }

end Tom.Machine.Fn.MpMulG5K
