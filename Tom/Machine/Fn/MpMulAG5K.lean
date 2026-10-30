import Tom.Machine.Api.MpMulGA
import Tom.Machine.Fn.MpMulG5K

/-!
# `mp_mul(a, b, a)`'s assembly: the Pre, the callees' parameters and residues, the exits' `Q`

`Fn/MpMulG5K.lean` with `c = a`, for the generated `Fn/MpMulAMainG.lean`
(`experiments/asm/mmula.asm.json`, a variant of `mmul.asm.json`).
-/

namespace Tom.Machine.Fn.MpMulAG5K

open Tom.Machine Tom.Machine.Api Tom.Machine.Std Tom.Machine.Api.Alloc Tom.Machine.Api.Heap
open Tom.Machine.Api.MpMulA (P)
open Tom.Machine.Api.MpMul (μ)

/-- `mp_mul(a, b, a)`'s Pre (the Statement's hypotheses). -/
structure MPreA (p : P) (m : Mem) (ra : BitVec 64) : Prop where
  ra4 : ra.toNat % 4 = 0
  res : Api.MpMulGA.Res p
  lay : Sound (MpMulA.lay p) MpMulA.isW
  bund : Bundle (MpMulA.lay p) (MpMulA.kind p) m
  heap : AHeap m (MpMulA.hin p)
  off : ∀ r, Off (MpMulA.lay p r) (MpMulA.hin p)

/-- The algorithms' parameters: `mp_mul`'s, at `sp - 32`. -/
def subPA (p : P) : P := { p with sp := p.sp - 32 }

/-- `s_mp_mul_digs(_fast)(a, b, a, a->used + b->used + 1)` at `sp - 32`. -/
def digsPA (p : P) : SMpMulDigsA.P :=
  ⟨p.sp - 32, p.pa, p.adp, p.pb, p.bdp, p.a.used + p.b.used + 1, p.a, p.b, p.H⟩

/-- `s_mp_mul_digs(_fast)`'s regions in `mp_mul(a, b, a)`'s. -/
def embRA : SMpMulDigsA.R → MpMulA.R
  | .stk => .stk | .aS => .aS | .aD => .aD | .bS => .bS | .bD => .bD | .code => .code

variable {p : P}

theorem algBaseA (h : Api.MpMulGA.Res p) : MulAlgA.Base (subPA p) := by
  res_from [MpMulA.F, MpMul.Fm, μ, subPA, MulAlgA.F] h

theorem dresA (h : Api.MpMulGA.Res p) (hf : ¬ (p.a.used + p.b.used + 1 < 512 ∧ min p.a.used p.b.used ≤ 256)) :
    DigsARes (digsPA p) :=
  ⟨by res_from [MpMulA.F, MpMul.Fm, μ, digsPA, SMpMulDigsA.F, SMpMulDigs.Fast] h, h.gaps.digsA⟩

theorem fresA (h : Api.MpMulGA.Res p) (hf : p.a.used + p.b.used + 1 < 512) (hm : min p.a.used p.b.used ≤ 256) :
    FastHARes (digsPA p) := by
  have hsg : (digsPA p).a.sign = Layout.mpZpos ∨ (digsPA p).a.sign = Layout.mpNeg := h.va.sign_ok
  exact ⟨by res_from [MpMulA.F, MpMul.Fm, μ, digsPA] h, h.gaps.fastA⟩

/-! ## `mp_mul(a, b, a)`'s `Q` after the sign store (`mul_post`, once) -/

theorem outA (h : Api.MpMulGA.Res p) {ok : Bool} {c1 : MpInt} (hs : c1.Shape) (hp : 0 < c1.alloc)
    (ht : ok = true → 0 < c1.used → c1.digit (c1.used - 1) ≠ 0) (hm : ok = true → c1.mag = p.a.mag * p.b.mag) :
    MpMulA.Out p ok (withSign p.a p.b c1) :=
  ⟨withSign_shape hs, withSign_sign _ _ _, hp, fun hk => mul_post h.va.toU h.vb.toU hs (ht hk) (hm hk)⟩

theorem post_digsA (h : Api.MpMulGA.Res p) {q : Nat} {c1 : MpInt} (hq : SMpMulDigsA.Digs (digsPA p) q c1) :
    MpMulA.Out p true (withSign p.a p.b c1) :=
  outA h hq.valid.toShape (by rw [hq.alloc]; unfold initPrec minPrec; simp only [Layout.digitBits]; omega)
    (fun _ => hq.valid.top) fun _ => by rw [hq.mag]; exact mag_full h.va.toShapeU h.vb.toShapeU

end Tom.Machine.Fn.MpMulAG5K
