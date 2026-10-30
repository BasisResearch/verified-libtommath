import Tom.Machine.Fn.MulFastCore
import Tom.Machine.Api.MulFast

/-!
# `s_mp_mul_digs_fast` on the machine: the contracts

`Fn/MulFastCore.lean`'s `whole` for the three placements: distinct operands
(`correct : Api.MulFast.Statement`, regions `Api/Bin.lean`) and `c = a`,
`c = b` (`correct_inplaceA`/`correct_inplaceB`, regions `Api/Two.lean`). Each
reads its `Ent` (the frame and `c` off the text, the frame off the operands)
from `Pre.lay`, and its frame back from `whole`'s.
-/

namespace Tom.Machine.Fn.MulFast

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api

/-- The frame `[sp - 2192, sp)` off an interval. -/
theorem kd {sp p n : Nat} (hsp : 2192 ≤ sp) (h : Iv.Disj ⟨sp - 2192, 2192⟩ ⟨p, n⟩) :
    sp ≤ p ∨ p + n ≤ sp - 2192 := by
  unfold Iv.Disj Disj at h; simp only at h; rwa [Nat.sub_add_cancel hsp] at h

theorem td {p n : Nat} (h : Iv.Disj textIv ⟨p, n⟩) : textBase + textLen ≤ p ∨ p + n ≤ textBase := h

theorem entry_reshape {ra s0 : BitVec 64} {v : Abi} {sp pa pb pc dg : Nat} {m : Mem} {outp : Array String}
    {Q : Vsa.Machine.Config → Prop}
    (h : Triple (At 0x800042f0#64 (entL ra s0 v sp pa pb pc dg) m (kF v) outp) Q) :
    Triple (At MulFast.entry (MulFast.entryL ra s0 sp pa pb pc dg) m v.keepR outp) Q :=
  Triple.lmap (fun _ h => h.reshape (by simp [entL, MulFast.entryL, Abi.keepR, sKeepL])
    (by simp [kF, Abi.keepR, sKeepL])) h

theorem ret_reshape {ra s0 : BitVec 64} {v : Abi} {sp : Nat} {M : Mem} {outp : Array String}
    {cf : Vsa.Machine.Config} (h : At ra (rL ra s0 v sp) M (kF v) outp cf) :
    At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf :=
  h.reshape (by simp [rL]) (by simp [rL, kF, Abi.keepR, sKeepL])

/-- Off the frame and `c` (what `whole` keeps), from off the written regions. -/
theorem off3 {sp pc cdp al x : Nat} (hsp : 2192 ≤ sp)
    (h : ¬ ((sp - 2192 ≤ x ∧ x < sp - 2192 + 2192) ∨ (pc ≤ x ∧ x < pc + 24) ∨ (cdp ≤ x ∧ x < cdp + 4 * al))) :
    (x < sp - 2192 ∨ sp ≤ x) ∧ (x < pc ∨ pc + 24 ≤ x) ∧ (x < cdp ∨ cdp + 4 * al ≤ x) := by
  rw [Nat.sub_add_cancel hsp] at h; omega

/-- **`s_mp_mul_digs_fast(a, b, c, digs)` on the machine.** -/
theorem correct : Api.MulFast.Statement := by
  intro m v outp sp pa adp pb bdp pc cdp dg a b c ra s0 hP
  have hS := hP.lay; have hsp := hP.sp_ge
  open Tom.Machine.Api.Bin in
  have h : Ent m sp pa adp pb bdp pc cdp dg a b c ra :=
    { ra_ := hP.ra_, rb := hP.rb, rc := hP.rc, sa := hP.sa, sb := hP.sb, sc := hP.sc, ga := hP.ga, gb := hP.gb
      gc := hP.gc, dg_w := hP.cond.dg_w, maxf := hP.cond.maxf, uab := hP.cond.uab, room := hP.room
      rs := hP.rs, sp_al := hP.sp_al, sp_ge := hsp, ra_al := hP.ra_al, img := hP.img
      k_as := kd hsp (hS.disj (r := R.stk) (s := R.aS)), k_ad := kd hsp (hS.disj (r := R.stk) (s := R.aD))
      k_bs := kd hsp (hS.disj (r := R.stk) (s := R.bS)), k_bd := kd hsp (hS.disj (r := R.stk) (s := R.bD))
      k_cs := kd hsp (hS.disj (r := R.stk) (s := R.cS)), k_cd := kd hsp (hS.disj (r := R.stk) (s := R.cD))
      k_t := kd hsp (hS.disj (r := R.stk) (s := R.code))
      t_cs := td (hS.disj (r := R.code) (s := R.cS)), t_cd := td (hS.disj (r := R.code) (s := R.cD)) }
  refine entry_reshape (Triple.rmap (fun cf ⟨c', M, hat, hr, hm, hM⟩ => ⟨c', M, ret_reshape hat, hr, hm,
    fun x hx => ?_⟩) (whole (s0 := s0) (v := v) (outp := outp) h))
  have := off3 hsp (by simpa only [InAny, Iv.In, Bin.lay, Bin.ws, or_false] using hx)
  exact hM x this.1 this.2.1 this.2.2

/-- **`s_mp_mul_digs_fast(a, b, a, digs)` on the machine** (`c = a`). -/
theorem correct_inplaceA : Api.MulFast.StatementInPlaceA := by
  intro m v outp sp pa adp pb bdp dg a b ra s0 hP hC
  have hS := hP.lay; have hsp := hP.sp_ge
  open Tom.Machine.Api.Two in
  have h : Ent m sp pa adp pb bdp pa adp dg a b a ra :=
    { ra_ := hP.ry, rb := hP.rx, rc := hP.ry, sa := hP.sy.toU, sb := hP.sx.toU, sc := hP.sy, ga := hP.gy, gb := hP.gx
      gc := hP.gy, dg_w := hC.dg_w, maxf := hC.maxf, uab := hC.uab, room := hP.room
      rs := hP.rs, sp_al := hP.sp_al, sp_ge := hsp, ra_al := hP.ra_al, img := hP.img
      k_as := kd hsp (hS.disj (r := R.stk) (s := R.bS)), k_ad := kd hsp (hS.disj (r := R.stk) (s := R.bD))
      k_bs := kd hsp (hS.disj (r := R.stk) (s := R.aS)), k_bd := kd hsp (hS.disj (r := R.stk) (s := R.aD))
      k_cs := kd hsp (hS.disj (r := R.stk) (s := R.bS)), k_cd := kd hsp (hS.disj (r := R.stk) (s := R.bD))
      k_t := kd hsp (hS.disj (r := R.stk) (s := R.code))
      t_cs := td (hS.disj (r := R.code) (s := R.bS)), t_cd := td (hS.disj (r := R.code) (s := R.bD)) }
  refine entry_reshape (Triple.rmap (fun cf ⟨c', M, hat, hr, hm, hM⟩ => ⟨c', M, ret_reshape hat, hr, hm,
    fun x hx => ?_⟩) (whole (s0 := s0) (v := v) (outp := outp) h))
  have := off3 hsp (by simpa only [InAny, Iv.In, Two.lay, Two.ws, or_false] using hx)
  exact hM x this.1 this.2.1 this.2.2

/-- **`s_mp_mul_digs_fast(a, b, b, digs)` on the machine** (`c = b`). -/
theorem correct_inplaceB : Api.MulFast.StatementInPlaceB := by
  intro m v outp sp pa adp pb bdp dg a b ra s0 hP hC
  have hS := hP.lay; have hsp := hP.sp_ge
  open Tom.Machine.Api.Two in
  have h : Ent m sp pa adp pb bdp pb bdp dg a b b ra :=
    { ra_ := hP.rx, rb := hP.ry, rc := hP.ry, sa := hP.sx.toU, sb := hP.sy.toU, sc := hP.sy, ga := hP.gx, gb := hP.gy
      gc := hP.gy, dg_w := hC.dg_w, maxf := hC.maxf, uab := hC.uab, room := hP.room
      rs := hP.rs, sp_al := hP.sp_al, sp_ge := hsp, ra_al := hP.ra_al, img := hP.img
      k_as := kd hsp (hS.disj (r := R.stk) (s := R.aS)), k_ad := kd hsp (hS.disj (r := R.stk) (s := R.aD))
      k_bs := kd hsp (hS.disj (r := R.stk) (s := R.bS)), k_bd := kd hsp (hS.disj (r := R.stk) (s := R.bD))
      k_cs := kd hsp (hS.disj (r := R.stk) (s := R.bS)), k_cd := kd hsp (hS.disj (r := R.stk) (s := R.bD))
      k_t := kd hsp (hS.disj (r := R.stk) (s := R.code))
      t_cs := td (hS.disj (r := R.code) (s := R.bS)), t_cd := td (hS.disj (r := R.code) (s := R.bD)) }
  refine entry_reshape (Triple.rmap (fun cf ⟨c', M, hat, hr, hm, hM⟩ => ⟨c', M, ret_reshape hat, hr, hm,
    fun x hx => ?_⟩) (whole (s0 := s0) (v := v) (outp := outp) h))
  have := off3 hsp (by simpa only [InAny, Iv.In, Two.lay, Two.ws, or_false] using hx)
  exact hM x this.1 this.2.1 this.2.2

end Tom.Machine.Fn.MulFast
