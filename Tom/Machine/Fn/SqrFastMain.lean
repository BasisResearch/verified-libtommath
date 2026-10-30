import Tom.Machine.Fn.SqrFastCore
import Tom.Machine.Api.SqrFast

/-!
# `s_mp_sqr_fast` on the machine: the contracts

`Fn/SqrFastCore.lean`'s `whole` for distinct operands (`correct :
Api.SqrFast.Statement`, regions `Api/Two.lean`) and in place
(`correct_inplace : Api.SqrFast.StatementInPlace`, regions `Api/Un.lean`).
-/

namespace Tom.Machine.Fn.SqrFast

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api
open Tom.Machine.Fn.MulFast (kF rL)

theorem kd {sp p n : Nat} (hsp : 2208 ≤ sp) (h : Iv.Disj ⟨sp - 2208, 2208⟩ ⟨p, n⟩) :
    sp ≤ p ∨ p + n ≤ sp - 2208 := by
  unfold Iv.Disj Disj at h; simp only at h; rwa [Nat.sub_add_cancel hsp] at h

theorem td {p n : Nat} (h : Iv.Disj textIv ⟨p, n⟩) : textBase + textLen ≤ p ∨ p + n ≤ textBase := h

theorem ret_reshape {ra s0 : BitVec 64} {v : Abi} {sp : Nat} {M : Mem} {outp : Array String}
    {cf : Vsa.Machine.Config} (h : At ra (rL ra s0 v sp) M (kF v) outp cf) :
    At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf :=
  h.reshape (by simp [rL]) (by simp [rL, kF, Abi.keepR, sKeepL])

theorem entry_reshape {ra s0 : BitVec 64} {v : Abi} {sp pa pb : Nat} {m : Mem} {outp : Array String}
    {Q : Vsa.Machine.Config → Prop}
    (h : Triple (At 0x80007010#64 (entL ra s0 v sp pa pb) m (kF v) outp) Q) :
    Triple (At SqrFast.entry (SqrFast.entryL ra s0 sp pa pb) m v.keepR outp) Q :=
  Triple.lmap (fun _ h => h.reshape (by simp [entL, SqrFast.entryL, Abi.keepR, sKeepL])
    (by simp [kF, Abi.keepR, sKeepL])) h

theorem off3 {sp pc cdp al x : Nat} (hsp : 2208 ≤ sp)
    (h : ¬ ((sp - 2208 ≤ x ∧ x < sp - 2208 + 2208) ∨ (pc ≤ x ∧ x < pc + 24) ∨ (cdp ≤ x ∧ x < cdp + 4 * al))) :
    (x < sp - 2208 ∨ sp ≤ x) ∧ (x < pc ∨ pc + 24 ≤ x) ∧ (x < cdp ∨ cdp + 4 * al ≤ x) := by
  rw [Nat.sub_add_cancel hsp] at h; omega

/-- **`s_mp_sqr_fast(a, b)` on the machine.** -/
theorem correct : Api.SqrFast.Statement := by
  intro m v outp sp pa adp pb bdp a b ra s0 hP
  have hS := hP.lay; have hsp := hP.sp_ge
  open Tom.Machine.Api.Two in
  have h : SEnt m sp pa adp pb bdp a b ra :=
    { ra_ := hP.ra_, rb := hP.rb, sa := hP.sa, sb := hP.sb, ga := hP.ga, gb := hP.gb, warr := hP.warr
      room := hP.room, rs := hP.rs, sp_al := hP.sp_al, sp_ge := hsp, ra_al := hP.ra_al, img := hP.img
      k_as := kd hsp (hS.disj (r := R.stk) (s := R.aS)), k_ad := kd hsp (hS.disj (r := R.stk) (s := R.aD))
      k_bs := kd hsp (hS.disj (r := R.stk) (s := R.bS)), k_bd := kd hsp (hS.disj (r := R.stk) (s := R.bD))
      k_t := kd hsp (hS.disj (r := R.stk) (s := R.code))
      t_bs := td (hS.disj (r := R.code) (s := R.bS)), t_bd := td (hS.disj (r := R.code) (s := R.bD)) }
  refine entry_reshape (Triple.rmap (fun cf ⟨c', M, hat, hr, hm, hM⟩ => ⟨c', M, ret_reshape hat, hr, hm,
    fun x hx => ?_⟩) (whole (s0 := s0) (v := v) (outp := outp) h))
  have := off3 hsp (by simpa only [InAny, Iv.In, SqrFast.lay, Two.lay, Two.ws, or_false] using hx)
  exact hM x this.1 this.2.1 this.2.2

/-- **`s_mp_sqr_fast(a, a)` on the machine.** -/
theorem correct_inplace : Api.SqrFast.StatementInPlace := by
  intro m v outp sp pa adp a ra s0 hP
  have hS := hP.lay; have hsp := hP.sp_ge
  open Tom.Machine.Api.Un in
  have h : SEnt m sp pa adp pa adp a a ra :=
    { ra_ := hP.ra_, rb := hP.ra_, sa := hP.sa, sb := hP.sa, ga := hP.ga, gb := hP.ga, warr := hP.warr
      room := hP.room, rs := hP.rs, sp_al := hP.sp_al, sp_ge := hsp, ra_al := hP.ra_al, img := hP.img
      k_as := kd hsp (hS.disj (r := R.stk) (s := R.aS)), k_ad := kd hsp (hS.disj (r := R.stk) (s := R.aD))
      k_bs := kd hsp (hS.disj (r := R.stk) (s := R.aS)), k_bd := kd hsp (hS.disj (r := R.stk) (s := R.aD))
      k_t := kd hsp (hS.disj (r := R.stk) (s := R.code))
      t_bs := td (hS.disj (r := R.code) (s := R.aS)), t_bd := td (hS.disj (r := R.code) (s := R.aD)) }
  refine entry_reshape (Triple.rmap (fun cf ⟨c', M, hat, hr, hm, hM⟩ => ⟨c', M, ret_reshape hat, hr, hm,
    fun x hx => ?_⟩) (whole (s0 := s0) (v := v) (outp := outp) h))
  have := off3 hsp (by simpa only [InAny, Iv.In, SqrFast.layI, Un.lay, Un.ws, or_false] using hx)
  exact hM x this.1 this.2.1 this.2.2

end Tom.Machine.Fn.SqrFast
