import Tom.Machine.Fn.MpSubAlias
import Tom.Machine.Fn.MpAddAlias
import Tom.Machine.Api.MpSubAddS

/-!
# `mp_sub(a, b, a)` (same signs) and `mp_add(a, b, a)` (different signs) on the machine

`Api.MpSubAddS.StatementS`/`StatementD`: `Fn/MpSubAlias.lean`'s and `Fn/MpAddAlias.lean`'s
proofs with the `s_mp_add` branch excluded by the signs, so the room is `max(used) ≤ alloc`.
-/

namespace Tom.Machine.Fn.MpSubAddS

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.BinA

theorem correctS : MpSubAddS.StatementS := by
  intro m v outp sp pa adp pb bdp a b ra s0 hP
  have hroom := hP.room
  have hfs := MpSub.flip_sign (a := a) hP.va.sign_ok
  have hT : ∀ M, Frm (BinA.lay 64 sp pa adp pb bdp a b) [BinA.R.stk] m M →
      BinATail.TA m M sp pa adp pb bdp a b ra :=
    fun M hF => { base := hP.toBase, sa := hP.va.toShape, sb := hP.vb.toShape, lay := hP.lay, fr := hF }
  refine Triple.lmap (fun cf h => h.reshape (L' := MpSub.entry1 ra s0 v.s.s1 sp pa pb pa) (K' := v.keepR1)
    (by simp [Fn.SSub.entryL, MpSub.entry1, Abi.keepR, sKeepL])
    (by simp [Fn.SSub.entryL, Abi.keepR1, Abi.keepR, sKeepL])) ?_
  refine MpSub.Alias.skel hP.lay rfl hP.toBase hP.va hP.vb
    (MpSub.Alias.csign (r := BinA.R.aS) hP.lay rfl rfl (Or.inl hP.ga)) ?_ ?_ ?_
  · intro hne; exact absurd hP.same hne
  · intro he hge M hF
    exact Triple.rmap (MpSub.Alias.retA fun c' q => ⟨fun h => absurd he h, fun _ _ => q, fun _ h => absurd h hge⟩)
      (BinATail.subA (hT M hF) (cmpMag_ge_used hP.va hP.vb hge) _ hP.va.sign_ok)
  · intro he hlt M hF
    exact Triple.rmap (MpSub.Alias.retA fun c' q => ⟨fun h => absurd he h, fun _ h => absurd hlt h,
        fun _ _ => by rw [← hfs.1]; exact q⟩)
      (BinATail.subBA (hT M hF) (cmpMag_lt_used hP.va hP.vb hlt) (by omega) _ hfs.2)

theorem correctD : MpSubAddS.StatementD := by
  intro m v outp sp pa adp pb bdp a b ra s0 hP
  have hroom := hP.room
  have hT : ∀ M, Frm (BinA.lay 64 sp pa adp pb bdp a b) [BinA.R.stk] m M → BinATail.TA m M sp pa adp pb bdp a b ra :=
    fun M hF => { base := hP.toBase, sa := hP.va.toShape, sb := hP.vb.toShape, lay := hP.lay, fr := hF }
  refine Triple.lmap (fun cf h => h.reshape (L' := MpSub.entry1 ra s0 v.s.s1 sp pa pb pa) (K' := v.keepR1)
    (by simp [SSub.entryL, MpSub.entry1, Abi.keepR, sKeepL])
    (by simp [SSub.entryL, Abi.keepR1, Abi.keepR, sKeepL])) ?_
  refine MpAdd.Alias.skel hP.lay rfl hP.toBase hP.va hP.vb
    (MpAdd.Alias.csign (r := BinA.R.aS) hP.lay rfl rfl (Or.inl hP.ga)) ?_ ?_ ?_
  · intro he; exact absurd he hP.diff
  · intro hne hlt M hF
    exact Triple.rmap (MpAdd.Alias.retA fun c' q => ⟨fun h => absurd h hne, fun _ _ => q, fun _ h => absurd hlt h⟩)
      (BinATail.subBA (hT M hF) (cmpMag_lt_used hP.va hP.vb hlt) (by omega) _ hP.vb.sign_ok)
  · intro hne hge M hF
    exact Triple.rmap (MpAdd.Alias.retA fun c' q => ⟨fun h => absurd h hne, fun _ h => absurd h hge, fun _ _ => q⟩)
      (BinATail.subA (hT M hF) (cmpMag_ge_used hP.va hP.vb hge) _ hP.va.sign_ok)

end Tom.Machine.Fn.MpSubAddS
