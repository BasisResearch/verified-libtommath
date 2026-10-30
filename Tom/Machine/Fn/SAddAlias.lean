import Tom.Machine.Fn.SAddDst
import Tom.Machine.Api.SAddAlias

/-!
# `s_mp_add` in place on the machine

`Api.SAddAlias.StatementCA`/`StatementCB` from the one assembly
`Fn.SAdd.AnyDst.correct`: the destination kernel sits in `BinA`'s regions by
`kA`/`kB` (its layout by `Sound.pull`, its frame back by `Frm.push`); the
destination operand is `Src.self`, the other `Src.own`.
-/

namespace Tom.Machine.Fn.SAdd

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.BinA

/-- **`s_mp_add(a, b, a)` on the machine.** -/
theorem correctCA : SAddAlias.StatementCA := by
  intro m v outp sp pa adp pb bdp a b ra s0 hP
  have hsub := sub_kA (pa := pa) (adp := adp) (a := a) (pb := pb) (bdp := bdp) (b := b) (code := ⟨sMpAddBase, 432⟩) (F := 64)
    (Nat.le_refl _) hP.sp_ge Bin.sub_text
  have hP' : AnyDst.Pre m sp pa adp pb bdp pa adp a b a ra :=
    { rc := hP.ra_, srcA := .self, srcB := src_ownB hP.lay hsub hP.rb
      sa := hP.sa, sb := hP.sb, sc := hP.sa, csign := hP.asign, ga := hP.ga, gb := hP.gb, gc := hP.ga
      room := hP.room, rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge, ra_al := hP.ra_al
      code := hP.img.sMpAdd, code_ms := hP.img.memset, code_cl := hP.img.mpClamp
      lay := hP.lay.pull kA _ Dst.all hsub }
  exact Triple.rmap (fun _ ⟨a', M, hat, hpost⟩ =>
      ⟨a', M, hat, hpost.repr, hpost.sadd, (Frm.push kA hsub hpost.frame).mono⟩)
    (AnyDst.correct hP')

/-- **`s_mp_add(a, b, b)` on the machine.** -/
theorem correctCB : SAddAlias.StatementCB := by
  intro m v outp sp pa adp pb bdp a b ra s0 hP
  have hsub := sub_kB (pa := pa) (adp := adp) (a := a) (pb := pb) (bdp := bdp) (b := b) (code := ⟨sMpAddBase, 432⟩) (F := 64)
    (Nat.le_refl _) hP.sp_ge Bin.sub_text
  have hP' : AnyDst.Pre m sp pa adp pb bdp pb bdp a b b ra :=
    { rc := hP.rb, srcA := src_ownA hP.lay hsub hP.ra_, srcB := .self
      sa := hP.sa, sb := hP.sb, sc := hP.sb, csign := hP.bsign, ga := hP.ga, gb := hP.gb, gc := hP.gb
      room := hP.room, rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge, ra_al := hP.ra_al
      code := hP.img.sMpAdd, code_ms := hP.img.memset, code_cl := hP.img.mpClamp
      lay := hP.lay.pull kB _ Dst.all hsub }
  exact Triple.rmap (fun _ ⟨b', M, hat, hpost⟩ =>
      ⟨b', M, hat, hpost.repr, hpost.sadd, (Frm.push kB hsub hpost.frame).mono⟩)
    (AnyDst.correct hP')

end Tom.Machine.Fn.SAdd
