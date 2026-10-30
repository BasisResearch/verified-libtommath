import Tom.Machine.Api.StdHeapFn

/-!
# `mp_grow(a, size)` for a caller that re-places its own region

`Std.mpGrowH` (`Api/StdHeapFn.lean`) with one more fact in the grown case: the new block is
`Fresh` for the other blocks (`MpGrow.Post.ok`'s `fresh`). A caller whose own contract region
is the site (`mp_lshd(a, b)`, `mp_mul_2d(a, b, a)`, `mp_mul_d(a, b, c)` growing `a` or `c`)
re-places that region in its own `HPost` by `Place.regrow`, which needs it; `HContract.after`
consumes the callee's `HPost.place`, so the fact must come through `Q`. Everything else is
`mpGrowH`'s (`Gr.out`, `Gr.site'`, `Gr.hout`, `GrRes`).
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `Gr.Q` with the fresh block in the grown case. -/
def Gr.QF (p : GrP) : GrX → Prop
  | none => p.size ≤ p.a.alloc
  | some none => p.a.alloc < p.size
  | some (some (q, a')) => p.a.alloc < p.size ∧ GrowPost p.a p.size a' ∧ Fresh p.H q (4 * a'.alloc)

def mpGrowF : HContract where
  P := GrP
  X := GrX
  R := Un.R
  all := [.stk, .aS, .aD, .code]
  hall := Un.all
  entry := Fn.MpGrowR.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.size)]
  rets _ x ra := [(1, ra), (10, match x with | some none => MpGrow.memBV | _ => 0#64)]
  lay p := Un.lay MpGrow.F p.sp p.pa p.adp p.a
  kind p := Tom.Machine.Un.kind p.pa p.adp p.a
  out := Gr.out
  isW := Un.isW
  ws := Un.ws
  site := .aD
  site' := Gr.site'
  hin p := digBlk p.adp p.a :: p.H
  hout := Gr.hout
  Res := GrRes
  Q := Gr.QF
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | _ | ⟨q, a'⟩ <;> cases r <;> simp_all [Gr.out, Tom.Machine.Un.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    cases r with
    | stk => exact .inl (show 0 < MpGrow.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by have := h.apos; omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := by
    intro p m v outp ra hra hres hS hB hH hoff c hc
    obtain ⟨sp, pa, adp, a, size, H⟩ := p
    obtain ⟨hst, hso, hsh, hap, hsz⟩ := hres
    have hctx := hst.ctx hc rfl rfl (hB .code).2 hH.imp hra
    have g := Hdr.geom (hB .aS).2
    have hpre : MpGrow.Pre m v H sp pa adp a size ra :=
      { repr := Hdr.mpAt (hB .aS).2 (hB .aD).2, shape := hsh, heap := hH.heap
        st := by simpa [Layout.sizeofMpInt] using g.st, st_al := g.st_al, soff := hso, size_lt := hsz
        ctx := ⟨hctx.img, hctx.impure, hctx.gp, hctx.sp_v, hctx.sp_al, hctx.sp_lo, hctx.sp_hi⟩
        ra_al := hra, lay := hS }
    obtain ⟨c', hs, r, M, hat, hpost⟩ := Fn.MpGrowR.correct hpre c (hc.subL rfl)
    have hb := Fn.Alloc.Heap.blk hH.heap (List.mem_cons_self ..)
    have hstr : Ram pa 24 := by simpa [Layout.sizeofMpInt] using g.st
    have himp : ∀ (M : Mem), HFrm (MpGrow.lay sp pa adp a) Un.ws H m M → ImpureAt M := fun M hf =>
      ImpureAt.of_keep hf (fun x h1 h2 hw => hw.elim (fun hw => by
          rcases hw with h | h | h | h
          · exact offHeap_imp hst.off h.1 h.2 ⟨h1, h2⟩
          · exact offHeap_imp hso h.1 h.2 ⟨h1, h2⟩
          · have e : heapStart = 0x80019d10 := rfl
            have hb1 : heapStart + 16 ≤ adp := hb.1
            have := h.1; simp only [Un.lay] at this; unfold impurePtr at h2; omega
          · exact h.elim) (impure_off_foot h1 h2)) hH.imp
    have hfr : ∀ (M : Mem), HFrm (MpGrow.lay sp pa adp a) Un.ws H m M →
        HFrm (Un.lay MpGrow.F sp pa adp a) Un.ws (digBlk adp a :: H) m M := fun M hf =>
      Keep.mono hf fun x h => h.elim .inl fun hf =>
        (foot_uncons (e := digBlk adp a) hf).elim .inr fun hb' => .inl (.inr (.inr (.inl hb')))
    cases hpost with
    | keep hle same =>
      rw [same] at hat
      refine ⟨c', hs, none, m, hat, hle, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | aS => exact hB .aS
                | aD => exact absurd rfl hrs
                | code => simp [Un.ws] at hr
              wsite := hB .aD, place := .keep, frame := fun _ _ => rfl, heap := hH
              foot := fun a ha => .inl ha, off := hoff .aD }
    | @ok q a' hlt hf heap repr grow frame =>
      have hn : 0 < size := by omega
      have g' := geom_fresh hstr g.st_al hso (grow.alloc ▸ hf) (by rw [grow.alloc]; exact hn)
      refine ⟨c', hs, some (some (q, a')), M, hat, ⟨hlt, grow, grow.alloc ▸ hf⟩, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | aS => exact ⟨Iv.sub_self _, Hdr.of_mpAt repr g'⟩
                | aD => exact absurd rfl hrs
                | code => simp [Un.ws] at hr
              wsite := ⟨Iv.sub_self _, Dig.of_mpAt repr g'⟩
              place := .regrow (grow.alloc ▸ hf) (by rw [grow.alloc]; omega) rfl
              frame := hfr M frame, heap := ⟨by rw [Gr.hout, grow.alloc]; exact heap, himp M frame⟩
              foot := fun x hx => foot_uncons (e := digBlk adp a) (Foot.of_cons hx)
              off := by show Off ⟨q, 4 * a'.alloc⟩ ((q, 4 * a'.alloc) :: H); exact off_blk (grow.alloc ▸ hf) (by rw [grow.alloc]; omega) }
    | mem hlt heap repr frame =>
      refine ⟨c', hs, some none, M, hat, hlt, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | aS => exact ⟨Iv.sub_self _, Hdr.of_mpAt repr g⟩
                | aD => exact absurd rfl hrs
                | code => simp [Un.ws] at hr
              wsite := ⟨Iv.sub_self _, Dig.of_mpAt repr g⟩, place := .keep
              frame := hfr M frame, heap := ⟨heap, himp M frame⟩
              foot := fun x hx => .inl hx, off := hoff .aD }

end Tom.Machine.Std
