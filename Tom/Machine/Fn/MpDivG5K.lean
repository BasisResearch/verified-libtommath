import Tom.Machine.Api.MpDiv
import Tom.Machine.Api.Std_r8a
import Tom.Machine.Kit.Run
import Tom.Machine.Kit.OneSite
import Tom.Machine.Kit.Sites
import Tom.Machine.Kit.AnnFacts
import Tom.Machine.Fn.MpDivG
import Tom.Spec.MpDivStep5
import Tom.Spec.IntFacts

/-!
# `mp_div`'s assembly: helpers

For the generated `Fn/MpDivMainG.lean` (annotation `experiments/asm/mdiv.asm.json`; the region type
with the temporaries' digit arrays, `soundG` and `GPre` generated from its `"region"`):
* the contract's post `Post2` (two re-placed sites) from the final state: `post2_mem`,
  `post2_small`, `post2_big`;
* the small and big cases' `Q` (`small_Q`, `big_Q`);
* the step-3 spill facts `LS` and the 7-piece region tactic `kfast`.
-/

namespace Tom.Machine.Fn.MpDivG5K

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpDiv (P lay kind isW ws hin hout out siteC siteD Post2 Q Res)
open Tom

/-- **`MP_MEM`**: `c`, `d` and the heap's blocks as before. -/
theorem post2_mem {p : P} {m M : Mem} (hS : Sound (lay p) isW) (hoff : ∀ r, Off (lay p r) (hin p))
    (hw : ∀ r, r ∈ ws → r ≠ .cD → r ≠ .dD → (kind p r).Fits (lay p r) ∧ (kind p r).Wit (lay p r) M)
    (hc : (kind p .cD).Fits (lay p .cD) ∧ (kind p .cD).Wit (lay p .cD) M)
    (hd : (kind p .dD).Fits (lay p .dD) ∧ (kind p .dD).Wit (lay p .dD) M)
    (hfr : Keep (fun a => InAny (lay p) ws a ∨ Foot (hin p) a) m M) (hh : AHeap M (hin p)) :
    Post2 (lay p) ws .cD .dD (out p .mem) (siteC p .mem) (siteD p .mem) (hin p) (hout p .mem) m M :=
  { wit := fun r hr h1 h2 => by cases r <;> exact hw _ hr h1 h2
    wsc := hc, wsd := hd, placec := .keep, placed := .keep, sep := hS .cD .dD (by decide)
    frame := hfr, heap := hh, foot := fun _ h => .inl h, offc := hoff .cD, offd := hoff .dD }

/-- **`|a| < |b|`**: `c'`, `d'` in place. -/
theorem post2_small {p : P} {m M : Mem} {c' d' : MpInt} (hS : Sound (lay p) isW)
    (hoff : ∀ r, Off (lay p r) (hin p)) (hstk : Ram (lay p .stk).base (lay p .stk).len)
    (hcS : Hdr M p.pc p.cdp c') (hcD : Dig M p.cdp p.c.alloc c'.digit)
    (hdS : Hdr M p.pd p.ddp d') (hdD : Dig M p.ddp p.d.alloc d'.digit)
    (hfr : Keep (fun a => InAny (lay p) ws a ∨ Foot (hin p) a) m M) (hh : AHeap M (hin p)) :
    Post2 (lay p) ws .cD .dD (out p (.small c' d')) (siteC p (.small c' d')) (siteD p (.small c' d'))
      (hin p) (hout p (.small c' d')) m M :=
  { wit := fun r hr h1 h2 => by
      cases r <;> simp [ws] at hr h1 h2
      · exact ⟨trivial, hstk⟩
      · exact ⟨Iv.sub_self _, hcS⟩
      · exact ⟨Iv.sub_self _, hdS⟩
    wsc := ⟨Iv.sub_self _, hcD⟩, wsd := ⟨Iv.sub_self _, hdD⟩, placec := .keep, placed := .keep
    sep := hS .cD .dD (by decide)
    frame := hfr, heap := hh, foot := fun _ h => .inl h, offc := hoff .cD, offd := hoff .dD }

/-- The small case's `Q`: `mp_copy(a, d)` and `mp_zero(c)`. -/
theorem small_Q {p : P} {c' d' : MpInt} (hres : Res p) (hlt : p.a.mag < p.b.mag) (hz : ZeroPost p.c c')
    (hcp : CopyPost p.a p.d d') : Q p (.small c' d') := by
  have ha := hres.va
  refine ⟨hlt, ⟨fun _ => ?_, fun h => absurd h (Nat.not_le.2 hlt)⟩, ⟨fun _ => ?_, fun h => absurd h (Nat.not_le.2 hlt)⟩⟩
  · exact ⟨hz.alloc, hz.len, funext hz.digit, by rw [hz.used]; rfl, by rw [hz.sign]; split <;> rfl⟩
  · refine ClampedTo.of_copy ha hcp.alloc hcp.len (funext fun i => ?_) hcp.used hcp.sign
    rw [hcp.digit i]
    by_cases h1 : i < p.a.used
    · rw [if_pos h1]
    · rw [if_neg h1, ha.high_zero i (by omega)]
      by_cases h2 : i < p.d.used
      · rw [if_pos h2]
      · rw [if_neg h2, hres.dsh.high_zero i (by omega)]

/-- The own frame's spills during step 3: `0(sp) = 4t - 4`, `8(sp)`, `16(sp)` the signs. -/
structure LS (F : Mem) (sp t sa sb : Nat) : Prop where
  l0 : MpDivG.L0 F sp t
  sg : MpDivG.SG F sp sa sb

theorem bytesT8_wl_out {m : Mem} {a b : Nat} {v : BitVec 64} (h : b + 8 ≤ a ∨ a + 8 ≤ b) :
    bytesT8 (writeLog m [(a, 8, v)]) b = bytesT8 m b :=
  bytesT8_congr (fun x h1 h2 => writeLog_out _ _ _ ⟨by dsimp only; omega, trivial⟩)

/-- The spill of `q.dp`'s address at `24(sp)` keeps them. -/
theorem LS.push {F : Mem} {sp t sa sb : Nat} (h : LS F sp t sa sb) (v : BitVec 64) (hs : 272 ≤ sp) :
    LS (writeLog F [(sp - 248, 8, v)]) sp t sa sb :=
  ⟨⟨by rw [bytesT8_wl_out (by omega)]; exact h.l0.f0⟩,
   ⟨by rw [bytesT8_wl_out (by omega)]; exact h.sg.f0, by rw [bytesT8_wl_out (by omega)]; exact h.sg.f1⟩⟩

/-- The big case's `Q`. -/
theorem big_Q {p : P} {qc qd : Nat} {c' d' : MpInt} (hge : p.b.mag ≤ p.a.mag) (hq : DivBigQuot p.a p.b c')
    (hr : DivBigRem p.a p.b d') : Q p (.big qc c' qd d') :=
  ⟨hge, ⟨fun h => absurd hge (Nat.not_le.2 h), fun _ => hq⟩, ⟨fun h => absurd hge (Nat.not_le.2 h), fun _ => hr⟩⟩

/-- **The long division done**: `c'` at `q`'s block, `d'` at `x`'s, both fresh for the heap before,
the old blocks freed. -/
theorem post2_big {p : P} {m M : Mem} {qc qd nc nd : Nat} {c' d' : MpInt}
    (hres : Res p) (hS : Sound (lay p) isW) (hoff : ∀ r, Off (lay p r) (hin p)) (hstk : Ram (lay p .stk).base (lay p .stk).len)
    (hcS : Hdr M p.pc qc c') (hcD : Dig M qc c'.alloc c'.digit) (hdS : Hdr M p.pd qd d') (hdD : Dig M qd d'.alloc d'.digit)
    (hnc : c'.alloc = nc) (hnd : d'.alloc = nd) (hc0 : 0 < nc) (hd0 : 0 < nd)
    (hfc : Fresh (hin p) qc (4 * nc)) (hfd : Fresh (hin p) qd (4 * nd)) (hsep : Iv.Disj ⟨qc, 4 * nc⟩ ⟨qd, 4 * nd⟩)
    (hfr : Keep (fun a => InAny (lay p) ws a ∨ Foot (hin p) a) m M)
    (hh : AHeap M ((qd, 4 * nd) :: (qc, 4 * nc) :: p.H))
    (hfoot : ∀ a, Foot ((qd, 4 * nd) :: (qc, 4 * nc) :: p.H) a → InAny (lay p) ws a ∨ Foot (hin p) a)
    (hoc : Off ⟨qc, 4 * nc⟩ ((qd, 4 * nd) :: (qc, 4 * nc) :: p.H))
    (hod : Off ⟨qd, 4 * nd⟩ ((qd, 4 * nd) :: (qc, 4 * nc) :: p.H)) :
    Post2 (lay p) ws .cD .dD (out p (.big qc c' qd d')) (siteC p (.big qc c' qd d')) (siteD p (.big qc c' qd d'))
      (hin p) (hout p (.big qc c' qd d')) m M := by
  subst hnc hnd
  have hp : List.Perm ((qd, 4 * d'.alloc) :: (qc, 4 * c'.alloc) :: p.H) ((qc, 4 * c'.alloc) :: (qd, 4 * d'.alloc) :: p.H) :=
    List.Perm.swap _ _ _
  have hso := hres.stk.off
  have hco := hres.coff
  have hdo := hres.doff
  refine { wit := fun r hr h1 h2 => ?_, wsc := ⟨Iv.sub_self _, hcD⟩, wsd := ⟨Iv.sub_self _, hdD⟩
           placec := .fresh hfc (by omega), placed := .fresh hfd (by omega), sep := hsep, frame := hfr
           heap := hh.perm hp, foot := fun a ha => ?_, offc := hoc.perm hp, offd := hod.perm hp }
  · cases r <;> simp [ws] at hr h1 h2
    · exact ⟨trivial, hstk⟩
    · exact ⟨Iv.sub_self _, hcS⟩
    · exact ⟨Iv.sub_self _, hdS⟩
  · have hf := (foot_perm hp).2 ha
    rcases hfoot a hf with h | h
    · simp only [ws, InAny, lay, Iv.In] at h
      rcases h with h | h | h | h | h | h
      · exact absurd (foot_offHeap ha hso h.1 (by simpa using h.2)) id
      · exact absurd (foot_offHeap ha hco h.1 h.2) id
      · exact .inr (.inl h)
      · exact absurd (foot_offHeap ha hdo h.1 h.2) id
      · exact .inr (.inr h)
      · exact h.elim
    · exact .inl h

/-- Regions of the generated 7-piece type equal by computation, the contract's names case by case first
(`rfl` on an unsplit `r` unfolds the whole state). -/
macro "kfast" : tactic =>
  `(tactic| (intro r; rcases r with _ | _ | _ | _ | _ | _ | _ | r <;> first | (cases r <;> rfl) | rfl))

end Tom.Machine.Fn.MpDivG5K
