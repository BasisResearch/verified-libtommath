import Tom.Machine.Api.MpAbs
import Tom.Machine.Api.MpCopy
import Tom.Machine.Fn.MpCopyMain
import Tom.Machine.Kit.Refine
import Tom.Machine.Kit.Call

/-!
# `mp_abs` on the machine: the whole function

`mp_copy(a, b)` (`Api.MpCopy.Statement`, called at `05dc` with this frame's
`sp`), then `b->sign := MP_ZPOS`. `mp_abs` reads its own frame (the saved
`ra` and `b`) after the call, so the contract's stack name is split into
this frame `fr` and the callee's `cs` (`R`, `Sound.refine`); `mp_copy`'s
layout is pulled from it by renaming its stack to `cs`, and its frame comes
back in `cs`, `bS`, `bD` (`Frm.push`), which miss `fr`.
-/


namespace Tom.Machine.Fn.MpAbs

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api

/-- `mp_abs`'s regions: its frame, `mp_copy`'s stack, the operands, the code. -/
inductive R | fr | cs | aS | aD | bS | bD | code
  deriving DecidableEq

def isW : R → Bool
  | .fr | .cs | .bS | .bD => true
  | _ => false

def lay (sp pa adp pb bdp : Nat) (a b : MpInt) : R → Iv
  | .fr => ⟨sp - 32, 32⟩
  | .cs => ⟨sp - 64, 32⟩
  | .aS => ⟨pa, 24⟩
  | .aD => ⟨adp, 4 * a.alloc⟩
  | .bS => ⟨pb, 24⟩
  | .bD => ⟨bdp, 4 * b.alloc⟩
  | .code => textIv

/-- Into the contract's names. -/
def up : R → Two.R
  | .fr | .cs => .stk
  | .aS => .aS | .aD => .aD | .bS => .bS | .bD => .bD | .code => .code

/-- `mp_copy`'s names in ours. -/
def down : Two.R → R
  | .stk => .cs
  | .aS => .aS | .aD => .aD | .bS => .bS | .bD => .bD | .code => .code

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt}
  {ra s0 : BitVec 64}

local notation "ρ" => lay sp pa adp pb bdp a b

theorem sub_up (hs : 64 ≤ sp) : ∀ k, (ρ k).Sub (Two.lay 64 sp pa adp pb bdp a b (up k)) := by
  intro k; cases k <;> first | exact Iv.sub_self _ | (simp only [Iv.Sub, lay, Two.lay, up]; omega)

theorem sound (hP : MpAbs.Pre m sp pa adp pb bdp a b ra) : Sound ρ isW := by
  have := hP.sp_ge
  refine Sound.refine up hP.lay (sub_up this) fun k l h1 h2 => ?_
  cases k <;> cases l <;> simp_all [Sep, isW, up, Two.isW] <;> simp only [Iv.Disj, Disj, lay] <;> omega

theorem sub_down (_hs : 64 ≤ sp) :
    ∀ k, (Two.lay 32 (sp - 32) pa adp pb bdp a b k).Sub (ρ (down k)) := by
  intro k; cases k <;> first | exact Iv.sub_self _ | (simp only [Iv.Sub, lay, Two.lay, down]; omega)

theorem all : ∀ k : Two.R, k ∈ [Two.R.stk, .aS, .aD, .bS, .bD, .code] := Two.all

/-- What stays as at the entry. -/
structure RO (M : Mem) (pa adp pb bdp : Nat) (a b : MpInt) : Prop where
  img : Img M
  ra_ : MpAt M pa adp a
  rb : MpAt M pb bdp b

theorem RO.of (hP : MpAbs.Pre m sp pa adp pb bdp a b ra) {M : Mem} (hF : Frm ρ [R.fr] m M) :
    RO M pa adp pb bdp a b :=
  have hS := sound hP
  { img := hF.keep hS (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
    ra_ := hF.keep hS (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_
    rb := hF.keep hS (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _)) hP.rb }

end

/-- **`mp_abs` on the machine** (distinct operands). -/
theorem correct : Api.MpAbs.Statement := by
  intro m v outp sp pa adp pb bdp a b ra s0 hP
  have hS := sound hP
  have := hP.sp_ge
  have h1 := hS.disj (r := R.aS) (s := R.bS)
  have h2 := hS.disj (r := R.fr) (s := R.bS)
  have h3 := hS.sub (r := R.fr) (s := R.code) (Iv.sub_self _) (⟨by decide, by decide⟩ : Iv.Sub ⟨mpAbsBase, 60⟩ textIv)
  have h4 := hS.sub (r := R.bS) (s := R.code) (Iv.sub_self _) (⟨by decide, by decide⟩ : Iv.Sub ⟨mpAbsBase, 60⟩ textIv)
  simp only [Iv.Disj, Disj, lay] at h1 h2 h3 h4
  have hra : Ram pa 24 := by simpa [Layout.sizeofMpInt] using hP.ga.st
  have hrb : Ram pb 24 := by simpa [Layout.sizeofMpInt] using hP.gb.st
  have ⟨_, _, _⟩ := ram_bounds hra; have ⟨_, _, _⟩ := ram_bounds hrb
  have hff : FFacts sp :=
    { rs := ⟨by have := hP.rs.lo_ge; omega, by have := hP.rs.hi_le; omega, by have := hP.rs.off; omega⟩
      sp_al := hP.sp_al, sp_ge := by omega, code_off := by omega }
  have hF1 : Frm (lay sp pa adp pb bdp a b) [R.fr] m (writeLog m (frameLog ra sp pb)) :=
    Frm.store (by simp only [LogIn, frameLog, Iv.Sub, lay, and_true]; omega)
  have hro := RO.of hP hF1
  have hcp : MpCopy.Pre (writeLog m (frameLog ra sp pb)) (sp - 32) pa adp pb bdp a b 0x800005e0#64 :=
    { ra_ := hro.ra_, rb := hro.rb, sa := hP.sa, sb := hP.sb, asign := hP.asign, ga := hP.ga, gb := hP.gb
      room := hP.room
      rs := ⟨by have := hP.rs.lo_ge; omega, by have := hP.rs.hi_le; omega, by have := hP.rs.off; omega⟩
      sp_al := by have := hP.sp_al; omega, sp_ge := by omega, ra_al := by decide, img := hro.img
      lay := hS.pull down _ all (sub_down (by omega)) }
  refine Triple.seq (p_step ra s0 v outp sp pa pb m hP.img.mpAbs hff (by omega) (by omega) (by omega))
    (Triple.seq (jal_step 0x800005dc#64 0x204000ef#32 0x00204#21
      [(2, BitVec.ofNat 64 (sp - 32)), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)]
      hro.img.mpAbs [entryL] [Abi.keepR]) ?_)
  have hpc : (0x800005dc#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x00204#21) = MpCopy.entry := by
    decide
  rw [hpc]
  refine Triple.dimap (fun cf h => h.reshape (L' := Fn.MpCopy.entryL 0x800005e0#64 s0 (sp - 32) pa pb)
      (by simp [Fn.MpCopy.entryL, Sail.BitVec.addInt]) (fun p hp => by simp [hp]))
    (fun cf h => h) (Fn.MpCopy.correct (v := v) hcp) |>.seq ?_
  intro cf ⟨b', M, hat, hpost⟩
  have hFc := Frm.push down (sub_down (by omega)) hpost.frame
  have hM1 : bytesT8 (writeLog m (frameLog ra sp pb)) (sp - 8) = ra ∧
      bytesT8 (writeLog m (frameLog ra sp pb)) (sp - 24) = BitVec.ofNat 64 pb :=
    ⟨bytesT8_log _ _ 0 _ _ rfl (by simp [frameLog, OutLRange]; omega), bytesT8_log _ _ 1 _ _ rfl (by simp [frameLog, OutLRange])⟩
  have hrf : RFacts M ra sp pb :=
    { rs := hff.rs, sp_al := hP.sp_al, sp_ge := by omega, ra_al := hP.ra_al
      ra_v := hFc.keep hS (Reads.w8 (r := R.fr) (by simp only [Iv.Sub, lay]; omega)) hM1.1
      pb_v := hFc.keep hS (Reads.w8 (r := R.fr) (by simp only [Iv.Sub, lay]; omega)) hM1.2
      s_b := by omega }
  have hro2 := hFc.keep hS (Img.reads (r := R.code) (Iv.sub_self _)) hro.img
  refine Triple.rmap (fun cf h => ⟨b'.withSign 0, _, h, ?_⟩)
    (r_step ra s0 v outp sp pb M hro2.mpAbs hrf ⟨hrb, hP.gb.st_al, by omega⟩) cf
    (hat.reshape (by simp) (fun p hp => by simp [hp]))
  have hcopy := hpost.copy
  have hF3 : Frm (lay sp pa adp pb bdp a b) [R.bS] M (writeLog M [(pb + 8, 4, 0#64)]) :=
    Frm.sw (by simp only [Iv.Sub, lay]; omega)
  exact { repr := hpost.repr.set_sign (by rw [hcopy.alloc]; exact hP.gb) 0 (by decide)
          abs := AbsPost.of_copy hcopy
          frame := (Frm.push up (sub_up (by omega)) ((hF1.trans hFc).trans hF3)).mono }

/-- **`mp_abs(a, a)` on the machine.** -/
theorem alias_correct : Api.MpAbs.AliasStatement := by
  intro m v outp sp pa adp a ra s0 hP
  have hS := hP.lay
  have h4 := hS.sub (r := Un.R.aS) (s := Un.R.code) (Iv.sub_self _)
    (⟨by decide, by decide⟩ : Iv.Sub ⟨mpAbsBase, 60⟩ textIv)
  simp only [Iv.Disj, Disj, Un.lay] at h4
  have hra : Ram pa 24 := by simpa [Layout.sizeofMpInt] using hP.ga.st
  refine Triple.rmap (fun cf h => ⟨a.withSign 0, _, h, ?_⟩)
    (a_step ra s0 v outp sp pa m hP.img.mpAbs ⟨hra, hP.ga.st_al, by omega⟩ hP.ra_al)
  exact { repr := hP.ra_.set_sign hP.ga 0 (by decide)
          abs := { alloc := rfl, len := hP.sa.len, used := rfl, sign := rfl
                   digit := fun i => by
                     simp only [MpInt.withSign]
                     by_cases h : i < a.used <;> simp [h] <;> rfl }
          frame := (Frm.sw (w := Un.R.aS) (by simp only [Iv.Sub, Un.lay]; omega)).mono }

end Tom.Machine.Fn.MpAbs
