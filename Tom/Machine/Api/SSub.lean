import Tom.Machine.Api.Bin
import Tom.Machine.Fn.SSubMain

/-!
# `s_mp_sub`: the standard contract

`Fn.SSub.correct` restated over `Bin`'s named regions (stack depth 48):
the layout is `Sound`, all code is `Img`, the frame is `Frm`.
-/

namespace Tom.Machine.Api.SSub

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Bin

abbrev lay (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt) := Bin.lay 48 sp pa adp pb bdp pc cdp a b c

/-- What `s_mp_sub(a, b, c)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  rc : MpAt m pc cdp c
  sa : a.Shape
  sb : b.Shape
  sc : c.Shape
  csign : c.sign = Layout.mpZpos ∨ c.sign = Layout.mpNeg
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  gc : MpGeom pc cdp c.alloc
  ge : b.used ≤ a.used
  room : a.used ≤ c.alloc
  rs : Ram (sp - 48) 48
  sp_al : sp % 16 = 0
  sp_ge : 48 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp pc cdp a b c) isW

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp pc cdp : Nat) (a b c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  ssub : SSubPost a b c c'
  frame : Frm (lay sp pa adp pb bdp pc cdp a b c) ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp pc cdp a b c c' M

def entry : BitVec 64 := 0x80004564#64

theorem correct {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat}
    {a b c : MpInt} {ra s0 : BitVec 64} (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Triple (At entry (Fn.SSub.entryL ra s0 sp pa pb pc) m v.keepR outp)
      (Ret m v outp sp pa adp pb bdp pc cdp a b c ra s0) := by
  have hS := hP.lay
  have hc := fun {b k : Nat} (h1 : textBase ≤ b) (h2 : b + k ≤ textBase + textLen) =>
    sub_text (b := b) (k := k) h1 h2
  have hP' : Fn.SSub.Pre m sp pa adp pb bdp pc cdp a b c ra :=
    { hP with
      code := hP.img.sMpSub, code_ms := hP.img.memset, code_cl := hP.img.mpClamp
      lay :=
       { s_cs := hS.disj (r := R.stk) (s := R.cS), s_cd := hS.disj (r := R.stk) (s := R.cD)
         s_as := hS.disj (r := R.stk) (s := R.aS), s_ad := hS.disj (r := R.stk) (s := R.aD)
         s_bs := hS.disj (r := R.stk) (s := R.bS), s_bd := hS.disj (r := R.stk) (s := R.bD)
         s_code := hS.sub (r := R.stk) (s := R.code) (Iv.sub_self _) (hc (by decide) (by decide))
         s_ms := hS.sub (r := R.stk) (s := R.code) (Iv.sub_self _) (hc (by decide) (by decide))
         s_cl := hS.sub (r := R.stk) (s := R.code) (Iv.sub_self _) (hc (by decide) (by decide))
         cs_as := hS.disj (r := R.cS) (s := R.aS), cs_ad := hS.disj (r := R.cS) (s := R.aD)
         cs_bs := hS.disj (r := R.cS) (s := R.bS), cs_bd := hS.disj (r := R.cS) (s := R.bD)
         cs_code := hS.sub (r := R.cS) (s := R.code) (Iv.sub_self _) (hc (by decide) (by decide))
         cs_ms := hS.sub (r := R.cS) (s := R.code) (Iv.sub_self _) (hc (by decide) (by decide))
         cs_cl := hS.sub (r := R.cS) (s := R.code) (Iv.sub_self _) (hc (by decide) (by decide))
         cd_as := hS.disj (r := R.cD) (s := R.aS), cd_ad := hS.disj (r := R.cD) (s := R.aD)
         cd_bs := hS.disj (r := R.cD) (s := R.bS), cd_bd := hS.disj (r := R.cD) (s := R.bD)
         cd_code := hS.sub (r := R.cD) (s := R.code) (Iv.sub_self _) (hc (by decide) (by decide))
         cd_ms := hS.sub (r := R.cD) (s := R.code) (Iv.sub_self _) (hc (by decide) (by decide))
         cd_cl := hS.sub (r := R.cD) (s := R.code) (Iv.sub_self _) (hc (by decide) (by decide)) } }
  exact Triple.rmap (fun _ ⟨c', M, hat, hpost⟩ => ⟨c', M, hat, hpost.repr, hpost.ssub,
      Frm.ofClause hpost.frame fun x h => by
        simp only [Fn.SSub.InW, InAny, Iv.In, lay, Bin.lay, ws, or_false] at h ⊢; omega⟩)
    (Fn.SSub.correct hP')

end Tom.Machine.Api.SSub
