import Tom.Machine.Fn.SAddAlias
import Tom.Machine.Fn.SSubAlias
import Tom.Machine.Fn.MpSub
import Tom.Spec.Alias

/-!
# In-place tail calls of `mp_add`/`mp_sub`

`mp_add(a, b, c)` and `mp_sub(a, b, c)` end by storing `c->sign := s` and
tail-jumping to `s_mp_add` or `s_mp_sub`. With `c = a` the calls are
`s_mp_add(a, b, a)`, `s_mp_sub(a, b, a)` and `s_mp_sub(b, a, a)`; with
`c = b`, `s_mp_add(a, b, b)`, `s_mp_sub(a, b, b)` and `s_mp_sub(b, a, b)`.
Each lemma here takes the memory `M` at the jump (changed since the entry
only in the stack, `TA`/`TB`), the sign store, and the in-place contract
of the callee (`SAdd.correctCA`, …; `s_mp_sub(b, a, ·)` with the operands
exchanged by `BinA.swap`), and gives the result in the caller's regions:
the callee's post with the destination operand as it was before the sign
store (`Tom/Spec/Alias.lean`), its frame by `Frm.push`. `mp_add` and
`mp_sub` share them.
-/

namespace Tom.Machine.Fn.BinATail

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.BinA

/-- What a tail call leaves: the destination `d'` at `(p, dp)`, `Q`, memory
changed only in `ws`. -/
structure Out (ρ : R → Iv) (ws : List R) (m M : Mem) (p dp : Nat) (d' : MpInt) (Q : Prop) : Prop where
  repr : MpAt M p dp d'
  q : Q
  frame : Frm ρ ws m M

/-- The return state with the destination described by `Q`. -/
def RetQ (m : Mem) (v : Abi) (outp : Array String) (sp : Nat) (ρ : R → Iv) (ws : List R) (p dp : Nat)
    (ra s0 : BitVec 64) (Q : MpInt → Prop) (cf : Vsa.Machine.Config) : Prop :=
  ∃ d' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Out ρ ws m M p dp d' (Q d')

/-- At a tail call of `op(a, b, a)`: the entry facts, and since the entry
only the stack changed. -/
structure TA (m M : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  base : Base m 64 sp pa adp pb bdp a b ra
  sa : a.Shape
  sb : b.Shape
  lay : Sound (BinA.lay 64 sp pa adp pb bdp a b) isWA
  fr : Frm (BinA.lay 64 sp pa adp pb bdp a b) [R.stk] m M

/-- At a tail call of `op(a, b, b)`. -/
structure TB (m M : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  base : Base m 64 sp pa adp pb bdp a b ra
  sa : a.Shape
  sb : b.Shape
  lay : Sound (BinA.lay 64 sp pa adp pb bdp a b) isWB
  fr : Frm (BinA.lay 64 sp pa adp pb bdp a b) [R.stk] m M

/-- After the sign store into the destination `d` (struct `pd`, digits `ddp`;
the other operand `o`): what the callee needs, and the frame so far. -/
structure After (ρ : R → Iv) (ws : List R) (m M' : Mem) (pd ddp : Nat) (d : MpInt) (po odp : Nat) (o : MpInt) :
    Prop where
  rd : MpAt M' pd ddp d
  ro : MpAt M' po odp o
  img : Img M'
  fr : Frm ρ ws m M'

section
variable {m M : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt}
  {ra s0 : BitVec 64}

local notation "ρ" => BinA.lay 64 sp pa adp pb bdp a b

theorem sign_lt {s : Nat} (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg) : s < 2 ^ 32 := by
  simp only [Layout.mpZpos, Layout.mpNeg] at hs; omega

theorem TA.after (h : TA m M sp pa adp pb bdp a b ra) (s : Nat) (hs : s < 2 ^ 32) :
    After ρ [R.stk, R.aS] m (writeLog M [(pa + 8, 4, BitVec.ofNat 64 s)]) pa adp (a.withSign s) pb bdp b :=
  have hF3 := h.fr.trans (Frm.sw (w := R.aS) (v := BitVec.ofNat 64 s)
    (show Iv.Sub ⟨pa + 8, 4⟩ (ρ R.aS) by simp only [Iv.Sub, BinA.lay]; omega))
  { rd := (h.fr.keep h.lay (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _))
      h.base.ra_).set_sign h.base.ga s hs
    ro := hF3.keep h.lay (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _)) h.base.rb
    img := hF3.keep h.lay (Img.reads (r := R.code) (Iv.sub_self _)) h.base.img
    fr := hF3 }

theorem TB.after (h : TB m M sp pa adp pb bdp a b ra) (s : Nat) (hs : s < 2 ^ 32) :
    After ρ [R.stk, R.bS] m (writeLog M [(pb + 8, 4, BitVec.ofNat 64 s)]) pb bdp (b.withSign s) pa adp a :=
  have hF3 := h.fr.trans (Frm.sw (w := R.bS) (v := BitVec.ofNat 64 s)
    (show Iv.Sub ⟨pb + 8, 4⟩ (ρ R.bS) by simp only [Iv.Sub, BinA.lay]; omega))
  { rd := (h.fr.keep h.lay (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _))
      h.base.rb).set_sign h.base.gb s hs
    ro := hF3.keep h.lay (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) h.base.ra_
    img := hF3.keep h.lay (Img.reads (r := R.code) (Iv.sub_self _)) h.base.img
    fr := hF3 }

theorem shape_sign {c : MpInt} (hc : c.Shape) (s : Nat) : (c.withSign s).Shape :=
  ⟨hc.len, hc.used_le, hc.alloc_lt, hc.digit_lt, hc.high_zero⟩

/-! ## `c = a` -/

/-- `s_mp_add(a, b, a)` after `a->sign := s`. -/
theorem addA (h : TA m M sp pa adp pb bdp a b ra) (hroom : max a.used b.used + 1 ≤ a.alloc) (s : Nat)
    (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg) :
    Triple (At 0x8000219c#64 (MpSub.entry1 ra s0 v.s.s1 sp pa pb pa) (writeLog M [(pa + 8, 4, BitVec.ofNat 64 s)])
        v.keepR1 outp)
      (RetQ m v outp sp ρ wsA pa adp ra s0 (SAddPost a b (a.withSign s))) := by
  have hx := h.after s (sign_lt hs); have := h.base.sp_ge
  have hsub := sub_id (F := 64) (F' := 64) (sp := sp) (pa := pa) (adp := adp) (pb := pb) (bdp := bdp)
    (a := a) (b := b) (a' := a.withSign s) (b' := b) (Nat.le_refl _) (by omega) rfl rfl
  have hpre : SAddAlias.PreCA (writeLog M [(pa + 8, 4, BitVec.ofNat 64 s)]) sp pa adp pb bdp (a.withSign s) b ra :=
    { h.base with
      ra_ := hx.rd, rb := hx.ro, img := hx.img, sa := shape_sign h.sa s, sb := h.sb, asign := hs
      room := hroom, lay := h.lay.pull id _ BinA.all hsub }
  refine Triple.dimap (fun cf h => ?_)
    (fun cf ⟨a', M', hat, hpost⟩ => ⟨a', M', hat, hpost.repr, hpost.sadd.unsign_a,
      (hx.fr.trans (Frm.push id hsub hpost.frame)).mono⟩)
    (SAdd.correctCA hpre)
  exact h.reshape (by simp [Fn.SAdd.entryL, MpSub.entry1, Abi.keepR1])
    (by simp [MpSub.entry1, Abi.keepR1, Abi.keepR, sKeepL])

/-- `s_mp_sub(a, b, a)` after `a->sign := s`. -/
theorem subA (h : TA m M sp pa adp pb bdp a b ra) (hge : b.used ≤ a.used) (s : Nat)
    (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg) :
    Triple (At 0x80004564#64 (MpSub.entry1 ra s0 v.s.s1 sp pa pb pa) (writeLog M [(pa + 8, 4, BitVec.ofNat 64 s)])
        v.keepR1 outp)
      (RetQ m v outp sp ρ wsA pa adp ra s0 (SSubPost a b (a.withSign s))) := by
  have hx := h.after s (sign_lt hs); have := h.base.sp_ge; have hrs := h.base.rs
  have hsub := sub_id (F := 48) (F' := 64) (sp := sp) (pa := pa) (adp := adp) (pb := pb) (bdp := bdp)
    (a := a) (b := b) (a' := a.withSign s) (b' := b) (by decide) (by omega) rfl rfl
  have hpre : SSubAlias.PreCA (writeLog M [(pa + 8, 4, BitVec.ofNat 64 s)]) sp pa adp pb bdp (a.withSign s) b ra :=
    { h.base with
      ra_ := hx.rd, rb := hx.ro, img := hx.img, sa := shape_sign h.sa s, sb := h.sb, asign := hs
      rs := ⟨by have := hrs.lo_ge; omega, by have := hrs.hi_le; omega, by have := hrs.off; omega⟩
      sp_ge := by omega, ge := hge, lay := h.lay.pull id _ BinA.all hsub }
  refine Triple.dimap (fun cf h => ?_)
    (fun cf ⟨a', M', hat, hpost⟩ => ⟨a', M', hat, hpost.repr, hpost.ssub.unsign_a,
      (hx.fr.trans (Frm.push id hsub hpost.frame)).mono⟩)
    (SSub.correctCA hpre)
  exact h.reshape (by simp [Fn.SSub.entryL, MpSub.entry1, Abi.keepR1])
    (by simp [MpSub.entry1, Abi.keepR1, Abi.keepR, sKeepL])

/-- `s_mp_sub(b, a, a)` after `a->sign := s`: `SSubAlias.StatementCB` with
the operands exchanged. -/
theorem subBA (h : TA m M sp pa adp pb bdp a b ra) (hge : a.used ≤ b.used) (hroom : b.used ≤ a.alloc)
    (s : Nat) (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg) :
    Triple (At 0x80004564#64 (MpSub.entry1 ra s0 v.s.s1 sp pb pa pa) (writeLog M [(pa + 8, 4, BitVec.ofNat 64 s)])
        v.keepR1 outp)
      (RetQ m v outp sp ρ wsA pa adp ra s0 (SSubPost b a (a.withSign s))) := by
  have hx := h.after s (sign_lt hs); have := h.base.sp_ge; have hrs := h.base.rs
  have hsub := sub_swap (F := 48) (F' := 64) (sp := sp) (pa := pa) (adp := adp) (pb := pb) (bdp := bdp)
    (a := a) (b := b) (a' := a.withSign s) (b' := b) (by decide) (by omega) rfl rfl
  have hpre : SSubAlias.PreCB (writeLog M [(pa + 8, 4, BitVec.ofNat 64 s)]) sp pb bdp pa adp b (a.withSign s) ra :=
    { ra_ := hx.ro, rb := hx.rd, ga := h.base.gb, gb := h.base.ga, img := hx.img
      rs := ⟨by have := hrs.lo_ge; omega, by have := hrs.hi_le; omega, by have := hrs.off; omega⟩
      sp_al := h.base.sp_al, sp_ge := by omega, ra_al := h.base.ra_al
      sa := h.sb, sb := shape_sign h.sa s, bsign := hs, ge := hge, room := hroom
      lay := h.lay.pull swap _ BinA.all hsub }
  refine Triple.dimap (fun cf h => ?_)
    (fun cf ⟨a', M', hat, hpost⟩ => ⟨a', M', hat, hpost.repr, hpost.ssub.unsign_b,
      (hx.fr.trans (Frm.push swap hsub hpost.frame)).mono⟩)
    (SSub.correctCB hpre)
  exact h.reshape (by simp [Fn.SSub.entryL, MpSub.entry1, Abi.keepR1])
    (by simp [MpSub.entry1, Abi.keepR1, Abi.keepR, sKeepL])

/-! ## `c = b` -/

/-- `s_mp_add(a, b, b)` after `b->sign := s`. -/
theorem addB (h : TB m M sp pa adp pb bdp a b ra) (hroom : max a.used b.used + 1 ≤ b.alloc) (s : Nat)
    (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg) :
    Triple (At 0x8000219c#64 (MpSub.entry1 ra s0 v.s.s1 sp pa pb pb) (writeLog M [(pb + 8, 4, BitVec.ofNat 64 s)])
        v.keepR1 outp)
      (RetQ m v outp sp ρ wsB pb bdp ra s0 (SAddPost a b (b.withSign s))) := by
  have hx := h.after s (sign_lt hs); have := h.base.sp_ge
  have hsub := sub_id (F := 64) (F' := 64) (sp := sp) (pa := pa) (adp := adp) (pb := pb) (bdp := bdp)
    (a := a) (b := b) (a' := a) (b' := b.withSign s) (Nat.le_refl _) (by omega) rfl rfl
  have hpre : SAddAlias.PreCB (writeLog M [(pb + 8, 4, BitVec.ofNat 64 s)]) sp pa adp pb bdp a (b.withSign s) ra :=
    { h.base with
      ra_ := hx.ro, rb := hx.rd, img := hx.img, sa := h.sa, sb := shape_sign h.sb s, bsign := hs
      room := hroom, lay := h.lay.pull id _ BinA.all hsub }
  refine Triple.dimap (fun cf h => ?_)
    (fun cf ⟨b', M', hat, hpost⟩ => ⟨b', M', hat, hpost.repr, hpost.sadd.unsign_b,
      (hx.fr.trans (Frm.push id hsub hpost.frame)).mono⟩)
    (SAdd.correctCB hpre)
  exact h.reshape (by simp [Fn.SAdd.entryL, MpSub.entry1, Abi.keepR1])
    (by simp [MpSub.entry1, Abi.keepR1, Abi.keepR, sKeepL])

/-- `s_mp_sub(a, b, b)` after `b->sign := s`. -/
theorem subB (h : TB m M sp pa adp pb bdp a b ra) (hge : b.used ≤ a.used) (hroom : a.used ≤ b.alloc)
    (s : Nat) (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg) :
    Triple (At 0x80004564#64 (MpSub.entry1 ra s0 v.s.s1 sp pa pb pb) (writeLog M [(pb + 8, 4, BitVec.ofNat 64 s)])
        v.keepR1 outp)
      (RetQ m v outp sp ρ wsB pb bdp ra s0 (SSubPost a b (b.withSign s))) := by
  have hx := h.after s (sign_lt hs); have := h.base.sp_ge; have hrs := h.base.rs
  have hsub := sub_id (F := 48) (F' := 64) (sp := sp) (pa := pa) (adp := adp) (pb := pb) (bdp := bdp)
    (a := a) (b := b) (a' := a) (b' := b.withSign s) (by decide) (by omega) rfl rfl
  have hpre : SSubAlias.PreCB (writeLog M [(pb + 8, 4, BitVec.ofNat 64 s)]) sp pa adp pb bdp a (b.withSign s) ra :=
    { h.base with
      ra_ := hx.ro, rb := hx.rd, img := hx.img, sa := h.sa, sb := shape_sign h.sb s, bsign := hs
      rs := ⟨by have := hrs.lo_ge; omega, by have := hrs.hi_le; omega, by have := hrs.off; omega⟩
      sp_ge := by omega, ge := hge, room := hroom, lay := h.lay.pull id _ BinA.all hsub }
  refine Triple.dimap (fun cf h => ?_)
    (fun cf ⟨b', M', hat, hpost⟩ => ⟨b', M', hat, hpost.repr, hpost.ssub.unsign_b,
      (hx.fr.trans (Frm.push id hsub hpost.frame)).mono⟩)
    (SSub.correctCB hpre)
  exact h.reshape (by simp [Fn.SSub.entryL, MpSub.entry1, Abi.keepR1])
    (by simp [MpSub.entry1, Abi.keepR1, Abi.keepR, sKeepL])

/-- `s_mp_sub(b, a, b)` after `b->sign := s`: `SSubAlias.StatementCA` with
the operands exchanged. -/
theorem subAB (h : TB m M sp pa adp pb bdp a b ra) (hge : a.used ≤ b.used) (s : Nat)
    (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg) :
    Triple (At 0x80004564#64 (MpSub.entry1 ra s0 v.s.s1 sp pb pa pb) (writeLog M [(pb + 8, 4, BitVec.ofNat 64 s)])
        v.keepR1 outp)
      (RetQ m v outp sp ρ wsB pb bdp ra s0 (SSubPost b a (b.withSign s))) := by
  have hx := h.after s (sign_lt hs); have := h.base.sp_ge; have hrs := h.base.rs
  have hsub := sub_swap (F := 48) (F' := 64) (sp := sp) (pa := pa) (adp := adp) (pb := pb) (bdp := bdp)
    (a := a) (b := b) (a' := a) (b' := b.withSign s) (by decide) (by omega) rfl rfl
  have hpre : SSubAlias.PreCA (writeLog M [(pb + 8, 4, BitVec.ofNat 64 s)]) sp pb bdp pa adp (b.withSign s) a ra :=
    { ra_ := hx.rd, rb := hx.ro, ga := h.base.gb, gb := h.base.ga, img := hx.img
      rs := ⟨by have := hrs.lo_ge; omega, by have := hrs.hi_le; omega, by have := hrs.off; omega⟩
      sp_al := h.base.sp_al, sp_ge := by omega, ra_al := h.base.ra_al
      sa := shape_sign h.sb s, sb := h.sa, asign := hs, ge := hge
      lay := h.lay.pull swap _ BinA.all hsub }
  refine Triple.dimap (fun cf h => ?_)
    (fun cf ⟨b', M', hat, hpost⟩ => ⟨b', M', hat, hpost.repr, hpost.ssub.unsign_a,
      (hx.fr.trans (Frm.push swap hsub hpost.frame)).mono⟩)
    (SSub.correctCA hpre)
  exact h.reshape (by simp [Fn.SSub.entryL, MpSub.entry1, Abi.keepR1])
    (by simp [MpSub.entry1, Abi.keepR1, Abi.keepR, sKeepL])

end

end Tom.Machine.Fn.BinATail
