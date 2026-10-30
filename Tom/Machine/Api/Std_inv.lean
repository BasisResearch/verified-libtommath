import Tom.Machine.Api.Invmod
import Tom.Machine.Api.CmpD
import Tom.Machine.Api.StdLib
import Tom.Machine.Fn.CmpDMain
import Tom.Machine.Api.Std_r6c
import Tom.Machine.Api.Std_r10aM
import Tom.Machine.Api.Std_t7
import Tom.Machine.Api.Std_multi8
import Tom.Machine.Kit.HeapBlk

/-!
# Callee contracts of `mp_invmod` and its workers

* `cmpDc`: `mp_cmp_d(a, d)` (`Api/CmpD.lean`, `Fn.CmpD.correct`) as a `Contract` over one
  `mp_int` (`Ob`): `a0 = ordNG (cmpD a d)` (the `Nat` the rows compare), nothing written.
* `mpModPos`: `mp_mod(a, b, c)` (`Std.mpModH`) whose `Q` also says `c'`'s digit block is nonempty
  (from its post's heap and `Off`, `Off.pos_blk`): the alloc fact of a temporary `mp_mod` re-places.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-! ## `mp_cmp_d(a, d)` -/

structure CdP where
  p : Nat
  dp : Nat
  a : MpInt
  d : Nat

def cmpDc : Contract where
  P := CdP
  X := Unit
  R := Ob
  all := [.S, .D, .code]
  hall := Ob.all
  entry := CmpD.entry
  args p := [(10, BitVec.ofNat 64 p.p), (11, BitVec.ofNat 64 p.d)]
  rets p ra := [(1, ra), (10, BitVec.ofNat 64 (ordNG (cmpD p.a p.d)))]
  lay p := Ob.lay p.p p.dp p.a.alloc
  kind p := Ob.kind p.p p.dp p.a
  out p _ := Ob.kind p.p p.dp p.a
  isW _ := false
  ws := []
  Res p := p.a.Valid ∧ 1 ≤ p.a.alloc ∧ p.d < radix
  Q _ _ := True
  fits p r := by cases r <;> exact Iv.sub_self _
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB
    obtain ⟨qp, qdp, a, d⟩ := p
    have hpre : CmpD.Pre m qp qdp a d ra :=
      { ra_ := Hdr.mpAt (hB .S).2 (hB .D).2, va := hres.1, ga := Hdr.geom (hB .S).2, alloc_pos := hres.2.1
        db := hres.2.2, ra_al := hra, img := (hB .code).2 }
    have h : Triple (At CmpD.entry (Fn.CmpD.entryL ra qp d) m v.keep outp)
        (fun cf => At ra [(1, ra), (10, BitVec.ofInt 64 (ordCode (cmpD a d)))] m v.keep outp cf) :=
      Fn.CmpD.correct hpre
    rw [ofInt_ordCodeG] at h
    exact Triple.rmap (fun cf hc => ⟨(), m, hc, trivial, hB, Frm.refl _ _⟩) h

/-! ## `mp_mod(a, b, c)` with `c`'s new block nonempty -/

theorem mod_pos {p : Api.MpMod.P} {x : Api.MpMod.Out} {m M : Mem}
    (h : HPost (Api.MpMod.lay p) Api.MpMod.ws .cD (Api.MpMod.out p x) (Api.MpMod.site' p x) (Api.MpMod.hin p)
      (Api.MpMod.hout p x) m M) {q : Nat} {c' : MpInt} (hx : x = .ok q c') : 0 < c'.alloc := by
  subst hx
  exact Off.pos_blk h.off h.heap.heap (List.mem_cons_self ..)

def mpModPos : HContract :=
  { mpModH with
    Q := fun p x => Api.MpMod.Q p x ∧ ∀ q c', x = .ok q c' → 0 < c'.alloc
    spec := by
      intro p m v outp ra hra hres hS hB hH hoff
      exact Triple.rmap (fun _ ⟨x, M, hat, hq, hpo⟩ => ⟨x, M, hat, ⟨hq, fun _ _ hx => mod_pos hpo hx⟩, hpo⟩)
        (mpModH.spec hra hres hS hB hH hoff) }

abbrev mpInitMulti6 : HContractN := mpInitMultiN 6
abbrev mpClearMulti6 : HContractN := mpClearMultiN 6
abbrev mpInitMulti8 : HContractN := mpInitMultiN 8
abbrev mpClearMulti8 : HContractN := mpClearMultiN 8

/-! ## The workers of `mp_invmod`, as allocating contracts -/

structure InvFastRes (p : Invmod.P) : Prop where
  res : InvmodFastG.Res p
  stmt : InvmodFastG.Statement

structure InvSlowRes (p : Invmod.P) : Prop where
  res : InvmodSlowG.Res p
  stmt : InvmodSlowG.Statement

theorem Invmod.pos {p : Invmod.P} (h : Invmod.BaseG p) (r : Invmod.R) :
    0 < (Invmod.lay p r).len ∨ (Invmod.lay p r).base < heapStart ∨ heapEnd ≤ (Invmod.lay p r).base := by
  have := h.apos; have := h.bpos; have := h.cpos
  left
  cases r with
  | code => exact (show 0 < textLen by decide)
  | stk => exact (show 0 < Invmod.F by decide)
  | aS | bS | cS => exact (show 0 < 24 by decide)
  | aD => exact (show 0 < 4 * p.a.alloc by omega)
  | bD => exact (show 0 < 4 * p.b.alloc by omega)
  | cD => exact (show 0 < 4 * p.c.alloc by omega)

theorem Invmod.out_ind (p : Invmod.P) (x : Invmod.Out) (r : Invmod.R) (h : (Invmod.out p x r).isRam = false) :
    (Invmod.out p x r).indep = true := by
  cases x <;> cases r <;> simp_all [Invmod.out, Invmod.kind, Kind.isRam, Kind.indep]

def invmodFastH : HContract where
  P := Invmod.P
  X := Invmod.Out
  R := Invmod.R
  all := [.stk, .aS, .aD, .bS, .bD, .cS, .cD, .code]
  hall := Invmod.all
  entry := InvmodFast.entry
  args := Invmod.args
  rets := Invmod.rets
  lay := Invmod.lay
  kind := Invmod.kind
  out := Invmod.out
  isW := Invmod.isW
  ws := Invmod.ws
  site := .cD
  site' := Invmod.site'
  hin := Invmod.hin
  hout := Invmod.hout
  Res := InvFastRes
  Q := InvmodFast.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r _ _ h := Invmod.out_ind p x r h
  pos p h := Invmod.pos h.res.toBaseG
  spec := fun hra hres => hres.stmt hra hres.res

def invmodSlowH : HContract where
  P := Invmod.P
  X := Invmod.Out
  R := Invmod.R
  all := [.stk, .aS, .aD, .bS, .bD, .cS, .cD, .code]
  hall := Invmod.all
  entry := InvmodSlow.entry
  args := Invmod.args
  rets := Invmod.rets
  lay := Invmod.lay
  kind := Invmod.kind
  out := Invmod.out
  isW := Invmod.isW
  ws := Invmod.ws
  site := .cD
  site' := Invmod.site'
  hin := Invmod.hin
  hout := Invmod.hout
  Res := InvSlowRes
  Q := InvmodSlow.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r _ _ h := Invmod.out_ind p x r h
  pos p h := Invmod.pos h.res.toBaseG
  spec := fun hra hres => hres.stmt hra hres.res

end Tom.Machine.Std
