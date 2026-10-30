import Tom.Machine.Api.BalMul
import Tom.Machine.Api.MulAlgA
import Tom.Machine.Fn.KMulG5K
import Tom.Machine.Api.Std_t7
import Tom.Machine.Kit.StructCopy
import Tom.Machine.Api.Std_multi8
import Tom.Machine.Kit.AnnFacts
import Tom.Machine.Fn.BalMulG
import Tom.Spec.BalMulStep

/-!
# `s_mp_balance_mul`'s assembly: the callees it needs beyond the library's

* `Std.mpMulBUK`: `mp_mul(a, b, c)` below a bound with operands only `ValidU`
  (`Api.MpMul.ResU`, `Api.MulRec.MulBelow.mulU`): `a0` is a slice with stale digits above its
  `used` and, nested, the shorter operand `B` may be one;
* `Std.clampU`: `mp_clamp` of an `mp_int` with stale digits (`Fn.Clamp.correctU`), the left-over
  slice's;
* `outKeepB`: `c` as it was, the `MP_MEM` exits.
-/

namespace Tom.Machine.Fn.BalMulG5K

open Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Fn.KMulG5K

/-! ## `mp_mul` over `ValidU` operands, below a bound -/

/-- `mp_mul`'s residue over `ValidU` operands, the bound and the hypothesis. -/
structure MulBURes (p : MulBP) : Prop where
  res : MpMul.ResU p.toP
  lt : MpMul.μ p.a p.b < p.n
  ih : MulRec.MulBelow p.n

theorem mpMulU_pos (p : MpMul.P) (h : MpMul.ResU p) (r : MpMul.R) :
    0 < (MpMul.lay p r).len ∨ (MpMul.lay p r).base < heapStart ∨ heapEnd ≤ (MpMul.lay p r).base := by
  cases r with
  | stk => exact .inl (by simp only [MpMul.lay]; omega)
  | aS | bS | cS | kc | tc => exact .inl (by simp [MpMul.lay])
  | aD => exact .inl (show 0 < 4 * p.a.alloc by have := h.apos; omega)
  | bD => exact .inl (show 0 < 4 * p.b.alloc by have := h.bpos; omega)
  | cD => exact .inl (show 0 < 4 * p.c.alloc by have := h.cpos; omega)
  | code => exact .inl (show 0 < textLen by decide)

/-- `Std.mpMulBK` with `ValidU` operands. -/
def _root_.Tom.Machine.Std.mpMulBUK : HContract :=
  { Std.mpMulBK with
    Res := fun p => MulBURes p.toB
    pos := fun p h r => mpMulU_pos p.toB.toP h.res r
    spec := fun hra hres => hres.ih.mulU hres.lt hra hres.res }

/-- `Std.mpMulBUK`'s residue from its fields: the call's parameter record is matched constructor by
constructor (the residue's projections through `MulBKP.toB`/`MulBP.toP` would otherwise be unfolded
against the caller's operands, e.g. `p.b` against `z.p.b`, by structure eta). -/
theorem mulBURes_mk {sp pa adp pb bdp pc cdp : Nat} {a b c : MpInt} {H : List (Nat × Nat)} {n kc tc : Nat}
    (stk : StkRes sp (MpMul.Fm (a.used + b.used))) (va : a.ValidU) (vb : b.ValidU) (sc : c.Shape)
    (csign : c.sign = Layout.mpZpos ∨ c.sign = Layout.mpNeg) (uab : a.used + b.used < 2 ^ 30)
    (apos : 0 < a.alloc) (bpos : 0 < b.alloc) (cpos : 0 < c.alloc)
    (aoff : OffHeap pa 24) (boff : OffHeap pb 24) (coff : OffHeap pc 24)
    (lt : a.used + b.used < n) (ih : MulRec.MulBelow n) :
    Std.mpMulBUK.Res ⟨sp, pa, adp, pb, bdp, pc, cdp, a, b, c, H, n, kc, tc⟩ :=
  ⟨⟨stk, va, vb, sc, csign, uab, apos, bpos, cpos, aoff, boff, coff⟩, lt, ih⟩

/-! ## `mp_clamp` of an `mp_int` with stale digits -/

def _root_.Tom.Machine.Std.clampU : Contract :=
  { Std.clamp with
    Res := fun p => p.a.ShapeU
    spec := by
      intro p m v outp ra hra hres hS hB
      obtain ⟨qp, qdp, qa⟩ := p
      have hco := hS.sub (r := Ob.S) (s := Ob.code) (Iv.sub_self _)
        (show Iv.Sub ⟨mpClampBase, 64⟩ textIv from ⟨by decide, by decide⟩) (by decide)
      have hpre : Fn.Clamp.PreU m qp qdp qa :=
        { repr := Hdr.mpAt (hB .S).2 (hB .D).2, shape := hres, geom := Hdr.geom (hB .S).2
          code := Img.mpClamp (hB .code).2, code_off := hco }
      refine Triple.rmap (fun cf ⟨a', M, hat, hpost⟩ => ?_) (Fn.Clamp.correctU ra v outp qp qdp qa m hra hpre)
      have hF : Frm (Ob.lay qp qdp qa.alloc) [Ob.S] m M :=
        Frm.call (w := Ob.S) hpost.frame (by simp only [Iv.Sub, Ob.lay]; omega)
      refine ⟨a', M, hat.sub rfl rfl, hpost.clamp, ?_, hF⟩
      intro r; cases r
      · exact witS hpost.repr (Hdr.geom (hB .S).2) hpost.clamp.alloc (Iv.sub_self _)
      · exact hB.keep hS hF Ob.D
      · exact hB.keep hS hF Ob.code }

/-! ## `mp_init_multi` with its placements: the accumulator's block is fresh -/

/-- `HContractN` with its sites' placements in `Q` (as `HContract.withPlace`). -/
def _root_.Tom.Machine.HContractN.withPlace (C : HContractN) : HContractN :=
  { C with
    Q := fun p x => C.Q p x ∧ ∀ s, s ∈ C.sites → PlaceM (C.hin p) (C.lay p s) (C.site' p x s)
    spec := fun hra hres hS hB hH hoff => Triple.rmap
      (fun _ ⟨x, M, hat, hq, hpo⟩ => ⟨x, M, hat, ⟨hq, hpo.place⟩, hpo⟩) (C.spec hra hres hS hB hH hoff) }

/-- `mp_init_multi(p, q, NULL)` with the blocks' placements. -/
abbrev _root_.Tom.Machine.Std.mpInitMulti2P : HContractN := (Std.mpInitMultiN 2).withPlace

/-- A block `mp_init_multi` placed (off every block before, a live block after) is fresh. -/
theorem fresh_of_placeM {H Hn : List (Nat × Nat)} {M : Mem} {q n : Nat} (hp : PlaceM H Iv.nil ⟨q, n⟩)
    (hn : 0 < n) (hh : Heap M Hn) (hm : (q, n) ∈ Hn) : Fresh H q n := by
  cases hp with
  | place h =>
    cases h with
    | nil => simp [Iv.nil] at hn
    | keep => simp [Iv.nil] at hn
    | fresh hf _ => exact hf
    | regrow hf _ hH =>
      subst hH
      refine { hf with disj := fun e he a ha hb => ?_ }
      rcases List.mem_cons.1 he with rfl | he
      · simp [InBlk, Iv.nil] at hb; omega
      · exact hf.disj e he a ha hb
  | foot hn' hlo hhi hd =>
    have eS : heapStart = 0x80019d10 := rfl
    exact ⟨by simp only at hlo; omega, Heap.al16 hh hm, hlo, hhi, fun e he a ha hb => hd e he a ha hb⟩

/-- The two- and three-struct calls' residues, index by index. -/
theorem al2 {a b : Nat} (ha : a % 8 = 0) (hb : b % 8 = 0) : ∀ i : Fin 2, [a, b].getD i 0 % 8 = 0
  | ⟨0, _⟩ => ha
  | ⟨1, _⟩ => hb

theorem off2 {a b : Nat} (ha : OffHeap a 24) (hb : OffHeap b 24) : ∀ i : Fin 2, OffHeap ([a, b].getD i 0) 24
  | ⟨0, _⟩ => ha
  | ⟨1, _⟩ => hb

/-! ## The struct copy `B = *b` -/

theorem copy_geom {M : Mem} {p q dp : Nat} {a : MpInt} (h : Hdr M p dp a) (hq : Ram q 24) (hal : q % 8 = 0)
    (hd : q + 24 ≤ dp ∨ dp + 4 * a.alloc ≤ q) : MpGeom q dp a.alloc :=
  ⟨by simpa [Layout.sizeofMpInt] using hq, hal, h.geom.ds, h.geom.ds_al, by simpa [Layout.sizeofMpInt, Layout.sizeofDigit] using hd⟩

/-! ## `mp_clear_multi(&a0, &tmp, &r, NULL)`: the heap in the arguments' order -/

/-- The live blocks `tmp r a0` (front first) as `a0 tmp r` (`MP_MEM`). -/
theorem perm_xe {α : Type} (a b c : α) (l : List α) : List.Perm (a :: b :: c :: l) (c :: a :: b :: l) :=
  ((List.Perm.swap c b l).cons a).trans (List.Perm.swap c a (b :: l))

/-- After `mp_exch(&r, c)`: `tmp r a0 c` as `a0 tmp c r` (the old `c` in `r`'s struct, freed). -/
theorem perm_xo {α : Type} (a b c d : α) (l : List α) :
    List.Perm (a :: b :: c :: d :: l) (c :: a :: d :: b :: l) :=
  ((List.Perm.swap c b (d :: l)).cons a).trans
    ((List.Perm.swap c a (b :: d :: l)).trans (((List.Perm.swap d b l).cons a).cons c))

/-! ## The `MP_MEM` exits: the destination as it was -/

theorem outKeepB {p : MpMul.P} (h : BalMul.Res p) : MulAlg.Q p (false, p.cdp, p.c) :=
  ⟨h.sc, h.cpos, (fun e => nomatch e), (fun e => nomatch e)⟩

theorem outKeepBA {p : MpMulA.P} (h : BalMulA.Res p) : MulAlgA.Q p (false, p.adp, p.a) :=
  ⟨h.va.toShape, h.apos, (fun e => nomatch e), (fun e => nomatch e)⟩

end Tom.Machine.Fn.BalMulG5K
