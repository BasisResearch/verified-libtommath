import Tom.Machine.Kit.UnTail

/-!
# The tail of `mp_add_d(a, b, a)`-like functions

`Kit/DTail.lean` for `Un`'s regions (the operand written in place):
`Saved2`, `Tail2`, `Snap2` and their rules over the names `aS`, `aD`.
-/

namespace Tom.Machine.Api.Un

open Vsa.Sim Tom.Machine Tom.Machine.Code

/-- `ra`, `s0` saved at `sp - 8`, `sp - 16`. -/
structure Saved2 (M : Mem) (ra s0 : BitVec 64) (sp : Nat) : Prop where
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0

theorem Saved2.keep {F sp pb bdp : Nat} {b : MpInt} {M M' : Mem} {ws' : List R} {ra s0 : BitVec 64}
    (hS : Sound (lay F sp pb bdp b) isW) (hF : 16 ≤ F) (hsp : F ≤ sp) (h : Saved2 M ra s0 sp)
    (hFr : Frm (lay F sp pb bdp b) ws' M M') (hm : Misses isW [R.stk] ws' = true := by decide) :
    Saved2 M' ra s0 sp :=
  { ra_v := hFr.keep hS (Reads.w8 (r := R.stk) (by simp only [Iv.Sub, lay]; omega)) h.ra_v hm
    s0_v := hFr.keep hS (Reads.w8 (r := R.stk) (by simp only [Iv.Sub, lay]; omega)) h.s0_v hm }

/-- After a digit loop: memory changed only in `ws` since `m`, the saved
registers, `b`'s struct with `used = n`, its digits `f`. -/
structure Tail2 (ρ : R → Iv) (m M : Mem) (ra s0 : BitVec 64) (sp pb bdp n al sg : Nat) (f : Nat → Nat) :
    Prop where
  fr : Frm ρ ws m M
  sv : Saved2 M ra s0 sp
  hdr : HdrAt M pb bdp n al sg
  arr : ArrAt M bdp al f

/-- After the prologue: memory changed only in the stack and `b`'s struct
since `m`, the saved registers, `b`'s struct with `used = ua`, its digits `f`. -/
structure Snap2 (ρ : R → Iv) (m M : Mem) (ra s0 : BitVec 64) (sp pb bdp ua al sg : Nat) (f : Nat → Nat) :
    Prop where
  fr : Frm ρ [R.stk, R.aS] m M
  sv : Saved2 M ra s0 sp
  hdr : HdrAt M pb bdp ua al sg
  arr : ArrAt M bdp al f

/-- A digit loop's join point (changes only in `b`'s digits since the snapshot) as a `Tail2`. -/
theorem Snap2.tail {F sp pb bdp : Nat} {b : MpInt} {m m2 M : Mem} {ra s0 : BitVec 64}
    {ua sg : Nat} {f f' : Nat → Nat} (hS : Sound (lay F sp pb bdp b) isW) (hF : 16 ≤ F) (hsp : F ≤ sp)
    (hsn : Snap2 (lay F sp pb bdp b) m m2 ra s0 sp pb bdp ua b.alloc sg f)
    (hI : ArrFrm (lay F sp pb bdp b) R.aD m2 M bdp b.alloc f') :
    Tail2 (lay F sp pb bdp b) m M ra s0 sp pb bdp ua b.alloc sg f' :=
  { fr := (hsn.fr.trans hI.fr).mono
    sv := hsn.sv.keep hS hF hsp hI.fr
    hdr := hI.fr.keep hS (HdrAt.reads (r := R.aS) (Iv.sub_self _)) hsn.hdr
    arr := hI.arr }

/-- `memset(b->dp + n, 0, 4 (k - n))`: the digits `[n, k)` become zero. -/
theorem Tail2.fill {F sp pb bdp : Nat} {b : MpInt} {m M M' : Mem} {ra s0 : BitVec 64}
    {n k sg : Nat} {g old : Nat → Nat} (hS : Sound (lay F sp pb bdp b) isW) (hF : 16 ≤ F) (hsp : F ≤ sp)
    (hT : Tail2 (lay F sp pb bdp b) m M ra s0 sp pb bdp n b.alloc sg (ovl g old n))
    (hnk : n ≤ k) (hk : k ≤ b.alloc) (hpost : Fn.Memset.Post M (bdp + 4 * n) (4 * (k - n)) 0#8 M')
    (hg : ∀ j, n ≤ j → j < k → g j = 0) :
    Tail2 (lay F sp pb bdp b) m M' ra s0 sp pb bdp n b.alloc sg (ovl g old k) :=
  have hA := (ArrFrm.init (w := R.aD) (Iv.sub_self _) hT.arr :
    ArrFrm (lay F sp pb bdp b) R.aD M M bdp b.alloc (ovl g old n)).fill hnk hk hpost.fill hpost.frame hg
  { fr := Frm.step hT.fr hA.fr
    sv := hT.sv.keep hS hF hsp hA.fr
    hdr := hA.fr.keep hS (HdrAt.reads (r := R.aS) (Iv.sub_self _)) hT.hdr
    arr := hA.arr }

theorem Tail2.congr {ρ : R → Iv} {m M : Mem} {ra s0 : BitVec 64} {sp pb bdp n al sg : Nat} {f f' : Nat → Nat}
    (hT : Tail2 ρ m M ra s0 sp pb bdp n al sg f) (h : ∀ j, j < al → f j = f' j) :
    Tail2 ρ m M ra s0 sp pb bdp n al sg f' :=
  { hT with arr := hT.arr.congr h }

end Tom.Machine.Api.Un
