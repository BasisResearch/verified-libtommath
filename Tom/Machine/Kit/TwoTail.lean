import Tom.Machine.Api.Two
import Tom.Machine.Kit.Hdr
import Tom.Machine.Fn.Memset

/-!
# The tail of a two-operand function that writes `b`

`mp_mul_2(a, b)`, `mp_div_2(a, b)` and their kin write `b`'s digits in a
loop, then `b`'s struct (`used`, `sign`) and zero `b`'s excess digits by
`memset`. After the loop their state is a `Tail`: memory changed only in
`Two.ws` since the entry, the saved registers, `b`'s struct as an `HdrAt`
and its digits as an `ArrAt`. `Saved` is a frame that keeps `ra`, `s0`,
`s1` at `sp - 8`, `sp - 16`, `sp - 24`; `Saved.keep` and `Tail.keep` carry
them across a change off the stack (`Frm.keep`); `Tail.fill` is the
`memset` of the excess digits (`ArrFrm.fill`).
-/

namespace Tom.Machine.Api.Two

open Vsa.Sim Tom.Machine Tom.Machine.Code

/-- `ra`, `s0`, `s1` saved at `sp - 8`, `sp - 16`, `sp - 24`. -/
structure Saved (M : Mem) (ra s0 s1 : BitVec 64) (sp : Nat) : Prop where
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  s1_v : bytesT8 M (sp - 24) = s1

theorem Saved.keep {F sp pa adp pb bdp : Nat} {a b : MpInt} {M M' : Mem} {ws' : List R} {ra s0 s1 : BitVec 64}
    (hS : Sound (lay F sp pa adp pb bdp a b) isW) (hF : 24 ≤ F) (hsp : F ≤ sp) (h : Saved M ra s0 s1 sp)
    (hFr : Frm (lay F sp pa adp pb bdp a b) ws' M M') (hm : Misses isW [R.stk] ws' = true := by decide) :
    Saved M' ra s0 s1 sp :=
  { ra_v := hFr.keep hS (Reads.w8 (r := R.stk) (by simp only [Iv.Sub, lay]; omega)) h.ra_v hm
    s0_v := hFr.keep hS (Reads.w8 (r := R.stk) (by simp only [Iv.Sub, lay]; omega)) h.s0_v hm
    s1_v := hFr.keep hS (Reads.w8 (r := R.stk) (by simp only [Iv.Sub, lay]; omega)) h.s1_v hm }

/-- After a digit loop: memory changed only in `ws` since `m`, the saved
registers, `b`'s struct with `used = n`, its digits `f`. -/
structure Tail (ρ : R → Iv) (m M : Mem) (ra s0 s1 : BitVec 64) (sp pb bdp n al sg : Nat) (f : Nat → Nat) :
    Prop where
  fr : Frm ρ ws m M
  sv : Saved M ra s0 s1 sp
  hdr : HdrAt M pb bdp n al sg
  arr : ArrAt M bdp al f

/-- After the prologue: memory changed only in the stack and `b`'s struct
since `m`, the saved registers, `b`'s struct with `used = ua`, its digits `f`. -/
structure Snap (ρ : R → Iv) (m M : Mem) (ra s0 s1 : BitVec 64) (sp pb bdp ua al sg : Nat) (f : Nat → Nat) :
    Prop where
  fr : Frm ρ [R.stk, R.bS] m M
  sv : Saved M ra s0 s1 sp
  hdr : HdrAt M pb bdp ua al sg
  arr : ArrAt M bdp al f

/-- A digit loop's join point (changes only in `b`'s digits since the snapshot) as a `Tail`. -/
theorem Snap.tail {F sp pa adp pb bdp : Nat} {a b : MpInt} {m m2 M : Mem} {ra s0 s1 : BitVec 64}
    {ua sg : Nat} {f f' : Nat → Nat} (hS : Sound (lay F sp pa adp pb bdp a b) isW) (hF : 24 ≤ F) (hsp : F ≤ sp)
    (hsn : Snap (lay F sp pa adp pb bdp a b) m m2 ra s0 s1 sp pb bdp ua b.alloc sg f)
    (hI : ArrFrm (lay F sp pa adp pb bdp a b) R.bD m2 M bdp b.alloc f') :
    Tail (lay F sp pa adp pb bdp a b) m M ra s0 s1 sp pb bdp ua b.alloc sg f' :=
  { fr := (hsn.fr.trans hI.fr).mono
    sv := hsn.sv.keep hS hF hsp hI.fr
    hdr := hI.fr.keep hS (HdrAt.reads (r := R.bS) (Iv.sub_self _)) hsn.hdr
    arr := hI.arr }

/-- `memset(b->dp + n, 0, 4 (k - n))`: the digits `[n, k)` become zero. -/
theorem Tail.fill {F sp pa adp pb bdp : Nat} {a b : MpInt} {m M M' : Mem} {ra s0 s1 : BitVec 64}
    {n k sg : Nat} {g old : Nat → Nat} (hS : Sound (lay F sp pa adp pb bdp a b) isW) (hF : 24 ≤ F) (hsp : F ≤ sp)
    (hT : Tail (lay F sp pa adp pb bdp a b) m M ra s0 s1 sp pb bdp n b.alloc sg (ovl g old n))
    (hnk : n ≤ k) (hk : k ≤ b.alloc) (hpost : Fn.Memset.Post M (bdp + 4 * n) (4 * (k - n)) 0#8 M')
    (hg : ∀ j, n ≤ j → j < k → g j = 0) :
    Tail (lay F sp pa adp pb bdp a b) m M' ra s0 s1 sp pb bdp n b.alloc sg (ovl g old k) :=
  have hA := (ArrFrm.init (w := R.bD) (Iv.sub_self _) hT.arr :
    ArrFrm (lay F sp pa adp pb bdp a b) R.bD M M bdp b.alloc (ovl g old n)).fill hnk hk hpost.fill hpost.frame hg
  { fr := Frm.step hT.fr hA.fr
    sv := hT.sv.keep hS hF hsp hA.fr
    hdr := hA.fr.keep hS (HdrAt.reads (r := R.bS) (Iv.sub_self _)) hT.hdr
    arr := hA.arr }

theorem Tail.congr {ρ : R → Iv} {m M : Mem} {ra s0 s1 : BitVec 64} {sp pb bdp n al sg : Nat} {f f' : Nat → Nat}
    (hT : Tail ρ m M ra s0 s1 sp pb bdp n al sg f) (h : ∀ j, j < al → f j = f' j) :
    Tail ρ m M ra s0 s1 sp pb bdp n al sg f' :=
  { hT with arr := hT.arr.congr h }

/-- The text section holds `memset`. -/
theorem memset_sub : Iv.Sub ⟨memsetBase, 4 * memsetCode.length⟩ textIv := ⟨by decide, by decide⟩

/-- `memset`'s precondition for `b`'s digits `[n, k)`. -/
theorem memset_pre {F sp pa adp pb bdp : Nat} {a b : MpInt} {M : Mem} {n k : Nat}
    (hS : Sound (lay F sp pa adp pb bdp a b) isW) (hg : MpGeom pb bdp b.alloc) (himg : Img M)
    (hnk : n ≤ k) (hk : k ≤ b.alloc) : Fn.Memset.Pre M (bdp + 4 * n) 0 (4 * (k - n)) :=
  have hrb : Ram bdp (4 * b.alloc) := by simpa [Layout.sizeofDigit] using hg.ds
  { byte := by decide, code := himg.memset
    ram := ⟨by have := hrb.lo_ge; omega, by have := hrb.hi_le; omega, by have := hrb.off; omega⟩
    code_off := hS.sub (r := R.bD) (s := R.code) (I := ⟨bdp + 4 * n, 4 * (k - n)⟩)
      ⟨by simp [lay], by simp only [lay]; omega⟩ memset_sub }

end Tom.Machine.Api.Two
