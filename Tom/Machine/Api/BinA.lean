import Tom.Machine.Api.Bin
import Tom.Machine.Kit.Dst

/-!
# Standard contracts: the regions of an in-place binary operation

`op(a, b, a)` (`c = a`) and `op(a, b, b)` (`c = b`): as `Api/Bin.lean`, the
stack `[sp - F, sp)`, the structs and digit arrays of `a` and `b`, the code;
the destination's struct and digits are the operand's. Written: the stack
and `a` (`isWA`, `wsA`), or the stack and `b` (`isWB`, `wsB`).

The destination kernel of an in-place routine (`Kit/Dst.lean`) sits inside
these regions by the renamings `kA` (`c = a`) and `kB` (`c = b`): its frame
inside the stack, `c` onto the operand, all code onto the text section
(`sub_kA`, `sub_kB`). The other operand is a `Dst.Src.own` (`src_ownB`,
`src_ownA`), kept by `Frm.keep` through the kernel's frame pushed into
these names.
-/

namespace Tom.Machine.Api.BinA

open Tom.Machine Tom.Machine.Code
open Tom.Machine.Dst (K)

inductive R | stk | aS | aD | bS | bD | code
  deriving DecidableEq

/-- `c = a`: the stack and `a` written. -/
def isWA : R → Bool
  | .stk | .aS | .aD => true
  | _ => false

/-- `c = b`: the stack and `b` written. -/
def isWB : R → Bool
  | .stk | .bS | .bD => true
  | _ => false

/-- The placement, for a stack depth `F`. -/
def lay (F sp pa adp pb bdp : Nat) (a b : MpInt) : R → Iv
  | .stk => ⟨sp - F, F⟩
  | .aS => ⟨pa, 24⟩
  | .aD => ⟨adp, 4 * a.alloc⟩
  | .bS => ⟨pb, 24⟩
  | .bD => ⟨bdp, 4 * b.alloc⟩
  | .code => textIv

def wsA : List R := [.stk, .aS, .aD]
def wsB : List R := [.stk, .bS, .bD]

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .code] := by cases r <;> simp

/-- `a` and `b` exchanged: `op(b, a, a)` in the names of `op(a, b, a)`'s `isWB`
form, and back. -/
def swap : R → R
  | .aS => .bS | .aD => .bD | .bS => .aS | .bD => .aD | r => r

/-- A callee's placement with the operands exchanged (and the destination's
sign changed), inside ours. -/
theorem sub_swap {F F' sp pa adp pb bdp : Nat} {a b a' b' : MpInt} (hF : F ≤ F') (hs : F' ≤ sp)
    (ha : a'.alloc = a.alloc) (hb : b'.alloc = b.alloc) :
    ∀ k, (lay F sp pb bdp pa adp b' a' k).Sub (lay F' sp pa adp pb bdp a b (swap k)) := by
  intro k; cases k <;> simp only [Iv.Sub, lay, swap, ha, hb] <;> omega

/-- A callee's placement (the destination's sign changed), inside ours. -/
theorem sub_id {F F' sp pa adp pb bdp : Nat} {a b a' b' : MpInt} (hF : F ≤ F') (hs : F' ≤ sp)
    (ha : a'.alloc = a.alloc) (hb : b'.alloc = b.alloc) :
    ∀ k, (lay F sp pa adp pb bdp a' b' k).Sub (lay F' sp pa adp pb bdp a b (id k)) := by
  intro k; cases k <;> simp only [Iv.Sub, lay, id, ha, hb] <;> omega

/-- What every in-place contract needs (stack depth `F`): the operands in
memory, the stack, the code. -/
structure Base (m : Mem) (F sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  rs : Ram (sp - F) F
  sp_al : sp % 16 = 0
  sp_ge : F ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m

/-! ## The destination kernel inside -/

/-- The kernel of `op(a, b, a)`. -/
def kA : K → R
  | .fr => .stk | .cS => .aS | .cD => .aD | _ => .code

/-- The kernel of `op(a, b, b)`. -/
def kB : K → R
  | .fr => .stk | .cS => .bS | .cD => .bD | _ => .code

section
variable {F F' sp pa adp pb bdp : Nat} {a b : MpInt} {code : Iv}

theorem sub_kA (hF : F ≤ F') (hs : F' ≤ sp) (hc : code.Sub textIv) :
    ∀ k, (Dst.lay F sp pa adp a code k).Sub (lay F' sp pa adp pb bdp a b (kA k)) := by
  intro k
  cases k
  · simp only [Iv.Sub, Dst.lay, lay, kA]; omega
  · exact Iv.sub_self _
  · exact Iv.sub_self _
  · exact hc
  · exact Bin.sub_text
  · exact Bin.sub_text

theorem sub_kB (hF : F ≤ F') (hs : F' ≤ sp) (hc : code.Sub textIv) :
    ∀ k, (Dst.lay F sp pb bdp b code k).Sub (lay F' sp pa adp pb bdp a b (kB k)) := by
  intro k
  cases k
  · simp only [Iv.Sub, Dst.lay, lay, kB]; omega
  · exact Iv.sub_self _
  · exact Iv.sub_self _
  · exact hc
  · exact Bin.sub_text
  · exact Bin.sub_text

/-- `c = a`: `b` is its own operand, kept through the kernel's frame. -/
theorem src_ownB {m : Mem} (hS : Sound (lay F' sp pa adp pb bdp a b) isWA)
    (hsub : ∀ k, (Dst.lay F sp pa adp a code k).Sub (lay F' sp pa adp pb bdp a b (kA k)))
    (hb : MpAt m pb bdp b) : Dst.Src (Dst.lay F sp pa adp a code) m pa adp a pb bdp b :=
  .own (fun M hF => (Frm.push kA hsub hF).keep hS
      (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _)) hb)
    (hS.sub (r := R.bS) (s := R.stk) (Iv.sub_self _) (hsub .fr))
    (hS.disj (r := R.bS) (s := R.aS))

/-- `c = b`: `a` is its own operand, kept through the kernel's frame. -/
theorem src_ownA {m : Mem} (hS : Sound (lay F' sp pa adp pb bdp a b) isWB)
    (hsub : ∀ k, (Dst.lay F sp pb bdp b code k).Sub (lay F' sp pa adp pb bdp a b (kB k)))
    (ha : MpAt m pa adp a) : Dst.Src (Dst.lay F sp pb bdp b code) m pb bdp b pa adp a :=
  .own (fun M hF => (Frm.push kB hsub hF).keep hS
      (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) ha)
    (hS.sub (r := R.aS) (s := R.stk) (Iv.sub_self _) (hsub .fr))
    (hS.disj (r := R.aS) (s := R.bS))

end

end Tom.Machine.Api.BinA
