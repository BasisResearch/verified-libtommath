import Tom.Machine.Fn.SSubStmt
import Tom.Machine.Fn.SSubDst

/-!
# `s_mp_sub` on the machine: the whole function

`correct_Statement` (`c` distinct from `a` and `b`) as an instance of the
assembly for every destination, `Fn.SSub.AnyDst.correct` (`SSubDst.lean`):
both operands are `Dst.Src.own`, kept by `Frm.keep` in the regions `R`
(placed by `lay`; the written ones, `fr`, `cS`, `cD`, disjoint from every
other by `sound`, once, from `Pre.lay`) through the kernel's frame pushed by
`kR`.
-/

namespace Tom.Machine.Fn.SSub

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

/-! ## Regions -/

/-- `s_mp_sub`'s regions: its stack frame, the three structs and digit
arrays, the three functions' code. -/
inductive R | fr | cS | cD | aS | aD | bS | bD | code | ms | cl
  deriving DecidableEq

/-- The regions it writes. -/
def isW : R → Bool
  | .fr | .cS | .cD => true
  | _ => false

/-- Their placement. -/
def lay (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt) : R → Iv
  | .fr => ⟨sp - 48, 48⟩
  | .cS => ⟨pc, 24⟩
  | .cD => ⟨cdp, 4 * c.alloc⟩
  | .aS => ⟨pa, 24⟩
  | .aD => ⟨adp, 4 * a.alloc⟩
  | .bS => ⟨pb, 24⟩
  | .bD => ⟨bdp, 4 * b.alloc⟩
  | .code => ⟨sMpSubBase, 380⟩
  | .ms => ⟨memsetBase, 220⟩
  | .cl => ⟨mpClampBase, 64⟩

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat} {a b c : MpInt}
  {ra s0 : BitVec 64}

/-- **Disjointness, once**: from `Pre.lay` and `c`'s geometry. -/
theorem sound (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Sound (lay sp pa adp pb bdp pc cdp a b c) isW := by
  have hg : Disj pc 24 cdp (4 * c.alloc) := hP.gc.disj
  have L := hP.lay
  cases L
  sound_cases

end

/-- The kernel's regions are ours. -/
def kR : Tom.Machine.Dst.K → R
  | .fr => .fr | .cS => .cS | .cD => .cD | .code => .code | .ms => .ms | .cl => .cl

/-- **`s_mp_sub` on the machine** (H1). -/
theorem correct : correct_Statement := by
  intro m v outp sp pa adp pb bdp pc cdp a b c ra s0 hP
  have hS := sound hP
  have hsub : ∀ k, (AnyDst.lay sp pc cdp c k).Sub (lay sp pa adp pb bdp pc cdp a b c (kR k)) := by
    intro k; cases k <;> exact Iv.sub_self _
  have hP' : AnyDst.Pre m sp pa adp pb bdp pc cdp a b c ra :=
    { hP with
      srcA := .own (fun M hF => (Frm.push kR hsub hF).keep hS
          (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_)
        (hS.disj (r := R.aS) (s := R.fr)) (hS.disj (r := R.aS) (s := R.cS))
      srcB := .own (fun M hF => (Frm.push kR hsub hF).keep hS
          (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _)) hP.rb)
        (hS.disj (r := R.bS) (s := R.fr)) (hS.disj (r := R.bS) (s := R.cS))
      lay := hS.pull kR _ Tom.Machine.Dst.all hsub }
  exact Triple.rmap (fun _ ⟨c', M, hat, hpost⟩ => ⟨c', M, hat,
      { repr := hpost.repr, ssub := hpost.ssub
        frame := (Frm.push kR hsub hpost.frame).clause fun x hx => by
          have := hP.sp_ge
          simp only [InAny, Iv.In, lay, InW, Tom.Machine.Dst.ws, List.map, kR, or_false] at hx ⊢; omega }⟩)
    (AnyDst.correct hP')

end Tom.Machine.Fn.SSub
