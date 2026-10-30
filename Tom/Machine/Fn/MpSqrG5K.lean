import Tom.Machine.Api.MpSqrI
import Tom.Machine.Api.Std_r6h
import Tom.Machine.Kit.Run
import Tom.Machine.Kit.ResFrom
import Tom.Spec.MpSqrStep

/-!
# `mp_sqr`'s assembly: the hypotheses bundle and the callees' residues

The generated assemblies (`Fn/MpSqrMainG.lean`, `Fn/MpSqrAMainG.lean`, annotations
`msqr.asm.json`, `msqra.asm.json`, style `"pre"`: the stack depth `2224 + 8 a->used` is not a
literal) run over the contract's regions with the hypotheses bundled (`GPre`, `GPreA`): the
contract's, the induction hypothesis and the algorithms' Statements (named premises).
-/

namespace Tom.Machine.Fn.MpSqrG5K

open Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

/-! ## `mp_sqr(a, b)` -/

section
open Tom.Machine.Api.MpSqr (P lay kind isW hin)

/-- The contract's kinds, with the memory argument the generator passes. -/
abbrev kindG (p : P) (_ : Mem) : MpSqr.R → Kind := kind p

/-- The contract's hypotheses, the induction hypothesis and the algorithms' Statements. -/
structure GPre (p : P) (m : Mem) (ra : BitVec 64) : Prop where
  ra4 : ra.toNat % 4 = 0
  res : SqrRec.ResI p
  lay : Sound (MpSqr.lay p) isW
  bund : Bundle (MpSqr.lay p) (kind p) m
  heap : AHeap m (hin p)
  off : ∀ r, Off (MpSqr.lay p r) (hin p)
  hK : KSqr.Statement
  hT : ToomSqr.Statement

/-- The algorithms' common residue at the callee's stack pointer `sp - 16`. -/
theorem algBase {p : P} (h : MpSqr.Res p) :
    SqrAlg.Base ⟨p.sp - 16, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩ := by
  res_from [MpSqr.F, MpSqr.Fs, SqrAlg.F, SqrAlg.Fa] h

/-- `s_mp_sqr_fast(a, b)`'s residue below the karatsuba cut-off. -/
theorem fastRes {p : P} (h : MpSqr.Res p) (hu : p.a.used < 120) :
    SqrFastRes ⟨p.sp - 16, p.pa, p.adp, p.pb, p.bdp, p.a, p.b⟩ := by
  res_from [MpSqr.F, MpSqr.Fs, heapEnd] h

end

/-! ## `mp_sqr(a, a)` -/

section
open Tom.Machine.Api.MpSqrA (P lay kind isW hin)

abbrev kindGA (p : P) (_ : Mem) : MpSqrA.R → Kind := kind p

structure GPreA (p : P) (m : Mem) (ra : BitVec 64) : Prop where
  ra4 : ra.toNat % 4 = 0
  res : SqrRec.AResI p
  lay : Sound (MpSqrA.lay p) isW
  bund : Bundle (MpSqrA.lay p) (kind p) m
  heap : AHeap m (hin p)
  off : ∀ r, Off (MpSqrA.lay p r) (hin p)
  hK : KSqr.StatementA
  hT : ToomSqr.StatementA

theorem algBaseA {p : P} (h : MpSqrA.Res p) :
    SqrAlg.BaseA ⟨p.sp - 16, p.pa, p.adp, p.a, p.H⟩ := by
  res_from [MpSqrA.F, MpSqr.Fs, SqrAlg.FA, SqrAlg.Fa] h

theorem fastResA {p : P} (h : MpSqrA.Res p) (hu : p.a.used < 120) :
    SqrFastARes ⟨p.sp - 16, p.pa, p.adp, p.a⟩ := by
  res_from [MpSqrA.F, MpSqr.Fs, heapEnd] h

end

end Tom.Machine.Fn.MpSqrG5K
