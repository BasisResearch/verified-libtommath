import Tom.Machine.Api.MulRec
import Tom.Machine.Api.KMul
import Tom.Machine.Api.BalMul
import Tom.Machine.Api.ToomMul
import Tom.Machine.Api.MulFastH
import Tom.Machine.Fn.SMpMulDigsMainG

/-!
# Callee contracts of the multiplication group

* `mpMulB`: `mp_mul(a, b, c)` (`Api/MpMul.lean`) for a caller holding the induction
  hypothesis `MulBelow n` (`Api/MulRec.lean`) with `μ(a, b) < n`: its residue is
  `MpMul.Res`, the bound and the hypothesis, and its `spec` is the hypothesis.
* `mpMulAB`: `mp_mul(a, b, a)` likewise.

The parameters are `MpMul.P`'s (`MpMulA.P`'s) fields and the bound `n`, flat (the
generator's anonymous constructor).
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap
open Tom.Machine.Api.MulRec

/-! ## `mp_mul(a, b, c)` below a bound -/

structure MulBP where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  pc : Nat
  cdp : Nat
  a : MpInt
  b : MpInt
  c : MpInt
  H : List (Nat × Nat)
  n : Nat

def MulBP.toP (p : MulBP) : MpMul.P := ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.pc, p.cdp, p.a, p.b, p.c, p.H⟩

/-- `mp_mul`'s residue, the bound and the hypothesis. -/
structure MulBRes (p : MulBP) : Prop where
  res : MpMul.Res p.toP
  lt : MpMul.μ p.a p.b < p.n
  ih : MulBelow p.n

theorem mpMul_pos (p : MpMul.P) (h : MpMul.Res p) (r : MpMul.R) :
    0 < (MpMul.lay p r).len ∨ (MpMul.lay p r).base < heapStart ∨ heapEnd ≤ (MpMul.lay p r).base := by
  cases r with
  | stk => exact .inl (by simp only [MpMul.lay]; omega)
  | aS | bS | cS | kc | tc => exact .inl (by simp [MpMul.lay])
  | aD => exact .inl (show 0 < 4 * p.a.alloc by have := h.apos; omega)
  | bD => exact .inl (show 0 < 4 * p.b.alloc by have := h.bpos; omega)
  | cD => exact .inl (show 0 < 4 * p.c.alloc by have := h.cpos; omega)
  | code => exact .inl (show 0 < textLen by decide)

def mpMulB : HContract where
  P := MulBP
  X := MpMul.X
  R := MpMul.R
  all := [.stk, .aS, .aD, .bS, .bD, .cS, .cD, .kc, .tc, .code]
  hall := MpMul.all
  entry := MpMul.entry
  args p := MpMul.args p.toP
  rets p := MpMul.rets p.toP
  lay p := MpMul.lay p.toP
  kind p := MpMul.kind p.toP
  out p := MpMul.out p.toP
  isW := MpMul.isW
  ws := MpMul.ws
  site := .cD
  site' p := MpMul.site' p.toP
  hin p := MpMul.hin p.toP
  hout p := MpMul.hout p.toP
  Res := MulBRes
  Q p := MpMul.Q p.toP
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _ | simp [Kind.Fits, MpMul.kind, MpMul.lay, Iv.Sub]
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpMul.out, MpMul.kind, MpMul.ws, Kind.isRam, Kind.indep]
  pos p h r := mpMul_pos p.toP h.res r
  spec := fun hra hres => hres.ih.mul hres.lt hra hres.res

/-! ## `mp_mul(a, b, a)` below a bound -/

structure MulABP where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt
  H : List (Nat × Nat)
  n : Nat

def MulABP.toP (p : MulABP) : MpMulA.P := ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩

structure MulABRes (p : MulABP) : Prop where
  res : MpMulA.Res p.toP
  lt : MpMul.μ p.a p.b < p.n
  ih : MulBelow p.n

theorem mpMulA_pos (p : MpMulA.P) (h : MpMulA.Res p) (r : MpMulA.R) :
    0 < (MpMulA.lay p r).len ∨ (MpMulA.lay p r).base < heapStart ∨ heapEnd ≤ (MpMulA.lay p r).base := by
  cases r with
  | stk => exact .inl (by simp only [MpMulA.lay]; omega)
  | aS | bS | kc | tc => exact .inl (by simp [MpMulA.lay])
  | aD => exact .inl (show 0 < 4 * p.a.alloc by have := h.apos; omega)
  | bD => exact .inl (show 0 < 4 * p.b.alloc by have := h.bpos; omega)
  | code => exact .inl (show 0 < textLen by decide)

def mpMulAB : HContract where
  P := MulABP
  X := MpMul.X
  R := MpMulA.R
  all := [.stk, .aS, .aD, .bS, .bD, .kc, .tc, .code]
  hall := MpMulA.all
  entry := MpMul.entry
  args p := MpMulA.args p.toP
  rets p := MpMulA.rets p.toP
  lay p := MpMulA.lay p.toP
  kind p := MpMulA.kind p.toP
  out p := MpMulA.out p.toP
  isW := MpMulA.isW
  ws := MpMulA.ws
  site := .aD
  site' p := MpMulA.site' p.toP
  hin p := MpMulA.hin p.toP
  hout p := MpMulA.hout p.toP
  Res := MulABRes
  Q p := MpMulA.Q p.toP
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _ | simp [Kind.Fits, MpMulA.kind, MpMulA.lay, Iv.Sub]
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpMulA.out, MpMulA.kind, MpMulA.ws, Kind.isRam, Kind.indep]
  pos p h r := mpMulA_pos p.toP h.res r
  spec := fun hra hres => hres.ih.mulA hres.lt hra hres.res

/-! ## A callee's placement in its result

`call_heap` hands the continuation the callee's `St`/`HP`, not its `HPost.place`/`foot`. A
caller whose own site is the callee's (`mp_mul` returns the block its algorithm placed)
needs both for its own `HPost`: `withPlace` adds them to the callee's `Q`. -/

def _root_.Tom.Machine.HContract.withPlace (C : HContract) : HContract :=
  { C with
    Q := fun p x => C.Q p x ∧ Place (C.hin p) (C.lay p C.site) (C.site' p x) ∧
      (∀ a, Foot (C.hout p x) a → Foot (C.hin p) a ∨ (C.lay p C.site).In a)
    spec := fun hra hres hS hB hH hoff => Triple.rmap
      (fun _ ⟨x, M, hat, hq, hpo⟩ => ⟨x, M, hat, ⟨hq, hpo.place, hpo.foot⟩, hpo⟩)
      (C.spec hra hres hS hB hH hoff) }

/-! ## The algorithms (`Api/MulAlg.lean`), their contract a premise in the residue -/

structure AlgRes (e : BitVec 64) (Rs : MpMul.P → Prop) (p : MpMul.P) : Prop where
  base : MulAlg.Base p
  rs : Rs p
  /-- The algorithm's contract (a named premise of the caller). -/
  spec : ∀ q, MulAlg.SpecR e Rs q

theorem mulAlg_pos (p : MpMul.P) (h : MulAlg.Base p) (r : MpMul.R) :
    0 < (MulAlg.lay p r).len ∨ (MulAlg.lay p r).base < heapStart ∨ heapEnd ≤ (MulAlg.lay p r).base := by
  cases r with
  | stk => exact .inl (by simp only [MulAlg.lay]; omega)
  | aS | bS | cS | kc | tc => exact .inl (by simp [MulAlg.lay])
  | aD => exact .inl (show 0 < 4 * p.a.alloc by have := h.apos; omega)
  | bD => exact .inl (show 0 < 4 * p.b.alloc by have := h.bpos; omega)
  | cD => exact .inl (show 0 < 4 * p.c.alloc by have := h.cpos; omega)
  | code => exact .inl (show 0 < textLen by decide)

/-- An algorithm at `e` with residue `Rs` (karatsuba, balance, toom). -/
def algH (e : BitVec 64) (Rs : MpMul.P → Prop) : HContract where
  P := MpMul.P
  X := MpMul.X
  R := MpMul.R
  all := [.stk, .aS, .aD, .bS, .bD, .cS, .cD, .kc, .tc, .code]
  hall := MpMul.all
  entry := e
  args := MpMul.args
  rets := MpMul.rets
  lay := MulAlg.lay
  kind := MpMul.kind
  out := MpMul.out
  isW := MpMul.isW
  ws := MpMul.ws
  site := .cD
  site' := MpMul.site'
  hin := MpMul.hin
  hout := MpMul.hout
  Res := AlgRes e Rs
  Q := MulAlg.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _ | simp [Kind.Fits, MpMul.kind, MulAlg.lay, Iv.Sub]
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpMul.out, MpMul.kind, MpMul.ws, Kind.isRam, Kind.indep]
  pos p h r := mulAlg_pos p h.base r
  spec := fun hra hres => hres.spec _ hra hres.rs

def kmulP : HContract := (algH KMul.entry KMul.Res).withPlace
def balP : HContract := (algH BalMul.entry BalMul.Res).withPlace
def toomP : HContract := (algH ToomMul.entry ToomMul.Res).withPlace

/-! ## `s_mp_mul_digs` (`Fn.SMpMulDigsG5.correct`) -/

theorem sMpMulDigs_pos (p : SMpMulDigs.P) (h : SMpMulDigs.Res p) (r : SMpMulDigs.R) :
    0 < (SMpMulDigs.lay p r).len ∨ (SMpMulDigs.lay p r).base < heapStart ∨ heapEnd ≤ (SMpMulDigs.lay p r).base := by
  cases r with
  | stk => exact .inl (show 0 < SMpMulDigs.F by decide)
  | aS | bS | cS => exact .inl (show 0 < 24 by decide)
  | aD => exact .inl (show 0 < 4 * p.a.alloc by have := h.apos; omega)
  | bD => exact .inl (show 0 < 4 * p.b.alloc by have := h.bpos; omega)
  | cD => exact .inl (show 0 < 4 * p.c.alloc by have := h.cpos; omega)
  | code => exact .inl (show 0 < textLen by decide)

/-- `Api.SMpMulDigs.site'` with the kept site spelled out (not through `lay`). -/
def sMpMulDigsSite (p : SMpMulDigs.P) : Option (Nat × MpInt) → Iv
  | none => ⟨p.cdp, 4 * p.c.alloc⟩
  | some (q, c') => ⟨q, 4 * c'.alloc⟩

def sMpMulDigsH : HContract where
  P := SMpMulDigs.P
  X := Option (Nat × MpInt)
  R := SMpMulDigs.R
  all := [.stk, .aS, .aD, .bS, .bD, .cS, .cD, .code]
  hall := SMpMulDigs.all
  entry := SMpMulDigs.entry
  args := SMpMulDigs.args
  rets := fun _ x ra => [(1, ra), (10, if x.isSome then 0#64 else MpInit.memBV)]
  lay := SMpMulDigs.lay
  kind := SMpMulDigs.kind
  out := SMpMulDigs.out
  isW := SMpMulDigs.isW
  ws := SMpMulDigs.ws
  site := .cD
  site' := sMpMulDigsSite
  hin := SMpMulDigs.hin
  hout := SMpMulDigs.hout
  Res := SMpMulDigs.Res
  Q := SMpMulDigs.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨_, _⟩ <;> cases r <;> simp_all [SMpMulDigs.out, SMpMulDigs.kind, SMpMulDigs.ws, Kind.isRam, Kind.indep]
  pos p h r := sMpMulDigs_pos p h r
  spec := fun {p} {m} {v} {outp} {ra} hra hres hS hB hH hoff => by
    have h := Fn.SMpMulDigsG5.correct (p := p) (m := m) (v := v) (outp := outp) (ra := ra) hra hres hS hB hH hoff
    refine Triple.rmap (fun cf ⟨x, M, hat, hq, hpo⟩ => ⟨x, M, ?_, hq, ?_⟩) h
    · rcases x with _ | ⟨q, c'⟩ <;> exact hat
    · rcases x with _ | ⟨q, c'⟩ <;> exact hpo

def sMpMulDigsP : HContract := sMpMulDigsH.withPlace

/-! ## `s_mp_mul_digs_fast` with growth (`Api/MulFastH.lean`, a named premise) -/

structure FastHRes (p : SMpMulDigs.P) : Prop where
  res : MulFastH.Res p
  /-- The growing fast multiplier's contract (a named premise of the caller). -/
  spec : MulFastH.Statement

def mulFastH : HContract where
  P := SMpMulDigs.P
  X := MpMul.X
  R := SMpMulDigs.R
  all := [.stk, .aS, .aD, .bS, .bD, .cS, .cD, .code]
  hall := SMpMulDigs.all
  entry := MulFastH.entry
  args := SMpMulDigs.args
  rets := MulFastH.rets
  lay := MulFastH.lay
  kind := SMpMulDigs.kind
  out := MulFastH.out
  isW := SMpMulDigs.isW
  ws := SMpMulDigs.ws
  site := .cD
  site' := MulFastH.site'
  hin := MulFastH.hin
  hout := MulFastH.hout
  Res := FastHRes
  Q := MulFastH.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MulFastH.out, SMpMulDigs.kind, SMpMulDigs.ws, Kind.isRam, Kind.indep]
  pos p h r := by
    cases r with
    | stk => exact .inl (show 0 < MulFastH.F by decide)
    | aS | bS | cS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by have := h.res.apos; omega)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by have := h.res.bpos; omega)
    | cD => exact .inl (show 0 < 4 * p.c.alloc by have := h.res.cpos; omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := fun hra hres => hres.spec hra hres.res

def mulFastP : HContract := mulFastH.withPlace

end Tom.Machine.Std
