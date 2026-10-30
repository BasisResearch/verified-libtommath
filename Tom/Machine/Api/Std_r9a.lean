import Tom.Machine.Api.Std_r6g
import Tom.Machine.Api.MulAlgA
import Tom.Machine.Api.SMpMulDigsA

/-!
# Callee contracts of `mp_mul(a, b, a)`

`Api/Std_r6g.lean`'s `algH`, `sMpMulDigsH`, `mulFastH` in place (`c = a`): the in-place
algorithms (`Api/MulAlgA.lean`) and the two schoolbook multipliers (`Api/SMpMulDigsA.lean`), each
with its contract a premise in the residue (the caller's `Gaps`), and the placement added to `Q`
by `HContract.withPlace` (`mp_mul` returns the block its callee placed).
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-! ## The in-place algorithms -/

structure AlgResA (e : BitVec 64) (Rs : MpMulA.P → Prop) (p : MpMulA.P) : Prop where
  base : MulAlgA.Base p
  rs : Rs p
  /-- The algorithm's contract (a named premise of the caller). -/
  spec : ∀ q, MulAlgA.SpecR e Rs q

theorem mulAlgA_pos (p : MpMulA.P) (h : MulAlgA.Base p) (r : MpMulA.R) :
    0 < (MulAlgA.lay p r).len ∨ (MulAlgA.lay p r).base < heapStart ∨ heapEnd ≤ (MulAlgA.lay p r).base := by
  cases r with
  | stk => exact .inl (by simp only [MulAlgA.lay]; omega)
  | aS | bS | kc | tc => exact .inl (by simp [MulAlgA.lay])
  | aD => exact .inl (show 0 < 4 * p.a.alloc by have := h.apos; omega)
  | bD => exact .inl (show 0 < 4 * p.b.alloc by have := h.bpos; omega)
  | code => exact .inl (show 0 < textLen by decide)

/-- An in-place algorithm at `e` with residue `Rs` (karatsuba, balance, toom with `c = a`). -/
def algHA (e : BitVec 64) (Rs : MpMulA.P → Prop) : HContract where
  P := MpMulA.P
  X := MpMul.X
  R := MpMulA.R
  all := [.stk, .aS, .aD, .bS, .bD, .kc, .tc, .code]
  hall := MpMulA.all
  entry := e
  args := MpMulA.args
  rets := MpMulA.rets
  lay := MulAlgA.lay
  kind := MpMulA.kind
  out := MpMulA.out
  isW := MpMulA.isW
  ws := MpMulA.ws
  site := .aD
  site' := MpMulA.site'
  hin := MpMulA.hin
  hout := MpMulA.hout
  Res := AlgResA e Rs
  Q := MulAlgA.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _ | simp [Kind.Fits, MpMulA.kind, MulAlgA.lay, Iv.Sub]
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpMulA.out, MpMulA.kind, MpMulA.ws, Kind.isRam, Kind.indep]
  pos p h r := mulAlgA_pos p h.base r
  spec := fun hra hres => hres.spec _ hra hres.rs

def kmulAP : HContract := (algHA KMul.entry KMulA.Res).withPlace
def balAP : HContract := (algHA BalMul.entry BalMulA.Res).withPlace
def toomAP : HContract := (algHA ToomMul.entry ToomMulA.Res).withPlace

/-! ## `s_mp_mul_digs(a, b, a, digs)` (a named premise) -/

structure DigsARes (p : SMpMulDigsA.P) : Prop where
  res : SMpMulDigsA.Res p
  /-- The in-place contract (a named premise of the caller). -/
  spec : SMpMulDigsA.Statement

theorem sMpMulDigsA_pos (p : SMpMulDigsA.P) (h : SMpMulDigsA.Res p) (r : SMpMulDigsA.R) :
    0 < (SMpMulDigsA.lay p r).len ∨ (SMpMulDigsA.lay p r).base < heapStart ∨
      heapEnd ≤ (SMpMulDigsA.lay p r).base := by
  cases r with
  | stk => exact .inl (show 0 < SMpMulDigs.F by decide)
  | aS | bS => exact .inl (show 0 < 24 by decide)
  | aD => exact .inl (show 0 < 4 * p.a.alloc by have := h.apos; omega)
  | bD => exact .inl (show 0 < 4 * p.b.alloc by have := h.bpos; omega)
  | code => exact .inl (show 0 < textLen by decide)

def sMpMulDigsAH : HContract where
  P := SMpMulDigsA.P
  X := Option (Nat × MpInt)
  R := SMpMulDigsA.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := SMpMulDigsA.all
  entry := SMpMulDigs.entry
  args := SMpMulDigsA.args
  rets := SMpMulDigsA.rets
  lay := SMpMulDigsA.lay
  kind := SMpMulDigsA.kind
  out := SMpMulDigsA.out
  isW := SMpMulDigsA.isW
  ws := SMpMulDigsA.ws
  site := .aD
  site' := SMpMulDigsA.site'
  hin := SMpMulDigsA.hin
  hout := SMpMulDigsA.hout
  Res := DigsARes
  Q := SMpMulDigsA.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨_, _⟩ <;> cases r <;> simp_all [SMpMulDigsA.out, SMpMulDigsA.kind, SMpMulDigsA.ws, Kind.isRam, Kind.indep]
  pos p h r := sMpMulDigsA_pos p h.res r
  spec := fun hra hres => hres.spec hra hres.res

def sMpMulDigsAP : HContract := sMpMulDigsAH.withPlace

/-! ## `s_mp_mul_digs_fast(a, b, a, digs)` with growth (a named premise) -/

structure FastHARes (p : SMpMulDigsA.P) : Prop where
  res : MulFastHA.Res p
  /-- The in-place growing fast multiplier's contract (a named premise of the caller). -/
  spec : MulFastHA.Statement

def mulFastHA : HContract where
  P := SMpMulDigsA.P
  X := MpMul.X
  R := SMpMulDigsA.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := SMpMulDigsA.all
  entry := MulFastH.entry
  args := SMpMulDigsA.args
  rets := MulFastHA.rets
  lay := MulFastHA.lay
  kind := SMpMulDigsA.kind
  out := MulFastHA.out
  isW := SMpMulDigsA.isW
  ws := SMpMulDigsA.ws
  site := .aD
  site' := MulFastHA.site'
  hin := MulFastHA.hin
  hout := MulFastHA.hout
  Res := FastHARes
  Q := MulFastHA.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MulFastHA.out, SMpMulDigsA.kind, SMpMulDigsA.ws, Kind.isRam, Kind.indep]
  pos p h r := by
    cases r with
    | stk => exact .inl (show 0 < MulFastH.F by decide)
    | aS | bS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by have := h.res.apos; omega)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by have := h.res.bpos; omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := fun hra hres => hres.spec hra hres.res

def mulFastAP : HContract := mulFastHA.withPlace

end Tom.Machine.Std
