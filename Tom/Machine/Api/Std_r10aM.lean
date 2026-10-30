import Tom.Machine.Fn.MpModMainG
import Tom.Machine.Api.MpMulmod

/-!
# The callee contracts for `mp_mulmod`

* `mpModP`: `mp_mod(a, b, c)` (`Api/MpMod.lean`, `Fn.MpModG5.correct`), the placement of `c`'s
  digits in `Q` (`HContract.wp`);
* `mpMulH`: `mp_mul(a, b, c)` with its contract (`Api.MpMul.Statement`, proved: `Fn.MulGroupB.mulCorrect.1`)
  a conjunct of the residue, as `Api/Std_r6g.lean`'s `AlgRes.spec`.
-/

namespace Tom.Machine.Std

open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc

def mpModH : HContract where
  P := Api.MpMod.P
  X := Api.MpMod.Out
  R := Api.MpMod.R
  all := [.stk, .aS, .aD, .bS, .bD, .cS, .cD, .code]
  hall := Api.MpMod.all
  entry := Api.MpMod.entry
  args := Api.MpMod.args
  rets := Api.MpMod.rets
  lay := Api.MpMod.lay
  kind := Api.MpMod.kind
  out := Api.MpMod.out
  isW := Api.MpMod.isW
  ws := Api.MpMod.ws
  site := .cD
  site' := Api.MpMod.site'
  hin := Api.MpMod.hin
  hout := Api.MpMod.hout
  Res := Api.MpMod.Res
  Q := Api.MpMod.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | _ <;> cases r <;> simp_all [Api.MpMod.out, Api.MpMod.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.cpos; have := h.bnz; have := h.vb.used_le
    cases r with
    | stk => exact .inl (show 0 < Api.MpMod.F by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | cD => exact .inl (show 0 < 4 * p.c.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (show 0 < 24 by decide)
  spec := Fn.MpModG5.correct

/-- `mp_mod(a, b, c)` with the placement of `c`'s digits in `Q`. -/
def mpModP : HContract := mpModH.wp

/-- `mp_mul`'s parameters and the cut-off words' addresses (for the generator's region matching;
unused by the contract, as `Fn/KMulG5K.lean`'s `MulBKP`). -/
structure MulKP where
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
  kc : Nat
  tc : Nat

abbrev MulKP.toP (p : MulKP) : Api.MpMul.P := ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.pc, p.cdp, p.a, p.b, p.c, p.H⟩

/-- `mp_mul(a, b, c)`, its contract a premise of the call. -/
def mpMulH : HContract where
  P := MulKP
  X := Api.MpMul.X
  R := Api.MpMul.R
  all := [.stk, .aS, .aD, .bS, .bD, .cS, .cD, .kc, .tc, .code]
  hall := Api.MpMul.all
  entry := Api.MpMul.entry
  args p := Api.MpMul.args p.toP
  rets p := Api.MpMul.rets p.toP
  lay p := Api.MpMul.lay p.toP
  kind p := Api.MpMul.kind p.toP
  out p := Api.MpMul.out p.toP
  isW := Api.MpMul.isW
  ws := Api.MpMul.ws
  site := .cD
  site' p := Api.MpMul.site' p.toP
  hin p := Api.MpMul.hin p.toP
  hout p := Api.MpMul.hout p.toP
  Res p := Api.MpMul.Res p.toP ∧ Api.MpMul.Statement
  Q p := Api.MpMul.Q p.toP
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [Api.MpMul.out, Api.MpMul.kind, Api.MpMul.ws, Kind.isRam, Kind.indep]
  pos p h r := by
    have h1 : 0 < p.a.alloc := h.1.apos; have h2 : 0 < p.b.alloc := h.1.bpos; have h3 : 0 < p.c.alloc := h.1.cpos
    cases r with
    | stk => exact .inl (by simp only [Api.MpMul.lay]; omega)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | cD => exact .inl (show 0 < 4 * p.c.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (by simp [Api.MpMul.lay])
  spec := fun hra hres => hres.2 _ hra hres.1

end Tom.Machine.Std
