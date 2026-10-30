import Tom.Machine.Api.KSqrI
import Tom.Machine.Api.Std_r6h
import Tom.Machine.Kit.Run
import Tom.Spec.KSqrStep
import Tom.Machine.Fn.KSqrG
import Tom.Machine.Kit.StackCall
import Tom.Machine.Kit.Sites

/-!
# Karatsuba squaring's assembly: helpers

`s_mp_karatsuba_sqr` allocates six temporaries (`x0`, `x1`, `t1`, `t2`, `x0x0`, `x1x1`). The
assembly (`Fn/KSqrMainG.lean`, annotation `ksqr.asm.json`, style `"pre"`) runs over the contract's
regions plus their six digit arrays `dX … dW` (the region type, `soundG` and `GPre` generated from
the annotation's `"region"`). Here: `outKeep`, and `mp_sqr`'s contracts with the cut-off
words named.
-/

namespace Tom.Machine.Fn.KSqrG5K

open Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpSqr (P kind hin)

/-! ## The failure paths keep `b` -/

/-- `b` as it was (an `MP_MEM` before the last `mp_add`). -/
theorem outKeep {p : P} (h : KSqr.Res p) : SqrAlg.Q p (false, p.bdp, p.b) :=
  ⟨h.sb, h.bpos, (fun e => nomatch e), (fun e => nomatch e), Place.keep, Nat.le_refl _⟩

/-! ## `mp_sqr` with the cut-off words named (for the generator's region matching) -/

/-- `Std.sqrB`'s parameters and the four cut-off words' addresses (unused by the contract: they
let `scripts/gen_asm.py` match the callee's `ks ts km tm` regions with ours by address). -/
structure SqrBKP where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt
  H : List (Nat × Nat)
  n : Nat
  ks : Nat
  ts : Nat
  km : Nat
  tm : Nat

structure SqrABKP where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt
  H : List (Nat × Nat)
  n : Nat
  ks : Nat
  ts : Nat
  km : Nat
  tm : Nat

def SqrBKP.toB (p : SqrBKP) : SqrBP := ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H, p.n⟩
def SqrABKP.toB (p : SqrABKP) : SqrABP := ⟨p.sp, p.pa, p.adp, p.a, p.H, p.n⟩

/-- `Std.sqrB` over `SqrBKP`, the parameters spelled out (no `toP` for interval normalisation to see
through). -/
def _root_.Tom.Machine.Std.sqrBK : HContract where
  P := SqrBKP
  X := MpSqr.X
  R := MpSqr.R
  all := [.stk, .aS, .aD, .bS, .bD, .ks, .ts, .km, .tm, .code]
  hall := MpSqr.all
  entry := MpSqr.entry
  args p := MpSqr.args ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  rets p := MpSqr.rets ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  lay p := MpSqr.lay ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  kind p := MpSqr.kind ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  out p := MpSqr.out ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  isW := MpSqr.isW
  ws := MpSqr.ws
  site := .bD
  site' p := MpSqr.site' ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  hin p := MpSqr.hin ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  hout p := MpSqr.hout ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  Res p := SqrBRes p.toB
  Q p := MpSqr.Q ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  fits p := Std.sqrB.fits p.toB
  site_ws := by decide
  site_w := rfl
  out_ind p := Std.sqrB.out_ind p.toB
  pos p := Std.sqrB.pos p.toB
  spec := fun hra hres => Std.sqrB.spec (p := SqrBKP.toB _) hra hres

def _root_.Tom.Machine.Std.sqrABK : HContract where
  P := SqrABKP
  X := MpSqr.X
  R := MpSqrA.R
  all := [.stk, .aS, .aD, .ks, .ts, .km, .tm, .code]
  hall := MpSqrA.all
  entry := MpSqr.entry
  args p := MpSqrA.args ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  rets p := MpSqrA.rets ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  lay p := MpSqrA.lay ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  kind p := MpSqrA.kind ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  out p := MpSqrA.out ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  isW := MpSqrA.isW
  ws := MpSqrA.ws
  site := .aD
  site' p := MpSqrA.site' ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  hin p := MpSqrA.hin ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  hout p := MpSqrA.hout ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  Res p := SqrABRes p.toB
  Q p := MpSqrA.Q ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  fits p := Std.sqrAB.fits p.toB
  site_ws := by decide
  site_w := rfl
  out_ind p := Std.sqrAB.out_ind p.toB
  pos p := Std.sqrAB.pos p.toB
  spec := fun hra hres => Std.sqrAB.spec (p := SqrABKP.toB _) hra hres

end Tom.Machine.Fn.KSqrG5K
