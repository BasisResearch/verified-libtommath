import Tom.Machine.Api.KMul
import Tom.Machine.Api.Std_r6g
import Tom.Machine.Api.Std_r6h
import Tom.Machine.Api.Std_grow6
import Tom.Machine.Api.Std_grow6A
import Tom.Machine.Kit.Run
import Tom.Spec.KMulStepG
import Tom.Machine.Fn.KMulG
import Tom.Machine.Fn.KSqrG5K
import Tom.Machine.Fn.GrowH
import Tom.Machine.Kit.StackCall
import Tom.Machine.Kit.Sites

/-!
# Karatsuba multiplication's assembly: helpers

`s_mp_karatsuba_mul` allocates seven temporaries (`x0`, `x1`, `y0`, `y1`, `t1`, `x0y0`, `x1y1`).
The assembly (`Fn/KMulMainG.lean`, annotation `kmul.asm.json`, style `"pre"`, as karatsuba
squaring's `Fn/KSqrG5K.lean`) runs
over the contract's regions (`Api.MpMul.R`) plus the temporaries' digit arrays `dX dY dZ dW dT dU
dV` (the region type, `soundG` and `GPre` generated from the annotation's `"region"`).
-/

namespace Tom.Machine.Fn.KMulG5K

open Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpMul (P kind hin)

/-- `c` as it was (an `MP_MEM` before the last `mp_add`). -/
theorem outKeep {p : P} (h : KMul.Res p) : MulAlg.Q p (false, p.cdp, p.c) :=
  ⟨h.sc, h.cpos, (fun e => nomatch e), (fun e => nomatch e)⟩

/-! ## `mp_mul` with the cut-off words named (for the generator's region matching) -/

/-- `Std.mpMulB`'s parameters and the cut-off words' addresses (unused by the contract). -/
structure MulBKP where
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
  kc : Nat
  tc : Nat

structure MulABKP where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt
  H : List (Nat × Nat)
  n : Nat
  kc : Nat
  tc : Nat

def MulBKP.toB (p : MulBKP) : MulBP := ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.pc, p.cdp, p.a, p.b, p.c, p.H, p.n⟩
def MulABKP.toB (p : MulABKP) : MulABP := ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H, p.n⟩

/-- `Std.mpMulB` over `MulBKP`, the parameters spelled out. -/
def _root_.Tom.Machine.Std.mpMulBK : HContract where
  P := MulBKP
  X := MpMul.X
  R := MpMul.R
  all := [.stk, .aS, .aD, .bS, .bD, .cS, .cD, .kc, .tc, .code]
  hall := MpMul.all
  entry := MpMul.entry
  args p := MpMul.args ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.pc, p.cdp, p.a, p.b, p.c, p.H⟩
  rets p := MpMul.rets ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.pc, p.cdp, p.a, p.b, p.c, p.H⟩
  lay p := MpMul.lay ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.pc, p.cdp, p.a, p.b, p.c, p.H⟩
  kind p := MpMul.kind ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.pc, p.cdp, p.a, p.b, p.c, p.H⟩
  out p := MpMul.out ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.pc, p.cdp, p.a, p.b, p.c, p.H⟩
  isW := MpMul.isW
  ws := MpMul.ws
  site := .cD
  site' p := MpMul.site' ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.pc, p.cdp, p.a, p.b, p.c, p.H⟩
  hin p := MpMul.hin ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.pc, p.cdp, p.a, p.b, p.c, p.H⟩
  hout p := MpMul.hout ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.pc, p.cdp, p.a, p.b, p.c, p.H⟩
  Res p := MulBRes p.toB
  Q p := MpMul.Q ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.pc, p.cdp, p.a, p.b, p.c, p.H⟩
  fits p := Std.mpMulB.fits p.toB
  site_ws := by decide
  site_w := rfl
  out_ind p := Std.mpMulB.out_ind p.toB
  pos p := Std.mpMulB.pos p.toB
  spec := fun hra hres => Std.mpMulB.spec (p := MulBKP.toB _) hra hres

def _root_.Tom.Machine.Std.mpMulABK : HContract where
  P := MulABKP
  X := MpMul.X
  R := MpMulA.R
  all := [.stk, .aS, .aD, .bS, .bD, .kc, .tc, .code]
  hall := MpMulA.all
  entry := MpMul.entry
  args p := MpMulA.args ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  rets p := MpMulA.rets ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  lay p := MpMulA.lay ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  kind p := MpMulA.kind ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  out p := MpMulA.out ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  isW := MpMulA.isW
  ws := MpMulA.ws
  site := .aD
  site' p := MpMulA.site' ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  hin p := MpMulA.hin ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  hout p := MpMulA.hout ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  Res p := MulABRes p.toB
  Q p := MpMulA.Q ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  fits p := Std.mpMulAB.fits p.toB
  site_ws := by decide
  site_w := rfl
  out_ind p := Std.mpMulAB.out_ind p.toB
  pos p := Std.mpMulAB.pos p.toB
  spec := fun hra hres => Std.mpMulAB.spec (p := MulABKP.toB _) hra hres

end Tom.Machine.Fn.KMulG5K
