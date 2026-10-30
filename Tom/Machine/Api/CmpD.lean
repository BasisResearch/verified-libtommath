import Tom.Machine.Img
import Tom.Machine.Fn.CmpD
import Tom.Spec.Cmp

/-!
# `mp_cmp_d`: the standard contract

From the entry, `mp_cmp_d(a, b)` with `a` valid and `b` a digit returns to
`ra` with `a0` the `mp_ord` code of `cmpD a b` (`= compare (val a) b`,
`Tom.cmpD_spec`), the callee-saved registers and **all of memory**
unchanged: it has no frame and no store, so the read-only regions of
`Api/Un.lean` (`isR`) are not needed (the stack region is omitted; the
frame is the identity).

Beyond `Valid`: `1 ≤ alloc`, because the code reads `dp[0]` also when `a`
is zero (every `mp_int` libtommath builds has `alloc ≥ 1`). `b` arrives
sign-extended, as the psABI passes a 32-bit `mp_digit`; for `b < 2^28` that
is `BitVec.ofNat 64 b`.
-/

namespace Tom.Machine.Api.CmpD

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

/-- What `mp_cmp_d(a, b)` needs. -/
structure Pre (m : Mem) (pa adp : Nat) (a : MpInt) (b : Nat) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  va : a.Valid
  ga : MpGeom pa adp a.alloc
  alloc_pos : 1 ≤ a.alloc
  db : b < radix
  ra_al : ra.toNat % 4 = 0
  img : Img m

/-- Back at `ra` with the result in `a0`, memory unchanged. -/
def Ret (m : Mem) (v : Abi) (outp : Array String) (a : MpInt) (b : Nat) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  At ra [(1, ra), (10, BitVec.ofInt 64 (ordCode (cmpD a b)))] m v.keep outp cf

def entry : BitVec 64 := 0x80000728#64

/-- **`mp_cmp_d` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {pa adp : Nat} {a : MpInt} {b : Nat} {ra : BitVec 64},
    Pre m pa adp a b ra →
    Triple (At entry (Fn.CmpD.entryL ra pa b) m v.keep outp) (Ret m v outp a b ra)

end Tom.Machine.Api.CmpD
