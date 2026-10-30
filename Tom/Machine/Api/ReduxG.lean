import Tom.Machine.Api.MpReduce2k

/-!
# The growing reductions of `s_mp_exptmod_fast`: what they share

`s_mp_exptmod_fast`'s `redux(x, n, rho)` is `s_mp_montgomery_reduce_fast`, `mp_montgomery_reduce`,
`mp_dr_reduce` or `mp_reduce_2k`: each takes `(x, n, d)` in `a0`–`a2` (`d` an `mp_digit`: `rho`, `k`
or `d`) and grows `x` by `mp_grow` when its block is short. Each contract states its own stack depth `F` (`lay F`) and residue.
-/

namespace Tom.Machine.Api.ReduxG

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpReduce2k (R P kind)

/-- `(ok, q, x')`: `x'`'s digits at `q`. -/
abbrev X : Type := Bool × Nat × MpInt

def out (p : P) : X → R → Kind
  | (_, q, a'), .aS => .mpS p.pa q a'
  | (_, q, a'), .aD => .mpD q a'.alloc a'.digit
  | _, r => kind p r

def site' (_ : P) : X → Iv
  | (_, q, a') => ⟨q, 4 * a'.alloc⟩

/-- `x`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.adp p.a :: p.H

def hout (p : P) : X → List (Nat × Nat)
  | (_, q, a') => (q, 4 * a'.alloc) :: p.H

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpInit.memBV)]

/-- What `x` holds after: shaped, live, placed (inside the old block `L` or a fresh one); on
`MP_OKAY` the reduction `post`. -/
structure Out (p : P) (L : Iv) (post : MpInt → Prop) (x : X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) L (site' p x)
  post : x.1 = true → post x.2.2

theorem memBV_eq : MpGrow.memBV = MpInit.memBV := rfl

end Tom.Machine.Api.ReduxG
