import Tom.Machine.Api.MpReduceSetup
import Tom.Machine.Api.Expt2G

/-!
# `mp_reduce_setup(a, b)` growing `a`: the allocating contract

`Api/MpReduceSetup.lean` asks for room in `a` for `mp_2expt`'s `2 b->used + 1` digits (D5): with `a`
from `mp_init` (`MP_PREC = 32` digits) that is `b->used ≤ 15`. Here `mp_2expt(a, 56 b->used)` grows
`a` (`Std.mp2exptG`, `Api/Expt2G.lean`) and the tail call `mp_div(a, b, a, NULL)` re-places it
(`Api/MpDivQ.lean`), so there is no room premise. The site is `a`'s digit array; both outcomes
carry `a`'s block after:
* `mem q a'`: `MP_MEM` from `mp_2expt`'s `mp_grow` (`a` zeroed at its block) or from `mp_div`
  (`a = radix^(2 b->used)` at `mp_2expt`'s block); nothing stated about `a'`;
* `ok q a'`: `MP_OKAY`, `ReduceSetupPost b a'` (`a' = ⌊radix^(2 b->used) / b⌋`).
Regions, layout, arguments, stack depth (`mp_div`'s, on the whole stack) as `Api/MpReduceSetup.lean`.
-/

namespace Tom.Machine.Api.MpReduceSetupG

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpReduceSetup (entry P R lay kind isW ws args)

abbrev F := MpReduceSetup.F
abbrev hin := MpReduceSetup.hin

/-- `MP_MEM` or `MP_OKAY`, with `a`'s digits at `q` after. -/
inductive Out
  | mem (q : Nat) (a' : MpInt)
  | ok (q : Nat) (a' : MpInt)

def Out.q : Out → Nat
  | .mem q _ | .ok q _ => q

def Out.a : Out → MpInt
  | .mem _ a' | .ok _ a' => a'

def out (p : P) (x : Out) : R → Kind
  | .aS => .mpS p.pa x.q x.a
  | .aD => .mpD x.q x.a.alloc x.a.digit
  | r => kind p r

def site' (_ : P) (x : Out) : Iv := ⟨x.q, 4 * x.a.alloc⟩

def hout (p : P) (x : Out) : List (Nat × Nat) := (x.q, 4 * x.a.alloc) :: p.H

def rets (_ : P) (x : Out) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | .mem _ _ => MpInit.memBV | .ok _ _ => 0#64)]

/-- What `mp_reduce_setup(a, b)` needs: `Api/MpReduceSetup.lean`'s `Res` without `room`. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_2expt` zeroes and grows `a`. -/
  sa : p.a.Shape
  /-- The modulus: valid, positive. -/
  vb : p.b.Valid
  b0 : 0 < p.b.used
  bz : p.b.sign = Layout.mpZpos
  /-- `mp_2expt`'s `int b` (`56 b->used`). -/
  k_lt : p.b.used * 2 * Layout.digitBits < 2 ^ 31
  /-- `a`'s digits: `realloc`'s block, `mp_div`'s old block of `c = a`. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  /-- `mp_div`'s `mp_init_copy(&y, b)` copies from a live block. -/
  bblk : digBlk p.bdp p.b ∈ p.H

def Q (p : P) : Out → Prop
  | .mem _ a' => 0 < a'.alloc
  | .ok _ a' => Reduce.ReduceSetupPost p.b a'

/-- **`mp_reduce_setup(a, b)` on the machine, growing `a`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpReduceSetupG
