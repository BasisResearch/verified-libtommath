import Tom.Machine.Api.Reduce2kSetupL
import Tom.Machine.Api.Expt2G
import Tom.Spec.Reduce2kSetupGStep

/-!
# `mp_reduce_2k_setup_l(a, d)` growing `d`: the allocating contract

`Api/Reduce2kSetupL.lean` keeps `tmp` within `mp_init`'s `MP_PREC = 32` digits (`room`: `|a| < 2^896`)
and `d` in place (`droom`). Here `mp_2expt(&tmp, p)` grows `tmp` (`Std.mp2exptG`) and
`s_mp_sub(&tmp, a, d)` grows `d` (`Std.sSubG`), so `a` is any valid modulus with an `int` bit count.
`tmp` is freed on every path. The site is `d`'s digit array (`d`'s digits the front live block):
* `none`: `MP_MEM` from `mp_init`, `mp_2expt` or `s_mp_sub` (each fails before writing `d`): `d` as
  it was;
* `some (q, d')`: `MP_OKAY`, `Setup2kLPost a d'` (`|d'| = 2^p - |a|`, valid), `d'` at `q`.
Memory changes only in the stack `[sp - 672, sp)` (the 80-byte frame and the growing callees' 592),
`d` and the allocator's footprint.
-/

namespace Tom.Machine.Api.Reduce2kSetupLG

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Reduce Tom.Mont
open Tom.Machine.Api.Reduce2kSetupL (entry P R all isW ws args)

/-- The stack depth: the 80-byte frame and `mp_2expt`'s or `s_mp_sub`'s with `mp_grow`. -/
abbrev F : Nat := 80 + Expt2G.F

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .dS => ⟨p.pd, 24⟩
  | .dD => ⟨p.ddp, 4 * p.d.alloc⟩
  | .code => textIv

abbrev kind := Reduce2kSetupL.kind

def out (p : P) : Option (Nat × MpInt) → R → Kind
  | some (q, d'), .dS => .mpS p.pd q d'
  | some (q, d'), .dD => .mpD q d'.alloc d'.digit
  | _, r => kind p r

def site' (p : P) : Option (Nat × MpInt) → Iv
  | none => lay p .dD
  | some (q, d') => ⟨q, 4 * d'.alloc⟩

/-- `d`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.ddp p.d :: p.H

def hout (p : P) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => hin p
  | some (q, d') => (q, 4 * d'.alloc) :: p.H

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpInit.memBV | some _ => 0#64)]

/-- What `mp_reduce_2k_setup_l(a, d)` needs: `Api/Reduce2kSetupL.lean`'s `Res` without the rooms. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  /-- `mp_count_bits`'s `int` result. -/
  bits : Layout.digitBits * p.a.used < 2 ^ 31
  /-- `s_mp_sub`'s `Pre.sc`. -/
  sd : p.d.Shape
  /-- `s_mp_sub` keeps `d`'s sign for a nonzero result. -/
  dsign : p.d.sign = Layout.mpZpos ∨ p.d.sign = Layout.mpNeg
  apos : 0 < p.a.alloc
  /-- `d`'s digits: `realloc`'s block. -/
  dpos : 0 < p.d.alloc
  doff : OffHeap p.pd 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (_, d') => Setup2kLPost p.a d'

/-- **`mp_reduce_2k_setup_l(a, d)` on the machine, growing `d`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .dD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.Reduce2kSetupLG
