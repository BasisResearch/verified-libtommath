import Tom.Machine.Api.StdHeapFn
import Tom.Spec.DivD
import Tom.Spec.Init

/-!
# `mp_div_d(a, b, a, d)` in place: the allocating contract

`Api/MpDivD.lean` with `c = a`: the call `mp_to_radix` makes, `mp_div_d(&t, radix, &t, &d)`
(`bn_mp_to_radix.c`; `2 ≤ radix ≤ 64`, `t != 0`). The paths it reaches (`bn_mp_div_d.c`,
`0x80005388`):

* `b = 2^k`: the scan finds `k`, `*d := a->dp[0] & (b - 1)` (read before `a` changes), the
  tail call `mp_div_2d(a, k, a, NULL)` in place (`Std.div2dG`): `a`'s digits stay put;
* `b = 3`: the tail call `s_mp_div_3(a, a, d)` in place (`Fn.Div3IG5.correct`);
* otherwise: `mp_init_size(&q, a->used)`, the long division of `a`'s digits into `q`, `*d := w`,
  `mp_clamp(&q)`, `mp_exch(&q, a)`, `mp_clear(&q)` (freeing `a`'s old digits).

As an allocating contract: the site is `a`'s digit array, re-placed at a fresh block on the
long-division paths (`Place.fresh`) and kept by `mp_div_2d` (`Place.keep`); `*d = |a| mod b`
as a one-digit array; on `MP_MEM` everything is kept. Memory changes only in the stack
`[sp - 688, sp)`, `a`, `*d` and the allocator's footprint.

Not covered (named `Res` fields): `b < 2` (`MP_VAL` for `0`; `b = 1` tail-calls `mp_copy(a, a)`),
`a = 0` (`mp_copy(a, a)` again), `d = NULL`, `b ≥ radix`.

`Api/MpDivDIW.lean`: the form the generated assembly proves (`*d`'s slot as a one-digit array,
as `Api/MpDivDW.lean`) and `statement` back.
-/

namespace Tom.Machine.Api.MpDivDI

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x80005388#64

inductive R | stk | aS | aD | dS | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .dS, .code] := by cases r <;> simp

/-- The stack depth: the 112-byte frame and `mp_init_size`'s 576 (above `s_mp_div_3`'s 656,
`mp_div_2d`'s 96). -/
def F : Nat := 688

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pd : Nat
  a : MpInt
  /-- The divisor `b` (an `mp_digit`). -/
  v : Nat
  H : List (Nat × Nat)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .dS => ⟨p.pd, 4⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .dS => .ram
  | .code => .code

/-- The remainder `|a| mod b`. -/
abbrev rem (p : P) : Nat := p.a.mag % p.v

def out (p : P) : Option (Nat × MpInt) → R → Kind
  | none, r => kind p r
  | some (q, a'), .aS => .mpS p.pa q a'
  | some (q, a'), .aD => .mpD q a'.alloc a'.digit
  | some _, .dS => .mpD p.pd 1 (fun _ => rem p)
  | some _, r => kind p r

def isW : R → Bool
  | .stk | .aS | .aD | .dS => true
  | _ => false

def ws : List R := [.stk, .aS, .aD, .dS]

def site' (p : P) : Option (Nat × MpInt) → Iv
  | none => lay p .aD
  | some (q, a') => ⟨q, 4 * a'.alloc⟩

def hin (p : P) : List (Nat × Nat) := digBlk p.adp p.a :: p.H

def hout (p : P) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => hin p
  | some (q, a') => (q, 4 * a'.alloc) :: p.H

def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.v),
   (12, BitVec.ofNat 64 p.pa), (13, BitVec.ofNat 64 p.pd)]

/-- The return code: `MP_MEM` when `mp_init_size` (or `s_mp_div_3`'s) fails, else `MP_OKAY`. -/
def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpInit.memBV | some _ => 0#64)]

/-- What `mp_div_d(a, b, a, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  /-- `b ≥ 2` (`mp_to_radix`'s `radix ≥ 2`): `b = 0` returns `MP_VAL` and `b = 1` tail-calls
  `mp_copy(a, a)`, whose `a == b` return has no contract here. -/
  v_ge : 2 ≤ p.v
  /-- `a != 0` (`mp_to_radix` divides while `t != 0`): `a == 0` tail-calls `mp_copy(a, a)`. -/
  u_pos : 0 < p.a.used
  /-- `d != NULL`: the image's only caller passes `&d`. -/
  d_nn : p.pd ≠ 0
  d_al : p.pd % 4 = 0
  doff : OffHeap p.pd 4
  /-- `b` is a digit: the power-of-two scan stops at `MP_DIGIT_BIT`, and the long division's
  `w * 2^28 + a[i]` fits an `mp_word`. -/
  v_lt : p.v < radix

/-- `a` after: `DivDQuot a b a a'` (by path), nothing on `MP_MEM`. -/
def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (_, a') => DivDQuot p.a p.v p.a a'

/-- **`mp_div_d(a, b, a, d)` on the machine**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpDivDI
