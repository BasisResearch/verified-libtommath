import Tom.Machine.Api.StdHeapFn
import Tom.Machine.Fn.Div3
import Tom.Spec.Init

/-!
# `s_mp_div_3(a, a, d)` in place: the allocating contract

`Api/Div3.lean` with `c = a` (the call `mp_div_d(a, 3, a, d)` makes: `mp_to_radix`'s
`mp_div_d(&t, radix, &t, &d)` tail-calls `s_mp_div_3(&t, &t, &d)`). The code
(`bn_s_mp_div_3.c`, `0x80006640`) reads `a` only before `mp_exch(&q, c)`: the temporary
`q` (`mp_init_size(&q, a->used)`) receives the long division by `3` from `a`'s digits,
`*d := w`, then `mp_clamp(&q)`, `mp_exch(&q, a)` and `mp_clear(&q)`, which frees `a`'s old
digits. As an allocating contract: the site is `a`'s digit array, re-placed at the fresh
block `q` holding `a'` with `Div3Quot a a'`; `*d = |a| mod 3` as a one-digit array; on
`MP_MEM` everything is kept. Memory changes only in the stack `[sp - 656, sp)` (the
80-byte frame and `mp_init_size`'s 576), `a`, `*d` and the allocator's footprint.

`*d`'s slot is a one-digit array `dd` (its old word) at the entry, as `Api/MpDivDW.lean`
(the generated entry state proves a written region's RAM from its digit kind).
-/

namespace Tom.Machine.Api.Div3I

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

inductive R | stk | aS | aD | dS | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .dS, .code] := by cases r <;> simp

/-- The stack depth: the 80-byte frame and `mp_init_size`'s 576 (`mp_clear` needs less). -/
def F : Nat := 656

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pd : Nat
  a : MpInt
  H : List (Nat × Nat)
  /-- `*d`'s old word, as a one-digit array. -/
  dd : MpInt

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .dS => ⟨p.pd, 4 * p.dd.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .dS => .mpD p.pd p.dd.alloc p.dd.digit
  | .code => .code

/-- The remainder `|a| mod 3`. -/
abbrev rem (a : MpInt) : Nat := a.mag % 3

/-- After: `a` re-placed at `q`, `*d` the remainder; on `MP_MEM` `a` kept and `*d` untracked RAM. -/
def out (p : P) : Option (Nat × MpInt) → R → Kind
  | none, .dS => .ram
  | none, r => kind p r
  | some (q, a'), .aS => .mpS p.pa q a'
  | some (q, a'), .aD => .mpD q a'.alloc a'.digit
  | some _, .dS => .mpD p.pd 1 (fun _ => rem p.a)
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
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pa),
   (12, BitVec.ofNat 64 p.pd)]

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpInit.memBV | some _ => 0#64)]

/-- What `s_mp_div_3(a, a, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 656
  va : p.a.Valid
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  /-- `a != 0`: the `a->used == 0` branch (`6788`) is not covered; `mp_div_d` tail-calls
  `s_mp_div_3` only for `a != 0` (its quick out takes `a == 0`). -/
  u_pos : 0 < p.a.used
  /-- `d != NULL`: the `d == NULL` branches are not covered (`mp_div_d` passes its own
  non-`NULL` `d`; `s_mp_toom_mul`'s `s_mp_div_3(&a, &a, NULL)` is not this contract). -/
  d_nn : p.pd ≠ 0
  d_al : p.pd % 4 = 0
  doff : OffHeap p.pd 4
  /-- The slot is one word. -/
  dd1 : p.dd.alloc = 1

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (_, a') => Div3Quot p.a a'

/-- **`s_mp_div_3(a, a, d)` on the machine**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At Fn.Div3.entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.Div3I
