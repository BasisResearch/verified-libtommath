import Tom.Machine.Api.StdHeapFn
import Tom.Machine.Fn.Div3
import Tom.Spec.Init

/-!
# `s_mp_div_3(a, c, d)`: the allocating contract (over `Kit/MeetHeap.lean`)

`a` valid and live, `c` live (non-`NULL`; distinct from `a`, D6) at the front of
the heap's blocks, `d` `NULL` (`hasD = false`) or a 4-byte slot off the
allocator. The temporary `q` (`mp_init_size(&q, a->used)`) receives the long
division by `3`; then `mp_clamp(&q)`, `mp_exch(&q, c)`, `mp_clear(&q)` (which
frees `c`'s old digits). As an allocating contract: the site is `c`'s digit
array, re-placed at the fresh block `q` (`Place.fresh`) holding `c'` with
`Div3Quot a c'` (`DivLongQuot a 3`), `*d = |a| mod 3` as a one-digit array; on
`MP_MEM` everything is kept (`Place.keep`). Memory changes only in the stack
`[sp - 656, sp)` (the 80-byte frame and `mp_init_size`'s 576), `c`, `*d` and the
allocator's footprint.
-/

namespace Tom.Machine.Api.Div3

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

inductive R | stk | aS | aD | cS | cD | dS | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .cS, .cD, .dS, .code] := by cases r <;> simp

/-- The stack depth: the 80-byte frame and `mp_init_size`'s (`mp_clear` needs less). -/
abbrev F : Nat := 80 + MpInit.Fsize

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pc : Nat
  cdp : Nat
  hasD : Bool
  pd : Nat
  a : MpInt
  c : MpInt
  H : List (Nat × Nat)

/-- `*d`'s slot. -/
def dI : Bool → Nat → Iv
  | true, pd => ⟨pd, 4⟩
  | false, _ => Iv.nil

/-- `*d` after: the remainder as a one-digit array. -/
def dK : Bool → Nat → Nat → Kind
  | true, pd, r => .mpD pd 1 (fun _ => r)
  | false, _, _ => .ram

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .cS => ⟨p.pc, 24⟩
  | .cD => ⟨p.cdp, 4 * p.c.alloc⟩
  | .dS => dI p.hasD p.pd
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .cS => .mpS p.pc p.cdp p.c
  | .cD => .mpD p.cdp p.c.alloc p.c.digit
  | .dS => .ram
  | .code => .code

/-- The remainder `|a| mod 3`. -/
abbrev rem (a : MpInt) : Nat := Tom.ldR a.digit 3 a.used 0

def out (p : P) : Option (Nat × MpInt) → R → Kind
  | none, r => kind p r
  | some (q, c'), .cS => .mpS p.pc q c'
  | some (q, c'), .cD => .mpD q c'.alloc c'.digit
  | some _, .dS => dK p.hasD p.pd (rem p.a)
  | some _, r => kind p r

def isW : R → Bool
  | .stk | .cS | .cD | .dS => true
  | _ => false

def ws : List R := [.stk, .cS, .cD, .dS]

def site' (p : P) : Option (Nat × MpInt) → Iv
  | none => lay p .cD
  | some (q, c') => ⟨q, 4 * c'.alloc⟩

def hin (p : P) : List (Nat × Nat) := digBlk p.cdp p.c :: p.H

def hout (p : P) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => hin p
  | some (q, c') => (q, 4 * c'.alloc) :: p.H

def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pc),
   (12, BitVec.ofNat 64 p.pd)]

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpInit.memBV | some _ => 0#64)]

structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  apos : 0 < p.a.alloc
  cpos : 0 < p.c.alloc
  aoff : OffHeap p.pa 24
  coff : OffHeap p.pc 24
  dnull : p.hasD = false → p.pd = 0
  dslot : p.hasD = true → p.pd ≠ 0 ∧ p.pd % 4 = 0 ∧ OffHeap p.pd 4

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (_, c') => Div3Quot p.a c'

/-- **`s_mp_div_3(a, c, d)` on the machine**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At Fn.Div3.entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.Div3
