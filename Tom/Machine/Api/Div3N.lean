import Tom.Machine.Api.Div3I

/-!
# `s_mp_div_3(a, a, NULL)` in place: the allocating contract

`Api/Div3I.lean` with `d = NULL`, the call `s_mp_toom_mul` makes (`s_mp_div_3(&S2, &S2, NULL)`): the
code (`bn_s_mp_div_3.c`, `0x80006640`) skips the remainder's store (`beqz a2` at `6744`) and
otherwise runs as with a `d`: the temporary `q` (`mp_init_size(&q, a->used)`) receives the long
division by `3`, then `mp_clamp(&q)`, `mp_exch(&q, a)`, `mp_clear(&q)`. The site is `a`'s digit
array, re-placed at the fresh block `q` holding `a'` with `Div3Quot a a'`; on `MP_MEM` everything
is kept. Memory changes only in the stack `[sp - 656, sp)`, `a` and the allocator's footprint.
-/

namespace Tom.Machine.Api.Div3N

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

inductive R | stk | aS | aD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .code] := by cases r <;> simp

/-- The stack depth: the 80-byte frame and `mp_init_size`'s 576 (`mp_clear` needs less). -/
def F : Nat := 656

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt
  H : List (Nat × Nat)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .code => .code

/-- After: `a` re-placed at `q`; on `MP_MEM` everything kept. -/
def out (p : P) : Option (Nat × MpInt) → R → Kind
  | none, r => kind p r
  | some (q, a'), .aS => .mpS p.pa q a'
  | some (q, a'), .aD => .mpD q a'.alloc a'.digit
  | some _, r => kind p r

def isW : R → Bool
  | .stk | .aS | .aD => true
  | _ => false

def ws : List R := [.stk, .aS, .aD]

def site' (p : P) : Option (Nat × MpInt) → Iv
  | none => lay p .aD
  | some (q, a') => ⟨q, 4 * a'.alloc⟩

def hin (p : P) : List (Nat × Nat) := digBlk p.adp p.a :: p.H

def hout (p : P) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => hin p
  | some (q, a') => (q, 4 * a'.alloc) :: p.H

/-- The arguments: `a0 = a1 = a`, `a2 = NULL`. -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pa),
   (12, BitVec.ofNat 64 0)]

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpInit.memBV | some _ => 0#64)]

/-- What `s_mp_div_3(a, a, NULL)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 656
  va : p.a.Valid
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  /-- `a != 0`: the `a->used == 0` branch (`6788`) is not covered (as `Api/Div3I.lean`). -/
  u_pos : 0 < p.a.used

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (_, a') => Div3Quot p.a a'

/-- **`s_mp_div_3(a, a, NULL)` on the machine**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At Fn.Div3.entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.Div3N
