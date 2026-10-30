import Tom.Machine.Api.StdHeapFn
import Tom.Machine.Fn.SMpSqrG
import Tom.Spec.MulAlgo
import Tom.Spec.Init

/-!
# `s_mp_sqr(a, b)`: the allocating contract

`a` shaped with `a->used < 2^30` (so `2 a->used + 1` is an `int` and every
index of `t.dp` fits), `b` live (its digits a block at the front of the heap's
blocks, `0 < b->alloc`) and distinct from `a` (D6; `mp_sqr`'s `b == a` is not
covered). The temporary `t` (`mp_init_size(&t, 2 a->used + 1)`, its struct in
the frame at `sp - 136`) receives the schoolbook square (HAC 14.16: the
diagonal `t[2ix] + a[ix]²`, the doubled cross products `2 a[ix] a[iy]`, the
carry propagated upwards; every `mp_word` sum stays below `2^58`); then
`mp_clamp(&t)`, `mp_exch(&t, b)`, `mp_clear(&t)` (which frees `b`'s old
digits). As an allocating contract (the shape of `Api/Div3.lean`): the site is
`b`'s digit array, re-placed at the fresh block `q` holding `b'` with
`SqrPost a b'` (`b'` valid, `b' = a²`) and `b'->alloc = initPrec (2 a->used + 1)`;
on `MP_MEM` (from `mp_init_size`) everything is kept (`Place.keep`, `b` and the
heap unchanged). Memory changes only in the stack `[sp - 736, sp)` (the
160-byte frame and `mp_init_size`'s 576; `mp_clear`, `mp_exch`, `mp_clamp` and
`__muldi3` need less), `b` and the allocator's footprint.
-/

namespace Tom.Machine.Api.SMpSqr

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x80006e54#64

inductive R | stk | aS | aD | bS | bD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .code] := by cases r <;> simp

/-- The stack depth: the 160-byte frame and `mp_init_size`'s. -/
abbrev F : Nat := 160 + MpInit.Fsize

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt
  H : List (Nat × Nat)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .bS => .mpS p.pb p.bdp p.b
  | .bD => .mpD p.bdp p.b.alloc p.b.digit
  | .code => .code

/-- After: `none` on `MP_MEM`, `some (q, b')` with `b'`'s digits at the fresh block `q`. -/
def out (p : P) : Option (Nat × MpInt) → R → Kind
  | none, r => kind p r
  | some (q, b'), .bS => .mpS p.pb q b'
  | some (q, b'), .bD => .mpD q b'.alloc b'.digit
  | some _, r => kind p r

def isW : R → Bool
  | .stk | .bS | .bD => true
  | _ => false

def ws : List R := [.stk, .bS, .bD]

def site' (p : P) : Option (Nat × MpInt) → Iv
  | none => lay p .bD
  | some (q, b') => ⟨q, 4 * b'.alloc⟩

/-- `b`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.bdp p.b :: p.H

/-- After: `b`'s old block freed, `t`'s (now `b`'s) live. -/
def hout (p : P) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => hin p
  | some (q, b') => (q, 4 * b'.alloc) :: p.H

/-- The arguments: `a0 = a`, `a1 = b` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpInit.memBV | some _ => 0#64)]

/-- What `s_mp_sqr(a, b)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The square reads `a`'s digits below `used` only (`mp_sqr` passes it valid). -/
  sa : p.a.Shape
  /-- `2 a->used + 1` is an `int` (`slli`/`addiw` at `6e68`); the rows (`smsqrg`) bound
  every index of `t.dp` by it. -/
  au : p.a.used < 2 ^ 30
  apos : 0 < p.a.alloc
  /-- `b`'s old digits are freed by `mp_clear(&t)` after the exchange: a live, nonempty block. -/
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

/-- The square, and `t`'s allocation. -/
structure Sq (a b' : MpInt) : Prop where
  sqr : SqrPost a b'
  alloc : b'.alloc = initPrec (2 * a.used + 1)

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (_, b') => Sq p.a b'

/-- **`s_mp_sqr(a, b)` on the machine**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .bD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.SMpSqr
