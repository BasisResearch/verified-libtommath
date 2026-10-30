import Tom.Machine.Api.ReduxG
import Tom.Machine.Api.Expt2G
import Tom.Spec.Mont

/-!
# `mp_montgomery_calc_normalization(a, b)` growing `a`: the allocating contract

`Api/MontNorm.lean` (the frozen contract, `Std.montNormC`) asks for room: `b->used + 1 ≤ a->alloc`, so that
neither `mp_2expt`'s `mp_grow` nor `mp_mul_2`'s reallocates (D5). Here nothing about room: `mp_2expt(a, e)`
grows `a` (`Std.mp2exptG`) and each pass's `mp_mul_2(a, a)` may re-place it (`Std.mul2Hc`);
`s_mp_sub(a, b, a)` after `|a| ≥ |b|` never grows (`Std.sSubA`). The frame is `Api/ReduxG.lean`'s for this
function's regions (`a` written, `b` read): the site is `a`'s digit array, the result `(ok, q, a')` with
`a'`'s digits at `q` (`MP_MEM`: `a` as the code left it, at its block), `Out` the reductions' (shape, live,
placed; on `MP_OKAY` `Mont.NormPost b a'`: `a' = radix^b->used mod b` by `NormPost.spec`).

What it needs (`Res`): `b` a Montgomery modulus (valid, odd, `> 1`), `28 b->used < 2^31` (the C's `int`s:
`mp_count_bits(b)`, the exponent), `a` shaped and live. Memory changes only in the stack `[sp - 656, sp)` (the
64-byte frame and `mp_2expt`'s 592; `mp_mul_2` 576), `a` and the allocator's footprint.
-/

namespace Tom.Machine.Api.MontNormG

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x800058b4#64

/-- The stack depth: the 64-byte frame and `mp_2expt`'s 592 (the deepest callee; `F_eq`), a literal so
that callers' layout checks (`iv_omega`) see it. -/
abbrev F : Nat := 656

theorem F_eq : F = 64 + Expt2G.F := rfl

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt
  H : List (Nat × Nat)

inductive R | stk | aS | aD | bS | bD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .code] := by cases r <;> simp

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - 656, 656⟩
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

def isW : R → Bool
  | .stk | .aS | .aD => true
  | _ => false

def ws : List R := [.stk, .aS, .aD]

/-- `(ok, q, a')`: `a'`'s digits at `q`. -/
abbrev X : Type := ReduxG.X

def out (p : P) : X → R → Kind
  | (_, q, a'), .aS => .mpS p.pa q a'
  | (_, q, a'), .aD => .mpD q a'.alloc a'.digit
  | _, r => kind p r

def site' (_ : P) : X → Iv
  | (_, q, a') => ⟨q, 4 * a'.alloc⟩

/-- `a`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.adp p.a :: p.H

def hout (p : P) : X → List (Nat × Nat)
  | (_, q, a') => (q, 4 * a'.alloc) :: p.H

/-- The arguments: `a0 = a`, `a1 = b` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpInit.memBV)]

/-- What `mp_montgomery_calc_normalization(a, b)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_2expt` zeroes and grows `a`; `mp_set` writes it. -/
  sa : p.a.Shape
  /-- `b` a Montgomery modulus. -/
  vb : p.b.Valid
  odd : p.b.mag % 2 = 1
  gt1 : 1 < p.b.mag
  /-- The C's `int`s: `mp_count_bits(b)` and the exponent `28 (b->used - 1) + bits - 1`. -/
  bits : Layout.digitBits * p.b.used < 2 ^ 31
  /-- `a`'s digits are `realloc`'s block: live and nonempty. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

/-- What `a` holds after: shaped, live, placed (inside the old block or a fresh one); on `MP_OKAY`
`Mont.NormPost b a'`. -/
structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) (lay p .aD) (site' p x)
  post : x.1 = true → Mont.NormPost p.b x.2.2

def Q (p : P) (x : X) : Prop := Out p x

/-- **`mp_montgomery_calc_normalization(a, b)` on the machine, `a` growing**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MontNormG
