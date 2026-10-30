import Tom.Machine.Api.SMpMulDigs
import Tom.Machine.Api.MulFastH

/-!
# `s_mp_mul_digs(a, b, a, digs)` and the growing `s_mp_mul_digs_fast(a, b, a, digs)`

The two schoolbook callees of `mp_mul(a, b, a)` (`Api/MpMulA.lean`) in place: regions
`stk aS aD bS bD code` (written `stk aS aD`), the site `a`'s digit array; `a0 = a2 = a`, `a1 = b`.

* `SMpMulDigsA`: `Api/SMpMulDigs.lean` with `c = a`, **off the fast path** only: the slow path
  builds the product in its temporary `t` (reading `a`, `b`), clamps it, `mp_exch(&t, a)` and
  `mp_clear(&t)` frees `a`'s old digits. `mp_mul` calls it only when its own test
  (`digs < 512 ∧ min ≤ 256`) fails, which implies `¬ Fast` (`min < 256`): the residue's `slow`.
* `MulFastHA`: `Api/MulFastH.lean` with `c = a`: `mp_grow(a, digs)` may re-place `a`'s digits;
  the column loop reads `a` (at its block after the grow) and `b` into `W` before the copy loop
  writes `a`.

Both are proved: `Fn.SMpMulDigsAG5.correct` (`Fn/SMpMulDigsAMainG.lean`) and
`Fn.MulFastGAG5.correct` (`Fn/MulFastGAMainG.lean`).
-/

namespace Tom.Machine.Api.SMpMulDigsA

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.SMpMulDigs (entry Fast)

/-- The stack depth (`SMpMulDigs.F`: the slow path's 176 and `mp_init_size`'s 576 fit). -/
abbrev F : Nat := 2192

inductive R | stk | aS | aD | bS | bD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .code] := by cases r <;> simp

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  digs : Nat
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
  | none => ⟨p.adp, 4 * p.a.alloc⟩
  | some (q, a') => ⟨q, 4 * a'.alloc⟩

/-- `a`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.adp p.a :: p.H

def hout (p : P) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => hin p
  | some (q, a') => (q, 4 * a'.alloc) :: p.H

/-- The arguments: `a0 = a2 = a`, `a1 = b`, `a3 = digs`. -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
   (12, BitVec.ofNat 64 p.pa), (13, BitVec.ofNat 64 p.digs)]

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.isSome then 0#64 else MpInit.memBV)]

/-- What `s_mp_mul_digs(a, b, a, digs)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The operands are read (as `SMpMulDigs.Res.sa`/`sb`); `a`'s value is replaced. -/
  sa : p.a.Shape
  sb : p.b.Shape
  /-- The C's `int digs`, nonnegative. -/
  dg_lt : p.digs < 2 ^ 31
  /-- The C's `int` sums stay small (`SMpMulDigs.Res.uab`). -/
  uab : p.a.used + p.b.used < 2 ^ 30
  /-- Off the fast path (`mp_mul`'s caller test is stronger): no tail call. -/
  slow : ¬ Fast p.a p.b p.digs
  /-- Nonempty digit arrays; `a`'s is a live block that `mp_clear(&t)` frees. -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

/-- What `a` holds after, and where (`SMpMulDigs.Digs`'s slow path). -/
structure Digs (p : P) (q : Nat) (a' : MpInt) : Prop where
  valid : a'.Valid
  mag : a'.mag = (p.a.mag * p.b.mag) % radix ^ p.digs
  alloc : a'.alloc = initPrec p.digs
  sign : a'.sign = Layout.mpZpos

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (q, a') => Digs p q a'

/-- **`s_mp_mul_digs(a, b, a, digs)` on the machine** (off the fast path; proved: `Fn.SMpMulDigsAG5.correct`). -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.SMpMulDigsA

namespace Tom.Machine.Api.MulFastHA

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.SMpMulDigsA (R P kind isW ws args)
open Tom.Machine.Api.MpMul (X)
open Tom.Machine.Api.MulFastH (entry)

/-- The stack depth (`MulFastH.F`). -/
def F : Nat := 2736

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .code => textIv

def out (p : P) : X → R → Kind
  | (_, q, a'), .aS => .mpS p.pa q a'
  | (_, q, a'), .aD => .mpD q a'.alloc a'.digit
  | _, r => kind p r

def site' (_ : P) : X → Iv
  | (_, q, a') => ⟨q, 4 * a'.alloc⟩

def hin (p : P) : List (Nat × Nat) := digBlk p.adp p.a :: p.H

def hout (p : P) : X → List (Nat × Nat)
  | (_, q, a') => (q, 4 * a'.alloc) :: p.H

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpInit.memBV)]

/-- What `s_mp_mul_digs_fast(a, b, a, digs)` needs (`MulFastH.Res` in place). -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 2736
  sa : p.a.Shape
  sb : p.b.Shape
  /-- The fast path keeps `a`'s sign word for a nonzero result. -/
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  /-- `MulFast.Cond`: `digs < MP_WARRAY`, `min ≤ MP_MAXFAST`, the `int` sums. -/
  cond : Api.MulFast.Cond p.a p.b p.digs
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

/-- What `a` holds after (`MulFastH.Out` over the old `a`, `b`). -/
structure Out (p : P) (ok : Bool) (a' : MpInt) : Prop where
  shape : a'.Shape
  sign : a'.sign = Layout.mpZpos ∨ a'.sign = Layout.mpNeg
  pos : 0 < a'.alloc
  mag : ok = true → a'.mag = (p.a.mag * p.b.mag) % radix ^ p.digs
  top : ok = true → 0 < a'.used → a'.digit (a'.used - 1) ≠ 0
  /-- `a`'s block kept or grown. -/
  grow : p.a.alloc ≤ a'.alloc
  /-- A nonnegative `a` stays nonnegative. -/
  zsign : p.a.sign = Layout.mpZpos → a'.sign = Layout.mpZpos

def Q (p : P) : X → Prop
  | (ok, _, a') => Out p ok a'

/-- **`s_mp_mul_digs_fast(a, b, a, digs)` with growth** (proved: `Fn.MulFastGAG5.correct`). -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MulFastHA
