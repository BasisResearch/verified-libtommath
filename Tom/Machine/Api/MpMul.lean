import Tom.Machine.Api.StdHeapFn
import Tom.Spec.MulAlgo
import Tom.Spec.Init

/-!
# `mp_mul(a, b, c)`, `c` distinct from `a` and `b`: the allocating contract

Every branch is a call (`s_mp_balance_mul`, `s_mp_toom_mul`, `s_mp_karatsuba_mul`,
`s_mp_mul_digs_fast`, `s_mp_mul_digs`), each of which may re-place `c`'s digits
(`mp_grow`, or `mp_exch` with a temporary), so the site is `c`'s digit array `cD`, at a
block `q` after.

The cut-offs are mutable `.sdata` words (`c/tommath-arith.elf`'s initial values 80 and
350): their regions `kc`, `tc` are one-digit arrays holding those values (`Kind.mpD`), read
only. The stack depth `Fm (a.used + b.used)` is linear in the operand size.

Result `(ok, q, c')`: `c'` at `q`; `ok` the `MP_OKAY` return (`MP_MEM` else). On `MP_MEM`
`c'` is only shaped, with a live block (`s_mp_toom_mul` uses `c` as a temporary).
-/

namespace Tom.Machine.Api.MpMul

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x800018a8#64

/-- `KARATSUBA_MUL_CUTOFF` and `TOOM_MUL_CUTOFF` (`nm c/tommath-arith.elf`). -/
def kcAddr : Nat := 0x800194fc
def tcAddr : Nat := 0x800194f4

/-- The recursion's measure. -/
def μ (a b : MpInt) : Nat := a.used + b.used

/-- The stack depth at measure `n`: the leaf (`mp_mul`'s 32, `s_mp_mul_digs_fast`'s 2192 and the
`mp_grow` it calls at its bottom, `MpGrow.F = 544`) and 8 bytes per digit of the measure. -/
def Fm (n : Nat) : Nat := 2768 + 8 * n

inductive R | stk | aS | aD | bS | bD | cS | cD | kc | tc | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .cS, .cD, .kc, .tc, .code] := by cases r <;> simp

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  pc : Nat
  cdp : Nat
  a : MpInt
  b : MpInt
  c : MpInt
  H : List (Nat × Nat)

def F (p : P) : Nat := Fm (μ p.a p.b)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - (2768 + 8 * (p.a.used + p.b.used)), 2768 + 8 * (p.a.used + p.b.used)⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .cS => ⟨p.pc, 24⟩
  | .cD => ⟨p.cdp, 4 * p.c.alloc⟩
  | .kc => ⟨kcAddr, 4⟩
  | .tc => ⟨tcAddr, 4⟩
  | .code => textIv

/-- The cut-off words' contents. -/
def kcV : Nat → Nat := fun _ => 80
def tcV : Nat → Nat := fun _ => 350

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .bS => .mpS p.pb p.bdp p.b
  | .bD => .mpD p.bdp p.b.alloc p.b.digit
  | .cS => .mpS p.pc p.cdp p.c
  | .cD => .mpD p.cdp p.c.alloc p.c.digit
  | .kc => .mpD kcAddr 1 kcV
  | .tc => .mpD tcAddr 1 tcV
  | .code => .code

/-- The result: `MP_OKAY`?, `c'`'s digits at `q`, `c'`. -/
abbrev X : Type := Bool × Nat × MpInt

def out (p : P) : X → R → Kind
  | (_, q, c'), .cS => .mpS p.pc q c'
  | (_, q, c'), .cD => .mpD q c'.alloc c'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .cS | .cD => true
  | _ => false

def ws : List R := [.stk, .cS, .cD]

def site' (_ : P) : X → Iv
  | (_, q, c') => ⟨q, 4 * c'.alloc⟩

/-- `c`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.cdp p.c :: p.H

/-- After: `c'`'s block in front (`c`'s own, or the one it was re-placed at). -/
def hout (p : P) : X → List (Nat × Nat)
  | (_, q, c') => (q, 4 * c'.alloc) :: p.H

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator and the cut-offs). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
   (12, BitVec.ofNat 64 p.pc)]

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpInit.memBV)]

/-- What `mp_mul(a, b, c)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp (F p)
  /-- The algorithms read the operands' values; karatsuba's halves are valid because `a`, `b` are. -/
  va : p.a.Valid
  vb : p.b.Valid
  /-- `c` is written (grown, or exchanged with a temporary and freed): shaped. -/
  sc : p.c.Shape
  /-- `s_mp_mul_digs_fast` keeps `c`'s sign word for a nonzero result (`Api/SMpMulDigs.lean` `csign`). -/
  csign : p.c.sign = Layout.mpZpos ∨ p.c.sign = Layout.mpNeg
  /-- The C's `int` sums (`digs = a->used + b->used + 1`, `MulFast.Cond.uab`). -/
  uab : μ p.a p.b < 2 ^ 30
  /-- Nonempty digit arrays (`HContract.pos`); `c`'s is a live block that may be freed. -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  cpos : 0 < p.c.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24

/-- `Res` with the operands only `ValidU` (digits at and above `used` arbitrary): what the group
proves (`Api/MulRec.lean`), since `s_mp_balance_mul` multiplies a left-over slice with stale digits. -/
structure ResU (p : P) : Prop where
  stk : StkRes p.sp (F p)
  va : p.a.ValidU
  vb : p.b.ValidU
  sc : p.c.Shape
  csign : p.c.sign = Layout.mpZpos ∨ p.c.sign = Layout.mpNeg
  uab : μ p.a p.b < 2 ^ 30
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  cpos : 0 < p.c.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24

theorem Res.toU {p : P} (h : Res p) : ResU p :=
  ⟨h.stk, h.va.toU, h.vb.toU, h.sc, h.csign, h.uab, h.apos, h.bpos, h.cpos, h.aoff, h.boff, h.coff⟩

/-- What `c` holds after. -/
structure Out (p : P) (ok : Bool) (c' : MpInt) : Prop where
  shape : c'.Shape
  sign : c'.sign = Layout.mpZpos ∨ c'.sign = Layout.mpNeg
  pos : 0 < c'.alloc
  /-- `MP_OKAY`: the product (`Tom/Spec/MulAlgo.lean`). -/
  post : ok = true → MulPost p.a p.b c'

def Q (p : P) : X → Prop
  | (ok, _, c') => Out p ok c'

/-- The contract at one `p`, for a residue `Rs` (`Api/MulRec.lean` adds the induction hypothesis). -/
def SpecR (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

def Spec (p : P) : Prop := SpecR Res p

/-- **`mp_mul(a, b, c)` on the machine**, as an allocating contract. -/
def Statement : Prop := ∀ p : P, Spec p

/-- The contract for operands with stale digits above `used`. -/
def StatementU : Prop := ∀ p : P, SpecR ResU p

theorem StatementU.toStatement (h : StatementU) : Statement :=
  fun p _ _ _ _ hra hres => h p hra hres.toU

end Tom.Machine.Api.MpMul
