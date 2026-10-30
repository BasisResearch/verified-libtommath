import Tom.Machine.Api.StdHeapFn
import Tom.Spec.MulAlgo
import Tom.Spec.Init

/-!
# `mp_sqr(a, b)`, `b` distinct from `a`: the allocating contract

`vendor/libtommath/bn_mp_sqr.c`, compiled at `0x80006410` (37 instructions, frame 16): on
`a->used ≥ TOOM_SQR_CUTOFF` (`0x800194f0`, 400) `s_mp_toom_sqr(a, b)`, else on
`a->used ≥ KARATSUBA_SQR_CUTOFF` (`0x800194f8`, 120) `s_mp_karatsuba_sqr(a, b)`, else
(`2 a->used + 1 < MP_WARRAY` and `a->used < MP_MAXFAST / 2` hold below 120)
`s_mp_sqr_fast(a, b)` (the `s_mp_sqr` branch is dead at these cut-offs); then
`b->sign := MP_ZPOS`, whatever the callee returned.

The algorithms may re-place `b`'s digits (`mp_add` into `b` grows it), so the contract is an
allocating one with site `b`'s digit array, at a block `q` after. The cut-offs are mutable
`.sdata` words (the image's initial values; the harness never writes them): one-word read-only
regions `ks`, `ts`, and `mp_mul`'s `km`, `tm` (`KARATSUBA_MUL_CUTOFF` `0x800194fc`, 80,
`TOOM_MUL_CUTOFF` `0x800194f4`, 350), which `s_mp_toom_sqr`'s `mp_mul` reads.

The recursion:
karatsuba and toom call `mp_sqr` on operands of smaller `a->used`. The stack depth is linear
in `a->used`: `Fs n = 2224 + 8 n` (the leaf `mp_sqr`'s 16 and `s_mp_sqr_fast`'s 2208;
a level costs `16 + 192` bytes (karatsuba) and the measure drops by at least 59).

Result `(ok, q, b')`: `b'` at `q`; `ok` the `MP_OKAY` return (`MP_MEM` else). On `MP_MEM`
`b'` is only shaped, with a live block (toom uses `b` as a temporary).
-/

namespace Tom.Machine.Api.MpSqr

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x80006410#64

/-- The cut-off words (`nm c/tommath-arith.elf`). -/
abbrev ksAddr : Nat := 0x800194f8
abbrev tsAddr : Nat := 0x800194f0
abbrev kmAddr : Nat := 0x800194fc
abbrev tmAddr : Nat := 0x800194f4

/-- Their contents. -/
def ksV : Nat → Nat := fun _ => 120
def tsV : Nat → Nat := fun _ => 400
def kmV : Nat → Nat := fun _ => 80
def tmV : Nat → Nat := fun _ => 350

/-- The stack depth at `a->used = n`. -/
def Fs (n : Nat) : Nat := 2224 + 8 * n

inductive R | stk | aS | aD | bS | bD | ks | ts | km | tm | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .ks, .ts, .km, .tm, .code] := by
  cases r <;> simp

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt
  H : List (Nat × Nat)

/-- The stack depth (`lay`'s stack interval spells it out: interval normalisation computes it). -/
def F (p : P) : Nat := Fs p.a.used

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - (2224 + 8 * p.a.used), 2224 + 8 * p.a.used⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .ks => ⟨ksAddr, 4⟩
  | .ts => ⟨tsAddr, 4⟩
  | .km => ⟨kmAddr, 4⟩
  | .tm => ⟨tmAddr, 4⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .bS => .mpS p.pb p.bdp p.b
  | .bD => .mpD p.bdp p.b.alloc p.b.digit
  | .ks => .mpD ksAddr 1 ksV
  | .ts => .mpD tsAddr 1 tsV
  | .km => .mpD kmAddr 1 kmV
  | .tm => .mpD tmAddr 1 tmV
  | .code => .code

/-- The result: `MP_OKAY`?, `b'`'s digits at `q`, `b'`. -/
abbrev X : Type := Bool × Nat × MpInt

def out (p : P) : X → R → Kind
  | (_, q, b'), .bS => .mpS p.pb q b'
  | (_, q, b'), .bD => .mpD q b'.alloc b'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .bS | .bD => true
  | _ => false

def ws : List R := [.stk, .bS, .bD]

def site' (_ : P) : X → Iv
  | (_, q, b') => ⟨q, 4 * b'.alloc⟩

/-- `b`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.bdp p.b :: p.H

/-- After: `b'`'s block in front (`b`'s own, or the one it was re-placed at). -/
def hout (p : P) : X → List (Nat × Nat)
  | (_, q, b') => (q, 4 * b'.alloc) :: p.H

/-- The arguments: `a0 = a`, `a1 = b` (`gp` for the allocator and the cut-offs). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpInit.memBV)]

/-- What `mp_sqr(a, b)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp (F p)
  /-- The algorithms read `a`'s value; karatsuba's halves are valid because `a` is. -/
  va : p.a.Valid
  /-- `b` is written (in place, or exchanged with a temporary and freed): shaped. -/
  sb : p.b.Shape
  /-- `s_mp_sqr_fast` keeps `b`'s sign word for a nonzero result (`SqrFastPost.spec`). -/
  bsign : p.b.sign = Layout.mpZpos ∨ p.b.sign = Layout.mpNeg
  /-- The C's `int` arithmetic on `a->used` (`2 a->used`, `slliw` at `6434`; karatsuba's
  `mp_init_size(&t1, a->used * 2)`). -/
  au : p.a.used < 2 ^ 29
  /-- D5 for the comba path: `s_mp_sqr_fast` would `mp_grow` `b` otherwise. -/
  room : p.a.used < 120 → 2 * p.a.used ≤ p.b.alloc
  /-- Nonempty digit arrays (`HContract.pos`); `b`'s is a live block that may be freed. -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

/-- What `b` holds after (`x = (ok, q, b')`). -/
structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  /-- `b->sign := MP_ZPOS` at the end, on every path. -/
  sign : x.2.2.sign = Layout.mpZpos
  pos : 0 < x.2.2.alloc
  /-- `MP_OKAY`: the square (`Tom/Spec/MulAlgo.lean`). -/
  post : x.1 = true → SqrPost p.a x.2.2
  /-- Where `b'`'s digits are (`HPost.place`, restated for a caller that passes the site on). -/
  place : Place (hin p) (lay p .bD) (site' p x)
  /-- `b`'s digits only grow (`mp_grow`; a caller's D5 room for a later call survives). -/
  grow : p.b.alloc ≤ x.2.2.alloc

def Q (p : P) (x : X) : Prop := Out p x

/-- The contract at one `p`, for a residue `Rs` (`Api/SqrRec.lean` adds the induction hypothesis). -/
def SpecR (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .bD (out p x) (site' p x) (hin p) (hout p x) m M)

def Spec (p : P) : Prop := SpecR Res p

/-- **`mp_sqr(a, b)` on the machine**, as an allocating contract. -/
def Statement : Prop := ∀ p : P, Spec p

end Tom.Machine.Api.MpSqr
