import Tom.Machine.Api.StdHeapFn
import Tom.Spec.Reduce
import Tom.Spec.Init

/-!
# `s_mp_mul_high_digs(a, b, a, digs)`: the allocating contract, in place

The image's only caller, `mp_reduce`, passes `c = a` (`s_mp_mul_high_digs(&q, mu, &q, um)`),
so this is the contract of the in-place call (`a` read and written, `b` read only and
distinct, D6). For `0 ≤ digs < 2^31`, `a`, `b` shaped, two paths (`Fast`, the C's test
`a->used + b->used + 1 < MP_WARRAY && MP_MIN(a->used, b->used) < MP_MAXFAST`):

* fast (`69e0`–`6a0c`, `6ba4`–`6bb8`): the tail call `s_mp_mul_high_digs_fast(a, b, a, digs)`
  (`Api/MulHighFast.lean`, in place, `MulHighFastPost a b a a' digs`: `a`'s low digits below
  `digs` kept, the high product above), `a->dp` kept (`Place.keep`), no allocation, `MP_OKAY`;
* slow: `mp_init_size(&t, a->used + b->used + 1)` (struct in the frame at `sp - 136`),
  `t.used := a->used + b->used + 1`, the rows from `iy = digs - ix` (`MulHighPost`: the high
  product `highRows`, every `mp_word` sum below `2^57`), `mp_clamp(&t)`, `mp_exch(&t, a)`,
  `mp_clear(&t)` (freeing `a`'s old digits): the site `a->dp` re-placed at the fresh block,
  `a'` valid with sign `MP_ZPOS` and `a'->alloc = initPrec (a->used + b->used + 1)`; on
  `MP_MEM` everything is kept.

Memory changes only in the stack `[sp - 2192, sp)` (the tail-called fast routine's frame; the
slow path's 176 bytes and `mp_init_size`'s 576), `a` and the allocator's footprint. The depth
`F` is a plain `def`.
-/

namespace Tom.Machine.Api.SMpMulHighDigs

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std Tom.Reduce

def entry : BitVec 64 := 0x800069e0#64

inductive R | stk | aS | aD | bS | bD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .code] := by cases r <;> simp

/-- The stack depth: the tail-called `s_mp_mul_high_digs_fast`'s 2192 exceeds the slow path's
`176 + MpInit.Fsize = 752`. -/
def F : Nat := 2192

/-- The C's test for the fast routine. -/
def Fast (a b : MpInt) : Prop := a.used + b.used ≤ 510 ∧ min a.used b.used ≤ 255

instance (a b : MpInt) : Decidable (Fast a b) := inferInstanceAs (Decidable (_ ∧ _))

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

/-- After: `none` on `MP_MEM`, `some (q, a')` with `a'`'s digits at `q` (`q = a->dp` on the
fast path, a fresh block on the slow one). -/
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

/-- `a`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.adp p.a :: p.H

/-- After: the block holding `a'` in front (`a`'s own on the fast path, which then equals `hin`;
`t`'s on the slow path, `a`'s old block freed). -/
def hout (p : P) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => hin p
  | some (q, a') => (q, 4 * a'.alloc) :: p.H

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = c = a`, `a3 = digs` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
   (12, BitVec.ofNat 64 p.pa), (13, BitVec.ofNat 64 p.digs)]

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpInit.memBV | some _ => 0#64)]

/-- What `s_mp_mul_high_digs(a, b, a, digs)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 2192
  sa : p.a.Shape
  sb : p.b.Shape
  /-- The fast path keeps `a`'s sign for a nonzero result: a sign, for `a'` valid. -/
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  /-- The C's `int digs`, nonnegative (`bltz a3` at `69e8`; the rows take `a3` below `2^31`). -/
  dg_lt : p.digs < 2 ^ 31
  /-- `MulHighFast.Cond.dg_le`; on the slow path the empty rows' carry `t.dp[digs] := 0` stays
  inside `t` (`t->alloc ≥ a->used + b->used + 1`). -/
  dg_le : p.digs ≤ p.a.used + p.b.used
  /-- The slow path reads `b->dp + (digs - ix)` for every `ix < a->used`: in bounds only for
  `ix ≤ digs` (`Reduce.highRow`). `mp_reduce` passes `q` with `used ≤ um + 1`. -/
  ua_le : p.a.used ≤ p.digs + 1
  /-- `MulHighFast.Cond.ub_pos`. -/
  ub_pos : 1 ≤ p.b.used
  /-- The C's `int` sums (`a->used + b->used + 1`) stay small. -/
  uab : p.a.used + p.b.used < 2 ^ 30
  /-- D5 on the fast path: `s_mp_mul_high_digs_fast` does not call `mp_grow`
  (`MulHighFast.Pre.room`). -/
  room : Fast p.a p.b → p.a.used + p.b.used ≤ p.a.alloc
  /-- Nonempty digit arrays (`HContract.pos`); `a`'s is freed by `mp_clear(&t)` on the slow path. -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

/-- What `a` holds after, and where. -/
structure Digs (p : P) (q : Nat) (a' : MpInt) : Prop where
  valid : a'.Valid
  /-- The fast path: in place, `s_mp_mul_high_digs_fast`'s Post (`a`'s digits below `digs`
  kept, the high product above). -/
  fast : Fast p.a p.b → q = p.adp ∧ MulHighFastPost p.a p.b p.a a' p.digs
  /-- The slow path: the high product alone, in `t`'s allocation. -/
  slow : ¬ Fast p.a p.b → MulHighPost p.a p.b a' p.digs ∧ a'.alloc = initPrec (p.a.used + p.b.used + 1)

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (q, a') => Digs p q a'

/-- **`s_mp_mul_high_digs(a, b, a, digs)` on the machine**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.SMpMulHighDigs
