import Tom.Machine.Api.StdHeapFn
import Tom.Machine.Fn.SMpMulDigsG
import Tom.Spec.Mul
import Tom.Spec.Init

/-!
# `s_mp_mul_digs(a, b, c, digs)`: the allocating contract (fresh set; over `Kit/MeetHeap.lean`)

`|c| = |a| |b| mod radix^digs`, for `0 ≤ digs < 2^31` (the C's `int digs` when
nonnegative; `digs < 0` returns `MP_VAL`, not covered), `a`, `b` shaped (they
are read only and may be the same `mp_int`), `c` shaped, live and distinct from
both (D6). Two paths (`Fast`):

* `digs < MP_WARRAY = 512` and `min(a->used, b->used) < MP_MAXFAST = 256`
  (`40fc`–`4124`): the tail call `s_mp_mul_digs_fast(a, b, c, digs)` at `42c4`
  (`Api/MulFast.lean`), which writes `c` in place: with `digs ≤ c->alloc` (D5,
  no `mp_grow`) the site `c->dp` is kept (`Place.keep`), `MulFastPost a b c c' digs`
  (so `c->alloc` kept, `c`'s sign kept unless the result is zero). It needs
  `a->used + b->used < 2^30` (`MulFast.Cond`). No allocation, `MP_OKAY`.
* otherwise: `mp_init_size(&t, digs)` (struct in the frame at `sp - 136`),
  `t.used := digs`, the truncated schoolbook product (HAC 14.12: row `ix` adds
  `a[ix] b[iy]` for `ix + iy < digs`, the last carry stored only below `digs`;
  every `mp_word` sum below `2^57`), `mp_clamp(&t)`, `mp_exch(&t, c)`,
  `mp_clear(&t)` (freeing `c`'s old digits): as `Api/Div3.lean`, the site `c->dp`
  re-placed at the fresh block `q`, `c'` valid with sign `MP_ZPOS` and
  `c'->alloc = initPrec digs`; on `MP_MEM` everything is kept.

Memory changes only in the stack `[sp - 2192, sp)` (the tail-called
`s_mp_mul_digs_fast` runs at `sp` with its 2192 bytes; the slow path needs its
176-byte frame and `mp_init_size`'s 576), `c` and the allocator's footprint.
-/

namespace Tom.Machine.Api.SMpMulDigs

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x800040fc#64

inductive R | stk | aS | aD | bS | bD | cS | cD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .cS, .cD, .code] := by cases r <;> simp

/-- The stack depth: the tail-called `s_mp_mul_digs_fast`'s 2192 (`Api.MulFast`) exceeds the
slow path's `176 + MpInit.Fsize = 752`. -/
abbrev F : Nat := 2192

/-- The C's test for the fast multiplier (`digs < MP_WARRAY && MP_MIN(a->used, b->used) < MP_MAXFAST`). -/
def Fast (a b : MpInt) (digs : Nat) : Prop := digs < 512 ∧ min a.used b.used < 256

instance (a b : MpInt) (digs : Nat) : Decidable (Fast a b digs) := inferInstanceAs (Decidable (_ ∧ _))

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  pc : Nat
  cdp : Nat
  digs : Nat
  a : MpInt
  b : MpInt
  c : MpInt
  H : List (Nat × Nat)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .cS => ⟨p.pc, 24⟩
  | .cD => ⟨p.cdp, 4 * p.c.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .bS => .mpS p.pb p.bdp p.b
  | .bD => .mpD p.bdp p.b.alloc p.b.digit
  | .cS => .mpS p.pc p.cdp p.c
  | .cD => .mpD p.cdp p.c.alloc p.c.digit
  | .code => .code

/-- After: `none` on `MP_MEM`, `some (q, c')` with `c'`'s digits at `q` (`q = c->dp` on the
fast path, a fresh block on the slow one). -/
def out (p : P) : Option (Nat × MpInt) → R → Kind
  | none, r => kind p r
  | some (q, c'), .cS => .mpS p.pc q c'
  | some (q, c'), .cD => .mpD q c'.alloc c'.digit
  | some _, r => kind p r

def isW : R → Bool
  | .stk | .cS | .cD => true
  | _ => false

def ws : List R := [.stk, .cS, .cD]

def site' (p : P) : Option (Nat × MpInt) → Iv
  | none => lay p .cD
  | some (q, c') => ⟨q, 4 * c'.alloc⟩

/-- `c`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.cdp p.c :: p.H

/-- After: the block holding `c'` in front (`c`'s own on the fast path, which then equals `hin`;
`t`'s on the slow path, `c`'s old block freed). -/
def hout (p : P) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => hin p
  | some (q, c') => (q, 4 * c'.alloc) :: p.H

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = c`, `a3 = digs` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
   (12, BitVec.ofNat 64 p.pc), (13, BitVec.ofNat 64 p.digs)]

def rets (_ : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpInit.memBV | some _ => 0#64)]

/-- What `s_mp_mul_digs(a, b, c, digs)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  sa : p.a.ShapeU
  sb : p.b.ShapeU
  /-- `s_mp_mul_digs_fast`'s `Pre.sc`; on the slow path `c`'s value is discarded. -/
  sc : p.c.Shape
  /-- The fast path keeps `c`'s sign for a nonzero result: a sign, for `c'` valid. -/
  csign : p.c.sign = Layout.mpZpos ∨ p.c.sign = Layout.mpNeg
  /-- The C's `int digs`, nonnegative (`bltz a3` at `4104`; the rows take `a3` below `2^31`). -/
  dg_lt : p.digs < 2 ^ 31
  /-- `MulFast.Cond.uab`: the C's `int` sums in `s_mp_mul_digs_fast` stay small. -/
  uab : p.a.used + p.b.used < 2 ^ 30
  /-- D5 on the fast path: `s_mp_mul_digs_fast` does not call `mp_grow` (`MulFast.Pre.room`). -/
  room : Fast p.a p.b p.digs → p.digs ≤ p.c.alloc
  /-- Nonempty digit arrays (`HContract.pos`: an empty region inside the arena is not off it). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- `c`'s old digits are freed by `mp_clear(&t)` on the slow path: a live, nonempty block. -/
  cpos : 0 < p.c.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24

/-- What `c` holds after, and where. -/
structure Digs (p : P) (q : Nat) (c' : MpInt) : Prop where
  valid : c'.Valid
  mag : c'.mag = (p.a.mag * p.b.mag) % radix ^ p.digs
  /-- The fast path: in place, `s_mp_mul_digs_fast`'s Post. -/
  fast : Fast p.a p.b p.digs → q = p.cdp ∧ MulFastPost p.a p.b p.c c' p.digs
  /-- The slow path: `t`'s allocation and sign. -/
  slow : ¬ Fast p.a p.b p.digs → c'.alloc = initPrec p.digs ∧ c'.sign = Layout.mpZpos

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (q, c') => Digs p q c'

/-- **`s_mp_mul_digs(a, b, c, digs)` on the machine**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.SMpMulDigs
