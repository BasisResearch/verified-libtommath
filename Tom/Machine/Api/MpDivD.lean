import Tom.Machine.Api.StdHeapFn
import Tom.Spec.DivD
import Tom.Spec.Init

/-!
# `mp_div_d(a, b, c, d)`: the allocating contract

`c = a / b` truncated toward zero and `*d = |a| mod b` (`Tom/Spec/DivD.lean`: `DivDQuot`,
`DivDRem`), for `a` valid, `c` shaped, live and distinct from `a` (D6), `d` a 4-byte slot
off the allocator, `0 ≤ b < radix`. The paths (`bn_mp_div_d.c`, `0x80005388`, 131
instructions):

* `b = 0`: returns `MP_VAL`, nothing written (`x = none`);
* `b = 1` or `a = 0`: `*d := 0`, the tail call `mp_copy(a, c)` (in place: `Place.keep`);
* `b = 2^k`: the scan `ix := 1; while (ix < 28 && b != 1 << ix) ix++` finds `k`,
  `*d := a->dp[0] & (b - 1)`, the tail call `mp_div_2d(a, k, c, NULL)` (in place);
* `b = 3`: the tail call `s_mp_div_3(a, c, d)` (`Std.sMpDiv3`);
* otherwise: `mp_init_size(&q, a->used)` (struct in the 112-byte frame), `q.used`, `q.sign`
  from `a`, the long division from the top digit (`w = (w << 28) | a->dp[ix]`, the digit
  `w / b` by `__udivdi3`, `w -= t * b` by `__muldi3` when `w ≥ b`), `*d := w`,
  `mp_clamp(&q)`, `mp_exch(&q, c)`, `mp_clear(&q)` (freeing `c`'s old digits): the site
  `c->dp` re-placed at the fresh block (`Place.fresh`); on `MP_MEM` everything is kept.

`*d` after a non-`MP_VAL`, non-`MP_MEM` return: the remainder as a one-digit array
(`rem p = |a| mod b`). Memory changes only in the stack `[sp - 688, sp)` (the 112-byte
frame and `mp_init_size`'s 576; `s_mp_div_3` needs 656, `mp_div_2d` 96, `mp_copy` 32), `c`,
`*d` and the allocator's footprint.

Not covered (named `Res` fields): `c = NULL` (`mp_mod_d`, not in the image), `d = NULL`
(the image's only caller, `mp_to_radix`, passes `&d`), `b ≥ radix`. The image's caller
passes `c = a` (`mp_div_d(&t, radix, &t, &d)`): that aliasing is not this contract (D6).
-/

namespace Tom.Machine.Api.MpDivD

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

def entry : BitVec 64 := 0x80005388#64

inductive R | stk | aS | aD | cS | cD | dS | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .cS, .cD, .dS, .code] := by cases r <;> simp

/-- The stack depth: the 112-byte frame and `mp_init_size`'s 576 (above `s_mp_div_3`'s 656). -/
def F : Nat := 688

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pc : Nat
  cdp : Nat
  pd : Nat
  a : MpInt
  c : MpInt
  /-- The divisor `b` (an `mp_digit`). -/
  v : Nat
  H : List (Nat × Nat)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .cS => ⟨p.pc, 24⟩
  | .cD => ⟨p.cdp, 4 * p.c.alloc⟩
  | .dS => ⟨p.pd, 4⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .cS => .mpS p.pc p.cdp p.c
  | .cD => .mpD p.cdp p.c.alloc p.c.digit
  | .dS => .ram
  | .code => .code

/-- The remainder `|a| mod b`. -/
abbrev rem (p : P) : Nat := p.a.mag % p.v

def out (p : P) : Option (Nat × MpInt) → R → Kind
  | none, r => kind p r
  | some (q, c'), .cS => .mpS p.pc q c'
  | some (q, c'), .cD => .mpD q c'.alloc c'.digit
  | some _, .dS => .mpD p.pd 1 (fun _ => rem p)
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
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.v),
   (12, BitVec.ofNat 64 p.pc), (13, BitVec.ofNat 64 p.pd)]

/-- `MP_VAL`. -/
abbrev valBV : BitVec 64 := 0xfffffffffffffffd#64

/-- The return code: `MP_VAL` for `b = 0`, `MP_MEM` when `mp_init_size` (or
`s_mp_div_3`'s) fails, else `MP_OKAY`. -/
def retv (p : P) (x : Option (Nat × MpInt)) : BitVec 64 :=
  if p.v = 0 then valBV else match x with | none => MpInit.memBV | some _ => 0#64

def rets (p : P) (x : Option (Nat × MpInt)) (ra : BitVec 64) : GRegs := [(1, ra), (10, retv p x)]

/-- What `mp_div_d(a, b, c, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  sc : p.c.Shape
  apos : 0 < p.a.alloc
  cpos : 0 < p.c.alloc
  aoff : OffHeap p.pa 24
  coff : OffHeap p.pc 24
  /-- `c != NULL`: the `c == NULL` paths (`mp_mod_d`, not in the image) are not covered. They
  need `s_mp_div_3` with `c = NULL` and the branches that
  skip `mp_copy`/`mp_div_2d`/`mp_clamp`/`mp_exch`. -/
  c_nn : p.pc ≠ 0
  /-- `d != NULL`: the `d == NULL` branches (`53a4`, `5540`, `54d8`) are not covered; the
  image's only caller (`mp_to_radix`) passes `&d`. -/
  d_nn : p.pd ≠ 0
  d_al : p.pd % 4 = 0
  doff : OffHeap p.pd 4
  /-- `b` is a digit: the power-of-two scan stops at `MP_DIGIT_BIT` (`b = 2^29` would shift
  by 28), and the long division's `w * 2^28 + a[i]` fits an `mp_word` for `b ≤ 2^32`. -/
  v_lt : p.v < radix
  /-- D5: `mp_copy(a, c)` and `mp_div_2d(a, k, c, NULL)` do not call `mp_grow`. -/
  room : p.a.used ≤ p.c.alloc

/-- `c` after (non-`NULL`; `DivDQuot`, by path) and nothing on `MP_VAL`/`MP_MEM`. -/
def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (_, c') => DivDQuot p.a p.v p.c c'

/-- **`mp_div_d(a, b, c, d)` on the machine**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpDivD
