import Tom.Machine.Api.StdHeapFn
import Tom.Machine.Api.Std_r7a
import Tom.Spec.Radix

/-!
# `mp_to_radix(a, str, maxlen, written, radix)`: the allocating contract

`vendor/libtommath/bn_mp_to_radix.c`, compiled at `0x80001f80` (126 instructions). After
the early exits (`maxlen < 2`: `MP_BUF`; a radix outside `2..64`: `MP_VAL`; `a = 0`:
`"0\0"`), `mp_init_copy(&t, a)` (its struct in the 128-byte frame at `sp - 104`), the `'-'`
and `t.sign = MP_ZPOS` when negative, then per digit `mp_div_d(&t, radix, &t, &d)` in place
(`d` at `sp - 108`) and `*str++ = mp_s_rmap[d]`, until `t = 0` or the room is gone
(`MP_BUF`); then `s_mp_reverse(_s, digs)`, the NUL, `mp_clear(&t)`.

As an allocating contract (the shape of `Api/MpGcd.lean`): the site is the string buffer
`[str, str + maxlen)`, kept in place, of kind `.frz m0` before (`m0` the caller's snapshot of
its bytes) and `.frz B` after, `B` a memory holding the bytes it leaves. The temporary `t`'s
digits are a block allocated (`mp_init_copy`), re-placed (each `mp_div_d`) and freed
(`mp_clear`) inside: the heap's blocks are the same at the end on every path. The outcome
`x = (e, B)`: the return code `e` in `a0` and the buffer's bytes `B`, with
`ToRadixPost a maxlen radix false buf (bytesOf B …) 0 0 e` (`Tom/Spec/Radix.lean`) or
`e = MP_MEM`. The `MP_MEM` outcomes (the Spec, `Tom/Spec/Radix.lean`, takes the callees to
succeed and has none) are both kept as the C has them, with no claim on the bytes:

* `mp_init_copy(&t, a)` fails: `MP_MEM`, nothing written, nothing allocated;
* `mp_div_d(&t, radix, &t, &d)` fails (its `mp_init_size`, `Api/MpDivDI.lean`): `mp_clear(&t)`,
  `MP_MEM`, the sign and the digits so far left in `str`.

Not covered: `written != NULL` (`args` passes `a3 = 0`): the image's only caller (`put`,
`0x80000334`) passes `NULL`; a negative `radix` (`Res.rx_lt`). Memory changes only in the
stack `[sp - 816, sp)` (the 128-byte frame and `mp_div_d`'s 688; `mp_init_copy` 624,
`mp_clear` 544, `s_mp_reverse` none), the string, and the allocator's footprint.
-/

namespace Tom.Machine.Api.MpToRadix

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std Tom.Radix

def entry : BitVec 64 := 0x80001f80#64

inductive R | stk | aS | aD | str | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .str, .code] := by cases r <;> simp

/-- The stack depth: the 128-byte frame and `mp_div_d`'s 688. -/
def F : Nat := 816

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  /-- `str`, its room `maxlen`. -/
  pstr : Nat
  maxlen : Nat
  /-- The C's `int radix` (nonnegative, `Res.rx_lt`). -/
  radix : Nat
  a : MpInt
  /-- The buffer's bytes before (the caller's snapshot). -/
  m0 : Mem
  H : List (Nat × Nat)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .str => ⟨p.pstr, p.maxlen⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .str => .frz p.m0
  | .code => .code

/-- After: the buffer holds the bytes of `x.2`. -/
def out (p : P) (x : Int × Mem) : R → Kind
  | .str => .frz x.2
  | r => kind p r

def isW : R → Bool
  | .stk | .str => true
  | _ => false

def ws : List R := [.stk, .str]

/-- The string stays where it is. -/
def site' (p : P) (_ : Int × Mem) : Iv := lay p .str

def hin (p : P) : List (Nat × Nat) := p.H

/-- After: the same blocks (`t`'s freed on every path). -/
def hout (p : P) (_ : Int × Mem) : List (Nat × Nat) := p.H

/-- The arguments: `a0 = a`, `a1 = str`, `a2 = maxlen`, `a3 = written = NULL`, `a4 = radix`. -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pstr),
   (12, BitVec.ofNat 64 p.maxlen), (13, 0#64), (14, BitVec.ofNat 64 p.radix)]

def rets (_ : P) (x : Int × Mem) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, BitVec.ofInt 64 x.1)]

/-- What `mp_to_radix(a, str, maxlen, NULL, radix)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_init_copy` copies a valid `a`; the digit loop reads its value. -/
  va : p.a.Valid
  /-- `mp_init_copy` reads `a`'s digit block: live and nonempty (`IcRes`). -/
  ablk : digBlk p.adp p.a ∈ p.H
  apos : 0 < p.a.alloc
  /-- `a`'s struct lies off the arena (`IcRes`). -/
  aoff : OffHeap p.pa 24
  /-- The C's `int radix`, nonnegative: the rows (`mtoradix`) take `a4` as a natural number
  below `2^31` (`addiw`/`bltu` on its low word); a negative radix is not covered. -/
  rx_lt : p.radix < 2 ^ 31

/-- The bytes before and after, as `ToRadixPost` reads them. -/
def Q (p : P) (x : Int × Mem) : Prop :=
  ToRadixPost p.a p.maxlen p.radix false (bytesOf p.m0 p.pstr p.maxlen) (bytesOf x.2 p.pstr p.maxlen) 0 0 x.1 ∨
    x.1 = Layout.mpMem

/-- The buffer's bytes at the end, from a snapshot `F` with the same bytes (the generated exits). -/
theorem q_ok {p : P} {F M : Mem} {e : Int} (hb : bytesOf M p.pstr p.maxlen = bytesOf F p.pstr p.maxlen)
    (h : ToRadixPost p.a p.maxlen p.radix false (bytesOf p.m0 p.pstr p.maxlen) (bytesOf F p.pstr p.maxlen) 0 0 e) :
    Q p (e, M) := Or.inl (by rw [hb]; exact h)

theorem q_mem {p : P} {M : Mem} : Q p (Layout.mpMem, M) := Or.inr rfl

/-- **`mp_to_radix(a, str, maxlen, NULL, radix)` on the machine**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .str (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpToRadix
