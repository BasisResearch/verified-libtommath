import Tom.Machine.Api.Un
import Tom.Machine.Fn.ReadRadixG
import Tom.Spec.Radix

/-!
# `mp_read_radix(a, str, radix)`: the standard contract

From the entry (`0x80001b4c`), `mp_read_radix(a, str, radix)` with `a` shaped,
`str` the bytes `s` (all nonzero) followed by NUL, `0 ≤ radix < 2^31` (the C's
`int radix` when nonnegative) and `a->alloc` large enough for the value of
`|s|` radix-64 digits plus one (so neither `mp_mul_d(a, radix, a)` nor
`mp_add_d(a, y, a)` calls `mp_grow`, D5), returns to `ra` with
`a0 = readRet radix s` and `ReadRadixPost radix s a'` (`ReadRadixPost.spec`:
`a'` valid, `a'.val = readVal radix s`), `a->alloc` and `a->dp` kept, the
callee-saved registers restored, and memory changed only in the stack
`[sp - 160, sp)` (its 80-byte frame and the 80 of `mp_mul_d`; `mp_add_d` on a
nonnegative `a` needs 64, `mp_zero` none) and `a`. The string and the tables
`mp_s_rmap_reverse`, `mp_s_rmap_reverse_sz` (`.rodata`, inside `textIv`, read
through `Img`) are read only.

The model (`Tom/Spec/Radix.lean`) matches the compiled code: case folding only
for `radix ≤ 36` (`blt s4, s2` at `1c30`, `MP_TOUPPER` by `addiw -97`/`zext.b`/
`bltu 25`), `pos = (unsigned)(ch - '(')` (`addiw -40`, zero-extended), the bound
`pos ≤ 88` (`bgeu s5, a5`, with the byte past the table read for `pos = 88`:
`rmapRevPast = 44`, checked against `Code.rodataBytes`), the end test on the
stopping character (`c ≤ 13` and bit `c` of `0x…dbfe` clear: `'\0'`, `'\n'`,
`'\r'`), the sign stored only when `a->used ≠ 0`.

Regions: the stack, `a`'s struct and digits (written), the string (read), the
code (with `.rodata`).
-/

namespace Tom.Machine.Api.ReadRadix

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Radix

def entry : BitVec 64 := 0x80001b4c#64

/-- The stack depth: the 80-byte frame and `mp_mul_d`'s 80 (`mp_add_d(a, y, a)` on `a ≥ 0`:
64, `Api.AddD.StatementInPlacePos`; `mp_zero`: none). -/
abbrev F : Nat := 160

inductive R | stk | aS | aD | str | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .str, .code] := by cases r <;> simp

/-- `a` and the stack written; the string and the code read. -/
def isW : R → Bool
  | .stk | .aS | .aD => true
  | _ => false

def ws : List R := [.stk, .aS, .aD]

/-- The string's region: its bytes and the NUL. -/
def lay (sp pa adp pstr : Nat) (a : MpInt) (s : List Nat) : R → Iv
  | .stk => ⟨sp - F, F⟩
  | .aS => ⟨pa, 24⟩
  | .aD => ⟨adp, 4 * a.alloc⟩
  | .str => ⟨pstr, s.length + 1⟩
  | .code => textIv

/-- `str` holds the bytes `s` before its first NUL. -/
structure StrAt (m : Mem) (pstr : Nat) (s : List Nat) : Prop where
  ram : Ram pstr (s.length + 1)
  /-- Byte `i` of the string. -/
  bytes : ∀ i (h : i < s.length), bytesT1 m (pstr + i) = BitVec.ofNat 8 s[i]
  /-- Every byte before the NUL is a nonzero byte. -/
  byte : ∀ c ∈ s, 0 < c ∧ c < 256
  nul : bytesT1 m (pstr + s.length) = 0#8

/-- What `mp_read_radix(a, str, radix)` needs. -/
structure Pre (m : Mem) (sp pa adp pstr : Nat) (a : MpInt) (s : List Nat) (radix : Nat) (ra : BitVec 64) :
    Prop where
  ra_ : MpAt m pa adp a
  /-- `mp_zero(a)`'s requirement (`Std.mpZero`'s `Res`); `a`'s value is overwritten. -/
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  str : StrAt m pstr s
  /-- The C's `int radix`, nonnegative: the rows (`rradixg`) take `a2` as a natural number
  below `2^31` (`bltu`/`blt`/`bge` on its sign extension); a negative radix is not covered. -/
  rx_lt : radix < 2 ^ 31
  /-- No `mp_grow` (D5): after `k ≤ |s|` digits `a < radix^k ≤ 2^(6k)`, so `a->used + 1 ≤ a->alloc`
  before each `mp_mul_d(a, radix, a)` and `mp_add_d(a, y, a)`. -/
  room : 6 * s.length ≤ Layout.digitBits * (a.alloc - 1)
  rs : Ram (sp - F) F
  sp_al : sp % 16 = 0
  sp_ge : F ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pstr a s) isW

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pstr : Nat) (a : MpInt) (s : List Nat) (radix : Nat) (a' : MpInt) (M : Mem) :
    Prop where
  repr : MpAt M pa adp a'
  /-- Neither callee reallocates (D5). -/
  alloc : a'.alloc = a.alloc
  read : ReadRadixPost (radix : Int) s a' (readRet radix s)
  frame : Frm (lay sp pa adp pstr a s) ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pstr : Nat) (a : MpInt) (s : List Nat) (radix : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofInt 64 (readRet radix s))] M
      v.keepR outp cf ∧
    Post m sp pa adp pstr a s radix a' M

/-- The arguments: `a0 = a`, `a1 = str`, `a2 = radix`. -/
def entryL (ra s0 : BitVec 64) (sp pa pstr radix : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pstr),
   (12, BitVec.ofNat 64 radix)]

/-- **`mp_read_radix` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pstr radix : Nat} {a : MpInt} {s : List Nat}
    {ra s0 : BitVec 64}, Pre m sp pa adp pstr a s radix ra →
    Triple (At entry (entryL ra s0 sp pa pstr radix) m v.keepR outp)
      (Ret m v outp sp pa adp pstr a s radix ra s0)

end Tom.Machine.Api.ReadRadix
