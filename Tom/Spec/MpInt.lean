import Tom.Layout

/-!
# The `mp_int` representation

libtommath's `mp_int` (`vendor/libtommath/tommath.h`) is the struct
`{ int used; int alloc; mp_sign sign; mp_digit *dp; }`: `dp[0 .. alloc)` is
the digit array, `dp[0 .. used)` the magnitude in base `2^MP_DIGIT_BIT`,
least significant digit first. `MpInt` is that struct with the digit array
read out as a list; `Shape` and `Valid` are the representation invariants
libtommath's functions assume and keep (`bn.tex` §2.2–2.3 and the comments
of `mp_clamp`, `mp_grow`):

* `Shape`: `used ≤ alloc`, every digit below the radix, and the digits from
  `used` to `alloc` are zero. This is the invariant at every function entry
  and exit, including the intermediate states the low-level routines
  (`s_mp_add` before its `mp_clamp`) pass around.
* `Valid`: `Shape`, the top used digit is nonzero (clamped), the sign is
  `MP_ZPOS` or `MP_NEG`, and zero is never negative.

`mag` is the magnitude in `Nat`, `val` the value in `Int`.
-/

namespace Tom

/-- The radix `2^MP_DIGIT_BIT` (`2^28` for `MP_32BIT`, decision D1). -/
abbrev radix : Nat := 2 ^ Layout.digitBits

/-- Little-endian value of a digit list in base `radix`. -/
def natOf : List Nat → Nat
  | [] => 0
  | d :: ds => d + radix * natOf ds

/-- `Σ_{i<n} dig i * radix^i`. -/
def natUpTo (dig : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => natUpTo dig n + radix ^ n * dig n

/-- An `mp_int`: the struct's integer fields and its digit array
`dp[0 .. alloc)` as a list. -/
structure MpInt where
  used : Nat
  alloc : Nat
  sign : Nat
  digits : List Nat
  deriving Repr, DecidableEq

namespace MpInt

/-- Digit `i` of the array (`dp[i]`), `0` past its end. -/
def digit (a : MpInt) (i : Nat) : Nat := a.digits.getD i 0

/-- The structural invariant. -/
structure Shape (a : MpInt) : Prop where
  len : a.digits.length = a.alloc
  used_le : a.used ≤ a.alloc
  alloc_lt : a.alloc < 2 ^ 31
  digit_lt : ∀ i, a.digit i < radix
  high_zero : ∀ i, a.used ≤ i → a.digit i = 0

/-- The full representation invariant. -/
structure Valid (a : MpInt) : Prop extends Shape a where
  top : 0 < a.used → a.digit (a.used - 1) ≠ 0
  sign_ok : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg
  zero_pos : a.used = 0 → a.sign = Layout.mpZpos

/-- The magnitude: `Σ_{i<used} dp[i] * radix^i`. -/
def mag (a : MpInt) : Nat := natUpTo a.digit a.used

/-- The value. -/
def val (a : MpInt) : Int := if a.sign = Layout.mpNeg then -(a.mag : Int) else a.mag

end MpInt

/-- libtommath's `mp_ord` code of a comparison (`MP_LT`, `MP_EQ`, `MP_GT`). -/
def ordCode : Ordering → Int
  | .lt => Layout.mpLt
  | .eq => Layout.mpEq
  | .gt => Layout.mpGt

end Tom
