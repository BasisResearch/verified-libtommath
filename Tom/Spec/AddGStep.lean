import Tom.Spec.SAddGStep
import Tom.Spec.SSubGStep

/-!
# `mp_add(a, b, c)` with growth: the branch's sign and size

`mp_add` stores `c->sign` (`addSign`) and tail-calls `s_mp_add` or `s_mp_sub`, which grow the
destination to `addSize` when short. `AddG a b S L G`: what holds in each branch (`S`: equal
signs, `L`: `|a| < |b|`, `G`: otherwise), each the tail callee's post.
-/

namespace Tom

open MpInt

/-- The sign `mp_add(a, b, c)` gives `c` before its tail call. -/
def addSign (a b : MpInt) : Nat :=
  if a.sign = b.sign then a.sign else if a.mag < b.mag then b.sign else a.sign

/-- The size the tail callee grows `c` to (when `c->alloc` is less). -/
def addSize (a b : MpInt) : Nat :=
  if a.sign = b.sign then max a.used b.used + 1 else if a.mag < b.mag then b.used else a.used

/-- What `mp_add` leaves, by branch. -/
structure AddG (a b : MpInt) (S L G : Prop) : Prop where
  same : a.sign = b.sign → S
  lt : a.sign ≠ b.sign → a.mag < b.mag → L
  ge : a.sign ≠ b.sign → ¬ a.mag < b.mag → G

theorem addSign_same {a b : MpInt} (h : a.sign = b.sign) : addSign a b = a.sign := by simp [addSign, h]
theorem addSign_lt {a b : MpInt} (h : a.sign ≠ b.sign) (hl : a.mag < b.mag) : addSign a b = b.sign := by
  simp [addSign, h, hl]
theorem addSign_ge {a b : MpInt} (h : a.sign ≠ b.sign) (hl : ¬ a.mag < b.mag) : addSign a b = a.sign := by
  simp [addSign, h, hl]
theorem addSize_same {a b : MpInt} (h : a.sign = b.sign) : addSize a b = max a.used b.used + 1 := by
  simp [addSize, h]
theorem addSize_lt {a b : MpInt} (h : a.sign ≠ b.sign) (hl : a.mag < b.mag) : addSize a b = b.used := by
  simp [addSize, h, hl]
theorem addSize_ge {a b : MpInt} (h : a.sign ≠ b.sign) (hl : ¬ a.mag < b.mag) : addSize a b = a.used := by
  simp [addSize, h, hl]

theorem MpInt.Shape.withSign {a : MpInt} (ha : a.Shape) (s : Nat) : (a.withSign s).Shape :=
  { len := ha.len, used_le := ha.used_le, alloc_lt := ha.alloc_lt, digit_lt := ha.digit_lt
    high_zero := ha.high_zero }

end Tom
