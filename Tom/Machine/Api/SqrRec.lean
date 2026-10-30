import Tom.Machine.Api.MpSqrA

/-!
# The squaring group's recursion

`mp_sqr` calls karatsuba and toom on the same operand; they call `mp_sqr` (as
`mp_sqr(a, b)` or `mp_sqr(a, a)`) on operands with fewer digits. The measure is `a->used`;
the induction hypothesis is the two contracts below a bound:

* `SqrAt n`: both contracts at every `p` with `a->used = n`;
* `SqrBelow n`: `SqrAt k` for every `k < n`.

A function of the group proves its contract with `ih : SqrBelow a->used` in its residue, so
its generated assembly calls `mp_sqr` through an `HContract` whose own residue carries the
bound (`Api/Std_r6h.lean`, `sqrB`): no theorem parameter. `mp_sqr`'s proof is such a
contract (`ResI`, `AResI`), and `close` turns the two into `Api.MpSqr.Statement` and
`Api.MpSqrA.Statement` by strong induction.
-/

namespace Tom.Machine.Api.SqrRec

open Tom.Machine Tom.Machine.Api

/-- Both `mp_sqr` contracts at measure `n`. -/
def SqrAt (n : Nat) : Prop :=
  (∀ p : MpSqr.P, p.a.used = n → MpSqr.Spec p) ∧ (∀ p : MpSqrA.P, p.a.used = n → MpSqrA.Spec p)

/-- **The induction hypothesis**: both contracts below measure `n`. -/
def SqrBelow (n : Nat) : Prop := ∀ k, k < n → SqrAt k

theorem SqrBelow.mono {n n' : Nat} (h : SqrBelow n) (hn : n' ≤ n) : SqrBelow n' :=
  fun k hk => h k (Nat.lt_of_lt_of_le hk hn)

/-- `mp_sqr(a, b)` below the bound. -/
theorem SqrBelow.sqr {n : Nat} (h : SqrBelow n) {p : MpSqr.P} (hp : p.a.used < n) : MpSqr.Spec p :=
  (h _ hp).1 p rfl

/-- `mp_sqr(a, a)` below the bound. -/
theorem SqrBelow.sqrA {n : Nat} (h : SqrBelow n) {p : MpSqrA.P} (hp : p.a.used < n) : MpSqrA.Spec p :=
  (h _ hp).2 p rfl

/-- `mp_sqr(a, b)`'s residue with the induction hypothesis at its own measure. -/
structure ResI (p : MpSqr.P) : Prop extends MpSqr.Res p where
  ih : SqrBelow p.a.used

/-- `mp_sqr(a, a)`'s residue with the induction hypothesis. -/
structure AResI (p : MpSqrA.P) : Prop extends MpSqrA.Res p where
  ih : SqrBelow p.a.used

/-- What `mp_sqr`'s assembly proves: its contract given the hypothesis. -/
def StatementI : Prop := ∀ p : MpSqr.P, MpSqr.SpecR ResI p

def StatementAI : Prop := ∀ p : MpSqrA.P, MpSqrA.SpecR AResI p

/-- **The closing induction.** -/
theorem close (hI : StatementI) (hA : StatementAI) : MpSqr.Statement ∧ MpSqrA.Statement := by
  have h : ∀ n, SqrAt n := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      refine ⟨fun p hp => ?_, fun p hp => ?_⟩
      · intro m v outp ra hra hres
        exact hI p hra { toRes := hres, ih := hp ▸ ih }
      · intro m v outp ra hra hres
        exact hA p hra { toRes := hres, ih := hp ▸ ih }
  exact ⟨fun p => (h _).1 p rfl, fun p => (h _).2 p rfl⟩

end Tom.Machine.Api.SqrRec
