import Tom.Machine.Api.MpMulA

/-!
# The multiplication group's recursion

`mp_mul` calls karatsuba, toom and balance on the same operands; they call `mp_mul` (as
`mp_mul(a, b, c)` or `mp_mul(a, b, a)`) on operands of smaller measure
`μ = a.used + b.used`. The induction hypothesis is the two contracts below a bound:

* `MulAt n`: both contracts at every `p` of measure `n`, `mp_mul(a, b, c)`'s for operands
  that are only `ValidU` (`MpMul.ResU`: digits at and above `used` arbitrary), since
  `s_mp_balance_mul` multiplies a left-over slice with stale digits and, nested,
  passes such a slice on as either operand;
* `MulBelow n`: `MulAt k` for every `k < n`.

`MpMul.Res → MpMul.ResU` (`Res.toU`) gives the contract for valid operands back (`MulBelow.mul`).

A function of the group proves its contract with `ih : MulBelow μ` in its residue (a
`Res` field), so its generated assembly calls `mp_mul` through an `HContract` whose own
residue carries the bound (`Api/Std_r6g.lean`, `mpMulB`): no theorem parameter. `mp_mul`'s
proof is such a contract (`ResI`, `AResI`: `Res` and `ih`), and `close` turns the two into
`Api.MpMul.Statement` and `Api.MpMulA.Statement` by strong induction on `μ`.
-/

namespace Tom.Machine.Api.MulRec

open Tom.Machine Tom.Machine.Api

/-- Both `mp_mul` contracts at measure `n`. -/
def MulAt (n : Nat) : Prop :=
  (∀ p : MpMul.P, MpMul.μ p.a p.b = n → MpMul.SpecR MpMul.ResU p) ∧
    (∀ p : MpMulA.P, MpMul.μ p.a p.b = n → MpMulA.Spec p)

/-- **The induction hypothesis**: both contracts below measure `n`. -/
def MulBelow (n : Nat) : Prop := ∀ k, k < n → MulAt k

theorem MulBelow.mono {n n' : Nat} (h : MulBelow n) (hn : n' ≤ n) : MulBelow n' :=
  fun k hk => h k (Nat.lt_of_lt_of_le hk hn)

/-- `mp_mul(a, b, c)` below the bound, operands with stale digits. -/
theorem MulBelow.mulU {n : Nat} (h : MulBelow n) {p : MpMul.P} (hp : MpMul.μ p.a p.b < n) :
    MpMul.SpecR MpMul.ResU p := (h _ hp).1 p rfl

/-- `mp_mul(a, b, c)` below the bound. -/
theorem MulBelow.mul {n : Nat} (h : MulBelow n) {p : MpMul.P} (hp : MpMul.μ p.a p.b < n) :
    MpMul.Spec p := fun hra hres => h.mulU hp hra hres.toU

/-- `mp_mul(a, b, a)` below the bound. -/
theorem MulBelow.mulA {n : Nat} (h : MulBelow n) {p : MpMulA.P} (hp : MpMul.μ p.a p.b < n) :
    MpMulA.Spec p := (h _ hp).2 p rfl

/-- `mp_mul(a, b, c)`'s residue with the induction hypothesis at its own measure. -/
structure ResI (p : MpMul.P) : Prop extends MpMul.ResU p where
  ih : MulBelow (MpMul.μ p.a p.b)

/-- `mp_mul(a, b, a)`'s residue with the induction hypothesis. -/
structure AResI (p : MpMulA.P) : Prop extends MpMulA.Res p where
  ih : MulBelow (MpMul.μ p.a p.b)

/-- What `mp_mul`'s assembly proves: its contract given the hypothesis. -/
def StatementI : Prop := ∀ p : MpMul.P, MpMul.SpecR ResI p

def StatementAI : Prop := ∀ p : MpMulA.P, MpMulA.SpecR AResI p

/-- **The closing induction.** -/
theorem closeU (hI : StatementI) (hA : StatementAI) : MpMul.StatementU ∧ MpMulA.Statement := by
  have h : ∀ n, MulAt n := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      refine ⟨fun p hp => ?_, fun p hp => ?_⟩
      · intro m v outp ra hra hres
        exact hI p hra { toResU := hres, ih := hp ▸ ih }
      · intro m v outp ra hra hres
        exact hA p hra { toRes := hres, ih := hp ▸ ih }
  exact ⟨fun p => (h _).1 p rfl, fun p => (h _).2 p rfl⟩

theorem close (hI : StatementI) (hA : StatementAI) : MpMul.Statement ∧ MpMulA.Statement :=
  ⟨(closeU hI hA).1.toStatement, (closeU hI hA).2⟩

end Tom.Machine.Api.MulRec
