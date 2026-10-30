import Tom.Machine.Api.MpSqrAF
import Tom.Machine.Kit.Widen

/-!
# `mp_sqr(a, a)` at any size, growing `a`

`Api/MpSqrAF.lean` without `small`: below `KARATSUBA_SQR_CUTOFF` the comba path grows `a`
(`Std.sqrFastGA`); at and above it Karatsuba and Toom square into temporaries and add into `a`
(`mp_add` grows), so `Api/MpSqrA.lean`'s `room` is vacuous there. Regions, results, site and the
stack depth (`MpSqrAF.F = 2768 + 8 a->used`, above `MpSqrA.F`'s `2224 + 8 a->used`) are
`MpSqrAF`'s. `Spec.ofComba`/`Spec.ofGroup` derive the contract at one `p` from the comba path's statement
below the cut-off and from the group's above it (its shallower stack widened, `Kit/Widen.lean`);
`Fn/MpSqrAGClosed.lean` applies them to the proofs.
-/

namespace Tom.Machine.Api.MpSqrAG

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpSqr (entry)
open Tom.Machine.Api.MpSqrA (P R kind out isW ws site' hin hout args rets)
open Tom.Machine.Api.MpSqrAF (lay)

/-- What `mp_sqr(a, a)` needs at any size: `MpSqrAF.Res` without `small`. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp (MpSqrAF.F p)
  va : p.a.Valid
  /-- The C's `int` arithmetic on `a->used`. -/
  au : p.a.used < 2 ^ 29
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

/-- The contract at one `p`. -/
def Spec (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ MpSqrA.Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

/-- **`mp_sqr(a, a)` at any size, growing `a`.** -/
def Statement : Prop := ∀ p : P, Spec p

/-- Below `KARATSUBA_SQR_CUTOFF`, the comba path's growing contract. -/
theorem Spec.ofComba {p : P} (hs : p.a.used < 120) (st : MpSqrAF.Statement) : Spec p :=
  fun hra hres => st p hra ⟨hres.stk, hres.va, hres.au, hs, hres.apos, hres.aoff⟩

/-- At and above it, the in-place contract (`room` vacuous) over its shallower stack, widened. -/
theorem Spec.ofGroup {p : P} (hs : ¬ p.a.used < 120) (st : MpSqrA.Statement) : Spec p :=
  fun hra hres hS hB hH hoff => Triple.widenCv (fun hS' hB' hoff' => st p hra ⟨hres.stk.mono
      (by unfold MpSqrAF.F MpSqrA.F MpSqr.Fs; omega), hres.va, hres.au, fun h => absurd h hs, hres.apos, hres.aoff⟩
      hS' hB' hH hoff') id (fun _ _ _ h => h) (fun _ h => h) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) .stk (by decide)
    (fun r e => by cases r <;> first | exact absurd rfl e | rfl)
    (hres.stk.sub (by unfold MpSqrAF.F; omega)) rfl (fun ⟨_, _, _⟩ => rfl)
    (by show 0 < 2224 + 8 * p.a.used; omega) hS hB hoff

end Tom.Machine.Api.MpSqrAG
