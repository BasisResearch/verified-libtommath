import Tom.Machine.Api.SMpMulDigsAF
import Tom.Machine.Api.SMpMulHighDigsAF
import Tom.Machine.Kit.Widen

/-!
# `mp_reduce`'s in-place schoolbook multipliers on both paths

`s_mp_mul_digs(a, b, a, digs)` and `s_mp_mul_high_digs(a, b, a, digs)` at any size: the fast path's
growing contracts (`Api/SMpMulDigsAF.lean`, `Api/SMpMulHighDigsAF.lean`) and the slow
path's (`Api/SMpMulDigsA.lean`, `Api/SMpMulHighDigs.lean`: the product built in `mp_init_size`'s `t`,
`mp_exch(&t, a)`, `a`'s old block freed; their `room` premise is on the fast path only) under one
residue without the C's fast test. Regions, results `(ok, q, a')`, site and stack depth (2736, the
fast path's with `mp_grow`; the slow paths' 2192 widened, `Kit/Widen.lean`) are the fast path's;
the slow path's `none` (`MP_MEM`, `a` kept) is `(false, a->dp, a)`.

* `SMpMulDigsAG`: `MulFastHA.Out` without `grow` (the slow path's `t` has `initPrec digs` digits).
* `SMpMulHighDigsG`: the high product plus `low`: `a`'s old digits below `digs` on the fast path
  (`MulHighFastPost`), none on the slow one (`MulHighPost`); both below `radix ^ digs`, which is all
  Barrett's `mp_rshd(&q, um + 1)` needs (`ReduceStepG.q3_of`). The slow path reads
  `b->dp + (digs - ix)` only for `ix ≤ digs` (`ua_le`).

`Spec.ofFast`/`Spec.ofSlow` derive the contract at one `p` from the fast path's statement on the fast test and from
the slow path's off it (the slow `Option` result read through `cv`, its stack widened, `Kit/Widen.lean`);
`Fn/SMpMulDigsAGClosed.lean` applies them to the proofs.
-/

namespace Tom.Machine.Api.SMpMulDigsAG

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.SMpMulDigsA (R P kind isW ws args)
open Tom.Machine.Api.MulFastHA (lay out site' hin hout rets)

/-- What `s_mp_mul_digs(a, b, a, digs)` needs on either path. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 2736
  sa : p.a.Shape
  sb : p.b.Shape
  /-- The fast routine keeps `a`'s sign word for a nonzero result. -/
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  /-- The C's `int digs`, nonnegative. -/
  dg_lt : p.digs < 2 ^ 31
  /-- The C's `int` sums stay small. -/
  uab : p.a.used + p.b.used < 2 ^ 30
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

/-- What `a` holds after: `MulFastHA.Out` without `grow`. -/
structure Out (p : P) (ok : Bool) (a' : MpInt) : Prop where
  shape : a'.Shape
  sign : a'.sign = Layout.mpZpos ∨ a'.sign = Layout.mpNeg
  pos : 0 < a'.alloc
  mag : ok = true → a'.mag = (p.a.mag * p.b.mag) % radix ^ p.digs
  top : ok = true → 0 < a'.used → a'.digit (a'.used - 1) ≠ 0
  /-- A nonnegative `a` stays nonnegative. -/
  zsign : p.a.sign = Layout.mpZpos → a'.sign = Layout.mpZpos

def Q (p : P) : Api.MpMul.X → Prop
  | (ok, _, a') => Out p ok a'

/-- The contract at one `p`. -/
def Spec (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At SMpMulDigs.entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

/-- **`s_mp_mul_digs(a, b, a, digs)` on either path, `a` re-placed as needed.** -/
def Statement : Prop := ∀ {p : P}, Spec p

/-- The slow paths' `Option` result as the fast paths' triple: `MP_MEM` keeps `a`. -/
def cv (adp : Nat) (a : MpInt) : Option (Nat × MpInt) → Api.MpMul.X
  | none => (false, adp, a)
  | some (q, a') => (true, q, a')

theorem initPrec_pos (n : Nat) : 0 < initPrec n := by unfold initPrec; rw [minPrec_eq]; omega

/-- On the fast test, the fast path's contract. -/
theorem Spec.ofFast {p : P} (hf : SMpMulDigs.Fast p.a p.b p.digs) (st : SMpMulDigsAF.Statement) : Spec p :=
  fun hra hres hS hB hH hoff => Triple.widenCv (fun hS hB hoff => st hra ⟨hres.stk, hres.sa, hres.sb, hres.asign,
      hres.dg_lt, hres.uab, hf, hres.apos, hres.bpos, hres.aoff, hres.boff⟩ hS hB hH hoff) id (fun _ _ _ h => h)
    (fun ⟨_, _, _⟩ hq => ⟨hq.shape, hq.sign, hq.pos, hq.mag, hq.top, hq.zsign⟩) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) .stk (by decide) (fun _ _ => rfl) (Iv.sub_self _) rfl (fun ⟨_, _, _⟩ => rfl) (by show 0 < 2736; decide)
    hS hB hoff

/-- Off the fast test, the slow path's contract (`room` vacuous), its result through `cv`, its stack widened. -/
theorem Spec.ofSlow {p : P} (hf : ¬ SMpMulDigs.Fast p.a p.b p.digs) (st : SMpMulDigsA.Statement) : Spec p :=
  fun hra hres hS hB hH hoff => Triple.widenCv (fun hS hB hoff => st hra ⟨hres.stk.mono (by decide), hres.sa,
      hres.sb, hres.dg_lt, hres.uab, hf, hres.apos, hres.bpos, hres.aoff, hres.boff⟩ hS hB hH hoff) (cv p.adp p.a)
    (fun o _ _ h => by cases o <;> exact h)
    (fun | none, _ => ⟨hres.sa, hres.asign, hres.apos, nofun, nofun, id⟩
         | some (_, _), (hd : SMpMulDigsA.Digs _ _ _) => ⟨hd.valid.toShape, .inl hd.sign,
            by rw [hd.alloc]; exact initPrec_pos _, fun _ => hd.mag, fun _ => hd.valid.top, fun _ => hd.sign⟩)
    (fun o => funext fun r => by cases o <;> cases r <;> rfl) (fun o => by cases o <;> rfl) (fun o => by cases o <;> rfl)
    .stk (by decide) (fun r e => by cases r <;> first | exact absurd rfl e | rfl) (hres.stk.sub (by decide)) rfl
    (fun ⟨_, _, _⟩ => rfl) (by show 0 < 2192; decide) hS hB hoff

end Tom.Machine.Api.SMpMulDigsAG

namespace Tom.Machine.Api.SMpMulHighDigsG

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std Tom.Reduce
open Tom.Machine.Api.SMpMulHighDigs (R P kind isW ws args Fast)
open Tom.Machine.Api.MulHighFastHA (lay out site' hin hout rets)

/-- What `s_mp_mul_high_digs(a, b, a, digs)` needs on either path. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 2736
  sa : p.a.Shape
  sb : p.b.Shape
  /-- The fast path keeps `a`'s sign for a nonzero result. -/
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  /-- The C's `int digs`, nonnegative. -/
  dg_lt : p.digs < 2 ^ 31
  /-- No column below `digs` past `pa`; on the slow path `t.dp[digs]` inside `t`. -/
  dg_le : p.digs ≤ p.a.used + p.b.used
  /-- The slow path reads `b->dp + (digs - ix)` for `ix < a->used`. -/
  ua_le : p.a.used ≤ p.digs + 1
  ub_pos : 1 ≤ p.b.used
  /-- The C's `int` sums stay small. -/
  uab : p.a.used + p.b.used < 2 ^ 30
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

/-- The digits below `digs` beside the high product: `a`'s old ones on the fast path, none on the
slow one. -/
def low (p : P) : Nat := if Fast p.a p.b then natUpTo p.a.digit p.digs else 0

theorem low_lt {p : P} (sa : p.a.Shape) : low p < radix ^ p.digs := by
  unfold low; split
  · exact natUpTo_lt _ sa.digit_lt _
  · exact Nat.pow_pos radix_pos

/-- What `a` holds after: on `MP_OKAY` the high product plus `low`. -/
structure Out (p : P) (ok : Bool) (a' : MpInt) : Prop where
  shape : a'.Shape
  pos : 0 < a'.alloc
  /-- The sign kept, or reset for a zero result. -/
  sign : a'.sign = Layout.mpZpos ∨ a'.sign = p.a.sign
  valid : ok = true → a'.Valid
  mag : ok = true → a'.mag = low p + highProd p.a.digit p.b.digit p.a.used p.b.used p.digs
  /-- The low part is below `radix ^ digs`. -/
  low : low p < radix ^ p.digs

def Q (p : P) : Api.MpMul.X → Prop
  | (ok, _, a') => Out p ok a'

/-- The contract at one `p`. -/
def Spec (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At SMpMulHighDigs.entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

/-- **`s_mp_mul_high_digs(a, b, a, digs)` on either path, `a` re-placed as needed.** -/
def Statement : Prop := ∀ {p : P}, Spec p

open Tom.Machine.Api.SMpMulDigsAG (cv initPrec_pos)

/-- On the fast test, the fast path's contract (`low` is `a`'s old digits). -/
theorem Spec.ofFast {p : P} (hf : Fast p.a p.b) (st : SMpMulHighDigsAF.Statement) : Spec p :=
  fun hra hres hS hB hH hoff => Triple.widenCv (fun hS hB hoff => st hra ⟨hres.stk, hres.sa, hres.sb, hres.asign,
      hres.dg_lt, hres.dg_le, hres.ub_pos, hf, hres.apos, hres.bpos, hres.aoff, hres.boff⟩ hS hB hH hoff) id
    (fun _ _ _ h => h) (fun ⟨_, _, _⟩ hq => ⟨hq.shape, hq.pos, hq.sign, hq.valid,
      fun h => by rw [low, if_pos hf]; exact hq.mag h, low_lt hres.sa⟩) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) .stk (by decide) (fun _ _ => rfl) (Iv.sub_self _) rfl (fun ⟨_, _, _⟩ => rfl) (by show 0 < 2736; decide)
    hS hB hoff

/-- Off the fast test, the slow path's contract (`room` vacuous, `low = 0`), its result through `cv`, its stack
widened. -/
theorem Spec.ofSlow {p : P} (hf : ¬ Fast p.a p.b) (st : SMpMulHighDigs.Statement) : Spec p :=
  fun hra hres hS hB hH hoff => Triple.widenCv (fun hS hB hoff => st hra ⟨hres.stk.mono (by decide), hres.sa,
      hres.sb, hres.asign, hres.dg_lt, hres.dg_le, hres.ua_le, hres.ub_pos, hres.uab, fun h => absurd h hf, hres.apos,
      hres.bpos, hres.aoff, hres.boff⟩ hS hB hH hoff) (cv p.adp p.a) (fun o _ _ h => by cases o <;> exact h)
    (fun | none, _ => ⟨hres.sa, hres.apos, .inr rfl, nofun, nofun, low_lt hres.sa⟩
         | some (_, _), (hd : SMpMulHighDigs.Digs _ _ _) => ⟨hd.valid.toShape, by rw [(hd.slow hf).2]; exact initPrec_pos _,
            .inl (hd.slow hf).1.sign, fun _ => hd.valid,
            fun _ => by rw [low, if_neg hf, Nat.zero_add]; exact (hd.slow hf).1.spec.2, low_lt hres.sa⟩)
    (fun o => funext fun r => by cases o <;> cases r <;> rfl) (fun o => by cases o <;> rfl) (fun o => by cases o <;> rfl)
    .stk (by decide) (fun r e => by cases r <;> first | exact absurd rfl e | rfl) (hres.stk.sub (by decide)) rfl
    (fun ⟨_, _, _⟩ => rfl) (by show 0 < 2192; decide) hS hB hoff

end Tom.Machine.Api.SMpMulHighDigsG
