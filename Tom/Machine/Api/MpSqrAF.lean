import Tom.Machine.Api.MpSqrA

/-!
# `mp_sqr(a, a)` on the comba path, growing `a`

`Api/MpSqrA.lean` keeps `s_mp_sqr_fast(a, a)` in place (`room`: `2 a->used ≤ a->alloc` below
`KARATSUBA_SQR_CUTOFF`, D5): with `a` from `mp_init` (`MP_PREC = 32` digits) that is `a->used ≤ 16`.
Here the fast path's growing contract (`Std.sqrFastGA`, `Api/SqrFastHA.lean`: `mp_grow(a, 2 a->used)`
when short) replaces it, for operands on the comba path (`small`: `a->used < 120`, so `mp_sqr` takes
neither Toom nor Karatsuba). Results, site, regions and output record (`MpSqrA.Out`: valid square, `a`'s
block kept or re-placed, `grow`) as `Api/MpSqrA.lean`; the stack depth covers the growing fast path's
2752 bytes below the 16-byte frame (`F`). `s_mp_exptmod`'s `mp_sqr(&M[2^(w-1)], &M[2^(w-1)])` and
`mp_sqr(&res, &res)` on `mp_init`'s 32 digits.
-/

namespace Tom.Machine.Api.MpSqrAF

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpSqr (entry ksAddr tsAddr kmAddr tmAddr X)
open Tom.Machine.Api.MpSqrA (P R kind out isW ws site' hin hout args rets)

/-- The stack depth: the 16-byte frame and the growing `s_mp_sqr_fast`'s 2752 (more than `MpSqrA.F`'s
`2224 + 8 a->used` below 68 digits). -/
def F (p : P) : Nat := 2768 + 8 * p.a.used

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - (2768 + 8 * p.a.used), 2768 + 8 * p.a.used⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .ks => ⟨ksAddr, 4⟩
  | .ts => ⟨tsAddr, 4⟩
  | .km => ⟨kmAddr, 4⟩
  | .tm => ⟨tmAddr, 4⟩
  | .code => textIv

/-- What `mp_sqr(a, a)` needs on the comba path: `MpSqrA.Res` without `room`, with `small`. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp (F p)
  va : p.a.Valid
  au : p.a.used < 2 ^ 29
  /-- The comba path: below `KARATSUBA_SQR_CUTOFF` (and `TOOM_SQR_CUTOFF`). -/
  small : p.a.used < 120
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

/-- **`mp_sqr(a, a)` on the comba path, growing `a`.** -/
def Statement : Prop :=
  ∀ (p : P) {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ MpSqrA.Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpSqrAF
