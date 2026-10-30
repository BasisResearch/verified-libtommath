import Tom.Machine.Api.MpMulF
import Tom.Machine.Fn.MulGroupB
import Tom.Machine.Fn.MpSqrAGClosed
import Tom.Machine.Api.Std_red2g

/-!
* `mpMulG`: `mp_mul(a, b, c)` (`Api.MpMul.Statement`, `Fn.MulGroupB.mulCorrect.1`) and `mpMulAG`:
  `mp_mul(a, b, a)` (`Api.MpMulA.Statement`, `mulCorrect.2`), over every algorithm, with the placement
  of the destination's block in `Q` (`HContract.withPlace`). Their parameters are `Std.mpMulF`'s and
  `Std.mpMulAF`'s (the cut-off words named), their residues the group's (no `Small`): the destination
  is re-placed by whichever algorithm runs (`mp_grow` in `s_mp_mul_digs_fast`, `mp_exch` with a
  temporary in `s_mp_mul_digs` and `s_mp_balance_mul`, `mp_add`/`mp_lshd` into it in Karatsuba and
  Toom), so `mp_mul`'s contract never had a room premise on it.
* `mpSqrAG`: `mp_sqr(a, a)` at any size, growing `a` (`Api/MpSqrAG.lean`, `Fn.MpSqrAGClosed.correct`).

The residues and outputs read at the records' parameters (as `Std.mulF_*`), once, for their callers.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `mp_mul(a, b, c)` at any size, the cut-off words named. -/
def mpMulG0 : HContract := { mpMulF0 with
  Res p := MpMul.Res p.toP
  Q p := MpMul.Q p.toP
  pos p h r := mpMul_pos p.toP h r
  spec := fun hra hres => Fn.MulGroupB.mulCorrect.1 _ hra hres }

def mpMulG : HContract := mpMulG0.withPlace

/-- `mp_mul(a, b, a)` at any size, the cut-off words named. -/
def mpMulAG0 : HContract := { mpMulAF0 with
  Res p := MpMulA.Res p.toP
  Q p := MpMulA.Q p.toP
  pos p h r := mpMulA_pos p.toP h r
  spec := fun hra hres => Fn.MulGroupB.mulCorrect.2 _ hra hres }

def mpMulAG : HContract := mpMulAG0.withPlace

/-- `mp_sqr(a, a)` at any size, growing `a`. -/
def mpSqrAG : HContract := { mpSqrAF with
  Res := MpSqrAG.Res
  pos p h r := by
    have := h.apos
    cases r with
    | stk => exact .inl (show 0 < 2768 + 8 * p.a.used by omega)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (show 0 < 4 by decide)
  spec := Fn.MpSqrAGClosed.correct _ }

section MulG
variable {sp pa adp pb bdp pc cdp kc tc : Nat} {a b c a' : MpInt} {H : List (Nat × Nat)} {ok : Bool} {q : Nat}

theorem mulAG_res (hsp : sp % 16 = 0) (hlo : heapEnd + (2768 + 8 * (a.used + b.used)) ≤ sp)
    (hhi : sp ≤ 0x100000000) (va : a.Valid) (vb : b.Valid) (huab : a.used + b.used < 2 ^ 30)
    (hapos : 0 < a.alloc) (hbpos : 0 < b.alloc) (haoff : OffHeap pa 24) (hboff : OffHeap pb 24) :
    mpMulAG0.Res ⟨sp, pa, adp, pb, bdp, a, b, H, kc, tc⟩ :=
  (⟨⟨hsp, hlo, hhi⟩, va, vb, huab, hapos, hbpos, haoff, hboff⟩ : MpMulA.Res ⟨sp, pa, adp, pb, bdp, a, b, H⟩)

theorem mulAG_pos (h : mpMulAG0.Q ⟨sp, pa, adp, pb, bdp, a, b, H, kc, tc⟩ (ok, q, a')) : 0 < a'.alloc :=
  (show MpMulA.Out _ ok a' from h).pos

theorem mulAG_shape (h : mpMulAG0.Q ⟨sp, pa, adp, pb, bdp, a, b, H, kc, tc⟩ (ok, q, a')) : a'.Shape :=
  (show MpMulA.Out _ ok a' from h).shape

theorem mulAG_post (h : mpMulAG0.Q ⟨sp, pa, adp, pb, bdp, a, b, H, kc, tc⟩ (true, q, a')) :
    MulPost a b a' := (show MpMulA.Out _ true a' from h).post rfl

theorem mulG_res (hsp : sp % 16 = 0) (hlo : heapEnd + (2768 + 8 * (a.used + b.used)) ≤ sp)
    (hhi : sp ≤ 0x100000000) (va : a.Valid) (vb : b.Valid) (sc : c.Shape)
    (csign : c.sign = Layout.mpZpos ∨ c.sign = Layout.mpNeg) (huab : a.used + b.used < 2 ^ 30)
    (hapos : 0 < a.alloc) (hbpos : 0 < b.alloc) (hcpos : 0 < c.alloc) (haoff : OffHeap pa 24)
    (hboff : OffHeap pb 24) (hcoff : OffHeap pc 24) :
    mpMulG0.Res ⟨sp, pa, adp, pb, bdp, pc, cdp, a, b, c, H, kc, tc⟩ :=
  (⟨⟨hsp, hlo, hhi⟩, va, vb, sc, csign, huab, hapos, hbpos, hcpos, haoff, hboff, hcoff⟩ : MpMul.Res ⟨sp, pa, adp, pb, bdp, pc, cdp, a, b, c, H⟩)

theorem mulG_pos (h : mpMulG0.Q ⟨sp, pa, adp, pb, bdp, pc, cdp, a, b, c, H, kc, tc⟩ (ok, q, a')) :
    0 < a'.alloc := (show MpMul.Out _ ok a' from h).pos

theorem mulG_post (h : mpMulG0.Q ⟨sp, pa, adp, pb, bdp, pc, cdp, a, b, c, H, kc, tc⟩ (true, q, a')) :
    MulPost a b a' := (show MpMul.Out _ true a' from h).post rfl

end MulG

end Tom.Machine.Std
