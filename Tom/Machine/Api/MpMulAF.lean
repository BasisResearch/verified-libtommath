import Tom.Machine.Api.Std_r6g
import Tom.Machine.Kit.Placed

/-!
# `mp_mul(a, b, a)` on the comba path, with `a`'s allocation kept or grown

`Api/MpMulA.lean` restricted to small operands, `MpMulAF.Small a b` (`a->used < 80`, so `mp_mul`'s
`min_len < MP_KARATSUBA_MUL_CUTOFF` and none of balance/Toom/Karatsuba is taken, and
`a->used + b->used + 1 < MP_WARRAY`, so `s_mp_mul_digs_fast(a, b, a, digs)` runs), with one more
output field: `grow`, `a->alloc ≤ a'->alloc` (`s_mp_mul_digs_fast` calls `mp_grow(a, digs)` only when
`a->alloc < digs`, and `mp_grow` never shrinks). This is the `alloc` bound of the mul group's contract
gap in the form `mp_reduce_2k_l` needs: `q`'s room for `mp_copy(a, &q)` in the next pass's
`mp_div_2d` (D5). `MpMulA.Statement`'s statement is unchanged; this one is its strengthening on the
comba path, proved in `Fn/MpMulAFClosed.lean` (`Fn.MpMulAFG5.correct`, `experiments/asm/mmulaf.asm.json`,
over `MulFastHA.Out.grow`) with the closed group's residue (`Fn/MulGroupB.lean`).
-/

namespace Tom.Machine.Api.MpMulAF

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpMulA (P R lay kind out isW ws site' hin hout args rets)

/-- `mp_mul`'s comba path: no Karatsuba/Toom/balance (`min_len < 80`), `digs < MP_WARRAY`. -/
structure Small (a b : MpInt) : Prop where
  ua : a.used < 80
  digs : a.used + b.used + 1 < 512

structure Res (p : P) : Prop where
  res : MpMulA.Res p
  small : Small p.a p.b

structure Out (p : P) (ok : Bool) (a' : MpInt) : Prop where
  out : MpMulA.Out p ok a'
  /-- `a`'s digit block kept or grown (`mp_grow` in `s_mp_mul_digs_fast`). -/
  grow : p.a.alloc ≤ a'.alloc

def Q (p : P) : MpMul.X → Prop
  | (ok, _, a') => Out p ok a'

/-- **`mp_mul(a, b, a)` on the comba path, `alloc` kept or grown.** -/
def Statement : Prop :=
  ∀ (p : P) {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At MpMul.entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpMulAF

namespace Tom.Machine.Std

open Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `mp_mul(a, b, a)` on the comba path with the cut-off words named (as `Std.mpMulAK`). -/
structure MulAFP where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt
  H : List (Nat × Nat)
  kc : Nat
  tc : Nat

def MulAFP.toP (p : MulAFP) : MpMulA.P := ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩

structure MulAFRes (p : MulAFP) : Prop where
  res : MpMulAF.Res p.toP
  stmt : MpMulAF.Statement

def mpMulAF0 : HContract where
  P := MulAFP
  X := MpMul.X
  R := MpMulA.R
  all := [.stk, .aS, .aD, .bS, .bD, .kc, .tc, .code]
  hall := MpMulA.all
  entry := MpMul.entry
  args p := MpMulA.args p.toP
  rets p := MpMulA.rets p.toP
  lay p := MpMulA.lay p.toP
  kind p := MpMulA.kind p.toP
  out p := MpMulA.out p.toP
  isW := MpMulA.isW
  ws := MpMulA.ws
  site := .aD
  site' p := MpMulA.site' p.toP
  hin p := MpMulA.hin p.toP
  hout p := MpMulA.hout p.toP
  Res := MulAFRes
  Q p := MpMulAF.Q p.toP
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _ | simp [Kind.Fits, MpMulA.kind, MpMulA.lay, Iv.Sub]
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpMulA.out, MpMulA.kind, MpMulA.ws, Kind.isRam, Kind.indep]
  pos p h r := mpMulA_pos p.toP h.res.res r
  spec := fun hra hres => hres.stmt _ hra hres.res

/-- With the placement of `a`'s block in the result (`HContract.withPlace`). -/
def mpMulAF : HContract := mpMulAF0.withPlace

/-! The call's residue and output read at its parameters (the record's projections through `toP`
are atoms to `omega`): once per callee, for its callers. -/

section MulF
variable {sp pa adp pb bdp kc tc : Nat} {a b a' : MpInt} {H : List (Nat × Nat)} {ok : Bool} {q : Nat}

theorem mulF_res (hsp : sp % 16 = 0) (hlo : heapEnd + (2768 + 8 * (a.used + b.used)) ≤ sp)
    (hhi : sp ≤ 0x100000000) (va : a.Valid) (vb : b.Valid) (huab : a.used + b.used < 2 ^ 30)
    (hapos : 0 < a.alloc) (hbpos : 0 < b.alloc) (haoff : OffHeap pa 24) (hboff : OffHeap pb 24)
    (hua : a.used < 80) (hdigs : a.used + b.used + 1 < 512) (st : MpMulAF.Statement) :
    MulAFRes ⟨sp, pa, adp, pb, bdp, a, b, H, kc, tc⟩ :=
  ⟨⟨⟨⟨hsp, hlo, hhi⟩, va, vb, huab, hapos, hbpos, haoff, hboff⟩, ⟨hua, hdigs⟩⟩, st⟩

theorem mulF_out (h : mpMulAF0.Q ⟨sp, pa, adp, pb, bdp, a, b, H, kc, tc⟩ (ok, q, a')) :
    MpMulAF.Out ⟨sp, pa, adp, pb, bdp, a, b, H⟩ ok a' := h

theorem mulF_grow (h : mpMulAF0.Q ⟨sp, pa, adp, pb, bdp, a, b, H, kc, tc⟩ (ok, q, a')) :
    a.alloc ≤ a'.alloc := (mulF_out h).grow

theorem mulF_pos (h : mpMulAF0.Q ⟨sp, pa, adp, pb, bdp, a, b, H, kc, tc⟩ (ok, q, a')) :
    0 < a'.alloc := (mulF_out h).out.pos

theorem mulF_shape (h : mpMulAF0.Q ⟨sp, pa, adp, pb, bdp, a, b, H, kc, tc⟩ (ok, q, a')) :
    a'.Shape := (mulF_out h).out.shape

theorem mulF_post (h : mpMulAF0.Q ⟨sp, pa, adp, pb, bdp, a, b, H, kc, tc⟩ (true, q, a')) :
    MulPost a b a' := (mulF_out h).out.post rfl

/-- `a`'s block after the call: fresh for the caller's heap (the site re-placed in a loop). -/
theorem mulF_fresh {n : Nat} (hp : Place (digBlk adp a :: H) ⟨adp, 4 * a.alloc⟩ ⟨q, 4 * a'.alloc⟩)
    (hf : Fresh H adp n) (hn : n = 4 * a.alloc) (hpos : 0 < a'.alloc) : Fresh H q (4 * a'.alloc) := by
  subst hn; exact fresh_of_place (fun _ he => he) hp hf (by omega)

end MulF

end Tom.Machine.Std
