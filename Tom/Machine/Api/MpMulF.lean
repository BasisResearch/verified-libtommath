import Tom.Machine.Api.MpMulG
import Tom.Machine.Api.MpMulAF

/-!
# `mp_mul(a, b, c)` on the comba path, with `c`'s allocation kept or grown

`Api/MpMul.lean` restricted to small operands (`MpMulAF.Small a b`: `a->used < 80`, so `mp_mul`'s
`min_len < MP_KARATSUBA_MUL_CUTOFF`, and `a->used + b->used + 1 < MP_WARRAY`, so
`s_mp_mul_digs_fast(a, b, c, digs)` runs), with one more output field: `grow`, `c->alloc ≤ c'->alloc`
(`MulFastH.Out.grow`: `mp_grow(c, digs)` only when `c->alloc < digs`). `MpMul.Statement` is unchanged; this one is its
strengthening on the comba path, proved in `Fn/MpMulFClosed.lean` (`Fn.MpMulFG5.correct`,
`experiments/asm/mmulf.asm.json`, a variant of `mmul.asm.json`).

* `MpMulF`: the contract; `MpMulGF`: what the generated assembly proves (`MpMulG`'s residue and
  `Small`); `Std.mpMulF`: the callee record (`HContract.withPlace`), its residue and output read
  at its parameters.
-/

namespace Tom.Machine.Api.MpMulF

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpMul (P R lay kind out isW ws site' hin hout args rets)

structure Res (p : P) : Prop where
  res : MpMul.Res p
  small : MpMulAF.Small p.a p.b

structure Out (p : P) (ok : Bool) (c' : MpInt) : Prop where
  out : MpMul.Out p ok c'
  /-- `c`'s digit block kept or grown (`mp_grow` in `s_mp_mul_digs_fast`). -/
  grow : p.c.alloc ≤ c'.alloc

def Q (p : P) : MpMul.X → Prop
  | (ok, _, c') => Out p ok c'

/-- **`mp_mul(a, b, c)` on the comba path, `c->alloc` kept or grown.** -/
def Statement : Prop :=
  ∀ (p : P) {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At MpMul.entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpMulF

namespace Tom.Machine.Api.MpMulGF

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpMul (P lay kind out isW ws site' hin hout args rets)

structure Res (p : P) : Prop extends toG : MpMulG.Res p where
  small : MpMulAF.Small p.a p.b

def SpecR (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At MpMul.entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ MpMulF.Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

/-- **`mp_mul(a, b, c)` on the comba path**, under `MpMulG`'s residue. -/
def Statement : Prop := ∀ p : P, SpecR Res p

end Tom.Machine.Api.MpMulGF

namespace Tom.Machine.Std

open Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `mp_mul(a, b, c)` on the comba path with the cut-off words named (as `MulAFP`). -/
structure MulFP where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  pc : Nat
  cdp : Nat
  a : MpInt
  b : MpInt
  c : MpInt
  H : List (Nat × Nat)
  kc : Nat
  tc : Nat

def MulFP.toP (p : MulFP) : MpMul.P := ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.pc, p.cdp, p.a, p.b, p.c, p.H⟩

structure MulFRes (p : MulFP) : Prop where
  res : MpMulF.Res p.toP
  stmt : MpMulF.Statement

def mpMulF0 : HContract where
  P := MulFP
  X := MpMul.X
  R := MpMul.R
  all := [.stk, .aS, .aD, .bS, .bD, .cS, .cD, .kc, .tc, .code]
  hall := MpMul.all
  entry := MpMul.entry
  args p := MpMul.args p.toP
  rets p := MpMul.rets p.toP
  lay p := MpMul.lay p.toP
  kind p := MpMul.kind p.toP
  out p := MpMul.out p.toP
  isW := MpMul.isW
  ws := MpMul.ws
  site := .cD
  site' p := MpMul.site' p.toP
  hin p := MpMul.hin p.toP
  hout p := MpMul.hout p.toP
  Res := MulFRes
  Q p := MpMulF.Q p.toP
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _ | simp [Kind.Fits, MpMul.kind, MpMul.lay, Iv.Sub]
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpMul.out, MpMul.kind, MpMul.ws, Kind.isRam, Kind.indep]
  pos p h r := mpMul_pos p.toP h.res.res r
  spec := fun hra hres => hres.stmt _ hra hres.res

/-- With the placement of `c`'s block in the result (`HContract.withPlace`). -/
def mpMulF : HContract := mpMulF0.withPlace

section MulCF
variable {sp pa adp pb bdp pc cdp kc tc : Nat} {a b c c' : MpInt} {H : List (Nat × Nat)} {ok : Bool} {q : Nat}

theorem mulCF_res (hsp : sp % 16 = 0) (hlo : heapEnd + (2768 + 8 * (a.used + b.used)) ≤ sp)
    (hhi : sp ≤ 0x100000000) (va : a.Valid) (vb : b.Valid) (sc : c.Shape)
    (csign : c.sign = Layout.mpZpos ∨ c.sign = Layout.mpNeg) (huab : a.used + b.used < 2 ^ 30)
    (hapos : 0 < a.alloc) (hbpos : 0 < b.alloc) (hcpos : 0 < c.alloc) (haoff : OffHeap pa 24)
    (hboff : OffHeap pb 24) (hcoff : OffHeap pc 24) (hua : a.used < 80) (hdigs : a.used + b.used + 1 < 512)
    (st : MpMulF.Statement) : MulFRes ⟨sp, pa, adp, pb, bdp, pc, cdp, a, b, c, H, kc, tc⟩ :=
  ⟨⟨⟨⟨hsp, hlo, hhi⟩, va, vb, sc, csign, huab, hapos, hbpos, hcpos, haoff, hboff, hcoff⟩, ⟨hua, hdigs⟩⟩, st⟩

theorem mulCF_out (h : mpMulF0.Q ⟨sp, pa, adp, pb, bdp, pc, cdp, a, b, c, H, kc, tc⟩ (ok, q, c')) :
    MpMulF.Out ⟨sp, pa, adp, pb, bdp, pc, cdp, a, b, c, H⟩ ok c' := h

theorem mulCF_grow (h : mpMulF0.Q ⟨sp, pa, adp, pb, bdp, pc, cdp, a, b, c, H, kc, tc⟩ (ok, q, c')) :
    c.alloc ≤ c'.alloc := (mulCF_out h).grow

theorem mulCF_pos (h : mpMulF0.Q ⟨sp, pa, adp, pb, bdp, pc, cdp, a, b, c, H, kc, tc⟩ (ok, q, c')) :
    0 < c'.alloc := (mulCF_out h).out.pos

theorem mulCF_shape (h : mpMulF0.Q ⟨sp, pa, adp, pb, bdp, pc, cdp, a, b, c, H, kc, tc⟩ (ok, q, c')) :
    c'.Shape := (mulCF_out h).out.shape

theorem mulCF_post (h : mpMulF0.Q ⟨sp, pa, adp, pb, bdp, pc, cdp, a, b, c, H, kc, tc⟩ (true, q, c')) :
    MulPost a b c' := (mulCF_out h).out.post rfl

end MulCF

end Tom.Machine.Std
