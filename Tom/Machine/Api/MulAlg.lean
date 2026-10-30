import Tom.Machine.Api.MulRec

/-!
# The algorithms `mp_mul` dispatches to: their common contract shape

`s_mp_karatsuba_mul`, `s_mp_balance_mul`, `s_mp_toom_mul`
take `mp_mul`'s parameters (`Api.MpMul.P`), regions, results and heap, and differ in their
entry, their residue (the dispatch facts the code relies on, and the induction hypothesis
`ih : MulBelow μ`) and in what `MP_OKAY` promises: `|c'| = |a| |b|`, `c'` valid (the sign is
`mp_mul`'s to set, `c->sign := neg ∧ c->used > 0`).

The stack depth is `mp_mul`'s minus its 32-byte frame: `F = 2736 + 8 μ`. Each algorithm's
frame (karatsuba 240, balance 208, toom 336) plus the depth of a recursive `mp_mul` at
`μ' ≤ μ - 46` fits, and so do the non-recursive callees (all below 2736 bytes).
-/

namespace Tom.Machine.Api.MulAlg

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpMul (P R X μ)

/-- The algorithms' stack depth. -/
def F (p : P) : Nat := 2736 + 8 * μ p.a p.b

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - (2736 + 8 * (p.a.used + p.b.used)), 2736 + 8 * (p.a.used + p.b.used)⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .cS => ⟨p.pc, 24⟩
  | .cD => ⟨p.cdp, 4 * p.c.alloc⟩
  | .kc => ⟨MpMul.kcAddr, 4⟩
  | .tc => ⟨MpMul.tcAddr, 4⟩
  | .code => textIv

/-- What `c` holds after an algorithm. -/
structure Out (p : P) (ok : Bool) (c' : MpInt) : Prop where
  shape : c'.Shape
  pos : 0 < c'.alloc
  /-- `MP_OKAY`: `c'` valid with magnitude `|a| |b|`. -/
  valid : ok = true → c'.Valid
  mag : ok = true → c'.mag = p.a.mag * p.b.mag

def Q (p : P) : X → Prop
  | (ok, _, c') => Out p ok c'

/-- The contract of an algorithm at `entry` with residue `Rs`, at one `p`. -/
def SpecR (entry : BitVec 64) (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (lay p) MpMul.isW → Bundle (lay p) (MpMul.kind p) m → AHeap m (MpMul.hin p) →
    (∀ r, Off (lay p r) (MpMul.hin p)) →
    Triple (At entry ((1, ra) :: MpMul.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (MpMul.rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) MpMul.ws .cD (MpMul.out p x) (MpMul.site' p x) (MpMul.hin p) (MpMul.hout p x) m M)

/-- The residue every algorithm shares (`Api.MpMul.Res` at the depth `F`). -/
structure Base (p : P) : Prop where
  stk : StkRes p.sp (F p)
  va : p.a.ValidU
  vb : p.b.ValidU
  sc : p.c.Shape
  csign : p.c.sign = Layout.mpZpos ∨ p.c.sign = Layout.mpNeg
  uab : μ p.a p.b < 2 ^ 30
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  cpos : 0 < p.c.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24

end Tom.Machine.Api.MulAlg
