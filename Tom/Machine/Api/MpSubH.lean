import Tom.Machine.Api.MpAddH
import Tom.Machine.Api.MpAddHA

/-!
# `mp_sub(a, b, c)` and `mp_sub(a, b, a)` with growth: the allocating contracts

`bn_mp_sub.c` at `0x80001ef4` (frame 48, popped before the tail call): `c->sign` set, then a
tail call of `s_mp_add` (unequal signs) or `s_mp_sub` (`|a| ≥ |b|`: `s_mp_sub(a, b, c)`;
else `s_mp_sub(b, a, c)` with the sign flipped by `seqz` at `1f68`), whose growing contracts
(`Api/SAddG*.lean`, `Api/SSubG*.lean`) re-place `c`'s digits when short. The shape
is `mp_add`'s exactly (`Api/MpAddH.lean`, `Api/MpAddHA.lean`, same regions, stack 608, residue),
with the value `a − b`. Used by `s_mp_toom_sqr`'s proof (`mp_sub(&a0, &a1, b)`;
`mp_sub(&a0, b, &a0)`, `mp_sub(b, &a2, b)`, …). Proved by `Fn.GrowSubH.mpSubH`, `Fn.GrowSubH.mpSubHA`
(`Fn/GrowSubH.lean`).
-/

namespace Tom.Machine.Api.MpSubH

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.Bin (R isW ws)
open Tom.Machine.Api.MpAddH (P lay kind out site' hin hout args rets Res)

def entry : BitVec 64 := 0x80001ef4#64

/-- What `c` holds after: shaped, live, placed, grown only; on `MP_OKAY` the difference. -/
structure Out (p : P) (x : MpSqr.X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) (lay p .cD) (site' p x)
  grow : p.c.alloc ≤ x.2.2.alloc
  valid : x.1 = true → x.2.2.Valid
  val : x.1 = true → x.2.2.val = p.a.val - p.b.val

def Q (p : P) (x : MpSqr.X) : Prop := Out p x

/-- **`mp_sub(a, b, c)` with growth** (proved: `Fn.GrowSubH.mpSubH`). -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpSubH

namespace Tom.Machine.Api.MpSubHA

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.MpAddGA (P R lay kind isW ws hin args Res)
open Tom.Machine.Api.MpAddHA (out site' hout rets)

def entry : BitVec 64 := 0x80001ef4#64

/-- What `a` holds after: shaped, live, placed, grown only; on `MP_OKAY` the difference. -/
structure Out (p : P) (x : MpSqr.X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) (lay p .aD) (site' p x)
  grow : p.a.alloc ≤ x.2.2.alloc
  valid : x.1 = true → x.2.2.Valid
  val : x.1 = true → x.2.2.val = p.a.val - p.b.val

def Q (p : P) (x : MpSqr.X) : Prop := Out p x

/-- **`mp_sub(a, b, a)` with growth** (proved: `Fn.GrowSubH.mpSubHA`). -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpSubHA
