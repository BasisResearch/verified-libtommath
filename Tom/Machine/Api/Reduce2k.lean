import Tom.Machine.Api.Un
import Tom.Machine.Fn.Reduce2k
import Tom.Spec.ModShape

/-!
# `mp_reduce_is_2k`: the standard contract

From the entry, `mp_reduce_is_2k(a)` with `a` valid returns to `ra` with
`a0 = isReduce2k a`, `sp`, `s0` and the other callee-saved registers
restored, and memory changed only in the stack `[sp - 16, sp)` (its own
frame; the called `mp_count_bits` has none). Regions as `Api/Un.lean`,
read-only (`isR`), stack depth 16.

Beyond `Valid`: `28 * used < 2^31` (`mp_count_bits`'s `int` result).
-/

namespace Tom.Machine.Api.Reduce2k

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Un

abbrev lay (sp pa adp : Nat) (a : MpInt) := Un.lay 16 sp pa adp a

structure Pre (m : Mem) (sp pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  va : a.Valid
  ga : MpGeom pa adp a.alloc
  bits : Layout.digitBits * a.used < 2 ^ 31
  rs : Ram (sp - 16) 16
  sp_al : sp % 16 = 0
  sp_ge : 16 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp a) isR

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (ra s0 : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 (isReduce2k a))] M v.keepR outp cf ∧
    Frm (lay sp pa adp a) wsR m M

def entry : BitVec 64 := 0x80001d14#64

/-- **`mp_reduce_is_2k` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {ra s0 : BitVec 64},
    Pre m sp pa adp a ra →
    Triple (At entry (Fn.Reduce2k.entryL ra s0 sp pa) m v.keepR outp) (Ret m v outp sp pa adp a ra s0)

end Tom.Machine.Api.Reduce2k
