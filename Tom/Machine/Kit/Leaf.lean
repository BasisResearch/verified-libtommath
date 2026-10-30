import Tom.Machine.Repr
import Tom.Machine.Kit.Arith

/-!
# The `used` load of a one-operand leaf function

Every one-operand function starts with `lw rX,0(a0)` (`a->used`): `UFacts`
is that load's facts, `UFacts.sx` its sign-extended value, `UFacts.of` the
facts from `MpAt` and the shape (`mp_count_bits`, `mp_cnt_lsb`,
`mp_dr_is_modulus`, `mp_reduce_is_2k`, `mp_reduce_is_2k_l`).
-/

namespace Tom.Machine

open Vsa.Sim

/-- The `used` load. -/
structure UFacts (m : Mem) (pa u : Nat) : Prop where
  rs : Ram pa 24
  u_v : bytesT4 m pa = BitVec.ofNat 32 u
  u_lt : u < 2 ^ 31

theorem UFacts.sx {m : Mem} {pa u : Nat} (h : UFacts m pa u) :
    BitVec.signExtend 64 (bytesT4 m pa) = BitVec.ofNat 64 u := by
  rw [h.u_v, signExtend_ofNat32 _ h.u_lt]

theorem UFacts.of {m : Mem} {p dp : Nat} {a : MpInt} (h : MpAt m p dp a) (hg : MpGeom p dp a.alloc)
    (hs : a.Shape) : UFacts m p a.used :=
  have := hs.used_le; have := hs.alloc_lt
  { rs := by simpa [Layout.sizeofMpInt] using hg.st
    u_v := by simpa [Layout.offUsed] using h.used
    u_lt := by omega }

end Tom.Machine
