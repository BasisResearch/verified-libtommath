import Tom.Machine.Kit.At

/-!
# More keep-sets

`Abi.keepR2`: `Abi.keep` without `sp`, `s0`, `s1`, `s2`, for a function that
uses `s0..s2` as locals and restores them (`mp_init_multi`,
`mp_montgomery_setup`); they travel in the pin list.
-/

namespace Tom.Machine

/-- `Abi.keep` without `sp`, `s0`, `s1`, `s2`. -/
def Abi.keepR2 (v : Abi) : Vsa.Sim.GRegs :=
  [(3, v.gp), (4, v.tp), (19, v.s.s3), (20, v.s.s4), (21, v.s.s5), (22, v.s.s6), (23, v.s.s7), (24, v.s.s8),
   (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

abbrev abiKeysR2 : List Nat := [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27]

end Tom.Machine
