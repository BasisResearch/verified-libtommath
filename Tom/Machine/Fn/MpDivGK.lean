import Tom.Machine.Kit.Gen

/-! `mp_div`'s step 3.1 dividend (`c4c`–`c5c`): `(x[i] << 28) | x[i-1]` as the code forms it
(`slli 32; srli 4` of `x[i]`, `lwu` of `x[i-1]`), for two digits. -/

namespace Tom.Machine.Fn.MpDivG

theorem hi_lo (xi xi1 : Nat) (h1 : xi < 268435456) (h2 : xi1 < 268435456) :
    BitVec.ofNat 64 (xi1 % 4294967296) ||| BitVec.ofNat 64 (xi * 4294967296 % 18446744073709551616 / 16) =
      BitVec.ofNat 64 (xi * 268435456 + xi1) := by
  rw [Nat.mod_eq_of_lt (by omega : xi1 < 4294967296),
    Nat.mod_eq_of_lt (by omega : xi * 4294967296 < 18446744073709551616),
    show xi * 4294967296 / 16 = xi * 268435456 by omega]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : xi1 < 18446744073709551616),
    Nat.mod_eq_of_lt (by omega : xi * 268435456 < 18446744073709551616),
    Nat.mod_eq_of_lt (by omega : xi * 268435456 + xi1 < 18446744073709551616),
    show xi * 268435456 = xi <<< 28 by rw [Nat.shiftLeft_eq],
    Nat.shiftLeft_add_eq_or_of_lt (by omega : xi1 < 2 ^ 28), Nat.or_comm]

end Tom.Machine.Fn.MpDivG
