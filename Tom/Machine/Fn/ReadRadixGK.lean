import Tom.Machine.Kit.Gen

/-! `mp_read_radix`'s end-of-string test (`1c84`–`1c94`): bit `c` of `0x…dbfe` is
clear exactly for `c ∈ {'\0', '\n', '\r'}` when `c ≤ 13`. -/

namespace Tom.Machine.Fn.ReadRadixG

open LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- `sra a5, a5, a4` with `a5 = 0x…dbfe`, `a4 = c`. -/
def crlfMask (c : Nat) : BitVec 64 :=
  shift_bits_right_arith 0xffffffffffffdbfe#64 (Sail.BitVec.extractLsb (BitVec.ofNat 64 c) 5 0)

theorem crlf_tab : ∀ c, c < 14 → crlfMask c &&& 1#64 = if c = 0 ∨ c = 10 ∨ c = 13 then 0#64 else 1#64 := by
  decide

@[seg_val] theorem crlf_clr (c : Nat) (h : c < 14) (h' : c = 0 ∨ c = 10 ∨ c = 13) :
    crlfMask c &&& 1#64 = 0#64 := by rw [crlf_tab c h, if_pos h']

@[seg_val] theorem crlf_set (c : Nat) (h : c < 14) (h0 : c ≠ 0) (h1 : c ≠ 10) (h2 : c ≠ 13) :
    crlfMask c &&& 1#64 = 1#64 := by rw [crlf_tab c h, if_neg (by omega)]

end Tom.Machine.Fn.ReadRadixG
