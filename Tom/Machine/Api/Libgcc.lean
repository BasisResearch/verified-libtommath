import Tom.Machine.Img
import Tom.Machine.Kit.CodeBytes
import Vsa.Reloc.Libgcc.Code.«__umoddi3»

/-!
# libgcc's 64-bit multiply and divide: the contracts

The four routines libtommath calls, at their addresses in `c/tommath-arith.elf`:
`__muldi3` (`0x80017540`), `__divdi3` (`0x800175a4`), `__hidden___udivdi3`
(`0x800175ac`, alias `__udivdi3`) and `__moddi3` (`0x80017628`). Each is a
machine triple between `At` states: from the entry with the arguments in
`a0`/`a1` and the return address in `ra`, the machine returns to `ra` with the
result in `a0`, memory and console unchanged, and every pin of the caller's
keep-set `K` kept, provided its keys avoid the routine's write set (`KeepOK`;
`Abi.keep` always does: `keepOK_abi`). The write sets:

* `__muldi3`, `__udivdi3`: `a0`–`a3` (`x10`–`x13`); `ra` is kept;
* `__divdi3`, `__moddi3`: `a0`–`a3`, `ra` (`x1`, the inner `jal` to
  `__udivdi3`) and `t0` (`x5`, which carries the return address).

Side conditions: `ra` 4-aligned, the code in memory (`Img m`), a nonzero
divisor (`__divdi3`'s sign fix-ups run inside `__umoddi3`, whose code `Img`
carries: `scripts/gen_code.py` follows branches into other functions). No scratch register needs
to be defined at entry, and `__divdi3`'s wrapping case `intMin / -1` is
included (`BitVec.sdiv` wraps the same way).

The proofs: `__muldi3` and `__udivdi3` are the relocated sibling proofs of
`Vsa/Reloc/Libgcc/`.
`__moddi3` and `__divdi3` are segments around the `__udivdi3` contract
(`Tom/Machine/Fn/LibgccSigned.lean`).
-/

namespace Tom.Machine.Api.Libgcc

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine

/-- `__muldi3`'s entry. -/
def muldi3Entry : BitVec 64 := 0x80017540#64
/-- `__divdi3`'s entry. -/
def divdi3Entry : BitVec 64 := 0x800175a4#64
/-- `__hidden___udivdi3`'s (`__udivdi3`'s) entry. -/
def udivdi3Entry : BitVec 64 := 0x800175ac#64
/-- `__moddi3`'s entry. -/
def moddi3Entry : BitVec 64 := 0x80017628#64

/-- Registers `__muldi3` and `__udivdi3` write: `a0`–`a3`. -/
abbrev mulWrites : List Nat := [10, 11, 12, 13]
/-- Registers `__divdi3` and `__moddi3` write: `ra`, `t0`, `a0`–`a3`. -/
abbrev divWrites : List Nat := [1, 5, 10, 11, 12, 13]

namespace Muldi3

/-- **`__muldi3`**: `a0 := a0 * a1` (mod `2^64`). -/
def StatementK : Prop :=
  ∀ {m : Mem} {K : GRegs} {outp : Array String} {ra x y : BitVec 64},
    Img m → ra.toNat % 4 = 0 → KeepOK mulWrites K →
    Triple (At muldi3Entry [(1, ra), (10, x), (11, y)] m K outp)
      (At ra [(1, ra), (10, x * y)] m K outp)

/-- `StatementK` with the ABI keep-set. -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra x y : BitVec 64},
    Img m → ra.toNat % 4 = 0 →
    Triple (At muldi3Entry [(1, ra), (10, x), (11, y)] m v.keep outp)
      (At ra [(1, ra), (10, x * y)] m v.keep outp)

end Muldi3

namespace Udivdi3

/-- **`__udivdi3`**: `a0 := n / d`, `a1 := n % d` (unsigned), `d ≠ 0`. -/
def StatementK : Prop :=
  ∀ {m : Mem} {K : GRegs} {outp : Array String} {ra n d : BitVec 64},
    Img m → ra.toNat % 4 = 0 → d ≠ 0#64 → KeepOK mulWrites K →
    Triple (At udivdi3Entry [(1, ra), (10, n), (11, d)] m K outp)
      (At ra [(1, ra), (10, n / d), (11, n % d)] m K outp)

def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra n d : BitVec 64},
    Img m → ra.toNat % 4 = 0 → d ≠ 0#64 →
    Triple (At udivdi3Entry [(1, ra), (10, n), (11, d)] m v.keep outp)
      (At ra [(1, ra), (10, n / d), (11, n % d)] m v.keep outp)

end Udivdi3

namespace Moddi3

/-- **`__moddi3`**: `a0 := n.srem d` (C's `%` on `int64_t`), `d ≠ 0`. -/
def StatementK : Prop :=
  ∀ {m : Mem} {K : GRegs} {outp : Array String} {ra n d : BitVec 64},
    Img m → ra.toNat % 4 = 0 → d ≠ 0#64 → KeepOK divWrites K →
    Triple (At moddi3Entry [(1, ra), (10, n), (11, d)] m K outp) (At ra [(10, n.srem d)] m K outp)

def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra n d : BitVec 64},
    Img m → ra.toNat % 4 = 0 → d ≠ 0#64 →
    Triple (At moddi3Entry [(1, ra), (10, n), (11, d)] m v.keep outp)
      (At ra [(10, n.srem d)] m v.keep outp)

end Moddi3

namespace Divdi3

/-- **`__divdi3`**: `a0 := n.sdiv d` (C's `/` on `int64_t`, wrapping on `intMin / -1`), `d ≠ 0`. -/
def StatementK : Prop :=
  ∀ {m : Mem} {K : GRegs} {outp : Array String} {ra n d : BitVec 64},
    Img m → ra.toNat % 4 = 0 → d ≠ 0#64 → KeepOK divWrites K →
    Triple (At divdi3Entry [(1, ra), (10, n), (11, d)] m K outp) (At ra [(10, n.sdiv d)] m K outp)

def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra n d : BitVec 64},
    Img m → ra.toNat % 4 = 0 → d ≠ 0#64 →
    Triple (At divdi3Entry [(1, ra), (10, n), (11, d)] m v.keep outp)
      (At ra [(10, n.sdiv d)] m v.keep outp)

end Divdi3

end Tom.Machine.Api.Libgcc
