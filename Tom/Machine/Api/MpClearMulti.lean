import Tom.Machine.Api.Multi
import Tom.Machine.Api.MpClear
import Tom.Machine.Fn.MpClearMulti

/-!
# `mp_clear_multi`: the standard contract

`mp_clear_multi(x₀, …, x_{k-1}, NULL)` for live `mp_int`s `xs` (digits the
blocks `blocks xs` in front of the heap's other blocks `H`, pairwise apart;
structs `Structs`): every struct is cleared (`MpInt.cleared`), the heap is
`H`. Memory changes only in the stack `[sp - 640, sp)` (its 96-byte frame and
`mp_clear`'s 544), the structs, the freed blocks and `Foot H` (`W`). The
arguments are `argRegs` and `StackArgs` (`Api/Multi.lean`).
-/

namespace Tom.Machine.Api.MpClearMulti

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Api.Multi

/-- The stack depth: the 96-byte frame and `mp_clear`'s. -/
abbrev F : Nat := 96 + MpClear.F

/-- What `mp_clear_multi(xs…, NULL)` needs. -/
structure Pre (m : Mem) (v : Abi) (H : List (Nat × Nat)) (sp : Nat) (xs : List Arg) (ra : BitVec 64) : Prop where
  live : ∀ x ∈ xs, MpAt m x.1 x.2.1 x.2.2
  heap : Heap m (blocks xs ++ H)
  bpw : (blocks xs).Pairwise fun e e' => Disj e.1 e.2 e'.1 e'.2
  st : Structs (ptrs xs) (sp - F) (F + argLen (xs.length + 1))
  sargs : StackArgs m sp (args (ptrs xs))
  args_hi : sp + argLen (xs.length + 1) ≤ 0x100000000
  ctx : ACtx m v sp F
  ra_al : ra.toNat % 4 = 0

/-- What it may write: the stack, the structs and blocks, the footprint. -/
def W (xs : List Arg) (H : List (Nat × Nat)) (sp : Nat) (a : Nat) : Prop :=
  Stk sp F a ∨ (∃ x ∈ xs, InBlk (x.1, 24) a ∨ InBlk (digBlk x.2.1 x.2.2) a) ∨ Foot H a

/-- What it leaves. -/
structure Post (m : Mem) (H : List (Nat × Nat)) (sp : Nat) (xs : List Arg) (M : Mem) : Prop where
  cleared : ∀ x ∈ xs, MpAt M x.1 0 MpInt.cleared
  heap : Heap M H
  frame : Keep (W xs H sp) m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (H : List (Nat × Nat)) (sp : Nat) (xs : List Arg)
    (ra : BitVec 64) (c : Vsa.Machine.Config) : Prop :=
  ∃ M, At ra [(1, ra)] M v.keep outp c ∧ Post m H sp xs M

/-- **`mp_clear_multi` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp : Nat} {xs : List Arg}
    {ra : BitVec 64}, Pre m v H sp xs ra →
    Triple (At Fn.MpClearMulti.entry ((1, ra) :: argRegs 0 (args (ptrs xs))) m v.keep outp)
      (Ret m v outp H sp xs ra)

end Tom.Machine.Api.MpClearMulti
