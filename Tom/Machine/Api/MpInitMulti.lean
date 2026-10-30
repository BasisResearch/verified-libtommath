import Tom.Machine.Api.Multi
import Tom.Machine.Api.MpInit
import Tom.Machine.Api.MpClear
import Tom.Machine.Fn.MpInitMulti

/-!
# `mp_init_multi`: the standard contract

`mp_init_multi(p₀, …, p_{k-1}, NULL)` for fresh structs `xs` (`Structs`,
`Api/Multi.lean`): `mp_init` each in turn. All succeed (`Post.ok`, `MP_OKAY`):
`ys` with `ptrs ys = xs`, each `zeroN 32` at a fresh block, the blocks
pairwise apart and apart from `H`'s, the heap `blocks ys ++ H`. Some
`mp_init(p_k)` fails (`Post.mem`, `MP_MEM`): the `k` before it are cleared
again (`mp_clear`), `p_k->dp = NULL`, the heap `H`. Memory changes only in the
stack `[sp - 672, sp)` (its 112-byte frame and `mp_init`'s 560), the structs
and `Foot H` (`W`).
-/

namespace Tom.Machine.Api.MpInitMulti

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Api.Multi

/-- The stack depth: the 112-byte frame and `mp_init`'s (`mp_clear`'s is less). -/
abbrev F : Nat := 112 + MpInit.Finit

/-- What `mp_init_multi(xs…, NULL)` needs. -/
structure Pre (m : Mem) (v : Abi) (H : List (Nat × Nat)) (sp : Nat) (xs : List Nat) (ra : BitVec 64) : Prop where
  heap : Heap m H
  st : Structs xs (sp - F) (F + argLen (xs.length + 1))
  sargs : StackArgs m sp (args xs)
  args_hi : sp + argLen (xs.length + 1) ≤ 0x100000000
  len : xs.length + 1 < 2 ^ 31
  ctx : ACtx m v sp F
  ra_al : ra.toNat % 4 = 0

/-- What it may write: the stack, the structs, the footprint. -/
def W (xs : List Nat) (H : List (Nat × Nat)) (sp : Nat) (a : Nat) : Prop :=
  Stk sp F a ∨ (∃ p ∈ xs, InBlk (p, 24) a) ∨ Foot H a

/-- The blocks of `ys` are apart from each other and from `H`'s. -/
structure Apart (ys : List Multi.Arg) (H : List (Nat × Nat)) : Prop where
  pw : (blocks ys).Pairwise fun e e' => Disj e.1 e.2 e'.1 e'.2
  off : ∀ e ∈ blocks ys, ∀ e' ∈ H, ∀ a, InBlk e a → ¬ InBlk e' a

/-- **What it leaves**, with result `r`. -/
inductive Post (m M : Mem) (H : List (Nat × Nat)) (sp : Nat) (xs : List Nat) : BitVec 64 → Prop
  | ok (ys : List Multi.Arg) (hp : ptrs ys = xs) (zero : ∀ y ∈ ys, y.2.2 = MpInt.zeroN defPrec)
      (live : ∀ y ∈ ys, MpAt M y.1 y.2.1 y.2.2) (heap : Heap M (blocks ys ++ H)) (apart : Apart ys H)
      (frame : Keep (W xs H sp) m M) : Post m M H sp xs 0#64
  | mem (k : Nat) (hk : k < xs.length) (cleared : ∀ i (h : i < k), MpAt M (xs[i]'(by omega)) 0 MpInt.cleared)
      (dp : bytesT8 M (xs[k] + 16) = 0#64) (heap : Heap M H) (frame : Keep (W xs H sp) m M) :
      Post m M H sp xs MpInit.memBV

def Ret (m : Mem) (v : Abi) (outp : Array String) (H : List (Nat × Nat)) (sp : Nat) (xs : List Nat)
    (ra : BitVec 64) (c : Vsa.Machine.Config) : Prop :=
  ∃ r M, At ra [(1, ra), (10, r)] M v.keep outp c ∧ Post m M H sp xs r

/-- **`mp_init_multi` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp : Nat} {xs : List Nat}
    {ra : BitVec 64}, Pre m v H sp xs ra →
    Triple (At Fn.MpInitMulti.entry ((1, ra) :: argRegs 0 (args xs)) m v.keep outp) (Ret m v outp H sp xs ra)

end Tom.Machine.Api.MpInitMulti
