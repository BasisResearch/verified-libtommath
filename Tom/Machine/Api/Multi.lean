import Tom.Machine.Api.Heap

/-!
# Lists of `mp_int`s: the varargs functions (`mp_init_multi`, `mp_clear_multi`)

`f(mp, ...)` takes a `NULL`-terminated list of `mp_int *`. With the RISC-V
calling convention the first eight arguments are in `a0..a7` (`argRegs`) and
the rest on the caller's stack at `sp, sp + 8, …` (`StackArgs`). Both
functions spill `a1..a7` right below their entry `sp`, so argument `j ≥ 1`
then lies at `sp - 64 + 8 j`: one array of slots.

An argument is an `Arg`: struct, digit pointer, value. `Structs ps lo len`:
the structs are RAM, aligned, off the allocator, pairwise apart, apart from
the stack window `[lo, lo + len)` (the frames and the stack arguments) and
from the code.
-/

namespace Tom.Machine.Api.Multi

open Vsa.Sim Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- An `mp_int` argument: struct, digits, value. -/
abbrev Arg := Nat × Nat × MpInt

/-- The struct pointers. -/
def ptrs (xs : List Arg) : List Nat := xs.map (·.1)

/-- The digit blocks. -/
def blocks (xs : List Arg) : List (Nat × Nat) := xs.map fun x => digBlk x.2.1 x.2.2

/-- The argument list: the pointers and the terminating `NULL`. -/
def args (ps : List Nat) : List Nat := ps ++ [0]

/-- `a0..a7` hold the first eight arguments. -/
def argRegs : Nat → List Nat → GRegs
  | _, [] => []
  | i, x :: xs => if i < 8 then (10 + i, BitVec.ofNat 64 x) :: argRegs (i + 1) xs else []

/-- The bytes of stack arguments for `n` arguments. -/
def argLen (n : Nat) : Nat := 8 * (n - 8)

/-- Arguments from the ninth on lie on the caller's stack at `sp`. -/
def StackArgs (m : Mem) (sp : Nat) (xs : List Nat) : Prop :=
  ∀ j (h : j < xs.length), 8 ≤ j → bytesT8 m (sp + 8 * (j - 8)) = BitVec.ofNat 64 xs[j]

/-- The structs of the arguments. -/
structure Structs (ps : List Nat) (lo len : Nat) : Prop where
  ram : ∀ p ∈ ps, Ram p 24
  al : ∀ p ∈ ps, p % 8 = 0
  off : ∀ p ∈ ps, OffHeap p 24
  pw : ps.Pairwise fun p q => Disj p 24 q 24
  stk : ∀ p ∈ ps, Disj p 24 lo len
  code : ∀ p ∈ ps, Disj p 24 textBase textLen

theorem mem_argRegs : ∀ (k : Nat) (xs : List Nat) (i : Nat) (h : i < xs.length), k + i < 8 →
    (10 + k + i, BitVec.ofNat 64 xs[i]) ∈ argRegs k xs
  | _, [], _, h, _ => absurd h (by simp)
  | k, x :: ys, 0, _, hk => by simp [argRegs, show k < 8 by omega]
  | k, x :: ys, i + 1, h, hk => by
    simp only [argRegs, show k < 8 by omega, ↓reduceIte, List.mem_cons]
    refine .inr ?_
    have := mem_argRegs (k + 1) ys i (by simpa using h) (by omega)
    rw [show 10 + k + (i + 1) = 10 + (k + 1) + i by omega]
    simpa using this

theorem keys_argRegs : ∀ (k : Nat) (xs : List Nat), ∀ q ∈ argRegs k xs, 10 ≤ q.1 ∧ q.1 < 18
  | _, [], _, h => by simp [argRegs] at h
  | k, x :: ys, q, h => by
    simp only [argRegs] at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · simp only; omega
      · have := keys_argRegs (k + 1) ys q h; omega
    · simp at h

theorem ptrs_append (xs ys : List Arg) : ptrs (xs ++ ys) = ptrs xs ++ ptrs ys := List.map_append ..

theorem blocks_append (xs ys : List Arg) : blocks (xs ++ ys) = blocks xs ++ blocks ys := List.map_append ..

end Tom.Machine.Api.Multi
