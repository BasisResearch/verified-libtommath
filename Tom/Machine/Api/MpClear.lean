import Tom.Machine.Api.Heap
import Tom.Machine.Api.Un
import Tom.Machine.Fn.MpClear

/-!
# `mp_clear`: the standard contract

`mp_clear(a)` for a live `a` (its digits the block `(dp, 4 * a->alloc)` at the
front of the heap's blocks, `Api/Heap.lean`) frees the digits and zeroes the
struct: `MpAt M a 0 cleared`, `Heap M H`, memory changed only in `Un.ws` (the
stack `[sp - 544, sp)`: its 32-byte frame and `free`'s 512; the struct; the
freed digit array) and the allocator's footprint `Foot H`. The callee-saved
registers are kept (`v.keep`).

`NullStatement`: `a->dp == NULL` returns at once, memory untouched.
-/

namespace Tom.Machine.Api.MpClear

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- The stack depth: the 32-byte frame and `free`'s. -/
abbrev F : Nat := 32 + depth

abbrev lay (sp pa adp : Nat) (a : MpInt) := Un.lay F sp pa adp a

/-- A cleared `mp_int`: every field zero, no digits. -/
abbrev cleared : MpInt := MpInt.cleared

/-- What `mp_clear(a)` needs, `a` live. -/
structure Pre (m : Mem) (v : Abi) (H : List (Nat × Nat)) (sp pa adp : Nat) (a : MpInt)
    (ra : BitVec 64) : Prop where
  repr : MpAt m pa adp a
  heap : Heap m (digBlk adp a :: H)
  st : Ram pa 24
  st_al : pa % 8 = 0
  soff : OffHeap pa 24
  ctx : ACtx m v sp F
  ra_al : ra.toNat % 4 = 0
  lay : Sound (lay sp pa adp a) Un.isW

/-- What it leaves. -/
structure Post (m : Mem) (H : List (Nat × Nat)) (sp pa adp : Nat) (a : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa 0 cleared
  heap : Heap M H
  frame : HFrm (lay sp pa adp a) Un.ws H m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (H : List (Nat × Nat)) (sp pa adp : Nat) (a : MpInt)
    (ra : BitVec 64) (c : Vsa.Machine.Config) : Prop :=
  ∃ M, At ra [(1, ra)] M v.keep outp c ∧ Post m H sp pa adp a M

/-- The entry: `ra`, `a0 = a`. -/
def entryL (ra : BitVec 64) (pa : Nat) : GRegs := [(1, ra), (10, BitVec.ofNat 64 pa)]

/-- **`mp_clear` on the machine**, `a` live. -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp pa adp : Nat} {a : MpInt}
    {ra : BitVec 64}, Pre m v H sp pa adp a ra →
    Triple (At Fn.MpClear.entry (entryL ra pa) m v.keep outp)
      (Ret m v outp H sp pa adp a ra)

/-- **`mp_clear` of a cleared `mp_int`** (`a->dp == NULL`): nothing written. -/
def NullStatement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {pa : Nat} {ra : BitVec 64},
    bytesT8 m (pa + 16) = 0#64 → Ram pa 24 → Img m → ra.toNat % 4 = 0 →
    Triple (At Fn.MpClear.entry (entryL ra pa) m v.keep outp)
      (At ra [(1, ra)] m v.keep outp)

end Tom.Machine.Api.MpClear
