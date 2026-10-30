import Tom.Machine.Api.Heap
import Tom.Machine.Api.Un
import Tom.Machine.Fn.MpGrowR
import Tom.Spec.Init

/-!
# `mp_grow`: the standard contract, all paths

`mp_grow(a, size)` (`0 ≤ size < 2^31`) for a live `a` (its digits the block
`(dp, 4 * a->alloc)` at the front of the heap's blocks, `Api/Heap.lean`):

* `size ≤ a->alloc`: `MP_OKAY`, memory as it was (`Post.keep`);
* otherwise `realloc(dp, 4 * size)`: non-null (`Post.ok`): the fresh block
  `(q, 4 * size)` replaces `(dp, 4 * a->alloc)` in the heap, `a` is `a'` at
  `q` with `GrowPost a size a'` (the old digits, zeros above by `memset`,
  `alloc = size`; `GrowPost.spec`: same value, invariants kept); null
  (`Post.mem`, `MP_MEM`): the heap and `a` as they were.

Memory changes only in `Un.ws` (the stack `[sp - 544, sp)`: its 32-byte frame
and `realloc`'s 512; `a`'s struct and old digit array) and `Foot H` (where the
new block lies). The callee-saved registers are kept (`v.keep`).

`ValStatement`: `size < 0` returns `MP_VAL`, nothing written.
-/

namespace Tom.Machine.Api.MpGrow

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- The stack depth: the 32-byte frame and `realloc`'s (`memset` uses none). -/
abbrev F : Nat := 32 + depth

abbrev lay (sp p dp : Nat) (a : MpInt) := Un.lay F sp p dp a

/-- What `mp_grow(a, size)` needs. -/
structure Pre (m : Mem) (v : Abi) (H : List (Nat × Nat)) (sp p dp : Nat) (a : MpInt) (size : Nat)
    (ra : BitVec 64) : Prop where
  repr : MpAt m p dp a
  shape : a.Shape
  heap : Heap m (digBlk dp a :: H)
  st : Ram p 24
  st_al : p % 8 = 0
  soff : OffHeap p 24
  size_lt : size < 2 ^ 31
  ctx : ACtx m v sp F
  ra_al : ra.toNat % 4 = 0
  lay : Sound (lay sp p dp a) Un.isW

/-- `MP_MEM` as a register value. -/
abbrev memBV : BitVec 64 := 0xfffffffffffffffe#64

/-- **What it leaves**, with result `r`. -/
inductive Post (m M : Mem) (H : List (Nat × Nat)) (sp p dp : Nat) (a : MpInt) (size : Nat) :
    BitVec 64 → Prop
  /-- `size ≤ a->alloc`: nothing changed. -/
  | keep (hle : size ≤ a.alloc) (same : M = m) : Post m M H sp p dp a size 0#64
  /-- Reallocated: `a'` at the fresh block `q`. -/
  | ok {q : Nat} {a' : MpInt} (hlt : a.alloc < size) (fresh : Fresh H q (4 * size))
      (heap : Heap M ((q, 4 * size) :: H)) (repr : MpAt M p q a') (grow : GrowPost a size a')
      (frame : HFrm (lay sp p dp a) Un.ws H m M) : Post m M H sp p dp a size 0#64
  /-- `realloc` failed: the heap and `a` as they were. -/
  | mem (hlt : a.alloc < size) (heap : Heap M (digBlk dp a :: H)) (repr : MpAt M p dp a)
      (frame : HFrm (lay sp p dp a) Un.ws H m M) : Post m M H sp p dp a size memBV

def Ret (m : Mem) (v : Abi) (outp : Array String) (H : List (Nat × Nat)) (sp p dp : Nat) (a : MpInt)
    (size : Nat) (ra : BitVec 64) (c : Vsa.Machine.Config) : Prop :=
  ∃ r M, At ra [(1, ra), (10, r)] M v.keep outp c ∧ Post m M H sp p dp a size r

/-- The entry: `ra`, `a0 = a`, `a1 = size`. -/
def entryL (ra : BitVec 64) (p : Nat) (size : BitVec 64) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 p), (11, size)]

/-- **`mp_grow(a, size)` on the machine** (`0 ≤ size < 2^31`), all paths. -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp p dp : Nat} {a : MpInt}
    {size : Nat} {ra : BitVec 64}, Pre m v H sp p dp a size ra →
    Triple (At Fn.MpGrowR.entry (entryL ra p (BitVec.ofNat 64 size)) m v.keep outp)
      (Ret m v outp H sp p dp a size ra)

/-- **`mp_grow(a, size)` with `size < 0`**: `MP_VAL`, nothing written. -/
def ValStatement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {p : Nat} {size ra : BitVec 64},
    Img m → ra.toNat % 4 = 0 → zopz0zI_s size 0#64 = true →
    Triple (At Fn.MpGrowR.entry (entryL ra p size) m v.keep outp)
      (At ra [(1, ra), (10, 0xfffffffffffffffd#64)] m v.keep outp)

end Tom.Machine.Api.MpGrow
