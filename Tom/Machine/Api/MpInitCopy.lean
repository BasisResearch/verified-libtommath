import Tom.Machine.Api.MpInit
import Tom.Machine.Api.MpCopy
import Tom.Machine.Fn.MpInitCopy

/-!
# `mp_init_copy`: the standard contract

`mp_init_copy(a, b)` for a valid live `b` (`MpLive m H pb bdp b`) and a fresh
struct `a`: `mp_init_size(a, b->used)`, then `mp_copy(b, a)`. Non-null
(`MP_OKAY`): the block `(q, 4 n)` (`n = initPrec b->used`) is fresh and now
live, `a` is `MpLive` with `a'`, `CopyPost b (zeroN n) a'` (so `a'` is valid
with `b`'s value: `CopyPost.valid`). Null (`MP_MEM`): the heap as it was,
`a->dp = NULL`. Memory changes only in `ws` (the stack: its 48-byte frame and
`mp_init_size`'s 576 bytes, `mp_copy`'s 32 inside; `a`'s struct) and the
footprint `Foot H`; `b` is read only. Callee-saved registers kept.
-/

namespace Tom.Machine.Api.MpInitCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- The regions: the stack, `a`'s struct, `b`'s struct and digits, the code. -/
inductive R | stk | aS | bS | bD | code
  deriving DecidableEq

def isW : R → Bool
  | .stk | .aS => true
  | _ => false

def lay (F sp pa pb bdp : Nat) (b : MpInt) : R → Iv
  | .stk => ⟨sp - F, F⟩
  | .aS => ⟨pa, 24⟩
  | .bS => ⟨pb, 24⟩
  | .bD => ⟨bdp, 4 * b.alloc⟩
  | .code => textIv

def ws : List R := [.stk, .aS]

theorem all (r : R) : r ∈ [R.stk, .aS, .bS, .bD, .code] := by cases r <;> simp

/-- The stack depth: the 48-byte frame and `mp_init_size`'s. -/
abbrev F : Nat := 48 + MpInit.Fsize

/-- What `mp_init_copy(a, b)` needs. -/
structure Pre (m : Mem) (v : Abi) (H : List (Nat × Nat)) (sp pa pb bdp : Nat) (b : MpInt)
    (ra : BitVec 64) : Prop where
  heap : Heap m H
  st : Ram pa 24
  st_al : pa % 8 = 0
  soff : OffHeap pa 24
  live : MpLive m H pb bdp b
  vb : b.Valid
  apos : 0 < b.alloc
  gb : MpGeom pb bdp b.alloc
  ctx : ACtx m v sp F
  ra_al : ra.toNat % 4 = 0
  lay : Sound (lay F sp pa pb bdp b) isW

/-- **What it leaves** with result `r` (`n` digits allocated). -/
inductive Post (m M : Mem) (H : List (Nat × Nat)) (sp pa pb bdp : Nat) (b : MpInt) (n : Nat) :
    BitVec 64 → Prop
  | ok {q : Nat} {a' : MpInt} (fresh : Fresh H q (4 * n)) (heap : Heap M ((q, 4 * n) :: H))
      (live : MpLive M ((q, 4 * n) :: H) pa q a') (copy : CopyPost b (MpInt.zeroN n) a')
      (frame : HFrm (lay F sp pa pb bdp b) ws H m M) : Post m M H sp pa pb bdp b n 0#64
  | mem (heap : Heap M H) (dp : bytesT8 M (pa + 16) = 0#64) (frame : HFrm (lay F sp pa pb bdp b) ws H m M) :
      Post m M H sp pa pb bdp b n MpInit.memBV

def Ret (m : Mem) (v : Abi) (outp : Array String) (H : List (Nat × Nat)) (sp pa pb bdp : Nat) (b : MpInt)
    (ra : BitVec 64) (c : Vsa.Machine.Config) : Prop :=
  ∃ r M, At ra [(1, ra), (10, r)] M v.keep outp c ∧ Post m M H sp pa pb bdp b (initPrec b.used) r

/-- The entry: `ra`, `a0 = a`, `a1 = b`. -/
def entryL (ra : BitVec 64) (pa pb : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)]

/-- **`mp_init_copy(a, b)` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp pa pb bdp : Nat} {b : MpInt}
    {ra : BitVec 64}, Pre m v H sp pa pb bdp b ra →
    Triple (At Fn.MpInitCopy.entry (entryL ra pa pb) m v.keep outp)
      (Ret m v outp H sp pa pb bdp b ra)

end Tom.Machine.Api.MpInitCopy
