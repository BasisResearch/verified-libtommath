import Tom.Machine.Api.Heap
import Tom.Machine.Fn.MpInit
import Tom.Spec.Init

/-!
# `mp_init`, `mp_init_size`: the standard contracts

`mp_init_size(a, size)` (`0 ≤ size < 2^31`) and `mp_init(a)` allocate the
digits of `a` with `calloc(n, 4)` (`n = initPrec size = max(3, size)`,
resp. `32`) and set `a` to zero. Non-null (`MP_OKAY`): the block `(q, 4 n)`
is fresh and now live, and `a` is `MpLive` with `MpInt.zeroN n`
(`Api/Heap.lean`). Null (`MP_MEM`): the heap as it was, `a->dp = NULL`.
Either way memory changed only in `ws` (the stack: the function's frame and
`calloc`'s 544 bytes; `a`'s struct) and the footprint `Foot H` (the fresh
block lies there). The callee-saved registers are kept (`v.keep`).
-/

namespace Tom.Machine.Api.MpInit

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- The regions: the stack, `a`'s struct, the code. -/
inductive R | stk | aS | code
  deriving DecidableEq

def isW : R → Bool
  | .code => false
  | _ => true

def lay (F sp pa : Nat) : R → Iv
  | .stk => ⟨sp - F, F⟩
  | .aS => ⟨pa, 24⟩
  | .code => textIv

def ws : List R := [.stk, .aS]

theorem all (r : R) : r ∈ [R.stk, .aS, .code] := by cases r <;> simp

/-- The stack depth of `mp_init_size`: its 32-byte frame and `calloc`'s. -/
abbrev Fsize : Nat := 32 + callocDepth

/-- The stack depth of `mp_init`: its 16-byte frame and `calloc`'s. -/
abbrev Finit : Nat := 16 + callocDepth

/-- What `mp_init_size(a, ·)`/`mp_init(a)` need: the heap, `a`'s struct (RAM,
aligned, off the allocator), the call context with stack depth `F`. -/
structure Pre (m : Mem) (v : Abi) (H : List (Nat × Nat)) (sp pa F : Nat) (ra : BitVec 64) : Prop where
  heap : Heap m H
  st : Ram pa 24
  st_al : pa % 8 = 0
  soff : OffHeap pa 24
  ctx : ACtx m v sp F
  ra_al : ra.toNat % 4 = 0
  lay : Sound (lay F sp pa) isW

/-- `MP_MEM` as a register value. -/
abbrev memBV : BitVec 64 := 0xfffffffffffffffe#64

/-- **What they leave** with `n` digits requested and result `r`. -/
inductive Post (m M : Mem) (H : List (Nat × Nat)) (sp pa F n : Nat) : BitVec 64 → Prop
  | ok {q : Nat} (fresh : Fresh H q (4 * n)) (heap : Heap M ((q, 4 * n) :: H))
      (live : MpLive M ((q, 4 * n) :: H) pa q (MpInt.zeroN n)) (frame : HFrm (lay F sp pa) ws H m M) :
      Post m M H sp pa F n 0#64
  | mem (heap : Heap M H) (dp : bytesT8 M (pa + 16) = 0#64) (frame : HFrm (lay F sp pa) ws H m M) :
      Post m M H sp pa F n memBV

def Ret (m : Mem) (v : Abi) (outp : Array String) (H : List (Nat × Nat)) (sp pa F n : Nat) (ra : BitVec 64)
    (c : Vsa.Machine.Config) : Prop :=
  ∃ r M, At ra [(1, ra), (10, r)] M v.keep outp c ∧ Post m M H sp pa F n r

/-- The entry of `mp_init_size`: `ra`, `a0 = a`, `a1 = size`. -/
def sizeL (ra : BitVec 64) (pa : Nat) (size : BitVec 64) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 pa), (11, size)]

/-- **`mp_init_size(a, size)` on the machine** (`0 ≤ size < 2^31`). -/
def SizeStatement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp pa size : Nat} {ra : BitVec 64},
    Pre m v H sp pa Fsize ra → size < 2 ^ 31 →
    Triple (At Fn.MpInit.sizeEntry (sizeL ra pa (BitVec.ofNat 64 size)) m v.keep outp)
      (Ret m v outp H sp pa Fsize (initPrec size) ra)

/-- **`mp_init_size(a, size)` with `size < 0`**: `MP_VAL`, nothing written. -/
def SizeValStatement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {pa : Nat} {size ra : BitVec 64},
    Img m → ra.toNat % 4 = 0 → zopz0zI_s size 0#64 = true →
    Triple (At Fn.MpInit.sizeEntry (sizeL ra pa size) m v.keep outp)
      (At ra [(1, ra), (10, 0xfffffffffffffffd#64)] m v.keep outp)

/-- The entry of `mp_init`: `ra`, `a0 = a`. -/
def initL (ra : BitVec 64) (pa : Nat) : GRegs := [(1, ra), (10, BitVec.ofNat 64 pa)]

/-- **`mp_init(a)` on the machine** (`MP_PREC = 32` digits). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp pa : Nat} {ra : BitVec 64},
    Pre m v H sp pa Finit ra →
    Triple (At Fn.MpInit.initEntry (initL ra pa) m v.keep outp)
      (Ret m v outp H sp pa Finit defPrec ra)

end Tom.Machine.Api.MpInit
