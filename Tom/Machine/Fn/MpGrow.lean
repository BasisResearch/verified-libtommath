import Tom.Machine.Seg.MpGrow
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Img

/-!
# `mp_grow` on the machine: the paths without `realloc`

`mp_grow(a, size)` at `0x80001270` (35 instructions). With `size < 0` it
returns `MP_VAL` (`mgrowVal`); with `size ≤ a->alloc` it returns `MP_OKAY`
(`mgrowOK`); in both cases it writes nothing and touches no stack. The
`realloc` path (`a->alloc < size`) needs the allocator contract and is not covered here.
-/


namespace Tom.Machine.Fn.MpGrow

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mgrow_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpGrowBase = 0x80001270 := rfl
   have : mpGrowCode.length = 35 := rfl))

def entry : BitVec 64 := 0x80001270#64

/-- The arguments: `a0 = a`, `a1 = size` (an `int`, sign-extended). -/
def entryL (ra : BitVec 64) (p : Nat) (size : BitVec 64) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 p), (11, size)]

/-- The return: `a0 = r`. -/
def retL (ra r : BitVec 64) : GRegs := [(1, ra), (10, r)]

/-- `a->alloc ≥ size ≥ 0`: `MP_OKAY`, nothing written. -/
theorem ok_step (ra : BitVec 64) (v : Abi) (outp : Array String) (p al size : Nat) (m : Mem)
    (hc : CodeAt m mpGrowBase mpGrowCode) (hra : ra.toNat % 4 = 0) (hp : Ram p 24)
    (hal : bytesT4 m (p + 4) = BitVec.ofNat 32 al) (hal' : al < 2 ^ 31) (hs : size ≤ al) :
    Triple (At entry (entryL ra p (BitVec.ofNat 64 size)) m v.keep outp)
      (At ra (retL ra 0#64) (writeLog m []) v.keep outp) := by
  mgrow_ctx
  have hsx : BitVec.signExtend 64 (bytesT4 m (p + 4)) = BitVec.ofNat 64 al := by
    rw [hal, signExtend_ofNat32 _ hal']
  seg_step mgrowOK ra [rd4 m (p + 4)] [1, 10, 11] abiKeys [entry, entryL] [retL] [hsx] hc

/-- `size < 0` (`zopz0zI_s`, Sail's signed `<`): `MP_VAL`, nothing written. -/
theorem val_step (ra : BitVec 64) (v : Abi) (outp : Array String) (p : Nat) (size : BitVec 64) (m : Mem)
    (hc : CodeAt m mpGrowBase mpGrowCode) (hra : ra.toNat % 4 = 0) (hs : zopz0zI_s size 0#64 = true) :
    Triple (At entry (entryL ra p size) m v.keep outp)
      (At ra (retL ra 0xfffffffffffffffd#64) (writeLog m []) v.keep outp) := by
  mgrow_ctx
  seg_step mgrowVal ra ([] : List (List (BitVec 8))) [1, 10, 11] abiKeys [entry, entryL] [retL] [hs] hc

/-- What `mp_grow(a, size)` needs to return without reallocating. -/
structure PreOK (m : Mem) (p dp : Nat) (a : MpInt) (size : Nat) (ra : BitVec 64) : Prop where
  repr : MpAt m p dp a
  shape : a.Shape
  geom : MpGeom p dp a.alloc
  room : size ≤ a.alloc
  ra_al : ra.toNat % 4 = 0
  img : Img m

/-- **`mp_grow` without `realloc`**: `size ≤ a->alloc` returns `MP_OKAY` and
leaves memory and the callee-saved registers as they were. -/
theorem correct_ok {m : Mem} {v : Abi} {outp : Array String} {p dp size : Nat} {a : MpInt} {ra : BitVec 64}
    (hP : PreOK m p dp a size ra) :
    Triple (At entry (entryL ra p (BitVec.ofNat 64 size)) m v.keep outp) (At ra (retL ra 0#64) m v.keep outp) :=
  ok_step ra v outp p a.alloc size m hP.img.mpGrow hP.ra_al (by simpa [Layout.sizeofMpInt] using hP.geom.st)
    (by simpa [Layout.offAlloc] using hP.repr.alloc) hP.shape.alloc_lt hP.room

end Tom.Machine.Fn.MpGrow
