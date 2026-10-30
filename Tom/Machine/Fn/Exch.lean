import Tom.Machine.Seg.Exch
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Word
import Vsa.Sim.TripleCat

/-!
# `mp_exch` on the machine: the segment

`mp_exch(a, b)` at `0x80000e60` (13 instructions, no frame): `t = *a; *a = *b;
*b = t` as three `ld`/`sd` pairs into `a` and two `sd` and one `sw` (the
sign, without the padding after it) into `b`:
```
e60 ld a5,0(a1); ld a3,0(a0); lw a4,8(a0); sd a5,0(a0)
e70 ld a2,8(a1); ld a5,16(a0); sd a2,8(a0)
e7c ld a2,16(a1); sd a2,16(a0)
e84 sd a3,0(a1); sw a4,8(a1); sd a5,16(a1); ret
```
One chain; its write log is `exchLog`.
-/

namespace Tom.Machine.Fn.Exch

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "exch_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpExchBase = 0x80000e60 := rfl
   have : mpExchCode.length = 13 := rfl))

/-- Registers at the entry. -/
def entryL (ra : BitVec 64) (pa pb : Nat) : GRegs := [(1, ra), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)]

/-- The stores into `a`: `b`'s three doublewords. -/
def logA (m : Mem) (pa pb : Nat) : List WEntry :=
  [(pa, 8, bytesT8 m pb), (pa + 8, 8, bytesT8 m (pb + 8)), (pa + 16, 8, bytesT8 m (pb + 16))]

/-- The stores into `b`: `a`'s first doubleword, its sign, its digit pointer. -/
def logB (m : Mem) (pa pb sa : Nat) : List WEntry :=
  [(pb, 8, bytesT8 m pa), (pb + 8, 4, BitVec.ofNat 64 sa), (pb + 16, 8, bytesT8 m (pa + 16))]

/-- The two structs: in RAM, aligned, apart from each other and from the code. -/
structure Facts (m : Mem) (pa pb sa : Nat) : Prop where
  ra_ : Ram pa 24
  rb : Ram pb 24
  pa_al : pa % 8 = 0
  pb_al : pb % 8 = 0
  ab : pa + 24 ≤ pb ∨ pb + 24 ≤ pa
  a_code : pa + 24 ≤ mpExchBase ∨ mpExchBase + 52 ≤ pa
  b_code : pb + 24 ≤ mpExchBase ∨ mpExchBase + 52 ≤ pb
  sa_v : bytesT4 m (pa + 8) = BitVec.ofNat 32 sa
  sa_lt : sa < 2 ^ 31

/-- Registers at `e70`: `a3 = a`'s first doubleword, `a4 = a->sign`. -/
def l1 (ra : BitVec 64) (m : Mem) (pa pb sa : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb), (13, bytesT8 m pa), (14, BitVec.ofNat 64 sa)]

/-- Registers at `e7c`/`e84`: also `a5 = a->dp`. -/
def l2 (ra : BitVec 64) (m : Mem) (pa pb sa : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb), (13, bytesT8 m pa), (14, BitVec.ofNat 64 sa),
   (15, bytesT8 m (pa + 16))]

section
variable (ra : BitVec 64) (v : Abi) (outp : Array String) (pa pb sa : Nat) (m : Mem) (hf : Facts m pa pb sa)
include hf

theorem s1 (hc : CodeAt m mpExchBase mpExchCode) :
    Triple (At 0x80000e60#64 (entryL ra pa pb) m v.keep outp)
      (At 0x80000e70#64 (l1 ra m pa pb sa) (writeLog m [(pa, 8, bytesT8 m pb)]) v.keep outp) := by
  exch_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 m (pa + 8)) = BitVec.ofNat 64 sa := by
    rw [hf.sa_v, signExtend_ofNat32 _ hf.sa_lt]
  seg_stepw ex1 0x80000e70#64 [rd8 m pb, rd8 m pa, rd4 m (pa + 8)] [1, 10, 11] abiKeys [entryL] [l1] [h1] hc using
    ((repeat' apply And.intro) <;> first | rfl | exact True.intro | omega)

theorem s2 (M : Mem) (hc : CodeAt M mpExchBase mpExchCode) (e1 : bytesT8 M (pb + 8) = bytesT8 m (pb + 8))
    (e2 : bytesT8 M (pa + 16) = bytesT8 m (pa + 16)) :
    Triple (At 0x80000e70#64 (l1 ra m pa pb sa) M v.keep outp)
      (At 0x80000e7c#64 (l2 ra m pa pb sa) (writeLog M [(pa + 8, 8, bytesT8 m (pb + 8))]) v.keep outp) := by
  exch_ctx
  seg_stepw ex2 0x80000e7c#64 [rd8 M (pb + 8), rd8 M (pa + 16)] [1, 10, 11, 13, 14] abiKeys [l1] [l2] [e1, e2] hc using
    ((repeat' apply And.intro) <;> first | rfl | exact True.intro | omega)

theorem s3 (M : Mem) (hc : CodeAt M mpExchBase mpExchCode) (e1 : bytesT8 M (pb + 16) = bytesT8 m (pb + 16)) :
    Triple (At 0x80000e7c#64 (l2 ra m pa pb sa) M v.keep outp)
      (At 0x80000e84#64 (l2 ra m pa pb sa) (writeLog M [(pa + 16, 8, bytesT8 m (pb + 16))]) v.keep outp) := by
  exch_ctx
  seg_stepw ex3 0x80000e84#64 [rd8 M (pb + 16)] [1, 10, 11, 13, 14, 15] abiKeys [l2] [l2] [e1] hc using
    ((repeat' apply And.intro) <;> first | rfl | exact True.intro | omega)

theorem s4 (M : Mem) (hc : CodeAt M mpExchBase mpExchCode) (hra : ra.toNat % 4 = 0) :
    Triple (At 0x80000e84#64 (l2 ra m pa pb sa) M v.keep outp)
      (At ra [(1, ra)] (writeLog M (logB m pa pb sa)) v.keep outp) := by
  exch_ctx
  seg_stepw ex4 ra ([] : List (List (BitVec 8))) [1, 10, 11, 13, 14, 15] abiKeys [l2, logB] [] [] hc using
    ((repeat' apply And.intro) <;> first | rfl | exact True.intro | omega)

end

end Tom.Machine.Fn.Exch
