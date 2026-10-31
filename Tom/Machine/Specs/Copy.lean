import Tom.Machine.Conventions
import Tom.Machine.Fn.MpCopyGMainG
import Tom.Machine.Fn.MpCopyMain

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_copy`: the concise specifications (SPECS.lean), from `Fn.MpCopyGG5.correct`,
`Fn.MpCopy.alias_correct` -/

namespace Tom.Machine.Api.MpCopyG

/-- **`mp_copy(a, b)`**: `b ← a`, growing `b`; `MP_MEM` only when `b` had to grow. -/
theorem _root_.Specs.mp_copy {p : P} (cv : Conv m ra p.sp F (hin p)) (sound : Sound (lay p) isW)
    (a : MpOwn m p.H p.pa p.adp p.a) (b : MpOut m p.pb p.bdp p.b) (ne : p.pa ≠ p.pb) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb] optRet fun x M =>
      OptRes x (p.b.alloc < p.a.used) (fun b' => b'.Valid ∧ b'.val = p.a.val) ∧
      HPost (lay p) ws .bD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.MpCopyGG5.correct cv.ra_al
    ⟨cv.stk, a.valid.toShape, b.shape, a.valid.sign_ok, a.pos, ne, b.pos, b.off⟩ sound)
    cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => (CopyPost.specG a.valid b.shape hq).imp_right And.right

end Tom.Machine.Api.MpCopyG

namespace Tom.Machine.Api.MpCopy
open Tom.Machine.Api.Two

/-- **`mp_copy(a, a)`**: `MP_OKAY`, memory unchanged. -/
theorem _root_.Specs.mp_copy_alias {sp pa : Nat}
    {s0 : BitVec 64} (cv : ConvL m ra) :
    Triple (At entry ((1, ra) :: (2, BitVec.ofNat 64 sp) :: (8, s0) :: callArgs 10 [pa, pa]) m v.keepR outp)
      (At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] m v.keepR outp) :=
  Fn.MpCopy.alias_correct cv.ra_al cv.img

end Tom.Machine.Api.MpCopy
