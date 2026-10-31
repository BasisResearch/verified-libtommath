import Tom.Machine.Conventions
import Tom.Machine.Fn.MpAbsGMainG
import Tom.Machine.Fn.MpAbsMain

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_abs`: the concise specifications (SPECS.lean), from `Fn.MpAbsGG5.correct`,
`Fn.MpAbs.alias_correct` -/

namespace Tom.Machine.Api.MpAbsG

/-- **`mp_abs(a, b)`**: `b ← |a|`, growing `b`; `MP_MEM` only when `b` had to grow. -/
theorem _root_.Specs.mp_abs {p : P} (cv : Conv m ra p.sp F (hin p)) (sound : Sound (lay p) isW)
    (a : MpOwn m p.H p.pa p.adp p.a) (b : MpOut m p.pb p.bdp p.b) (ne : p.pa ≠ p.pb) :
    ApiTriple m v outp ra entry p.sp [p.pa, p.pb] optRet fun x M =>
      OptRes x (p.b.alloc < p.a.used) (fun b' => b'.Valid ∧ b'.val = p.a.mag) ∧
      HPost (lay p) ws .bD (out p x) (site' p x) (hin p) (hout p x) m M :=
  ApiTriple.of (Reg.call (Fn.MpAbsGG5.correct cv.ra_al
    ⟨cv.stk, a.valid.toShape, b.shape, a.valid.sign_ok, a.pos, ne, b.pos, b.off⟩ sound)
    cv.heap (by mp_regions)) fun
    | none, hq => hq
    | some _, hq => (AbsPost.spec a.valid (copyIn_grown b.shape
        (Nat.lt_of_le_of_lt a.valid.used_le a.valid.alloc_lt)).shape (copyIn_room _ _) hq).imp_right And.right

end Tom.Machine.Api.MpAbsG

namespace Tom.Machine.Api.MpAbs

/-- **`mp_abs(a, a)`**: `a ← |a|` (in place: the sign cleared). -/
theorem _root_.Specs.mp_abs_alias {sp pa adp : Nat}
    {a : MpInt} {s0 : BitVec 64} (cv : ConvL m ra) (sound : Sound (Un.lay 0 sp pa adp a) Un.isW)
    (ha : MpVal m pa adp a) :
    ApiTripleS m v outp ra s0 entry sp [pa, pa] 0#64 fun a' M =>
      (a'.Valid ∧ a'.val = a.mag) ∧ APost m sp pa adp a a' M :=
  ApiTripleS.of (Fn.MpAbs.alias_correct ⟨ha.mpAt, ha.valid.toShape, ha.geom, cv.ra_al, cv.img, sound⟩)
    fun _ _ h => (AbsPost.spec ha.valid ha.valid.toShape ha.valid.used_le h.abs).imp_right And.right

end Tom.Machine.Api.MpAbs
