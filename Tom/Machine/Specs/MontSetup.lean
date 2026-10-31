import Tom.Machine.Conventions
import Tom.Machine.Fn.MpMontSetupMain

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_montgomery_setup`: the concise specification (SPECS.lean), from
`Fn.MpMontSetup.correct` -/

namespace Tom.Machine.Api.MpMontSetup

/-- **`mp_montgomery_setup(n, rho)`**: for odd `n`, `*rho ← -1/n mod radix` and `MP_OKAY` (`MP_VAL`
for even `n`). -/
theorem _root_.Specs.mp_montgomery_setup {sp p dp rp rv : Nat} {n : MpInt}
    (cv : ConvS m ra sp 48 (lay sp p dp rp n) isW) (sp_v : v.sp = BitVec.ofNat 64 sp)
    (hn : MpOut m p dp n) (r : DigOut m rp rv) :
    Triple (At Fn.MpMontSetup.entry ((1, ra) :: callArgs 10 [p, rp]) m v.keep outp) fun cf =>
      ∃ ret rho M, At ra [(1, ra), (10, BitVec.ofInt 64 ret)] M v.keep outp cf ∧
        (n.mag % 2 = 1 → ret = Layout.mpOkay ∧ rho < radix ∧ (n.mag * rho + 1) % radix = 0) ∧
        Post m sp p dp rp n ret rho M :=
  Triple.rmap (fun _ ⟨ret, rho, M, hat, h⟩ => ⟨ret, rho, M, hat,
      fun hodd => Mont.SetupPost.spec hn.shape h.setup hodd, h⟩)
    (Fn.MpMontSetup.correct ⟨hn.mpAt, hn.shape, hn.pos, hn.geom, r.dig.ram, r.dig.al, cv.stk.ram,
      cv.stk.al, cv.sp_ge, sp_v, cv.ra_al, cv.img, cv.sound⟩)

end Tom.Machine.Api.MpMontSetup
