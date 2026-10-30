import Vsa.Elf
import Vsa.Sim.InitValues

/-!
`ext_decode bv` is definitionally `encdec_backwards
bv`, so the two statements coincide after unfolding.

Staging discipline: a one-pass simp times out; the decode is peeled
in stages, closing the width-coerced residuals with
`BitVec.eq_of_toNat_eq; decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem decode_spike_addi
    (σ : SequentialState RegisterType trivialChoiceSource)
    (_hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hpriv : σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hsec : σ.regs.get? Register.mseccfg =
      some ((0#64) : RegisterType Register.mseccfg)) :
    (ext_decode 0x00000513#32).run σ =
      .ok (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5,
        regidx.Regidx 0x0a#5, iop.ADDI)) σ := by
  simp only [ext_decode, encdec_backwards]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    get_xLPE, readReg, Vsa.Sim.initMisa]
  simp +decide [encdec_reg_backwards, encdec_iop_backwards,
    EStateM.bind, pure, EStateM.pure]

end Vsa.Sim
