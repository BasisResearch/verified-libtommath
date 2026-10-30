import Tom.Machine.Api.MpSqrS
import Tom.Machine.Api.Std_gap9
import Tom.Machine.Fn.MpSqrG5K
import Tom.Machine.Kit.AnnFacts

/-!
# `mp_sqr` below the karatsuba cut-off, no room: the hypotheses bundle

The generated assemblies `Fn/MpSqrSMainG.lean`, `Fn/MpSqrSAMainG.lean` (annotations
`msqrs.asm.json`, `msqrsa.asm.json`, style `"pre"` as `msqr.asm.json`) run over the regions of
`Api/MpSqrS.lean` (its arm equations `layS_<r>` generated) with the contract's hypotheses
bundled (`GPreS`, `GPreSA`); `fastResG`, `fastResGA`: the growing `s_mp_sqr_fast`'s residue at `sp - 16`.
-/

namespace Tom.Machine.Fn.MpSqrSG5K

open Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

section
open Tom.Machine.Api.MpSqr (P kind isW hin)

structure GPreS (p : P) (m : Mem) (ra : BitVec 64) : Prop where
  ra4 : ra.toNat % 4 = 0
  res : MpSqrS.Res p
  lay : Sound (MpSqrS.lay p) isW
  bund : Bundle (MpSqrS.lay p) (kind p) m
  heap : AHeap m (hin p)
  off : ∀ r, Off (MpSqrS.lay p r) (hin p)

theorem fastResG {p : P} (h : MpSqrS.Res p) :
    SqrFastH.Res ⟨p.sp - 16, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩ := by
  have := h.small
  exact { stk := StkRes.down h.stk (by decide) (by decide)
          sa := h.va.toShape, sb := h.sb, bsign := h.bsign, warr := show 2 * p.a.used + 1 < 512 by omega
          apos := h.apos, bpos := h.bpos, boff := h.boff }

end

section
open Tom.Machine.Api.MpSqrA (P kind isW hin)

structure GPreSA (p : P) (m : Mem) (ra : BitVec 64) : Prop where
  ra4 : ra.toNat % 4 = 0
  res : MpSqrSA.Res p
  lay : Sound (MpSqrSA.lay p) isW
  bund : Bundle (MpSqrSA.lay p) (kind p) m
  heap : AHeap m (hin p)
  off : ∀ r, Off (MpSqrSA.lay p r) (hin p)

theorem fastResGA {p : P} (h : MpSqrSA.Res p) :
    SqrFastHA.Res ⟨p.sp - 16, p.pa, p.adp, p.a, p.H⟩ := by
  have := h.small
  exact { stk := StkRes.down h.stk (by decide) (by decide)
          sa := h.va.toShape, asign := h.va.sign_ok, warr := show 2 * p.a.used + 1 < 512 by omega
          apos := h.apos, aoff := h.aoff }

end

end Tom.Machine.Fn.MpSqrSG5K
