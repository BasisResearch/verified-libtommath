import Tom.Machine.Seg.MontNorm
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.BitW
import Tom.Machine.Kit.BitD
import Vsa.Sim.TripleCat

/-!
# `mp_montgomery_calc_normalization` on the machine: the segments

`mp_montgomery_calc_normalization(a, b)` at `0x800058b4` (75 instructions). The
segments, in program order, with the calls between them (made by the assembly,
`call_std`): `p_step` (save `ra`, `s0`–`s3`) → `jal mp_count_bits(b)` at `58d8`.
`b->used > 1`: `ua_step` → `jal __moddi3(cb, 28)` at `58ec` → `a2_step` (the
exponent `28 (used - 1) + bits - 1`, `BitW.mul28W`) → `jal mp_2expt(a, e)` at `5910`
→ `a3_step` (save `s4`, `s5`; `x := bits - 1`). `b->used ≤ 1`: `ub_step` (save
`s4`, `s5`; `x := 0`) → `jal mp_set(a, 1)` at `59ac` → `b2_step`. The loop at
`5930`, counter `xv k` (`x = k - 1`, `xv 0 = -1`): `l1_step` → `jal mp_mul_2(a, a)`
at `5938` → `l2_step` → `jal mp_cmp_mag(a, b)` at `594c` → `MP_LT`: `lt_step`;
otherwise `ge_step` → `jal s_mp_sub(a, b, a)` at `5964` → `l4_step`; at `596c`
`n_step` (back) or `x_step` (`x = 28`: restore, `MP_OKAY`). The locals are
`s0`–`s5`: the segments keep `keepN`.
-/



namespace Tom.Machine.Fn.MontNorm

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mnorm_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpMontgomeryCalcNormalizationBase = 0x800058b4 := rfl
   have : mpMontgomeryCalcNormalizationCode.length = 75 := rfl))

def entry : BitVec 64 := 0x800058b4#64

/-- `Abi.keepR1` without `s2`–`s5` (locals here). -/
def keepN (v : Abi) : GRegs :=
  [(3, v.gp), (4, v.tp), (22, v.s.s6), (23, v.s.s7), (24, v.s.s8), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

abbrev keysN : List Nat := [3, 4, 22, 23, 24, 25, 26, 27]

/-- The entry: `a0 = a`, `a1 = b`. -/
def entryL (ra s0 : BitVec 64) (sp pa pb : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)]

/-- The callee-saved registers this function uses. -/
structure Sv where
  s1 : BitVec 64
  s2 : BitVec 64
  s3 : BitVec 64
  s4 : BitVec 64
  s5 : BitVec 64

/-- The entry, `s1`–`s5` carried. -/
def entry1 (ra s0 : BitVec 64) (w : Sv) (sp pa pb : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, w.s1), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb),
   (18, w.s2), (19, w.s3), (20, w.s4), (21, w.s5)]

/-- The return (`MP_OKAY`), `s1`–`s5` carried. -/
def ret1 (ra s0 : BitVec 64) (w : Sv) (sp : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, w.s1), (10, 0#64), (18, w.s2), (19, w.s3), (20, w.s4),
   (21, w.s5)]

/-- The stack frame. -/
structure FFacts (sp : Nat) : Prop where
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  code_off : sp ≤ mpMontgomeryCalcNormalizationBase ∨ mpMontgomeryCalcNormalizationBase + 300 ≤ sp - 64

/-- The first frame stores (`s0`, `s3`, `s1`, `ra`, `s2`). -/
def frameLog1 (ra s0 : BitVec 64) (w : Sv) (sp : Nat) : List WEntry :=
  [(sp - 16, 8, s0), (sp - 40, 8, w.s3), (sp - 24, 8, w.s1), (sp - 8, 8, ra), (sp - 32, 8, w.s2)]

/-- The second frame stores (`s4`, `s5`). -/
def frameLog2 (w : Sv) (sp : Nat) : List WEntry := [(sp - 48, 8, w.s4), (sp - 56, 8, w.s5)]

/-- At the `mp_count_bits(b)` call (`58d8`): `s0 = a`, `s3 = b`. -/
def cbL (w : Sv) (sp pa pb : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (9, w.s1), (10, BitVec.ofNat 64 pb), (18, w.s2),
   (19, BitVec.ofNat 64 pb), (20, w.s4), (21, w.s5)]

/-- Save the frame, set up `mp_count_bits(b)`. -/
theorem p_step (ra s0 : BitVec 64) (w : Sv) (v : Abi) (outp : Array String) (sp pa pb : Nat) (m : Mem)
    (hc : CodeAt m mpMontgomeryCalcNormalizationBase mpMontgomeryCalcNormalizationCode) (hs : FFacts sp) :
    Triple (At entry (entry1 ra s0 w sp pa pb) m (keepN v) outp)
      (At 0x800058d8#64 (cbL w sp pa pb) (writeLog m (frameLog1 ra s0 w sp)) (keepN v) outp) := by
  mnorm_ctx
  seg_step normP 0x800058d8#64 ([] : List (List (BitVec 8))) [1, 2, 8, 9, 10, 11, 18, 19, 20, 21] keysN
    [entry, entry1, frameLog1] [cbL] [] hc

/-- After `mp_count_bits`: `a0 = cb`. -/
def r0L (w : Sv) (sp pa pb cb : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (9, w.s1), (10, BitVec.ofNat 64 cb), (18, w.s2),
   (19, BitVec.ofNat 64 pb), (20, w.s4), (21, w.s5)]

/-- `b->used`. -/
structure BFacts (M : Mem) (pb u : Nat) : Prop where
  rb : Ram pb 24
  u_v : bytesT4 M pb = BitVec.ofNat 32 u
  u_lt : u < 2 ^ 31

/-- At the `__moddi3(cb, 28)` call (`58ec`): `s1 = b->used`. -/
def mdL (w : Sv) (sp pa pb u cb : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 u), (10, BitVec.ofNat 64 cb),
   (11, BitVec.ofNat 64 28), (18, w.s2), (19, BitVec.ofNat 64 pb), (20, w.s4), (21, w.s5)]

/-- `b->used > 1`: set up `__moddi3(cb, 28)`. -/
theorem ua_step (w : Sv) (v : Abi) (outp : Array String) (sp pa pb u cb : Nat) (M : Mem)
    (hc : CodeAt M mpMontgomeryCalcNormalizationBase mpMontgomeryCalcNormalizationCode) (hf : BFacts M pb u)
    (hu : 1 < u) :
    Triple (At 0x800058dc#64 (r0L w sp pa pb cb) M (keepN v) outp)
      (At 0x800058ec#64 (mdL w sp pa pb u cb) (writeLog M []) (keepN v) outp) := by
  mnorm_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pb) = BitVec.ofNat 64 u := by
    rw [hf.u_v, signExtend_ofNat32 _ hf.u_lt]
  seg_step normUA 0x800058ec#64 [rd4 M pb] [2, 8, 9, 10, 18, 19, 20, 21] keysN [r0L] [mdL] [h1] hc

/-- At the `mp_set(a, 1)` call (`59ac`): `s2 = 0`. -/
def stL (w : Sv) (sp pa pb u : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 u), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 1), (18, BitVec.ofNat 64 0), (19, BitVec.ofNat 64 pb), (20, w.s4), (21, w.s5)]

/-- `b->used ≤ 1`: save `s4`, `s5`, set up `mp_set(a, 1)`. -/
theorem ub_step (w : Sv) (v : Abi) (outp : Array String) (sp pa pb u cb : Nat) (M : Mem)
    (hc : CodeAt M mpMontgomeryCalcNormalizationBase mpMontgomeryCalcNormalizationCode) (hf : BFacts M pb u)
    (hs : FFacts sp) (hu : u ≤ 1) :
    Triple (At 0x800058dc#64 (r0L w sp pa pb cb) M (keepN v) outp)
      (At 0x800059ac#64 (stL w sp pa pb u) (writeLog M (frameLog2 w sp)) (keepN v) outp) := by
  mnorm_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pb) = BitVec.ofNat 64 u := by
    rw [hf.u_v, signExtend_ofNat32 _ hf.u_lt]
  seg_step normUB 0x800059ac#64 [rd4 M pb] [2, 8, 9, 10, 18, 19, 20, 21] keysN [r0L, frameLog2] [stL] [h1] hc

/-- The loop counter: `x = k - 1` (`xv 0 = -1`). -/
def xv (k : Nat) : BitVec 64 := if k = 0 then 18446744073709551615#64 else BitVec.ofNat 64 (k - 1)

/-- At the loop head (`5930`), counter `xv k`: `s4 = -1`, `s5 = 28`. -/
def hdL (s1 : BitVec 64) (sp pa pb k : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (9, s1), (18, xv k), (19, BitVec.ofNat 64 pb),
   (20, 18446744073709551615#64), (21, BitVec.ofNat 64 28)]

/-- After `mp_set`: on to the loop with `x = 0`. -/
theorem b2_step (s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb : Nat) (M : Mem)
    (hc : CodeAt M mpMontgomeryCalcNormalizationBase mpMontgomeryCalcNormalizationCode) :
    Triple (At 0x800059b0#64 [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (9, s1),
        (18, BitVec.ofNat 64 0), (19, BitVec.ofNat 64 pb)] M (keepN v) outp)
      (At 0x80005930#64 (hdL s1 sp pa pb 1) (writeLog M []) (keepN v) outp) := by
  mnorm_ctx
  seg_step normB2 0x80005930#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 19] keysN [] [hdL, xv] [] hc

/-- After `__moddi3`: `a0 = bits`. -/
def a0L (w : Sv) (sp pa pb u bits : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 u), (10, BitVec.ofNat 64 bits),
   (18, w.s2), (19, BitVec.ofNat 64 pb), (20, w.s4), (21, w.s5)]

/-- At the `mp_2expt(a, e)` call (`5910`): `s2 = bits`. -/
def e2L (w : Sv) (sp pa pb u e bits : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 (u - 1)), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 e),
   (18, BitVec.ofNat 64 bits), (19, BitVec.ofNat 64 pb), (20, w.s4), (21, w.s5)]

/-- `bits` returned: the exponent `28 (used - 1) + bits - 1`, set up `mp_2expt(a, e)`. -/
theorem a2_step (w : Sv) (v : Abi) (outp : Array String) (sp pa pb u bits : Nat) (M : Mem)
    (hc : CodeAt M mpMontgomeryCalcNormalizationBase mpMontgomeryCalcNormalizationCode) (hu : 1 < u)
    (hb : 28 * u < 2 ^ 31) (hbits : bits < 28) :
    Triple (At 0x800058f0#64 (a0L w sp pa pb u bits) M (keepN v) outp)
      (At 0x80005910#64 (e2L w sp pa pb u (28 * (u - 1) + bits - 1) bits) (writeLog M []) (keepN v) outp) := by
  mnorm_ctx
  seg_stepu normA2 0x80005910#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10, 18, 19, 20, 21] keysN [a0L] [e2L] [] hc
    using (try rw [show (u + 18446744073709551615) % 4294967296 % 4294967296 % 4294967296 = (u - 1) % 4294967296 by omega,
      BitW.mul28W' _ (by omega), BitD.norm_exp _ _ (by omega) hbits (by omega)]); exact ⟨congrArg (BitVec.ofNat 64) (by omega), rfl⟩

/-- After `mp_2expt`: save `s4`, `s5`; the counter `x := bits - 1`. -/
theorem a3_step (w : Sv) (v : Abi) (outp : Array String) (sp pa pb bits : Nat) (M : Mem)
    (hc : CodeAt M mpMontgomeryCalcNormalizationBase mpMontgomeryCalcNormalizationCode) (hs : FFacts sp)
    (hbits : bits < 28) :
    Triple (At 0x80005914#64 [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (10, 0#64),
        (18, BitVec.ofNat 64 bits), (19, BitVec.ofNat 64 pb), (20, w.s4), (21, w.s5)] M (keepN v) outp)
      (At 0x80005930#64 (hdL 0#64 sp pa pb bits) (writeLog M (frameLog2 w sp)) (keepN v) outp) := by
  mnorm_ctx
  seg_stepu normA3 0x80005930#64 ([] : List (List (BitVec 8))) [2, 8, 10, 18, 19, 20, 21] keysN [frameLog2] [hdL]
    [] hc using (rw [BitD.addiw_m1 bits (by omega)]; rfl)

/-- After a call in the loop: `a0 = r`. -/
def lrL (sp pa pb k : Nat) (r : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (10, r), (18, xv k), (19, BitVec.ofNat 64 pb),
   (20, 18446744073709551615#64), (21, BitVec.ofNat 64 28)]

/-- At the `mp_mul_2(a, a)` call (`5938`). -/
def mlL (s1 : BitVec 64) (sp pa pb k : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (9, s1), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pa),
   (18, xv k), (19, BitVec.ofNat 64 pb), (20, 18446744073709551615#64), (21, BitVec.ofNat 64 28)]

/-- The loop head: set up `mp_mul_2(a, a)`. -/
theorem l1_step (s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb k : Nat) (M : Mem)
    (hc : CodeAt M mpMontgomeryCalcNormalizationBase mpMontgomeryCalcNormalizationCode) :
    Triple (At 0x80005930#64 (hdL s1 sp pa pb k) M (keepN v) outp)
      (At 0x80005938#64 (mlL s1 sp pa pb k) (writeLog M []) (keepN v) outp) := by
  mnorm_ctx
  seg_step normL1 0x80005938#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 19, 20, 21] keysN [hdL] [mlL] [] hc

/-- At the `mp_cmp_mag(a, b)` call (`594c`): `s1 = MP_OKAY`. -/
def cmL (sp pa pb k : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (9, 0#64), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 pb), (18, xv k), (19, BitVec.ofNat 64 pb), (20, 18446744073709551615#64),
   (21, BitVec.ofNat 64 28)]

/-- `mp_mul_2` returned `MP_OKAY`: set up `mp_cmp_mag(a, b)`. -/
theorem l2_step (v : Abi) (outp : Array String) (sp pa pb k : Nat) (M : Mem)
    (hc : CodeAt M mpMontgomeryCalcNormalizationBase mpMontgomeryCalcNormalizationCode) :
    Triple (At 0x8000593c#64 (lrL sp pa pb k 0#64) M (keepN v) outp)
      (At 0x8000594c#64 (cmL sp pa pb k) (writeLog M []) (keepN v) outp) := by
  mnorm_ctx
  seg_step normL2 0x8000594c#64 ([] : List (List (BitVec 8))) [2, 8, 10, 18, 19, 20, 21] keysN [lrL] [cmL] [] hc

/-- After `mp_cmp_mag`: `s1 = MP_OKAY`, `a0 = r`. -/
def crL (sp pa pb k : Nat) (r : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (9, 0#64), (10, r), (18, xv k), (19, BitVec.ofNat 64 pb),
   (20, 18446744073709551615#64), (21, BitVec.ofNat 64 28)]

/-- At `596c`: one iteration done. -/
def jnL (sp pa pb k : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (9, 0#64), (18, xv k), (19, BitVec.ofNat 64 pb),
   (20, 18446744073709551615#64), (21, BitVec.ofNat 64 28)]

/-- `MP_LT`: no subtraction. -/
theorem lt_step (v : Abi) (outp : Array String) (sp pa pb k : Nat) (M : Mem)
    (hc : CodeAt M mpMontgomeryCalcNormalizationBase mpMontgomeryCalcNormalizationCode) :
    Triple (At 0x80005950#64 (crL sp pa pb k 18446744073709551615#64) M (keepN v) outp)
      (At 0x8000596c#64 (jnL sp pa pb k) (writeLog M []) (keepN v) outp) := by
  mnorm_ctx
  seg_step normLt 0x8000596c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10, 18, 19, 20, 21] keysN [crL] [jnL] [] hc

/-- At the `s_mp_sub(a, b, a)` call (`5964`). -/
def sbL (sp pa pb k : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pa), (9, 0#64), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 pb), (12, BitVec.ofNat 64 pa), (18, xv k), (19, BitVec.ofNat 64 pb),
   (20, 18446744073709551615#64), (21, BitVec.ofNat 64 28)]

/-- Not `MP_LT`: set up `s_mp_sub(a, b, a)`. -/
theorem ge_step (v : Abi) (outp : Array String) (sp pa pb k c : Nat) (M : Mem)
    (hc : CodeAt M mpMontgomeryCalcNormalizationBase mpMontgomeryCalcNormalizationCode) (hc1 : c ≤ 1) :
    Triple (At 0x80005950#64 (crL sp pa pb k (BitVec.ofNat 64 c)) M (keepN v) outp)
      (At 0x80005964#64 (sbL sp pa pb k) (writeLog M []) (keepN v) outp) := by
  mnorm_ctx
  seg_step normGe 0x80005964#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10, 18, 19, 20, 21] keysN [crL] [sbL] [] hc

/-- `s_mp_sub` returned `MP_OKAY`. -/
theorem l4_step (v : Abi) (outp : Array String) (sp pa pb k : Nat) (M : Mem)
    (hc : CodeAt M mpMontgomeryCalcNormalizationBase mpMontgomeryCalcNormalizationCode) :
    Triple (At 0x80005968#64 (crL sp pa pb k 0#64) M (keepN v) outp)
      (At 0x8000596c#64 (jnL sp pa pb k) (writeLog M []) (keepN v) outp) := by
  mnorm_ctx
  seg_step normL4 0x8000596c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10, 18, 19, 20, 21] keysN [crL] [jnL] [] hc

theorem xv_succ {k : Nat} (hk : k < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (xv k + 1#64)) = BitVec.ofNat 64 k := by
  unfold xv; split
  · subst_vars; decide
  · rw [show BitVec.ofNat 64 (k - 1) + 1#64 = BitVec.ofNat 64 k from by
      rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]; congr 1; omega,
      BitW.extractLsb_ofNatW _ (by omega)]
    exact signExtend_ofNat32 _ hk

/-- `x + 1 < 28`: back to the loop head. -/
theorem n_step (v : Abi) (outp : Array String) (sp pa pb k : Nat) (M : Mem)
    (hc : CodeAt M mpMontgomeryCalcNormalizationBase mpMontgomeryCalcNormalizationCode) (hk : k < 28) :
    Triple (At 0x8000596c#64 (jnL sp pa pb k) M (keepN v) outp)
      (At 0x80005930#64 (hdL 0#64 sp pa pb (k + 1)) (writeLog M []) (keepN v) outp) := by
  mnorm_ctx
  have hn := xv_succ (k := k) (by omega)
  seg_stepu normN 0x80005930#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 19, 20, 21] keysN [jnL] [hdL] [hn] hc
    using simp [xv]

/-- The whole saved frame. -/
structure RFacts (M : Mem) (ra s0 : BitVec 64) (w : Sv) (sp : Nat) : Prop where
  rs : Ram (sp - 64) 64
  sp_ge : 64 ≤ sp
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  s1_v : bytesT8 M (sp - 24) = w.s1
  s2_v : bytesT8 M (sp - 32) = w.s2
  s3_v : bytesT8 M (sp - 40) = w.s3
  s4_v : bytesT8 M (sp - 48) = w.s4
  s5_v : bytesT8 M (sp - 56) = w.s5
  ra_al : ra.toNat % 4 = 0

/-- `x = 28`: restore the frame, return `MP_OKAY`. -/
theorem x_step (ra s0 : BitVec 64) (w : Sv) (v : Abi) (outp : Array String) (sp pa pb : Nat) (M : Mem)
    (hc : CodeAt M mpMontgomeryCalcNormalizationBase mpMontgomeryCalcNormalizationCode) (hf : RFacts M ra s0 w sp) :
    Triple (At 0x8000596c#64 (jnL sp pa pb 28) M (keepN v) outp)
      (At ra (ret1 ra s0 w sp) (writeLog M []) (keepN v) outp) := by
  mnorm_ctx
  have hra := hf.ra_al
  have hn := xv_succ (k := 28) (by omega)
  have h1 : bytesT8 M (sp - 64 + 16) = w.s4 := by rw [show sp - 64 + 16 = sp - 48 by omega]; exact hf.s4_v
  have h2 : bytesT8 M (sp - 64 + 8) = w.s5 := by rw [show sp - 64 + 8 = sp - 56 by omega]; exact hf.s5_v
  have h3 : bytesT8 M (sp - 64 + 56) = ra := by rw [show sp - 64 + 56 = sp - 8 by omega]; exact hf.ra_v
  have h4 : bytesT8 M (sp - 64 + 48) = s0 := by rw [show sp - 64 + 48 = sp - 16 by omega]; exact hf.s0_v
  have h5 : bytesT8 M (sp - 64 + 32) = w.s2 := by rw [show sp - 64 + 32 = sp - 32 by omega]; exact hf.s2_v
  have h6 : bytesT8 M (sp - 64 + 24) = w.s3 := by rw [show sp - 64 + 24 = sp - 40 by omega]; exact hf.s3_v
  have h7 : bytesT8 M (sp - 64 + 40) = w.s1 := by rw [show sp - 64 + 40 = sp - 24 by omega]; exact hf.s1_v
  seg_step normX ra [rd8 M (sp - 64 + 16), rd8 M (sp - 64 + 8), rd8 M (sp - 64 + 56), rd8 M (sp - 64 + 48),
    rd8 M (sp - 64 + 32), rd8 M (sp - 64 + 24), rd8 M (sp - 64 + 40)] [2, 8, 9, 18, 19, 20, 21] keysN [jnL] [ret1]
    [hn, h1, h2, h3, h4, h5, h6, h7] hc

end Tom.Machine.Fn.MontNorm
