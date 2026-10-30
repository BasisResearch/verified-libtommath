import Tom.Machine.Seg.MontRedFast
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.MulCall
import Vsa.Sim.TripleCat

/-!
# `s_mp_montgomery_reduce_fast` on the machine: the segments

`s_mp_montgomery_reduce_fast(x, n, rho)` at `0x80003d9c` (216 instructions),
frame `4256` bytes: the spills at `[q, q + 48)` (`rho`, `olduse`,
`x`, `8 n->used`, `2 n->used`), the columns `W[MP_WARRAY]` (`mp_word`) at
`[q + 48, q + 4144)`, the saved `ra`, `s0`–`s11` at `[q + 4152, q + 4256)`.

* prologue `M1`–`M5` (`x->used ≤ MP_WARRAY`; `x->alloc > n->used`: no
  `mp_grow`, D5), `M6` (`x->dp`; `olduse = 0`: `M13`);
* the copy-in loop `M7`, `M8` (`W[i] = x[i]`), `M9` (`2 n->used ≥ olduse`:
  `M10` → `memset` of the high columns at `4038`, `M11`; else `M12`);
* the rows `M15`; per row `M16` → `jal __muldi3(W[ix] & MASK, rho)` at `3e84`
  → `M17` (`mu`); the inner loop `M18` → `jal __muldi3(n[iy], mu)` at `3ea4` →
  `M19` (`W[ix + iy] += …`); `M20` (`W[ix + 1] += W[ix] >> 28`);
* the tail carries `M21`–`M23`; the copy-out `M24`–`M26` (`x[i] = W[n->used +
  i] & MASK`, `i ≤ n->used`); `M27`, `M28` (`MP_ZERO_DIGITS` at `3f9c`);
  `M29` (`x->used := n->used + 1`) → `jal mp_clamp` at `3fb4`; `M30` → `jal
  mp_cmp_mag` at `3fc0`; `M31lt` + `M32` (return) or `M31ge` + `M33` (the
  epilogue and the tail call `s_mp_sub(x, n, x)`).

All of `s0`–`s11` are locals: the segments keep only `gp` and `tp` (`kF`).
-/


namespace Tom.Machine.Fn.MontRedFast

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mr_ctx" : tactic => `(tactic|
  (facts_ctx
   have : sMpMontgomeryReduceFastBase = 0x80003d9c := rfl
   have : sMpMontgomeryReduceFastCode.length = 216 := rfl))

/-- The registers every segment keeps. -/
def kF (v : Abi) : GRegs := [(3, v.gp), (4, v.tp)]

abbrev kFKeys : List Nat := [3, 4]

abbrev mask : BitVec 64 := 268435455#64

/-- The frame. -/
structure KF (q : Nat) : Prop where
  rs : Ram q 4256
  q_al : q % 16 = 0
  code_off : q + 4256 ≤ sMpMontgomeryReduceFastBase ∨ sMpMontgomeryReduceFastBase + 864 ≤ q

/-! ## The prologue -/

def entL (ra s0 : BitVec 64) (v : Abi) (q px pn rho : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (q + 4256)), (8, s0), (9, v.s.s1), (10, BitVec.ofNat 64 px), (11, BitVec.ofNat 64 pn),
   (12, BitVec.ofNat 64 rho), (18, v.s.s2), (19, v.s.s3), (20, v.s.s4), (21, v.s.s5), (22, v.s.s6), (23, v.s.s7),
   (24, v.s.s8), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

def m1L (ra s0 : BitVec 64) (v : Abi) (q' px pn rho ou : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 q'), (8, s0), (9, v.s.s1), (10, BitVec.ofNat 64 px), (11, BitVec.ofNat 64 pn),
   (12, BitVec.ofNat 64 rho), (14, BitVec.ofNat 64 ou), (18, v.s.s2), (19, v.s.s3), (20, v.s.s4), (21, v.s.s5),
   (22, v.s.s6), (23, v.s.s7), (24, v.s.s8), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

/-- `x->used`. -/
structure UFacts (m : Mem) (px ou : Nat) : Prop where
  rx : Ram px 24
  ou_v : bytesT4 m px = BitVec.ofNat 32 ou
  ou_lt : ou < 2 ^ 30

theorem m1_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (q px pn rho ou : Nat) (m : Mem)
    (hc : CodeAt m sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q) (hf : UFacts m px ou) :
    Triple (At 0x80003d9c#64 (entL ra s0 v q px pn rho) m (kF v) outp)
      (At 0x80003da4#64 (m1L ra s0 v (q + 4096) px pn rho ou) (writeLog m []) (kF v) outp) := by
  mr_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 m px) = BitVec.ofNat 64 ou := by
    rw [hf.ou_v, signExtend_ofNat32 _ (by have := hf.ou_lt; omega)]
  seg_step mrM1 0x80003da4#64 [rd4 m px]
    [1, 2, 8, 9, 10, 11, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [entL] [m1L] [h1] hc

/-- The saves of `ra`, `s0`–`s5`. -/
def log2a (ra s0 : BitVec 64) (v : Abi) (q : Nat) : List WEntry :=
  [(q + 4248, 8, ra), (q + 4240, 8, s0), (q + 4232, 8, v.s.s1), (q + 4224, 8, v.s.s2), (q + 4216, 8, v.s.s3),
   (q + 4208, 8, v.s.s4), (q + 4200, 8, v.s.s5)]

/-- The saves of `s6`–`s11`. -/
def log2b (v : Abi) (q : Nat) : List WEntry :=
  [(q + 4192, 8, v.s.s6), (q + 4184, 8, v.s.s7), (q + 4176, 8, v.s.s8), (q + 4168, 8, v.s.s9), (q + 4160, 8, v.s.s10),
   (q + 4152, 8, v.s.s11)]

theorem m2a_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (q px pn rho ou : Nat) (m : Mem)
    (hc : CodeAt m sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q) :
    Triple (At 0x80003da4#64 (m1L ra s0 v (q + 4096) px pn rho ou) m (kF v) outp)
      (At 0x80003dc0#64 (m1L ra s0 v (q + 4096) px pn rho ou) (writeLog m (log2a ra s0 v q)) (kF v) outp) := by
  mr_ctx
  seg_step mrM2a 0x80003dc0#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 12, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [m1L, log2a] [m1L] [] hc

theorem m2b_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (q px pn rho ou : Nat) (m : Mem)
    (hc : CodeAt m sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q) :
    Triple (At 0x80003dc0#64 (m1L ra s0 v (q + 4096) px pn rho ou) m (kF v) outp)
      (At 0x80003dd8#64 (m1L ra s0 v (q + 4096) px pn rho ou) (writeLog m (log2b v q)) (kF v) outp) := by
  mr_ctx
  seg_step mrM2b 0x80003dd8#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 12, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [m1L, log2b] [m1L] [] hc

/-- The frame, `olduse` spilled. -/
theorem m3_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (q px pn rho ou : Nat) (m : Mem)
    (hc : CodeAt m sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q) :
    Triple (At 0x80003dd8#64 (m1L ra s0 v (q + 4096) px pn rho ou) m (kF v) outp)
      (At 0x80003de4#64 (m1L ra s0 v (q) px pn rho ou)
        (writeLog m [(q + 16, 8, BitVec.ofNat 64 ou)]) (kF v) outp) := by
  mr_ctx
  seg_step mrM3 0x80003de4#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 12, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [m1L] [m1L] [] hc

/-- `m1L` without `a4`. -/
def m4L (ra s0 : BitVec 64) (v : Abi) (q' px pn rho : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 q'), (8, s0), (9, v.s.s1), (10, BitVec.ofNat 64 px), (11, BitVec.ofNat 64 pn),
   (12, BitVec.ofNat 64 rho), (18, v.s.s2), (19, v.s.s3), (20, v.s.s4), (21, v.s.s5),
   (22, v.s.s6), (23, v.s.s7), (24, v.s.s8), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

/-- `olduse ≤ MP_WARRAY`. -/
theorem m4_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (q px pn rho ou : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q)
    (hv : bytesT8 M (q + 16) = BitVec.ofNat 64 ou) (hou : ou ≤ 512) :
    Triple (At 0x80003de4#64 (m1L ra s0 v (q) px pn rho ou) M (kF v) outp)
      (At 0x80003df0#64 ((13, BitVec.ofNat 64 ou) :: m4L ra s0 v (q) px pn rho) (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_step mrM4 0x80003df0#64 [rd8 M (q + 16)]
    [1, 2, 8, 9, 10, 11, 12, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [m1L] [m4L] [hv] hc

/-- After the spills of `rho`, `x`: `s6 = n`, `s10 = n->used`, `a1 = olduse`. -/
def m5L (s0 : BitVec 64) (v : Abi) (q pn nu ou : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (q)), (8, s0), (9, v.s.s1), (11, BitVec.ofNat 64 ou), (18, v.s.s2), (19, v.s.s3),
   (20, v.s.s4), (21, v.s.s5), (22, BitVec.ofNat 64 pn), (23, v.s.s7), (24, v.s.s8), (25, v.s.s9),
   (26, BitVec.ofNat 64 nu), (27, v.s.s11)]

/-- The spills of `rho` and `x`. -/
def log5 (q px rho : Nat) : List WEntry := [(q + 8, 8, BitVec.ofNat 64 rho), (q + 24, 8, BitVec.ofNat 64 px)]

/-- `n->used`, `x->alloc`. -/
structure NFacts (M : Mem) (px pn nu al : Nat) : Prop where
  rx : Ram px 24
  rn : Ram pn 24
  nu_v : bytesT4 M pn = BitVec.ofNat 32 nu
  al_v : bytesT4 M (px + 4) = BitVec.ofNat 32 al
  nu_lt : nu < 2 ^ 30
  al_lt : al < 2 ^ 31

/-- `x->alloc > n->used` (no `mp_grow`). -/
theorem m5_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (q px pn rho ou nu al : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q) (hf : NFacts M px pn nu al)
    (hlt : nu < al) :
    Triple (At 0x80003df0#64 ((13, BitVec.ofNat 64 ou) :: m4L ra s0 v (q) px pn rho) M (kF v) outp)
      (At 0x80003e0c#64 (m5L s0 v q pn nu ou) (writeLog M (log5 q px rho)) (kF v) outp) := by
  mr_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pn) = BitVec.ofNat 64 nu := by
    rw [hf.nu_v, signExtend_ofNat32 _ (by have := hf.nu_lt; omega)]
  have h2 : BitVec.signExtend 64 (bytesT4 M (px + 4)) = BitVec.ofNat 64 al := by
    rw [hf.al_v, signExtend_ofNat32 _ hf.al_lt]
  seg_step mrM5 0x80003e0c#64 [rd4 M pn, rd4 M (px + 4)]
    [13, 1, 2, 8, 9, 10, 11, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [m4L, log5] [m5L] [h1, h2] hc

/-- `s4 = x->dp`. -/
abbrev m6L (s0 : BitVec 64) (v : Abi) (q pn nu ou xdp : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (q)), (8, s0), (9, v.s.s1), (11, BitVec.ofNat 64 ou), (18, v.s.s2), (19, v.s.s3),
   (20, BitVec.ofNat 64 xdp), (21, v.s.s5), (22, BitVec.ofNat 64 pn), (23, v.s.s7), (24, v.s.s8), (25, v.s.s9),
   (26, BitVec.ofNat 64 nu), (27, v.s.s11)]

/-- `x` from its spill, `x->dp`. -/
structure XFacts (M : Mem) (q px xdp : Nat) : Prop where
  k : KF q
  rx : Ram px 24
  px_v : bytesT8 M (q + 24) = BitVec.ofNat 64 px
  xdp_v : bytesT8 M (px + 16) = BitVec.ofNat 64 xdp

/-- `olduse = 0`. -/
theorem m6z_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (q px pn nu xdp : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hf : XFacts M q px xdp) :
    Triple (At 0x80003e0c#64 (m5L s0 v q pn nu 0) M (kF v) outp)
      (At 0x800040ac#64 (m6L s0 v q pn nu 0 xdp) (writeLog M []) (kF v) outp) := by
  mr_ctx
  have h1 := hf.px_v; have h2 := hf.xdp_v
  seg_step mrM6z 0x800040ac#64 [rd8 M (q + 24), rd8 M (px + 16)]
    [2, 8, 9, 11, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [m5L] [m6L] [h1, h2] hc

/-- `olduse > 0`. -/
theorem m6n_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (q px pn nu ou xdp : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hf : XFacts M q px xdp) (hou : 0 < ou)
    (hou' : ou < 2 ^ 30) :
    Triple (At 0x80003e0c#64 (m5L s0 v q pn nu ou) M (kF v) outp)
      (At 0x80003e18#64 (m6L s0 v q pn nu ou xdp) (writeLog M []) (kF v) outp) := by
  mr_ctx
  have h1 := hf.px_v; have h2 := hf.xdp_v
  seg_step mrM6n 0x80003e18#64 [rd8 M (q + 24), rd8 M (px + 16)]
    [2, 8, 9, 11, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [m5L] [m6L] [h1, h2] hc

/-! ## The copy-in loop -/

/-- The copy-in head `3e2c`, digit `i`: `a4 = &W[i]`, `a5 = &x[i]`, `a2 = &x[olduse]`, `s3 = W`. -/
abbrev cL (s0 : BitVec 64) (v : Abi) (q pn nu ou xdp i : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (q)), (8, s0), (9, v.s.s1), (11, BitVec.ofNat 64 ou),
   (12, BitVec.ofNat 64 (xdp + 4 * ou)), (14, BitVec.ofNat 64 ((q + 48) + 8 * i)), (15, BitVec.ofNat 64 (xdp + 4 * i)),
   (18, v.s.s2), (19, BitVec.ofNat 64 ((q + 48))), (20, BitVec.ofNat 64 xdp), (21, v.s.s5), (22, BitVec.ofNat 64 pn),
   (23, v.s.s7), (24, v.s.s8), (25, v.s.s9), (26, BitVec.ofNat 64 nu), (27, v.s.s11)]

theorem m7_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (q pn nu ou xdp : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q) (hou : ou < 2 ^ 30) :
    Triple (At 0x80003e18#64 (m6L s0 v q pn nu ou xdp) M (kF v) outp)
      (At 0x80003e2c#64 (cL s0 v q pn nu ou xdp 0) (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_step mrM7 0x80003e2c#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 11, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [m6L] [cL] [] hc

/-- A digit read. -/
structure DRead (M : Mem) (a y : Nat) : Prop where
  r : Ram a 4
  v : bytesT4 M a = BitVec.ofNat 32 y
  lt : y < 2 ^ 32

/-- The copy's store stays in `W`. -/
structure CFacts (q i : Nat) : Prop where
  k : KF q
  i_lt : i < 512

/-- `W[i] = x[i]`; the back edge. -/
theorem m8t_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (q pn nu ou xdp i y : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hf : CFacts q i)
    (hy : DRead M (xdp + 4 * i) y) (hi : i + 1 < ou) (hx : xdp + 4 * ou ≤ 2 ^ 32) :
    Triple (At 0x80003e2c#64 (cL s0 v q pn nu ou xdp i) M (kF v) outp)
      (At 0x80003e2c#64 (cL s0 v q pn nu ou xdp (i + 1))
        (writeLog M [((q + 48) + 8 * i, 8, BitVec.ofNat 64 y)]) (kF v) outp) := by
  mr_ctx
  have h1 : zero_extend (m := 64) (bytesT4 M (xdp + 4 * i)) = BitVec.ofNat 64 y := by
    rw [hy.v, zext32_ofNat _ hy.lt]
  seg_step mrM8t 0x80003e2c#64 [rd4 M (xdp + 4 * i)]
    [2, 8, 9, 11, 12, 14, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [cL] [cL] [h1] hc

/-- After the copy (`3e40`). -/
abbrev c1L (s0 : BitVec 64) (v : Abi) (q pn nu ou xdp : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (q)), (8, s0), (9, v.s.s1), (11, BitVec.ofNat 64 ou), (18, v.s.s2),
   (19, BitVec.ofNat 64 ((q + 48))), (20, BitVec.ofNat 64 xdp), (21, v.s.s5), (22, BitVec.ofNat 64 pn), (23, v.s.s7),
   (24, v.s.s8), (25, v.s.s9), (26, BitVec.ofNat 64 nu), (27, v.s.s11)]

/-- `W[i] = x[i]`; the exit. -/
theorem m8f_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (q pn nu ou xdp i y : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hf : CFacts q i)
    (hy : DRead M (xdp + 4 * i) y) (hi : i + 1 = ou) (hx : xdp + 4 * ou ≤ 2 ^ 32) :
    Triple (At 0x80003e2c#64 (cL s0 v q pn nu ou xdp i) M (kF v) outp)
      (At 0x80003e40#64 (c1L s0 v q pn nu ou xdp) (writeLog M [((q + 48) + 8 * i, 8, BitVec.ofNat 64 y)]) (kF v) outp) := by
  mr_ctx
  have h1 : zero_extend (m := 64) (bytesT4 M (xdp + 4 * i)) = BitVec.ofNat 64 y := by
    rw [hy.v, zext32_ofNat _ hy.lt]
  seg_step mrM8f 0x80003e40#64 [rd4 M (xdp + 4 * i)]
    [2, 8, 9, 11, 12, 14, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [cL] [c1L] [h1] hc

/-- The spill `2 n->used`. -/
theorem m9_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (q pn nu ou xdp : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q) (hnu : nu < 2 ^ 29) :
    Triple (At 0x80003e40#64 (c1L s0 v q pn nu ou xdp) M (kF v) outp)
      (At 0x80003e48#64 ((15, BitVec.ofNat 64 (2 * nu)) :: c1L s0 v q pn nu ou xdp)
        (writeLog M [(q + 40, 8, BitVec.ofNat 64 (2 * nu))]) (kF v) outp) := by
  mr_ctx
  seg_stepx mrM9 0x80003e48#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 11, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [c1L] [c1L] [] hc

/-- `2 n->used ≥ olduse`: zero the high columns. -/
theorem m9t_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (q pn nu ou xdp : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hnu : nu < 2 ^ 29) (hou : ou < 2 ^ 30)
    (hle : ou ≤ 2 * nu) :
    Triple (At 0x80003e48#64 ((15, BitVec.ofNat 64 (2 * nu)) :: c1L s0 v q pn nu ou xdp) M (kF v) outp)
      (At 0x80004014#64 ((15, BitVec.ofNat 64 (2 * nu)) :: c1L s0 v q pn nu ou xdp) (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_step mrM9t 0x80004014#64 ([] : List (List (BitVec 8)))
    [15, 2, 8, 9, 11, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [c1L] [c1L] [] hc

/-- `2 n->used < olduse`. -/
theorem m9f_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (q pn nu ou xdp : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hnu : nu < 2 ^ 29) (hou : ou < 2 ^ 30)
    (hlt : 2 * nu < ou) :
    Triple (At 0x80003e48#64 ((15, BitVec.ofNat 64 (2 * nu)) :: c1L s0 v q pn nu ou xdp) M (kF v) outp)
      (At 0x80003e4c#64 (c1L s0 v q pn nu ou xdp) (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_step mrM9f 0x80003e4c#64 ([] : List (List (BitVec 8)))
    [15, 2, 8, 9, 11, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [c1L] [c1L] [] hc

/-- At the rows (`3e50`): `s3 = W`, `s4 = x->dp`. -/
abbrev hL0 (s0 : BitVec 64) (v : Abi) (q pn nu xdp : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (q)), (8, s0), (9, v.s.s1), (18, v.s.s2), (19, BitVec.ofNat 64 ((q + 48))),
   (20, BitVec.ofNat 64 xdp), (21, v.s.s5), (22, BitVec.ofNat 64 pn), (23, v.s.s7), (24, v.s.s8), (25, v.s.s9),
   (26, BitVec.ofNat 64 nu), (27, v.s.s11)]

/-- `memset(&W[olduse], 0, 8 (2 n->used + 1 - olduse))` (as `memset` of the digits `[2 olduse, 4 n->used + 2)`). -/
theorem m10_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (q pn nu ou xdp : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q) (hnu : nu < 2 ^ 29)
    (hou : 0 < ou) (hle : ou ≤ 2 * nu) (hou' : ou < 2 ^ 30) :
    Triple (At 0x80004014#64 ((15, BitVec.ofNat 64 (2 * nu)) :: c1L s0 v q pn nu ou xdp) M (kF v) outp)
      (At 0x80004038#64 ((10, BitVec.ofNat 64 ((q + 48) + 4 * (2 * ou))) :: (11, 0#64) ::
          (12, BitVec.ofNat 64 (4 * (2 * (2 * nu + 1) - 2 * ou))) :: hL0 s0 v q pn nu xdp) (writeLog M []) (kF v) outp) := by
  mr_ctx
  have e : (ou + 18446744073709551615) % 4294967296 % 4294967296 * 4294967296 % 18446744073709551616 / 536870912 =
      8 * (ou - 1) := by omega
  seg_stepx mrM10 0x80004038#64 ([] : List (List (BitVec 8)))
    [15, 2, 8, 9, 11, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [c1L] [hL0] [e] hc

/-- After the `memset`: to the rows. -/
theorem m11_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (q pn nu xdp : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) :
    Triple (At 0x8000403c#64 (hL0 s0 v q pn nu xdp) M (kF v) outp)
      (At 0x80003e50#64 (hL0 s0 v q pn nu xdp) (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_step mrM11 0x80003e50#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [hL0] [hL0] [] hc

/-- `2 n->used < olduse`, `n->used > 0`: to the rows. -/
theorem m12_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (q pn nu ou xdp : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hnu : 0 < nu) (hnu' : nu < 2 ^ 29) :
    Triple (At 0x80003e4c#64 (c1L s0 v q pn nu ou xdp) M (kF v) outp)
      (At 0x80003e50#64 (hL0 s0 v q pn nu xdp) (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_step mrM12 0x80003e50#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 11, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [c1L] [hL0] [] hc

/-- `olduse = 0`: the spill `2 n->used`. -/
theorem m13a_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (q pn nu xdp : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q) (hnu : nu < 2 ^ 29) :
    Triple (At 0x800040ac#64 (m6L s0 v q pn nu 0 xdp) M (kF v) outp)
      (At 0x800040b4#64 ((15, BitVec.ofNat 64 (2 * nu)) :: m6L s0 v q pn nu 0 xdp)
        (writeLog M [(q + 40, 8, BitVec.ofNat 64 (2 * nu))]) (kF v) outp) := by
  mr_ctx
  seg_stepx mrM13a 0x800040b4#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 11, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [m6L] [m6L] [] hc

/-- `olduse = 0`: set up `memset(W, 0, 8 (2 n->used + 1))`. -/
theorem m13b_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (q pn nu xdp : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q) (hnu : nu < 2 ^ 29) :
    Triple (At 0x800040b4#64 ((15, BitVec.ofNat 64 (2 * nu)) :: m6L s0 v q pn nu 0 xdp) M (kF v) outp)
      (At 0x800040cc#64 ((10, BitVec.ofNat 64 ((q + 48) + 4 * 0)) :: (11, 0#64) ::
          (12, BitVec.ofNat 64 (4 * (2 * (2 * nu + 1) - 0))) :: hL0 s0 v q pn nu xdp) (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_stepx mrM13b 0x800040cc#64 ([] : List (List (BitVec 8)))
    [15, 2, 8, 9, 11, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [m6L] [hL0] [] hc

/-- After the `memset`, `n->used ≠ 0`: to the rows. -/
theorem m14_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (q pn nu xdp : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hnu : 0 < nu) (hnu' : nu < 2 ^ 29) :
    Triple (At 0x800040d0#64 (hL0 s0 v q pn nu xdp) M (kF v) outp)
      (At 0x80003e50#64 (hL0 s0 v q pn nu xdp) (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_step mrM14 0x80003e50#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [hL0] [hL0] [] hc

/-! ## The rows -/

/-- The row head `3e74`, row `ix`: `s2 = &W[ix]`, `s1 = &n[n->used]`, `s8 = n->dp`, `s9 = &W[n->used]`. -/
abbrev rowL (q pn nu xdp ndp ix : Nat) (j0 j7 j11 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (q)), (8, j0), (9, BitVec.ofNat 64 (ndp + 4 * nu)),
   (18, BitVec.ofNat 64 ((q + 48) + 8 * ix)), (19, BitVec.ofNat 64 ((q + 48))), (20, BitVec.ofNat 64 xdp), (21, mask),
   (22, BitVec.ofNat 64 pn), (23, j7), (24, BitVec.ofNat 64 ndp), (25, BitVec.ofNat 64 ((q + 48) + 8 * nu)),
   (26, BitVec.ofNat 64 nu), (27, j11)]

/-- `n->dp`. -/
structure NdFacts (M : Mem) (pn ndp : Nat) : Prop where
  rn : Ram pn 24
  ndp_v : bytesT8 M (pn + 16) = BitVec.ofNat 64 ndp

/-- The rows' set-up, the spill `8 n->used`. -/
theorem m15_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (q pn nu xdp ndp : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q) (hf : NdFacts M pn ndp)
    (hnu : nu < 2 ^ 29) :
    Triple (At 0x80003e50#64 (hL0 s0 v q pn nu xdp) M (kF v) outp)
      (At 0x80003e74#64 (rowL q pn nu xdp ndp 0 s0 v.s.s7 v.s.s11)
        (writeLog M [(q + 32, 8, BitVec.ofNat 64 (8 * nu))]) (kF v) outp) := by
  mr_ctx
  have h1 := hf.ndp_v
  seg_stepx mrM15 0x80003e74#64 [rd8 M (pn + 16)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [hL0] [rowL] [h1] hc

/-- A column read. -/
structure WRead (M : Mem) (a w : Nat) : Prop where
  r : Ram a 8
  v : bytesT8 M a = BitVec.ofNat 64 w
  lt : w < 2 ^ 64

/-- `a0 = W[ix] & MASK`, `a1 = rho`: the `mu` product. -/
theorem m16_step (v : Abi) (outp : Array String) (q pn nu xdp ndp ix rho w : Nat) (j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q)
    (hw : WRead M ((q + 48) + 8 * ix) w) (hr : bytesT8 M (q + 8) = BitVec.ofNat 64 rho) :
    Triple (At 0x80003e74#64 (rowL q pn nu xdp ndp ix j0 j7 j11) M (kF v) outp)
      (At 0x80003e84#64 ((10, BitVec.ofNat 64 (w % 268435456)) :: (11, BitVec.ofNat 64 rho) ::
        rowL q pn nu xdp ndp ix j0 j7 (BitVec.ofNat 64 ((q + 48) + 8 * ix))) (writeLog M []) (kF v) outp) := by
  mr_ctx
  have h1 := hw.v
  seg_step mrM16 0x80003e84#64 [rd8 M ((q + 48) + 8 * ix), rd8 M (q + 8)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [rowL] [rowL] [h1, hr] hc

/-- The inner head `3e98`: term `iy`, `s0 = mu`, `s7 = &n[iy]`, `s11 = &W[ix + iy]`. -/
abbrev iH (q pn nu xdp ndp ix iy mu : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (q)), (8, BitVec.ofNat 64 mu), (9, BitVec.ofNat 64 (ndp + 4 * nu)),
   (18, BitVec.ofNat 64 ((q + 48) + 8 * ix)), (19, BitVec.ofNat 64 ((q + 48))), (20, BitVec.ofNat 64 xdp), (21, mask),
   (22, BitVec.ofNat 64 pn), (23, BitVec.ofNat 64 (ndp + 4 * iy)), (24, BitVec.ofNat 64 ndp),
   (25, BitVec.ofNat 64 ((q + 48) + 8 * nu)), (26, BitVec.ofNat 64 nu), (27, BitVec.ofNat 64 ((q + 48) + 8 * (ix + iy)))]

/-- `mu = (W[ix] & MASK) rho & MASK`. -/
theorem m17_step (v : Abi) (outp : Array String) (q pn nu xdp ndp ix p : Nat) (j0 j7 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hp : p < 2 ^ 64) :
    Triple (At 0x80003e88#64 ((10, BitVec.ofNat 64 p) ::
        rowL q pn nu xdp ndp ix j0 j7 (BitVec.ofNat 64 ((q + 48) + 8 * ix))) M (kF v) outp)
      (At 0x80003e98#64 (iH q pn nu xdp ndp ix 0 (p % 268435456)) (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_stepx mrM17 0x80003e98#64 ([] : List (List (BitVec 8)))
    [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [rowL] [iH] [] hc

/-- Across the inner `__muldi3`: `s11` advanced. -/
abbrev iK (q pn nu xdp ndp ix iy mu : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (q)), (8, BitVec.ofNat 64 mu), (9, BitVec.ofNat 64 (ndp + 4 * nu)),
   (18, BitVec.ofNat 64 ((q + 48) + 8 * ix)), (19, BitVec.ofNat 64 ((q + 48))), (20, BitVec.ofNat 64 xdp), (21, mask),
   (22, BitVec.ofNat 64 pn), (23, BitVec.ofNat 64 (ndp + 4 * iy)), (24, BitVec.ofNat 64 ndp),
   (25, BitVec.ofNat 64 ((q + 48) + 8 * nu)), (26, BitVec.ofNat 64 nu),
   (27, BitVec.ofNat 64 ((q + 48) + 8 * (ix + iy) + 8))]

/-- `a0 = n[iy]`, `a1 = mu`. -/
theorem m18_step (v : Abi) (outp : Array String) (q pn nu xdp ndp ix iy mu y : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hy : DRead M (ndp + 4 * iy) y) :
    Triple (At 0x80003e98#64 (iH q pn nu xdp ndp ix iy mu) M (kF v) outp)
      (At 0x80003ea4#64 ((10, BitVec.ofNat 64 y) :: (11, BitVec.ofNat 64 mu) :: iK q pn nu xdp ndp ix iy mu)
        (writeLog M []) (kF v) outp) := by
  mr_ctx
  have h1 : zero_extend (m := 64) (bytesT4 M (ndp + 4 * iy)) = BitVec.ofNat 64 y := by
    rw [hy.v, zext32_ofNat _ hy.lt]
  seg_step mrM18 0x80003ea4#64 [rd4 M (ndp + 4 * iy)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [iH] [iK] [h1] hc

/-- The column store stays in `W`. -/
structure SFacts (q i : Nat) : Prop where
  k : KF q
  i_lt : i < 512

/-- `W[ix + iy] += n[iy] mu`; the back edge. -/
theorem m19t_step (v : Abi) (outp : Array String) (q pn nu xdp ndp ix iy mu w p : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hf : SFacts q (ix + iy))
    (hw : WRead M ((q + 48) + 8 * (ix + iy)) w) (hs : w + p < 2 ^ 64) (hi : iy + 1 < nu) (hn : ndp + 4 * nu ≤ 2 ^ 32) :
    Triple (At 0x80003ea8#64 ((10, BitVec.ofNat 64 p) :: iK q pn nu xdp ndp ix iy mu) M (kF v) outp)
      (At 0x80003e98#64 (iH q pn nu xdp ndp ix (iy + 1) mu)
        (writeLog M [((q + 48) + 8 * (ix + iy), 8, BitVec.ofNat 64 (w + p))]) (kF v) outp) := by
  mr_ctx
  have h1 := hw.v
  seg_step mrM19t 0x80003e98#64 [rd8 M ((q + 48) + 8 * (ix + iy))]
    [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [iK] [iH] [h1] hc

/-- After a row's terms (`3ebc`). -/
abbrev fxL (q pn nu xdp ndp ix mu : Nat) : GRegs := iH q pn nu xdp ndp ix nu mu

/-- `W[ix + iy] += n[iy] mu`; the exit. -/
theorem m19f_step (v : Abi) (outp : Array String) (q pn nu xdp ndp ix iy mu w p : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hf : SFacts q (ix + iy))
    (hw : WRead M ((q + 48) + 8 * (ix + iy)) w) (hs : w + p < 2 ^ 64) (hi : iy + 1 = nu) :
    Triple (At 0x80003ea8#64 ((10, BitVec.ofNat 64 p) :: iK q pn nu xdp ndp ix iy mu) M (kF v) outp)
      (At 0x80003ebc#64 (fxL q pn nu xdp ndp ix mu)
        (writeLog M [((q + 48) + 8 * (ix + iy), 8, BitVec.ofNat 64 (w + p))]) (kF v) outp) := by
  mr_ctx
  have h1 := hw.v
  seg_step mrM19f 0x80003ebc#64 [rd8 M ((q + 48) + 8 * (ix + iy))]
    [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [iK] [fxL, iH] [h1] hc

/-- `W[ix + 1] += W[ix] >> 28`; the next row. -/
theorem m20t_step (v : Abi) (outp : Array String) (q pn nu xdp ndp ix mu w0 w1 : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hf : SFacts q (ix + 1))
    (h0 : WRead M ((q + 48) + 8 * ix) w0) (h1 : WRead M ((q + 48) + 8 * ix + 8) w1) (hs : w1 + w0 / 268435456 < 2 ^ 64)
    (hi : ix + 1 < nu) (hnu : nu < 2 ^ 29) :
    Triple (At 0x80003ebc#64 (fxL q pn nu xdp ndp ix mu) M (kF v) outp)
      (At 0x80003e74#64 (rowL q pn nu xdp ndp (ix + 1) (BitVec.ofNat 64 mu) (BitVec.ofNat 64 (ndp + 4 * nu))
          (BitVec.ofNat 64 ((q + 48) + 8 * (ix + nu))))
        (writeLog M [((q + 48) + 8 * (ix + 1), 8, BitVec.ofNat 64 (w1 + w0 / 268435456))]) (kF v) outp) := by
  mr_ctx
  have e0 := h0.v; have e1 := h1.v
  seg_step mrM20t 0x80003e74#64 [rd8 M ((q + 48) + 8 * ix), rd8 M ((q + 48) + 8 * ix + 8)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [fxL, iH] [rowL] [e0, e1] hc

/-- After the rows (`3ed8`). -/
abbrev aL (q pn nu xdp ndp : Nat) (j0 j7 j11 : BitVec 64) : GRegs := rowL q pn nu xdp ndp nu j0 j7 j11

/-- `W[ix + 1] += W[ix] >> 28`; the rows' exit. -/
theorem m20f_step (v : Abi) (outp : Array String) (q pn nu xdp ndp ix mu w0 w1 : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hf : SFacts q (ix + 1))
    (h0 : WRead M ((q + 48) + 8 * ix) w0) (h1 : WRead M ((q + 48) + 8 * ix + 8) w1) (hs : w1 + w0 / 268435456 < 2 ^ 64)
    (hi : ix + 1 = nu) (hnu : nu < 2 ^ 29) :
    Triple (At 0x80003ebc#64 (fxL q pn nu xdp ndp ix mu) M (kF v) outp)
      (At 0x80003ed8#64 (aL q pn nu xdp ndp (BitVec.ofNat 64 mu) (BitVec.ofNat 64 (ndp + 4 * nu))
          (BitVec.ofNat 64 ((q + 48) + 8 * (ix + nu))))
        (writeLog M [((q + 48) + 8 * (ix + 1), 8, BitVec.ofNat 64 (w1 + w0 / 268435456))]) (kF v) outp) := by
  mr_ctx
  have e0 := h0.v; have e1 := h1.v
  seg_step mrM20f 0x80003ed8#64 [rd8 M ((q + 48) + 8 * ix), rd8 M ((q + 48) + 8 * ix + 8)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [fxL, iH] [aL, rowL] [e0, e1] hc

/-! ## The tail carries -/

/-- `2 n->used ≥ n->used + 1`. -/
theorem m21_step (v : Abi) (outp : Array String) (q pn nu xdp ndp : Nat) (j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q)
    (hv : bytesT8 M (q + 40) = BitVec.ofNat 64 (2 * nu)) (hnu : 1 ≤ nu) (hnu' : nu < 2 ^ 29) :
    Triple (At 0x80003ed8#64 (aL q pn nu xdp ndp j0 j7 j11) M (kF v) outp)
      (At 0x80003ee4#64 ((14, BitVec.ofNat 64 (nu + 1)) :: aL q pn nu xdp ndp j0 j7 j11) (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_stepx mrM21 0x80003ee4#64 [rd8 M (q + 40)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [aL, rowL] [aL, rowL] [hv] hc

/-- The tail head `3f14`, step `k`: `a2 = &W[n->used + k]`, `a5 = &W[n->used + k + 1]`, `a1 = &W[2 n->used + 1]`. -/
abbrev tL (q pn nu xdp ndp k : Nat) (j0 j7 j11 : BitVec 64) : GRegs :=
  (11, BitVec.ofNat 64 ((q + 48) + 8 * (2 * nu + 1))) :: (12, BitVec.ofNat 64 ((q + 48) + 8 * (nu + k))) ::
    (15, BitVec.ofNat 64 ((q + 48) + 8 * (nu + k + 1))) :: aL q pn nu xdp ndp j0 j7 j11

/-- The tail's set-up. -/
theorem m22_step (v : Abi) (outp : Array String) (q pn nu xdp ndp : Nat) (j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q)
    (h32 : bytesT8 M (q + 32) = BitVec.ofNat 64 (8 * nu))
    (h40 : bytesT8 M (q + 40) = BitVec.ofNat 64 (2 * nu)) (hnu : 1 ≤ nu) (hnu' : nu < 2 ^ 29) :
    Triple (At 0x80003ee4#64 ((14, BitVec.ofNat 64 (nu + 1)) :: aL q pn nu xdp ndp j0 j7 j11) M (kF v) outp)
      (At 0x80003f14#64 (tL q pn nu xdp ndp 0 j0 j7 j11) (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_stepx mrM22 0x80003f14#64 [rd8 M (q + 32), rd8 M (q + 40)]
    [14, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [aL, rowL] [tL, aL, rowL] [h32, h40] hc

/-- `W[n->used + k + 1] += W[n->used + k] >> 28`; the back edge. -/
theorem m23t_step (v : Abi) (outp : Array String) (q pn nu xdp ndp k w0 w1 : Nat) (j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hf : SFacts q (nu + k + 1))
    (h0 : WRead M ((q + 48) + 8 * (nu + k)) w0) (h1 : WRead M ((q + 48) + 8 * (nu + k + 1)) w1)
    (hs : w1 + w0 / 268435456 < 2 ^ 64) (hi : k + 1 < nu) :
    Triple (At 0x80003f14#64 (tL q pn nu xdp ndp k j0 j7 j11) M (kF v) outp)
      (At 0x80003f14#64 (tL q pn nu xdp ndp (k + 1) j0 j7 j11)
        (writeLog M [((q + 48) + 8 * (nu + k + 1), 8, BitVec.ofNat 64 (w1 + w0 / 268435456))]) (kF v) outp) := by
  mr_ctx
  have e0 := h0.v; have e1 := h1.v
  seg_step mrM23t 0x80003f14#64 [rd8 M ((q + 48) + 8 * (nu + k)), rd8 M ((q + 48) + 8 * (nu + k + 1))]
    [11, 12, 15, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [tL, aL, rowL] [tL, aL, rowL] [e0, e1] hc

/-- After the tail (`3f34`). -/
abbrev t1L (q pn nu xdp ndp : Nat) (j0 j7 j11 : BitVec 64) : GRegs := aL q pn nu xdp ndp j0 j7 j11

/-- `W[n->used + k + 1] += W[n->used + k] >> 28`; the exit. -/
theorem m23f_step (v : Abi) (outp : Array String) (q pn nu xdp ndp k w0 w1 : Nat) (j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hf : SFacts q (nu + k + 1))
    (h0 : WRead M ((q + 48) + 8 * (nu + k)) w0) (h1 : WRead M ((q + 48) + 8 * (nu + k + 1)) w1)
    (hs : w1 + w0 / 268435456 < 2 ^ 64) (hi : k + 1 = nu) :
    Triple (At 0x80003f14#64 (tL q pn nu xdp ndp k j0 j7 j11) M (kF v) outp)
      (At 0x80003f34#64 (t1L q pn nu xdp ndp j0 j7 j11)
        (writeLog M [((q + 48) + 8 * (nu + k + 1), 8, BitVec.ofNat 64 (w1 + w0 / 268435456))]) (kF v) outp) := by
  mr_ctx
  have e0 := h0.v; have e1 := h1.v
  seg_step mrM23f 0x80003f34#64 [rd8 M ((q + 48) + 8 * (nu + k)), rd8 M ((q + 48) + 8 * (nu + k + 1))]
    [11, 12, 15, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [tL, aL, rowL] [t1L, aL, rowL] [e0, e1] hc

/-! ## The copy-out -/

/-- The spill `8 n->used` again, `s3 = W`. -/
theorem m24_step (v : Abi) (outp : Array String) (q pn nu xdp ndp : Nat) (j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q) (hnu : nu < 2 ^ 29) :
    Triple (At 0x80003f34#64 (t1L q pn nu xdp ndp j0 j7 j11) M (kF v) outp)
      (At 0x80003f44#64 (t1L q pn nu xdp ndp j0 j7 j11) (writeLog M [(q + 32, 8, BitVec.ofNat 64 (8 * nu))])
        (kF v) outp) := by
  mr_ctx
  seg_step mrM24 0x80003f44#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [t1L, aL, rowL] [t1L, aL, rowL] [] hc

/-- The copy-out head `3f58`, digit `i`: `s3 = &W[n->used + i]`, `s4 = &x[i]`, `a4 = i`. -/
abbrev oL (q pn nu xdp ndp i : Nat) (j0 j7 j11 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (q)), (8, j0), (9, BitVec.ofNat 64 (ndp + 4 * nu)), (13, mask), (14, BitVec.ofNat 64 i),
   (18, BitVec.ofNat 64 ((q + 48) + 8 * nu)), (19, BitVec.ofNat 64 ((q + 48) + 8 * (nu + i))),
   (20, BitVec.ofNat 64 (xdp + 4 * i)), (21, mask), (22, BitVec.ofNat 64 pn), (23, j7), (24, BitVec.ofNat 64 ndp),
   (25, BitVec.ofNat 64 ((q + 48) + 8 * nu)), (26, BitVec.ofNat 64 nu), (27, j11)]

theorem m25_step (v : Abi) (outp : Array String) (q pn nu xdp ndp : Nat) (j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q)
    (h32 : bytesT8 M (q + 32) = BitVec.ofNat 64 (8 * nu)) (hnu : nu < 2 ^ 29) :
    Triple (At 0x80003f44#64 (t1L q pn nu xdp ndp j0 j7 j11) M (kF v) outp)
      (At 0x80003f58#64 (oL q pn nu xdp ndp 0 j0 j7 j11) (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_step mrM25 0x80003f58#64 [rd8 M (q + 32)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [t1L, aL, rowL] [oL] [h32] hc

/-- After the store of `x[i]` (`3f6c`). -/
abbrev o1L (q pn nu xdp ndp i : Nat) (j0 j7 j11 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (q)), (8, j0), (9, BitVec.ofNat 64 (ndp + 4 * nu)), (13, mask),
   (14, BitVec.ofNat 64 (i + 1)), (18, BitVec.ofNat 64 ((q + 48) + 8 * nu)),
   (19, BitVec.ofNat 64 ((q + 48) + 8 * (nu + i))), (20, BitVec.ofNat 64 (xdp + 4 * (i + 1))), (21, mask),
   (22, BitVec.ofNat 64 pn), (23, j7), (24, BitVec.ofNat 64 ndp), (25, BitVec.ofNat 64 ((q + 48) + 8 * nu)),
   (26, BitVec.ofNat 64 nu), (27, j11)]

/-- `x`'s digits off the code. -/
structure XdFacts (xdp al : Nat) : Prop where
  rx : Ram xdp (4 * al)
  al4 : xdp % 4 = 0
  code_d : xdp + 4 * al ≤ sMpMontgomeryReduceFastBase ∨ sMpMontgomeryReduceFastBase + 864 ≤ xdp

/-- `x[i] = W[n->used + i] & MASK`. -/
theorem m26a_step (v : Abi) (outp : Array String) (q pn nu xdp ndp i w al : Nat) (j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hf : XdFacts xdp al) (hi : i < al)
    (hw : WRead M ((q + 48) + 8 * (nu + i)) w) (hi' : i < 2 ^ 30) :
    Triple (At 0x80003f58#64 (oL q pn nu xdp ndp i j0 j7 j11) M (kF v) outp)
      (At 0x80003f6c#64 (o1L q pn nu xdp ndp i j0 j7 j11)
        (writeLog M [(xdp + 4 * i, 4, BitVec.ofNat 64 (w % 268435456))]) (kF v) outp) := by
  mr_ctx
  have e0 := hw.v
  seg_stepx mrM26a 0x80003f6c#64 [rd8 M ((q + 48) + 8 * (nu + i))]
    [2, 8, 9, 13, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [oL] [o1L] [e0] hc

/-- `n->used`. -/
structure N1Facts (M : Mem) (pn nu : Nat) : Prop where
  rn : Ram pn 24
  nu_v : bytesT4 M pn = BitVec.ofNat 32 nu
  nu_lt : nu < 2 ^ 29

/-- `n->used ≥ i + 1`: the back edge. -/
theorem m26t_step (v : Abi) (outp : Array String) (q pn nu xdp ndp i : Nat) (j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hf : N1Facts M pn nu)
    (hi : i + 1 ≤ nu) :
    Triple (At 0x80003f6c#64 (o1L q pn nu xdp ndp i j0 j7 j11) M (kF v) outp)
      (At 0x80003f58#64 (oL q pn nu xdp ndp (i + 1) j0 j7 j11) (writeLog M []) (kF v) outp) := by
  mr_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pn) = BitVec.ofNat 64 nu := by
    rw [hf.nu_v, signExtend_ofNat32 _ (by have := hf.nu_lt; omega)]
  seg_step mrM26t 0x80003f58#64 [rd4 M pn]
    [2, 8, 9, 13, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [o1L] [oL] [h1] hc

/-- After the copy-out (`3f78`): `a4 = n->used + 1`, `s4 = &x[n->used + 1]`. -/
abbrev o2L (q pn nu xdp ndp : Nat) (j0 j7 j11 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (q)), (8, j0), (9, BitVec.ofNat 64 (ndp + 4 * nu)), (14, BitVec.ofNat 64 (nu + 1)),
   (18, BitVec.ofNat 64 ((q + 48) + 8 * nu)), (19, BitVec.ofNat 64 ((q + 48) + 8 * (nu + nu + 1))),
   (20, BitVec.ofNat 64 (xdp + 4 * (nu + 1))), (21, mask), (22, BitVec.ofNat 64 pn), (23, j7),
   (24, BitVec.ofNat 64 ndp), (25, BitVec.ofNat 64 ((q + 48) + 8 * nu)), (26, BitVec.ofNat 64 nu), (27, j11)]

/-- `n->used < i + 1`: the exit. -/
theorem m26f_step (v : Abi) (outp : Array String) (q pn nu xdp ndp i : Nat) (j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hf : N1Facts M pn nu)
    (hi : i = nu) :
    Triple (At 0x80003f6c#64 (o1L q pn nu xdp ndp i j0 j7 j11) M (kF v) outp)
      (At 0x80003f78#64 (o2L q pn nu xdp ndp j0 j7 j11) (writeLog M []) (kF v) outp) := by
  mr_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pn) = BitVec.ofNat 64 nu := by
    rw [hf.nu_v, signExtend_ofNat32 _ (by have := hf.nu_lt; omega)]
  subst hi
  seg_step mrM26f 0x80003f78#64 [rd4 M pn]
    [2, 8, 9, 13, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [o1L] [o2L] [h1] hc

/-! ## `MP_ZERO_DIGITS`, `x->used`, the end -/

/-- `olduse - (n->used + 1) ≥ 0` spilled. -/
theorem m27p_step (v : Abi) (outp : Array String) (q pn nu xdp ndp ou : Nat) (j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q)
    (hv : bytesT8 M (q + 16) = BitVec.ofNat 64 ou) (hle : nu + 1 ≤ ou) (hou : ou < 2 ^ 30) :
    Triple (At 0x80003f78#64 (o2L q pn nu xdp ndp j0 j7 j11) M (kF v) outp)
      (At 0x80003f84#64 (o2L q pn nu xdp ndp j0 j7 j11)
        (writeLog M [(q + 16, 8, BitVec.ofNat 64 (ou - (nu + 1)))]) (kF v) outp) := by
  mr_ctx
  seg_stepx mrM27 0x80003f84#64 [rd8 M (q + 16)]
    [2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [o2L] [o2L] [hv] hc

/-- `olduse - (n->used + 1) < 0` spilled. -/
theorem m27n_step (v : Abi) (outp : Array String) (q pn nu xdp ndp ou : Nat) (j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q)
    (hv : bytesT8 M (q + 16) = BitVec.ofNat 64 ou) (hlt : ou < nu + 1) (hnu : nu < 2 ^ 29) :
    Triple (At 0x80003f78#64 (o2L q pn nu xdp ndp j0 j7 j11) M (kF v) outp)
      (At 0x80003f84#64 (o2L q pn nu xdp ndp j0 j7 j11)
        (writeLog M [(q + 16, 8, BitVec.ofNat 64 (18446744073709551616 - (nu + 1 - ou)))]) (kF v) outp) := by
  mr_ctx
  seg_stepx mrM27 0x80003f84#64 [rd8 M (q + 16)]
    [2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [o2L] [o2L] [hv] hc

/-- `o2L` without `a4`. -/
abbrev o3L (q pn nu xdp ndp : Nat) (j0 j7 j11 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (q)), (8, j0), (9, BitVec.ofNat 64 (ndp + 4 * nu)),
   (18, BitVec.ofNat 64 ((q + 48) + 8 * nu)), (19, BitVec.ofNat 64 ((q + 48) + 8 * (nu + nu + 1))),
   (20, BitVec.ofNat 64 (xdp + 4 * (nu + 1))), (21, mask), (22, BitVec.ofNat 64 pn), (23, j7),
   (24, BitVec.ofNat 64 ndp), (25, BitVec.ofNat 64 ((q + 48) + 8 * nu)), (26, BitVec.ofNat 64 nu), (27, j11)]

/-- Nothing to zero. -/
theorem m28z_step (v : Abi) (outp : Array String) (q pn nu xdp ndp d : Nat) (j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q)
    (hv : bytesT8 M (q + 16) = BitVec.ofNat 64 d) (hg : zopz0zKzJ_s (0#64) (BitVec.ofNat 64 d) = true) :
    Triple (At 0x80003f84#64 (o2L q pn nu xdp ndp j0 j7 j11) M (kF v) outp)
      (At 0x80003fa0#64 (o3L q pn nu xdp ndp j0 j7 j11) (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_step mrM28z 0x80003fa0#64 [rd8 M (q + 16)]
    [2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [o2L] [o3L] [hv, hg] hc

/-- Set up `memset(&x[n->used + 1], 0, 4 (olduse - n->used - 1))`. -/
theorem m28n_step (v : Abi) (outp : Array String) (q pn nu xdp ndp ou : Nat) (j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q)
    (hv : bytesT8 M (q + 16) = BitVec.ofNat 64 (ou - (nu + 1))) (hlt : nu + 1 < ou) (hou : ou < 2 ^ 30) :
    Triple (At 0x80003f84#64 (o2L q pn nu xdp ndp j0 j7 j11) M (kF v) outp)
      (At 0x80003f9c#64 ((10, BitVec.ofNat 64 (xdp + 4 * (nu + 1))) :: (11, 0#64) ::
        (12, BitVec.ofNat 64 (4 * (ou - (nu + 1)))) :: o3L q pn nu xdp ndp j0 j7 j11) (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_step mrM28n 0x80003f9c#64 [rd8 M (q + 16), rd8 M (q + 16)]
    [2, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [o2L] [o3L] [hv] hc

/-- `n->used`, `x` from its spill. -/
structure EFacts (M : Mem) (q px pn nu : Nat) : Prop where
  k : KF q
  rx : Ram px 24
  rn : Ram pn 24
  px_al : px % 8 = 0
  nu_v : bytesT4 M pn = BitVec.ofNat 32 nu
  px_v : bytesT8 M (q + 24) = BitVec.ofNat 64 px
  nu_lt : nu < 2 ^ 29
  code_x : px + 24 ≤ sMpMontgomeryReduceFastBase ∨ sMpMontgomeryReduceFastBase + 864 ≤ px

/-- `x->used := n->used + 1`, at the `mp_clamp(x)` call. -/
theorem m29_step (v : Abi) (outp : Array String) (q px pn nu xdp ndp : Nat) (j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hf : EFacts M q px pn nu) :
    Triple (At 0x80003fa0#64 (o3L q pn nu xdp ndp j0 j7 j11) M (kF v) outp)
      (At 0x80003fb4#64 ((10, BitVec.ofNat 64 px) :: o3L q pn nu xdp ndp j0 j7 j11)
        (writeLog M [(px, 4, BitVec.ofNat 64 (nu + 1))]) (kF v) outp) := by
  mr_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pn) = BitVec.ofNat 64 nu := by
    rw [hf.nu_v, signExtend_ofNat32 _ (by have := hf.nu_lt; omega)]
  have h2 := hf.px_v
  seg_stepx mrM29 0x80003fb4#64 [rd4 M pn, rd8 M (q + 24)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [o3L] [o3L] [h1, h2] hc

/-- At the `mp_cmp_mag(x, n)` call. -/
theorem m30_step (v : Abi) (outp : Array String) (q px pn nu xdp ndp : Nat) (j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q)
    (hv : bytesT8 M (q + 24) = BitVec.ofNat 64 px) :
    Triple (At 0x80003fb8#64 (o3L q pn nu xdp ndp j0 j7 j11) M (kF v) outp)
      (At 0x80003fc0#64 ((10, BitVec.ofNat 64 px) :: (11, BitVec.ofNat 64 pn) :: o3L q pn nu xdp ndp j0 j7 j11)
        (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_step mrM30 0x80003fc0#64 [rd8 M (q + 24)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [o3L] [o3L] [hv] hc

abbrev m1 : BitVec 64 := 18446744073709551615#64

/-- `x < n`: `MP_OKAY`. -/
theorem m31lt_step (v : Abi) (outp : Array String) (q pn nu xdp ndp : Nat) (r j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hr : r = m1) :
    Triple (At 0x80003fc4#64 ((10, r) :: o3L q pn nu xdp ndp j0 j7 j11) M (kF v) outp)
      (At 0x80003fd0#64 ((10, 0#64) :: o3L q pn nu xdp ndp j0 j7 j11) (writeLog M []) (kF v) outp) := by
  mr_ctx
  subst hr
  seg_step mrM31lt 0x80003fd0#64 ([] : List (List (BitVec 8)))
    [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [o3L] [o3L] [] hc

/-- `x ≥ n`: on to the tail call. -/
theorem m31ge_step (v : Abi) (outp : Array String) (q pn nu xdp ndp : Nat) (r j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hr : r ≠ m1) :
    Triple (At 0x80003fc4#64 ((10, r) :: o3L q pn nu xdp ndp j0 j7 j11) M (kF v) outp)
      (At 0x8000405c#64 (o3L q pn nu xdp ndp j0 j7 j11) (writeLog M []) (kF v) outp) := by
  mr_ctx
  have hb : (r == m1) = false := by simpa using hr
  seg_step mrM31ge 0x8000405c#64 ([] : List (List (BitVec 8)))
    [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [o3L] [o3L] [hb] hc

/-- The return: `a0 = MP_OKAY`, `s0`–`s11` restored. -/
def rL (ra s0 : BitVec 64) (v : Abi) (q : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (q + 4256)), (8, s0), (10, 0#64), (9, v.s.s1), (18, v.s.s2), (19, v.s.s3), (20, v.s.s4),
   (21, v.s.s5), (22, v.s.s6), (23, v.s.s7), (24, v.s.s8), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

/-- The saved registers. -/
structure HFacts (M : Mem) (ra s0 : BitVec 64) (v : Abi) (q : Nat) : Prop where
  k : KF q
  ra_al : ra.toNat % 4 = 0
  ra_v : bytesT8 M (q + 4248) = ra
  s0_v : bytesT8 M (q + 4240) = s0
  s1_v : bytesT8 M (q + 4232) = v.s.s1
  s2_v : bytesT8 M (q + 4224) = v.s.s2
  s3_v : bytesT8 M (q + 4216) = v.s.s3
  s4_v : bytesT8 M (q + 4208) = v.s.s4
  s5_v : bytesT8 M (q + 4200) = v.s.s5
  s6_v : bytesT8 M (q + 4192) = v.s.s6
  s7_v : bytesT8 M (q + 4184) = v.s.s7
  s8_v : bytesT8 M (q + 4176) = v.s.s8
  s9_v : bytesT8 M (q + 4168) = v.s.s9
  s10_v : bytesT8 M (q + 4160) = v.s.s10
  s11_v : bytesT8 M (q + 4152) = v.s.s11

/-- `q += 4096` (`lui t0`). -/
theorem m32a_step (v : Abi) (outp : Array String) (q : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q) :
    Triple (At 0x80003fd0#64 [(2, BitVec.ofNat 64 (q)), (10, 0#64)] M (kF v) outp)
      (At 0x80003fd8#64 [(2, BitVec.ofNat 64 (q + 4096)), (10, 0#64)] (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_stepx mrM32a 0x80003fd8#64 ([] : List (List (BitVec 8))) [2, 10] kFKeys [] [] [] hc

theorem m32_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (q : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hf : HFacts M ra s0 v q) :
    Triple (At 0x80003fd8#64 [(2, BitVec.ofNat 64 (q + 4096)), (10, 0#64)] M (kF v) outp)
      (At ra (rL ra s0 v q) (writeLog M []) (kF v) outp) := by
  mr_ctx
  have hra := hf.ra_al
  seg_step mrM32 ra [rd8 M (q + 4248), rd8 M (q + 4240), rd8 M (q + 4232), rd8 M (q + 4224), rd8 M (q + 4216),
      rd8 M (q + 4208), rd8 M (q + 4200), rd8 M (q + 4192), rd8 M (q + 4184), rd8 M (q + 4176), rd8 M (q + 4168),
      rd8 M (q + 4160), rd8 M (q + 4152)]
    [2, 10] kFKeys [] [rL]
    [hf.ra_v, hf.s0_v, hf.s1_v, hf.s2_v, hf.s3_v, hf.s4_v, hf.s5_v, hf.s6_v, hf.s7_v, hf.s8_v, hf.s9_v,
     hf.s10_v, hf.s11_v] hc

/-- At `s_mp_sub(x, n, x)` (the tail call): the caller's registers restored. -/
def tcL (ra s0 : BitVec 64) (v : Abi) (q px pn : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (q + 4256)), (8, s0), (10, BitVec.ofNat 64 px), (11, BitVec.ofNat 64 pn),
   (12, BitVec.ofNat 64 px), (9, v.s.s1), (18, v.s.s2), (19, v.s.s3), (20, v.s.s4), (21, v.s.s5), (22, v.s.s6),
   (23, v.s.s7), (24, v.s.s8), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

/-- `a2 = x`, `q += 4096` (`lui t0`). -/
theorem m33a_step (v : Abi) (outp : Array String) (q px pn nu xdp ndp : Nat) (j0 j7 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hk : KF q)
    (hv : bytesT8 M (q + 24) = BitVec.ofNat 64 px) :
    Triple (At 0x8000405c#64 (o3L q pn nu xdp ndp j0 j7 j11) M (kF v) outp)
      (At 0x80004068#64 [(2, BitVec.ofNat 64 (q + 4096)), (12, BitVec.ofNat 64 px), (22, BitVec.ofNat 64 pn)]
        (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_stepx mrM33a 0x80004068#64 [rd8 M (q + 24)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [o3L] [] [hv] hc

/-- The epilogue, then `j s_mp_sub`. -/
theorem m33_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (q px pn : Nat) (M : Mem)
    (hc : CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode) (hf : HFacts M ra s0 v q) :
    Triple (At 0x80004068#64 [(2, BitVec.ofNat 64 (q + 4096)), (12, BitVec.ofNat 64 px), (22, BitVec.ofNat 64 pn)]
        M (kF v) outp)
      (At 0x80004564#64 (tcL ra s0 v q px pn) (writeLog M []) (kF v) outp) := by
  mr_ctx
  seg_step mrM33 0x80004564#64 [rd8 M (q + 4248), rd8 M (q + 4240), rd8 M (q + 4232),
      rd8 M (q + 4224), rd8 M (q + 4216), rd8 M (q + 4208), rd8 M (q + 4200), rd8 M (q + 4184), rd8 M (q + 4176),
      rd8 M (q + 4168), rd8 M (q + 4160), rd8 M (q + 4152), rd8 M (q + 4192)]
    [2, 12, 22] kFKeys [] [tcL]
    [hf.ra_v, hf.s0_v, hf.s1_v, hf.s2_v, hf.s3_v, hf.s4_v, hf.s5_v, hf.s6_v, hf.s7_v, hf.s8_v, hf.s9_v,
     hf.s10_v, hf.s11_v] hc

end Tom.Machine.Fn.MontRedFast
