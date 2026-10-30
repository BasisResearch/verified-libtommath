import Tom.Machine.Seg.MpSet
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.AutoEq
import Tom.Machine.Kit.Alu1
import Tom.Machine.Fn.Memset
import Vsa.Sim.TripleCat

/-!
# `mp_set` on the machine: the segments

`mp_set(a, b)` at `0x80001eb0` (17 instructions):
```
1eb0 ld a4,16(a0); slli a1,a1,36; srli a1,a1,36; sw a1,0(a4)   -- dp[0] := b & MP_MASK
1ec0 sw zero,8(a0)                                             -- sign := MP_ZPOS
1ec4 lw a5,0(a4); lw a2,4(a0); snez a3,a5                      -- used := (dp[0] != 0)
1ed0 sw a3,0(a0); subw a2,a2,a3; blez a2,1ef0                  -- alloc - used ≤ 0: return
1edc slli a5,a3,2; add a0,a4,a5; slli a2,a2,2; li a1,0; j memset
1ef0 ret
```
`msetA` (the digit and sign stores), `msetB` (the reloads, cut before the
`snez`, which is `z_step` by `Kit/Alu1.lean`), `msetC0`/`msetC1` (the
`used` store; return, or the tail jump into `memset(dp + used, 0, 4 (alloc - used))`).
-/


namespace Tom.Machine.Fn.MpSet

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mset_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpSetBase = 0x80001eb0 := rfl
   have : mpSetCode.length = 17 := rfl))

def entry : BitVec 64 := 0x80001eb0#64

/-- The arguments: `a0 = a`, `a1 = b`. -/
def entryL (ra : BitVec 64) (p bn : Nat) : GRegs := [(1, ra), (10, BitVec.ofNat 64 p), (11, BitVec.ofNat 64 bn)]

/-- At `1ec4`: `a4 = dp`. -/
def aL (ra : BitVec 64) (p dp : Nat) : GRegs := [(1, ra), (10, BitVec.ofNat 64 p), (14, BitVec.ofNat 64 dp)]

/-- At the `snez` (`1ecc`): `a5 = dp[0]`, `a2 = alloc`. -/
def bL (ra : BitVec 64) (p dp d al : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 p), (14, BitVec.ofNat 64 dp), (15, BitVec.ofNat 64 d), (12, BitVec.ofNat 64 al)]

/-- After it (`1ed0`): `a3 = used`. -/
def cL (ra : BitVec 64) (p dp u al : Nat) : GRegs :=
  [(13, BitVec.ofNat 64 u), (1, ra), (10, BitVec.ofNat 64 p), (14, BitVec.ofNat 64 dp), (12, BitVec.ofNat 64 al)]

/-- The first stores: `dp[0] := d`, `sign := 0`. -/
def alog (p dp d : Nat) : List WEntry := [(dp, 4, BitVec.ofNat 64 d), (p + 8, 4, 0#64)]

/-- The struct and the first digit. -/
structure SFacts (m : Mem) (p dp : Nat) : Prop where
  rp : Ram p 24
  p_al : p % 8 = 0
  rd : Ram dp 4
  dp_al : dp % 4 = 0
  dp_v : bytesT8 m (p + 16) = BitVec.ofNat 64 dp
  code_p : p + 24 ≤ mpSetBase ∨ mpSetBase + 68 ≤ p
  code_d : dp + 4 ≤ mpSetBase ∨ mpSetBase + 68 ≤ dp

theorem mask28 (bn : Nat) : bn * 2 ^ 36 % 18446744073709551616 / 2 ^ 36 = bn % 268435456 := by
  rw [show (18446744073709551616 : Nat) = 268435456 * 2 ^ 36 by decide, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (by decide)]

/-- `dp[0] := b & MP_MASK`, `sign := 0`. -/
theorem a_step (ra : BitVec 64) (v : Abi) (outp : Array String) (p dp bn : Nat) (m : Mem)
    (hc : CodeAt m mpSetBase mpSetCode) (hf : SFacts m p dp) :
    Triple (At entry (entryL ra p bn) m v.keep outp)
      (At 0x80001ec4#64 (aL ra p dp) (writeLog m (alog p dp (bn % 268435456))) v.keep outp) := by
  mset_ctx
  seg_step_eq msetA 0x80001ec4#64 [rd8 m (p + 16)] [1, 10, 11] abiKeys [entry, entryL, alog] [aL]
    [hf.dp_v, mask28] hc

/-- The reloads: `dp[0]` and `alloc`. -/
theorem b_step (ra : BitVec 64) (v : Abi) (outp : Array String) (p dp d al : Nat) (M : Mem)
    (hc : CodeAt M mpSetBase mpSetCode) (hp : Ram p 24) (hd : Ram dp 4)
    (hd_v : bytesT4 M dp = BitVec.ofNat 32 d) (hal_v : bytesT4 M (p + 4) = BitVec.ofNat 32 al)
    (hdl : d < 2 ^ 31) (hall : al < 2 ^ 31) :
    Triple (At 0x80001ec4#64 (aL ra p dp) M v.keep outp)
      (At 0x80001ecc#64 (bL ra p dp d al) (writeLog M []) v.keep outp) := by
  mset_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M dp) = BitVec.ofNat 64 d := by rw [hd_v, signExtend_ofNat32 _ hdl]
  have h2 : BitVec.signExtend 64 (bytesT4 M (p + 4)) = BitVec.ofNat 64 al := by
    rw [hal_v, signExtend_ofNat32 _ hall]
  seg_step msetB 0x80001ecc#64 [rd4 M dp, rd4 M (p + 4)] [1, 10, 14] abiKeys [aL] [bL] [h1, h2] hc

theorem ite_ofNat_ne_zero {x : Nat} (hx : x < 2 ^ 64) :
    (if BitVec.ofNat 64 x = 0#64 then 0#64 else 1#64) = BitVec.ofNat 64 (if x = 0 then 0 else 1) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 x ≠ 0#64 := fun e => h (by
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
      simpa using this)
    simp only [this, h, ↓reduceIte]

/-- The `snez a3, a5` at `1ecc`: `used := (d != 0)`. -/
theorem z_step (ra : BitVec 64) (v : Abi) (outp : Array String) (p dp d al : Nat) (M : Mem)
    (hc : CodeAt M mpSetBase mpSetCode) (hdl : d < 2 ^ 64) :
    Triple (At 0x80001ecc#64 (bL ra p dp d al) M v.keep outp)
      (At 0x80001ed0#64 (cL ra p dp (if d = 0 then 0 else 1) al) M v.keep outp) := by
  have h := snez_at (pc := 0x80001ecc#64) (w := 0x00f036b3#32) (rd := 13) (rs2 := 15)
    (L := bL ra p dp d al) (keep := v.keep) (outp := outp)
    (hc.word (a := (0x80001ecc#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
    (fun s h1 h2 h3 => decodeW s h1 h2 h3)
    ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩
    (by decide) (Or.inr (by simp [keysG, bL])) (by decide) (by simp [keysG, bL])
    (by simp [Abi.keep, sKeepL, keysG]) (by simp [Abi.keep, sKeepL, keysG])
  have hpc : Sail.BitVec.addInt (0x80001ecc#64 : BitVec 64) 4 = 0x80001ed0#64 := by decide
  rw [hpc, show srcVal 15 (bL ra p dp d al) = BitVec.ofNat 64 d from by simp [srcVal, lookupG, bL],
    ite_ofNat_ne_zero hdl] at h
  exact Triple.rmap (fun cf h' => h'.reshape (by simp [bL, cL, eraseG]) (fun p hp => by simp [hp])) h

/-- `alloc ≤ used`: store `used`, return. -/
theorem c0_step (ra : BitVec 64) (v : Abi) (outp : Array String) (p dp u al : Nat) (M : Mem)
    (hc : CodeAt M mpSetBase mpSetCode) (hp : Ram p 24) (hpa : p % 8 = 0)
    (hcode : p + 24 ≤ mpSetBase ∨ mpSetBase + 68 ≤ p) (hra : ra.toNat % 4 = 0)
    (hu : u ≤ 1) (hal : al ≤ u) :
    Triple (At 0x80001ed0#64 (cL ra p dp u al) M v.keep outp)
      (At ra [(1, ra)] (writeLog M [(p, 4, BitVec.ofNat 64 u)]) v.keep outp) := by
  mset_ctx
  have ⟨_, _, _⟩ := ram_bounds hp
  seg_step msetC0 ra ([] : List (List (BitVec 8))) [13, 1, 10, 14, 12] abiKeys [cL] [] [] hc

/-- `alloc > used`: store `used`, tail-jump to `memset(dp + 4 used, 0, 4 (alloc - used))`. -/
theorem c1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (p dp u al : Nat) (M : Mem)
    (hc : CodeAt M mpSetBase mpSetCode) (hp : Ram p 24) (hpa : p % 8 = 0)
    (hcode : p + 24 ≤ mpSetBase ∨ mpSetBase + 68 ≤ p) (hd : dp + 4 * al ≤ 2 ^ 32)
    (hu : u ≤ 1) (hal : u < al) (hal' : al < 2 ^ 31) :
    Triple (At 0x80001ed0#64 (cL ra p dp u al) M v.keep outp)
      (At Memset.entry (Memset.entryL ra (dp + 4 * u) 0#64 (4 * (al - u)))
        (writeLog M [(p, 4, BitVec.ofNat 64 u)]) v.keep outp) := by
  mset_ctx
  have ⟨_, _, _⟩ := ram_bounds hp
  seg_step msetC1 Memset.entry ([] : List (List (BitVec 8))) [13, 1, 10, 14, 12] abiKeys [cL]
    [Memset.entryL] [] hc

end Tom.Machine.Fn.MpSet
