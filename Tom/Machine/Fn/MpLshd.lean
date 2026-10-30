import Tom.Machine.Seg.MpLshd
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.AutoEq
import Vsa.Sim.TripleCat

/-!
# `mp_lshd` on the machine: the segments

`mp_lshd(a, b)` at `0x800015b8` (50 instructions). `b ≤ 0` or `used = 0`:
return `MP_OKAY` (`mlshdN`, `mlshdZ`). Otherwise (`alloc ≥ used + b`, so no
`mp_grow`, D5): save `ra`, `used := used + b`, and set up the copy loop from
the top (`mlshdE1`–`mlshdE4`, split for the elaborator's memory; the `bge` at `15e8` is never taken since `used > 0`). The
loop at `1624` moves `dp[B]` to `dp[B + b]` for `B = used - 1` down to `0`
(`mlshdL`, `mlshdLe`, comparing the next store pointer with `dp + 4 (b - 1)`);
then `memset(dp, 0, 4 b)` at `1640` and the epilogue (`mlshdR`).
-/


namespace Tom.Machine.Fn.MpLshd

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mlshd_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpLshdBase = 0x800015b8 := rfl
   have : mpLshdCode.length = 50 := rfl))

def entry : BitVec 64 := 0x800015b8#64

/-- The entry: `a0 = a`, `a1 = b`. -/
def entryL (ra s0 : BitVec 64) (sp pa b : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 b)]

/-- The return (`MP_OKAY`). -/
def retL (ra s0 : BitVec 64) (sp : Nat) : GRegs := [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)]

/-- `b = 0`: return. -/
theorem n_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa : Nat) (m : Mem)
    (hc : CodeAt m mpLshdBase mpLshdCode) (hra : ra.toNat % 4 = 0) :
    Triple (At entry (entryL ra s0 sp pa 0) m v.keepR outp) (At ra (retL ra s0 sp) (writeLog m []) v.keepR outp) := by
  mlshd_ctx
  seg_step mlshdN ra ([] : List (List (BitVec 8))) [1, 2, 8, 10, 11] abiKeysR [entry, entryL] [retL] [] hc

/-- `a->used` (and `alloc`, the digit pointer). -/
structure SFacts (m : Mem) (pa dp u al : Nat) : Prop where
  ra_ : Ram pa 24
  pa_al : pa % 8 = 0
  u_v : bytesT4 m pa = BitVec.ofNat 32 u
  al_v : bytesT4 m (pa + 4) = BitVec.ofNat 32 al
  dp_v : bytesT8 m (pa + 16) = BitVec.ofNat 64 dp
  u_lt : u < 2 ^ 31
  al_lt : al < 2 ^ 31

/-- `used = 0`: return. -/
theorem z_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa dp al b : Nat) (m : Mem)
    (hc : CodeAt m mpLshdBase mpLshdCode) (hra : ra.toNat % 4 = 0) (hf : SFacts m pa dp 0 al) (hb : 0 < b)
    (hb' : b < 2 ^ 31) :
    Triple (At entry (entryL ra s0 sp pa b) m v.keepR outp) (At ra (retL ra s0 sp) (writeLog m []) v.keepR outp) := by
  mlshd_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 m pa) = BitVec.ofNat 64 0 := by rw [hf.u_v, signExtend_ofNat32 _ hf.u_lt]
  seg_step mlshdZ ra [rd4 m pa] [1, 2, 8, 10, 11] abiKeysR [entry, entryL] [retL] [h1] hc

/-- At the loop head (`1624`), `t` digits moved: `T = used + b - 1 - t`, `B = used - 1 - t`. -/
def kL (s0 : BitVec 64) (sp dp u b t : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (8, s0), (10, BitVec.ofNat 64 dp), (12, BitVec.ofNat 64 b),
   (13, BitVec.ofNat 64 (dp + 4 * b - 4)), (14, BitVec.ofNat 64 (dp + 4 * (u + b - 1 - t) - 4)),
   (15, BitVec.ofNat 64 (dp + 4 * (u - 1 - t))), (16, BitVec.ofNat 64 (dp + 4 * (u + b - 1 - t)))]

/-- At `15e0` (`alloc ≥ used + b`): `a4 = a`, `a2 = b`, `a1 = used + b`, `a5 = used`. -/
def e1L (s0 : BitVec 64) (sp pa u al b : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (8, s0), (14, BitVec.ofNat 64 pa), (12, BitVec.ofNat 64 b),
   (11, BitVec.ofNat 64 (u + b)), (15, BitVec.ofNat 64 u), (13, BitVec.ofNat 64 al)]

/-- The frame. -/
structure FFacts (sp pa : Nat) : Prop where
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  s_a : sp ≤ pa ∨ pa + 24 ≤ sp - 32
  code_s : sp ≤ mpLshdBase ∨ mpLshdBase + 200 ≤ sp - 32
  code_a : pa + 24 ≤ mpLshdBase ∨ mpLshdBase + 200 ≤ pa

/-- `0 < b`, `0 < used`, `used + b ≤ alloc`: save `ra` (no `mp_grow`). -/
theorem e1_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa dp u al b : Nat) (m : Mem)
    (hc : CodeAt m mpLshdBase mpLshdCode) (hf : SFacts m pa dp u al) (hs : FFacts sp pa) (hb : 0 < b)
    (hb' : b < 2 ^ 31) (hu : 0 < u) (hal : u + b ≤ al) :
    Triple (At entry (entryL ra s0 sp pa b) m v.keepR outp)
      (At 0x800015e0#64 (e1L s0 sp pa u al b) (writeLog m [(sp - 8, 8, ra)]) v.keepR outp) := by
  mlshd_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 m pa) = BitVec.ofNat 64 u := by rw [hf.u_v, signExtend_ofNat32 _ hf.u_lt]
  have h2 : BitVec.signExtend 64 (bytesT4 m (pa + 4)) = BitVec.ofNat 64 al := by
    rw [hf.al_v, signExtend_ofNat32 _ hf.al_lt]
  seg_step mlshdE1 0x800015e0#64 [rd4 m pa, rd4 m (pa + 4)] [1, 2, 8, 10, 11] abiKeysR [entry, entryL] [e1L]
    [h1, h2] hc

/-- At `15ec`: `a0 = dp`, `a1 = used + b`. -/
def e2L' (s0 : BitVec 64) (sp dp u b : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (8, s0), (10, BitVec.ofNat 64 dp), (12, BitVec.ofNat 64 b),
   (11, BitVec.ofNat 64 (u + b)), (15, BitVec.ofNat 64 u)]

/-- At `1600`: `a6 = 4 (used + b) - 4`, `a3 = used - 1`, `a4 = (used - 1) << 32`. -/
def e2L (s0 : BitVec 64) (sp dp u b : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (8, s0), (10, BitVec.ofNat 64 dp), (12, BitVec.ofNat 64 b),
   (16, BitVec.ofNat 64 (4 * (u + b) - 4)), (13, BitVec.ofNat 64 (u - 1)),
   (14, BitVec.ofNat 64 ((u - 1) * 2 ^ 32)), (15, BitVec.ofNat 64 u)]

/-- At `1618`: the top and bottom pointers. -/
def e3L (s0 : BitVec 64) (sp dp u b : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (8, s0), (10, BitVec.ofNat 64 dp), (12, BitVec.ofNat 64 b),
   (16, BitVec.ofNat 64 (dp + 4 * (u + b - 1))), (13, BitVec.ofNat 64 (4 * (u - 1))),
   (14, BitVec.ofNat 64 (dp + 4 * (u + b - 1) - 4)), (15, BitVec.ofNat 64 (dp + 4 * (u - 1)))]

/-- `used := used + b`, the digit pointer. -/
theorem e2_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa dp u al b : Nat) (M : Mem)
    (hc : CodeAt M mpLshdBase mpLshdCode) (hp : Ram pa 24) (hpa : pa % 8 = 0)
    (hcode : pa + 24 ≤ mpLshdBase ∨ mpLshdBase + 200 ≤ pa)
    (hdp : bytesT8 M (pa + 16) = BitVec.ofNat 64 dp)
    (hu : 0 < u) (hal : u + b ≤ al) (hal' : al < 2 ^ 31) :
    Triple (At 0x800015e0#64 (e1L s0 sp pa u al b) M v.keepR outp)
      (At 0x800015ec#64 (e2L' s0 sp dp u b) (writeLog M [(pa, 4, BitVec.ofNat 64 (u + b))]) v.keepR outp) := by
  mlshd_ctx
  have ⟨_, _, _⟩ := ram_bounds hp
  seg_step mlshdE2 0x800015ec#64 [rd8 M (pa + 16)] [2, 8, 14, 12, 11, 15, 13] abiKeysR [e1L] [e2L'] [hdp] hc

/-- The loop bounds. -/
theorem e2b_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (sp dp u b : Nat) (M : Mem)
    (hc : CodeAt M mpLshdBase mpLshdCode) (hb : 0 < b) (hu : 0 < u) (hub : u + b < 2 ^ 31) :
    Triple (At 0x800015ec#64 (e2L' s0 sp dp u b) M v.keepR outp)
      (At 0x80001600#64 (e2L s0 sp dp u b) (writeLog M []) v.keepR outp) := by
  mlshd_ctx
  seg_step mlshdE2b 0x80001600#64 ([] : List (List (BitVec 8))) [2, 8, 10, 12, 11, 15] abiKeysR [e2L'] [e2L] [] hc

/-- The pointer arithmetic. -/
theorem e3_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (sp dp u b : Nat) (M : Mem)
    (hc : CodeAt M mpLshdBase mpLshdCode) (hb : 0 < b) (hu : 0 < u) (hub : u + b < 2 ^ 31)
    (hd : dp + 4 * (u + b) ≤ 2 ^ 32) :
    Triple (At 0x80001600#64 (e2L s0 sp dp u b) M v.keepR outp)
      (At 0x80001618#64 (e3L s0 sp dp u b) (writeLog M []) v.keepR outp) := by
  mlshd_ctx
  seg_step mlshdE3 0x80001618#64 ([] : List (List (BitVec 8))) [2, 8, 10, 12, 16, 13, 14, 15] abiKeysR [e2L] [e3L]
    [] hc

/-- The end pointer `dp + 4 (b - 1)`, to the loop head. -/
theorem e4_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (sp dp u b : Nat) (M : Mem)
    (hc : CodeAt M mpLshdBase mpLshdCode) (hb : 0 < b) (hu : 0 < u) (hub : u + b < 2 ^ 31)
    (hd : dp + 4 * (u + b) ≤ 2 ^ 32) :
    Triple (At 0x80001618#64 (e3L s0 sp dp u b) M v.keepR outp)
      (At 0x80001624#64 (kL s0 sp dp u b 0) (writeLog M []) v.keepR outp) := by
  mlshd_ctx
  have hs : BitVec.ofNat 64 (dp + 4 * (u + b - 1) - 4) - BitVec.ofNat 64 (4 * (u - 1)) =
      BitVec.ofNat 64 (dp + 4 * b - 4) := by
    rw [ofNat_sub_ofNat _ _ (by omega) (by omega)]; congr 1; omega
  seg_step mlshdE4 0x80001624#64 ([] : List (List (BitVec 8))) [2, 8, 10, 12, 16, 13, 14, 15] abiKeysR [e3L] [kL]
    [hs] hc

/-- One iteration's memory facts: `y = dp[B]` (`B = used - 1 - t`), the store at `dp[B + b]`. -/
structure LFacts (M : Mem) (dp u b t y : Nat) : Prop where
  ry : Ram (dp + 4 * (u - 1 - t)) 4
  y_v : bytesT4 M (dp + 4 * (u - 1 - t)) = BitVec.ofNat 32 y
  y_lt : y < 2 ^ 31
  rd : Ram (dp + 4 * (u + b - 1 - t)) 4
  dp_al : dp % 4 = 0
  code_off : dp + 4 * (u + b - 1 - t) + 4 ≤ mpLshdBase ∨ mpLshdBase + 200 ≤ dp + 4 * (u + b - 1 - t)

/-- The loop's back edge (`t + 1 < used`). -/
theorem l_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (sp dp u b t y : Nat) (M : Mem)
    (hc : CodeAt M mpLshdBase mpLshdCode) (hf : LFacts M dp u b t y) (hb : 0 < b) (ht : t + 1 < u) :
    Triple (At 0x80001624#64 (kL s0 sp dp u b t) M v.keepR outp)
      (At 0x80001624#64 (kL s0 sp dp u b (t + 1))
        (writeLog M [(dp + 4 * (u + b - 1 - t), 4, BitVec.ofNat 64 y)]) v.keepR outp) := by
  mlshd_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M (dp + 4 * (u - 1 - t))) = BitVec.ofNat 64 y := by
    rw [hf.y_v, signExtend_ofNat32 _ hf.y_lt]
  seg_step mlshdL 0x80001624#64 [rd4 M (dp + 4 * (u - 1 - t))] [2, 8, 10, 12, 13, 14, 15, 16] abiKeysR
    [kL] [] [h1] hc

/-- At the `memset` call (`1640`): `memset(dp, 0, 4 b)`. -/
def msL (s0 : BitVec 64) (sp dp b : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (8, s0), (10, BitVec.ofNat 64 dp), (11, 0#64), (12, BitVec.ofNat 64 (4 * b))]

/-- The loop's last iteration (`t + 1 = used`), to the `memset` call. -/
theorem le_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (sp dp u b t y : Nat) (M : Mem)
    (hc : CodeAt M mpLshdBase mpLshdCode) (hf : LFacts M dp u b t y) (hb : 0 < b) (hb' : b < 2 ^ 31) (ht : t + 1 = u) :
    Triple (At 0x80001624#64 (kL s0 sp dp u b t) M v.keepR outp)
      (At 0x80001640#64 (msL s0 sp dp b)
        (writeLog M [(dp + 4 * (u + b - 1 - t), 4, BitVec.ofNat 64 y)]) v.keepR outp) := by
  mlshd_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M (dp + 4 * (u - 1 - t))) = BitVec.ofNat 64 y := by
    rw [hf.y_v, signExtend_ofNat32 _ hf.y_lt]
  seg_step mlshdLe 0x80001640#64 [rd4 M (dp + 4 * (u - 1 - t))] [2, 8, 10, 12, 13, 14, 15, 16] abiKeysR
    [kL] [msL] [h1] hc

/-- After `memset`: restore, return `MP_OKAY`. -/
theorem r_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M mpLshdBase mpLshdCode) (hs : Ram (sp - 32) 32) (hsp : 32 ≤ sp) (hra : ra.toNat % 4 = 0)
    (hrv : bytesT8 M (sp - 8) = ra) :
    Triple (At 0x80001644#64 [(2, BitVec.ofNat 64 (sp - 32)), (8, s0)] M v.keepR outp)
      (At ra (retL ra s0 sp) (writeLog M []) v.keepR outp) := by
  mlshd_ctx
  have h1 : bytesT8 M (sp - 32 + 24) = ra := by rw [show sp - 32 + 24 = sp - 8 by omega]; exact hrv
  seg_step mlshdR ra [rd8 M (sp - 32 + 24)] [2, 8] abiKeysR [] [retL] [h1] hc

end Tom.Machine.Fn.MpLshd
