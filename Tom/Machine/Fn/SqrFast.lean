import Tom.Machine.Seg.SqrFast
import Tom.Machine.Fn.MulFast

/-!
# `s_mp_sqr_fast` on the machine: the segments

`s_mp_sqr_fast(a, b)` at `0x80007010` (175 instructions), frame `2208` bytes:
the saved `ra`, `s0`–`s11` at `[sp - 104, sp)` (as in `s_mp_mul_digs_fast`),
`W[MP_WARRAY]` at `[sp - 2160, sp - 112)`, spills at `sp - 2208` (`a->used`),
`sp - 2200` (`a->used - 1`), `sp - 2192` (`b`), `sp - 2184` (`a->used`),
`sp - 2176` (`4 (a->used - 1)`), `sp - 2168` (`pa = 2 a->used`).

* prologue `sqP1a`–`sqP1d` (the `mp_grow` branch `b->alloc < pa` excluded, D5),
  `pa = 0` (`sqP2z`) or the set-up (`sqP2a`–`sqP2c`);
* the column head `70a8` (`qH`: `s1` = carry + twice the half column): even
  columns add the square `a[ix/2]²` by `__muldi3` (`sqE1`, `sqE2`, `sqSE`),
  odd ones do not (`sqSO`); the store `W[ix] := _W & MP_MASK`;
* the next column's set-up: `ix + 1 < a->used` (`sqN1`) or not (`sqN2`, then
  `sqM1`/`sqM2`, `sqMs` + `sqM3`/`sqM4`: `iy = min(…, (ty - tx + 1) >> 1)`, empty
  `sqM5` or `sqM6`), the inner loop (`sqI0`, `sqL1`, `__muldi3`, `sqL2`/`sqL2e`),
  doubling (`sqX`);
* after the last column (`sqD`): `b->used := pa` (`sqF1`/`sqF1b`), the copy
  loop `b->dp[j] := W[j] & MP_MASK` (`sqC`/`sqCe`), `memset` of the old digits
  above (`sqF2t`/`sqF2m`; `pa = 0`: `sqZ`, `sqZt`/`sqZm`), `mp_clamp(b)`
  (`sqGc`), the epilogue (`sqH`).

The segments keep `gp` and `tp` only (`MulFast.kF`).
-/


namespace Tom.Machine.Fn.SqrFast

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg
open Tom.Machine.Fn.MulFast (kF kFKeys abiL msL clL rL DRead zext_ofNat32)

macro "sq_ctx" : tactic => `(tactic|
  (facts_ctx
   have : sMpSqrFastBase = 0x80007010 := rfl
   have : sMpSqrFastCode.length = 175 := rfl))

/-- The frame. -/
structure KS (sp : Nat) : Prop where
  rs : Ram (sp - 2208) 2208
  sp_al : sp % 16 = 0
  sp_ge : 2208 ≤ sp
  code_off : sp ≤ sMpSqrFastBase ∨ sMpSqrFastBase + 700 ≤ sp - 2208

/-! ## The prologue -/

def entL (ra s0 : BitVec 64) (v : Abi) (sp pa pb : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, v.s.s1), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb),
   (18, v.s.s2), (19, v.s.s3), (20, v.s.s4), (21, v.s.s5), (22, v.s.s6), (23, v.s.s7), (24, v.s.s8),
   (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

def q1L (ra s0 : BitVec 64) (v : Abi) (sp pa pb ua al : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 2032)), (8, s0), (9, v.s.s1), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 pb), (13, BitVec.ofNat 64 al), (15, BitVec.ofNat 64 ua), (18, v.s.s2), (19, v.s.s3),
   (20, v.s.s4), (21, v.s.s5), (22, v.s.s6), (23, v.s.s7), (24, v.s.s8), (25, v.s.s9), (26, v.s.s10),
   (27, v.s.s11)]

def log1a (s0 : BitVec 64) (v : Abi) (sp : Nat) : List WEntry := [(sp - 16, 8, s0), (sp - 80, 8, v.s.s8)]

def log1b (ra : BitVec 64) (v : Abi) (sp : Nat) : List WEntry :=
  [(sp - 8, 8, ra), (sp - 24, 8, v.s.s1), (sp - 32, 8, v.s.s2), (sp - 40, 8, v.s.s3), (sp - 48, 8, v.s.s4)]

def log1c (v : Abi) (sp : Nat) : List WEntry :=
  [(sp - 56, 8, v.s.s5), (sp - 64, 8, v.s.s6), (sp - 72, 8, v.s.s7), (sp - 88, 8, v.s.s9),
   (sp - 96, 8, v.s.s10), (sp - 104, 8, v.s.s11)]

/-- `a->used`, `b->alloc`. -/
structure P1Facts (m : Mem) (pa pb ua al : Nat) : Prop where
  ra_ : Ram pa 24
  rb : Ram pb 24
  ua_v : bytesT4 m pa = BitVec.ofNat 32 ua
  al_v : bytesT4 m (pb + 4) = BitVec.ofNat 32 al
  ua_lt : ua < 2 ^ 30
  al_lt : al < 2 ^ 31

theorem P1Facts.sx {m : Mem} {pa pb ua al : Nat} (h : P1Facts m pa pb ua al) :
    BitVec.signExtend 64 (bytesT4 m pa) = BitVec.ofNat 64 ua ∧
      BitVec.signExtend 64 (bytesT4 m (pb + 4)) = BitVec.ofNat 64 al :=
  ⟨by rw [h.ua_v, signExtend_ofNat32 _ (by have := h.ua_lt; omega)], by rw [h.al_v, signExtend_ofNat32 _ h.al_lt]⟩

theorem p1a_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb ua al : Nat) (m : Mem)
    (hc : CodeAt m sMpSqrFastBase sMpSqrFastCode) (hk : KS sp) (hf : P1Facts m pa pb ua al) :
    Triple (At 0x80007010#64 (entL ra s0 v sp pa pb) m (kF v) outp)
      (At 0x80007024#64 (q1L ra s0 v sp pa pb ua al) (writeLog m (log1a s0 v sp)) (kF v) outp) := by
  sq_ctx
  have ⟨h1, h2⟩ := hf.sx
  seg_step sqP1a 0x80007024#64 [rd4 m pa, rd4 m (pb + 4)] [1, 2, 8, 9, 10, 11, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [entL, log1a] [q1L] [h1, h2] hc

theorem p1b_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb ua al : Nat) (m : Mem)
    (hc : CodeAt m sMpSqrFastBase sMpSqrFastCode) (hk : KS sp) :
    Triple (At 0x80007024#64 (q1L ra s0 v sp pa pb ua al) m (kF v) outp)
      (At 0x80007038#64 (q1L ra s0 v sp pa pb ua al) (writeLog m (log1b ra v sp)) (kF v) outp) := by
  sq_ctx
  seg_step sqP1b 0x80007038#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 13, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [q1L, log1b] [q1L] [] hc

theorem p1c_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb ua al : Nat) (m : Mem)
    (hc : CodeAt m sMpSqrFastBase sMpSqrFastCode) (hk : KS sp) :
    Triple (At 0x80007038#64 (q1L ra s0 v sp pa pb ua al) m (kF v) outp)
      (At 0x80007050#64 (q1L ra s0 v sp pa pb ua al) (writeLog m (log1c v sp)) (kF v) outp) := by
  sq_ctx
  seg_step sqP1c 0x80007050#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 13, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [q1L, log1c] [q1L] [] hc

/-- At `7064`: `s0 = a`, `s8 = pa`, `a5 = a->used`. -/
def q2L (v : Abi) (sp pa ua : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2208)), (8, BitVec.ofNat 64 pa), (9, v.s.s1), (15, BitVec.ofNat 64 ua),
   (18, v.s.s2), (19, v.s.s3), (20, v.s.s4), (21, v.s.s5), (22, v.s.s6), (23, v.s.s7),
   (24, BitVec.ofNat 64 (2 * ua)), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

/-- Save `b`; `s8 = pa`. -/
theorem p1d_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb ua al : Nat) (m : Mem)
    (hc : CodeAt m sMpSqrFastBase sMpSqrFastCode) (hk : KS sp) (hua : ua < 2 ^ 30) :
    Triple (At 0x80007050#64 (q1L ra s0 v sp pa pb ua al) m (kF v) outp)
      (At 0x80007060#64 ((13, BitVec.ofNat 64 al) :: q2L v sp pa ua) (writeLog m [(sp - 2192, 8, BitVec.ofNat 64 pb)])
        (kF v) outp) := by
  sq_ctx
  seg_stepx sqP1d 0x80007060#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 13, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [q1L] [q2L] [] hc

/-- `b->alloc ≥ pa` (no `mp_grow`). -/
theorem p1e_step (v : Abi) (outp : Array String) (sp pa ua al : Nat) (m : Mem)
    (hc : CodeAt m sMpSqrFastBase sMpSqrFastCode) (hua : ua < 2 ^ 30) (hal : al < 2 ^ 31) (hroom : 2 * ua ≤ al) :
    Triple (At 0x80007060#64 ((13, BitVec.ofNat 64 al) :: q2L v sp pa ua) m (kF v) outp)
      (At 0x80007064#64 (q2L v sp pa ua) (writeLog m []) (kF v) outp) := by
  sq_ctx
  seg_step sqP1e 0x80007064#64 ([] : List (List (BitVec 8)))
    [13, 2, 8, 9, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [q2L] [q2L] [] hc

/-- At `72b0` (`a->used = 0`). -/
def zL (v : Abi) (sp pa : Nat) : GRegs :=
  [(14, 0#64), (2, BitVec.ofNat 64 (sp - 2208)), (8, BitVec.ofNat 64 pa), (9, v.s.s1), (18, v.s.s2), (19, v.s.s3),
   (20, v.s.s4), (21, v.s.s5), (22, v.s.s6), (23, v.s.s7), (24, BitVec.ofNat 64 (2 * 0)), (25, v.s.s9),
   (26, v.s.s10), (27, v.s.s11)]

theorem p2z_step (v : Abi) (outp : Array String) (sp pa : Nat) (m : Mem)
    (hc : CodeAt m sMpSqrFastBase sMpSqrFastCode) :
    Triple (At 0x80007064#64 (q2L v sp pa 0) m (kF v) outp)
      (At 0x800072b0#64 (zL v sp pa) (writeLog m []) (kF v) outp) := by
  sq_ctx
  seg_step sqP2z 0x800072b0#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [q2L] [zL, q2L] [] hc

def log2a (sp ua : Nat) : List WEntry :=
  [(sp - 2184, 8, BitVec.ofNat 64 ua), (sp - 2200, 8, BitVec.ofNat 64 (ua - 1))]

/-- At `707c`: `a5 = 4 (a->used - 1)`. -/
def q3L (v : Abi) (sp pa ua : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2208)), (8, BitVec.ofNat 64 pa), (9, v.s.s1), (15, BitVec.ofNat 64 (4 * (ua - 1))),
   (18, v.s.s2), (19, v.s.s3), (20, v.s.s4), (21, v.s.s5), (22, v.s.s6), (23, v.s.s7),
   (24, BitVec.ofNat 64 (2 * ua)), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

theorem p2a_step (v : Abi) (outp : Array String) (sp pa ua : Nat) (m : Mem)
    (hc : CodeAt m sMpSqrFastBase sMpSqrFastCode) (hk : KS sp) (hua : 0 < ua) (hua' : ua < 2 ^ 30) :
    Triple (At 0x80007064#64 (q2L v sp pa ua) m (kF v) outp)
      (At 0x8000707c#64 (q3L v sp pa ua) (writeLog m (log2a sp ua)) (kF v) outp) := by
  sq_ctx
  seg_step sqP2a 0x8000707c#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [q2L, log2a] [q3L] [] hc

/-- At `7084`: `s7 = a->dp`. -/
def q4L (v : Abi) (sp pa ua adp : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2208)), (8, BitVec.ofNat 64 pa), (9, v.s.s1), (18, v.s.s2), (19, v.s.s3),
   (20, v.s.s4), (21, v.s.s5), (22, v.s.s6), (23, BitVec.ofNat 64 adp),
   (24, BitVec.ofNat 64 (2 * ua)), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

theorem p2b_step (v : Abi) (outp : Array String) (sp pa ua adp : Nat) (m : Mem)
    (hc : CodeAt m sMpSqrFastBase sMpSqrFastCode) (hk : KS sp) (hra : Ram pa 24)
    (hadp : bytesT8 m (pa + 16) = BitVec.ofNat 64 adp) :
    Triple (At 0x8000707c#64 (q3L v sp pa ua) m (kF v) outp)
      (At 0x80007084#64 (q4L v sp pa ua adp) (writeLog m [(sp - 2176, 8, BitVec.ofNat 64 (4 * (ua - 1)))])
        (kF v) outp) := by
  sq_ctx
  seg_step sqP2b 0x80007084#64 [rd8 m (pa + 16)] [2, 8, 9, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [q3L] [q4L] [hadp] hc

/-- The column head `70a8`: column `ix`, `s1 = s`; `s0`, `s9`–`s11` junk. -/
def qH (sp ua adp ix s : Nat) (j0 j9 j10 j11 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2208)), (8, j0), (9, BitVec.ofNat 64 s), (18, BitVec.ofNat 64 ix),
   (19, BitVec.ofNat 64 (2 * ua - 1 - ix)), (20, BitVec.ofNat 64 (sp - 2160)),
   (21, BitVec.ofNat 64 (sp - 2160 + 4 * ix)), (22, BitVec.ofNat 64 (adp + 4 * ix)), (23, BitVec.ofNat 64 adp),
   (24, BitVec.ofNat 64 (2 * ua)), (25, j9), (26, j10), (27, j11)]

def log2c (sp ua : Nat) : List WEntry :=
  [(sp - 2208, 8, BitVec.ofNat 64 ua), (sp - 2168, 8, BitVec.ofNat 64 (2 * ua))]

theorem p2c_step (v : Abi) (outp : Array String) (sp pa ua adp : Nat) (m : Mem)
    (hc : CodeAt m sMpSqrFastBase sMpSqrFastCode) (hk : KS sp) (hua : 0 < ua) (hua' : ua < 2 ^ 30)
    (hs : bytesT8 m (sp - 2184) = BitVec.ofNat 64 ua) :
    Triple (At 0x80007084#64 (q4L v sp pa ua adp) m (kF v) outp)
      (At 0x800070a8#64 (qH sp ua adp 0 0 (BitVec.ofNat 64 pa) v.s.s9 v.s.s10 v.s.s11) (writeLog m (log2c sp ua))
        (kF v) outp) := by
  sq_ctx
  have h1 : bytesT8 m (sp - 2208 + 24) = BitVec.ofNat 64 ua := by
    rw [show sp - 2208 + 24 = sp - 2184 by omega]; exact hs
  seg_step sqP2c 0x800070a8#64 [rd8 m (sp - 2208 + 24)] [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [q4L, log2c] [qH] [h1] hc

/-! ## A column -/

/-- An even column: `a5 = ix / 2`. -/
theorem e1_step (v : Abi) (outp : Array String) (sp ua adp ix s : Nat) (j0 j9 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (he : ix % 2 = 0) (hix : ix < 2 ^ 30) :
    Triple (At 0x800070a8#64 (qH sp ua adp ix s j0 j9 j10 j11) M (kF v) outp)
      (At 0x800070b4#64 ((15, BitVec.ofNat 64 (ix / 2)) :: qH sp ua adp ix s j0 j9 j10 j11) (writeLog M [])
        (kF v) outp) := by
  sq_ctx
  seg_stepx sqE1 0x800070b4#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [qH] [qH] [and1_ofNat] hc

/-- Its address. -/
theorem e2_step (v : Abi) (outp : Array String) (sp ua adp ix s : Nat) (j0 j9 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) :
    Triple (At 0x800070b4#64 ((15, BitVec.ofNat 64 (ix / 2)) :: qH sp ua adp ix s j0 j9 j10 j11) M (kF v) outp)
      (At 0x800070bc#64 ((15, BitVec.ofNat 64 (adp + 4 * (ix / 2))) :: qH sp ua adp ix s j0 j9 j10 j11)
        (writeLog M []) (kF v) outp) := by
  sq_ctx
  seg_step sqE2 0x800070bc#64 ([] : List (List (BitVec 8))) [15, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [qH] [qH] [] hc

/-- The square's operand `a->dp[ix / 2]`. -/
theorem e3_step (v : Abi) (outp : Array String) (sp ua adp ix s d : Nat) (j0 j9 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hd : DRead M (adp + 4 * (ix / 2)) d) :
    Triple (At 0x800070bc#64 ((15, BitVec.ofNat 64 (adp + 4 * (ix / 2))) :: qH sp ua adp ix s j0 j9 j10 j11) M
        (kF v) outp)
      (At 0x800070c4#64 ((10, BitVec.ofNat 64 d) :: (11, BitVec.ofNat 64 d) :: qH sp ua adp ix s j0 j9 j10 j11)
        (writeLog M []) (kF v) outp) := by
  sq_ctx
  have hz : zero_extend (m := 64) (bytesT4 M (adp + 4 * (ix / 2))) = BitVec.ofNat 64 d := by
    rw [hd.v, zext_ofNat32 _ (by have := hd.lt; omega)]
  seg_step sqE3 0x800070c4#64 [rd4 M (adp + 4 * (ix / 2))] [15, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [qH] [qH] [hz] hc

/-- The store point (`70dc`): `a5 = MP_MASK`. -/
def sP (sp ua adp ix s : Nat) (j0 j9 j10 j11 : BitVec 64) : GRegs :=
  (15, 268435455#64) :: qH sp ua adp ix s j0 j9 j10 j11

/-- Store an even column (after the square). -/
theorem se_step (v : Abi) (outp : Array String) (sp ua adp ix s p : Nat) (j0 j9 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hk : KS sp) (hix : ix < 512) (hs : s + p < 2 ^ 64) :
    Triple (At 0x800070c8#64 ((10, BitVec.ofNat 64 p) :: qH sp ua adp ix s j0 j9 j10 j11) M (kF v) outp)
      (At 0x800070dc#64 (sP sp ua adp ix (s + p) j0 j9 j10 j11)
        (writeLog M [(sp - 2160 + 4 * ix, 4, BitVec.ofNat 64 ((s + p) % 268435456))]) (kF v) outp) := by
  sq_ctx
  seg_step sqSE 0x800070dc#64 ([] : List (List (BitVec 8))) [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [qH] [sP, qH] [] hc

/-- Store an odd column. -/
theorem so_step (v : Abi) (outp : Array String) (sp ua adp ix s : Nat) (j0 j9 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hk : KS sp) (hix : ix < 512) (ho : ix % 2 = 1)
    (hs : s < 2 ^ 64) :
    Triple (At 0x800070a8#64 (qH sp ua adp ix s j0 j9 j10 j11) M (kF v) outp)
      (At 0x800070dc#64 (sP sp ua adp ix s j0 j9 j10 j11)
        (writeLog M [(sp - 2160 + 4 * ix, 4, BitVec.ofNat 64 (s % 268435456))]) (kF v) outp) := by
  sq_ctx
  seg_step sqSO 0x800070dc#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [qH] [sP, qH] [and1_ofNat] hc

/-- The last column (`ix + 1 = pa`). -/
theorem d_step (v : Abi) (outp : Array String) (sp ua adp ix s : Nat) (j0 j9 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hi : ix + 1 = 2 * ua) (hua : ua < 2 ^ 30) :
    Triple (At 0x800070dc#64 (sP sp ua adp ix s j0 j9 j10 j11) M (kF v) outp)
      (At 0x800071ec#64 (sP sp ua adp ix s j0 j9 j10 j11) (writeLog M []) (kF v) outp) := by
  sq_ctx
  seg_step sqD 0x800071ec#64 ([] : List (List (BitVec 8))) [15, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [sP, qH] [sP, qH] [] hc

/-- At the inner loop's set-up `7114`: `s0 = iy`, `s10 = a->dp + tx`, `s11 = a->dp + ty`, carry `c`. -/
def iS (sp ua adp ix c tx ty iy : Nat) (j9 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2208)), (8, BitVec.ofNat 64 iy), (9, BitVec.ofNat 64 c), (18, BitVec.ofNat 64 ix),
   (19, BitVec.ofNat 64 (2 * ua - 1 - ix)), (20, BitVec.ofNat 64 (sp - 2160)),
   (21, BitVec.ofNat 64 (sp - 2160 + 4 * ix)), (22, BitVec.ofNat 64 (adp + 4 * ix)), (23, BitVec.ofNat 64 adp),
   (24, BitVec.ofNat 64 (2 * ua)), (25, j9), (26, BitVec.ofNat 64 (adp + 4 * tx)), (27, BitVec.ofNat 64 (adp + 4 * ty))]

/-- `ix + 1 < a->used`: `tx = 0`, `ty = ix + 1`, `iy = ix / 2 + 1`. -/
theorem n1_step (v : Abi) (outp : Array String) (sp ua adp ix s : Nat) (j0 j9 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hk : KS sp) (hu : bytesT8 M (sp - 2208) = BitVec.ofNat 64 ua)
    (hi : ix + 1 < ua) (hua : ua < 2 ^ 30) (hs : s < 2 ^ 64) :
    Triple (At 0x800070dc#64 (sP sp ua adp ix s j0 j9 j10 j11) M (kF v) outp)
      (At 0x80007114#64 (iS sp ua adp (ix + 1) (s / 268435456) 0 (ix + 1) (ix / 2 + 1) j9) (writeLog M [])
        (kF v) outp) := by
  sq_ctx
  seg_stepx sqN1 0x80007114#64 [rd8 M (sp - 2208)] [15, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [sP, qH] [iS] [hu] hc

/-- At `71ac`/`71b8`/`71c0` (`ix + 1 ≥ a->used`): `a0 = ix' = ix + 1`; `s2` is still `ix`. -/
def mL (sp ua adp ix' c : Nat) (j0 j9 j10 j11 : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2208)), (8, j0), (9, BitVec.ofNat 64 c), (10, BitVec.ofNat 64 ix'),
   (18, BitVec.ofNat 64 (ix' - 1)), (19, BitVec.ofNat 64 (2 * ua - 1 - ix')), (20, BitVec.ofNat 64 (sp - 2160)),
   (21, BitVec.ofNat 64 (sp - 2160 + 4 * ix')), (22, BitVec.ofNat 64 (adp + 4 * ix')), (23, BitVec.ofNat 64 adp),
   (24, BitVec.ofNat 64 (2 * ua)), (25, j9), (26, j10), (27, j11)]

/-- `ix + 1 ≥ a->used`. -/
theorem n2_step (v : Abi) (outp : Array String) (sp ua adp ix s : Nat) (j0 j9 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hk : KS sp) (hu : bytesT8 M (sp - 2208) = BitVec.ofNat 64 ua)
    (hi : ua ≤ ix + 1) (hi' : ix + 1 < 2 * ua) (hua : ua < 2 ^ 30) (hs : s < 2 ^ 64) :
    Triple (At 0x800070dc#64 (sP sp ua adp ix s j0 j9 j10 j11) M (kF v) outp)
      (At 0x800071ac#64 (mL sp ua adp (ix + 1) (s / 268435456) j0 j9 j10 j11) (writeLog M []) (kF v) outp) := by
  sq_ctx
  seg_stepx sqN2 0x800071ac#64 [rd8 M (sp - 2208)] [15, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [sP, qH] [mL] [hu] hc

/-- `a->used - 1 < s3`: `a4 = a->used`. -/
theorem m1_step (v : Abi) (outp : Array String) (sp ua adp ix' c : Nat) (j0 j9 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hk : KS sp) (hu : bytesT8 M (sp - 2200) = BitVec.ofNat 64 (ua - 1))
    (hlt : ua - 1 < 2 * ua - 1 - ix') (hua : 1 ≤ ua) (hua' : ua < 2 ^ 30) (hix : ix' < 2 * ua) :
    Triple (At 0x800071ac#64 (mL sp ua adp ix' c j0 j9 j10 j11) M (kF v) outp)
      (At 0x800071b8#64 ((14, BitVec.ofNat 64 ua) :: mL sp ua adp ix' c j0 j9 j10 j11) (writeLog M []) (kF v) outp) := by
  sq_ctx
  have h1 : bytesT8 M (sp - 2208 + 8) = BitVec.ofNat 64 (ua - 1) := by
    rw [show sp - 2208 + 8 = sp - 2200 by omega]; exact hu
  seg_stepx sqM1 0x800071b8#64 [rd8 M (sp - 2208 + 8)] [2, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [mL] [mL] [h1] hc

/-- `s3 ≤ a->used - 1`: `a4 = s3`. -/
theorem m2_step (v : Abi) (outp : Array String) (sp ua adp ix' c : Nat) (j0 j9 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hk : KS sp) (hu : bytesT8 M (sp - 2200) = BitVec.ofNat 64 (ua - 1))
    (hge : 2 * ua - 1 - ix' ≤ ua - 1) (hua : 1 ≤ ua) (hua' : ua < 2 ^ 30) (hix : ix' < 2 * ua) :
    Triple (At 0x800071ac#64 (mL sp ua adp ix' c j0 j9 j10 j11) M (kF v) outp)
      (At 0x800071b8#64 ((14, BitVec.ofNat 64 (2 * ua - 1 - ix')) :: mL sp ua adp ix' c j0 j9 j10 j11) (writeLog M [])
        (kF v) outp) := by
  sq_ctx
  have h1 : bytesT8 M (sp - 2208 + 8) = BitVec.ofNat 64 (ua - 1) := by
    rw [show sp - 2208 + 8 = sp - 2200 by omega]; exact hu
  seg_stepx sqM2 0x800071b8#64 [rd8 M (sp - 2208 + 8)] [2, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [mL] [mL] [h1] hc

/-- `s0 = a5 = s3 >> 1`. -/
theorem ms_step (v : Abi) (outp : Array String) (sp ua adp ix' c a4 : Nat) (j0 j9 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hua : ua < 2 ^ 30) (hix : ix' < 2 * ua) :
    Triple (At 0x800071b8#64 ((14, BitVec.ofNat 64 a4) :: mL sp ua adp ix' c j0 j9 j10 j11) M (kF v) outp)
      (At 0x800071c0#64 ((14, BitVec.ofNat 64 a4) :: (15, BitVec.ofNat 64 ((2 * ua - 1 - ix') / 2)) ::
          mL sp ua adp ix' c (BitVec.ofNat 64 ((2 * ua - 1 - ix') / 2)) j9 j10 j11) (writeLog M []) (kF v) outp) := by
  sq_ctx
  seg_stepx sqMs 0x800071c0#64 ([] : List (List (BitVec 8))) [14, 2, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [mL] [mL] [] hc

/-- At `71c8`: `s0 = iy`. -/
def m4L (sp ua adp ix' c s0v : Nat) (j9 j10 j11 : BitVec 64) : GRegs := mL sp ua adp ix' c (BitVec.ofNat 64 s0v) j9 j10 j11

/-- `a4 ≥ s3 >> 1`: `iy = s3 >> 1`. -/
theorem m3_step (v : Abi) (outp : Array String) (sp ua adp ix' c a4 h : Nat) (j9 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hge : h ≤ a4) (hh : h < 2 ^ 31) (ha4 : a4 < 2 ^ 31) :
    Triple (At 0x800071c0#64 ((14, BitVec.ofNat 64 a4) :: (15, BitVec.ofNat 64 h) ::
        mL sp ua adp ix' c (BitVec.ofNat 64 h) j9 j10 j11) M (kF v) outp)
      (At 0x800071c8#64 (m4L sp ua adp ix' c h j9 j10 j11) (writeLog M []) (kF v) outp) := by
  sq_ctx
  seg_step sqM3 0x800071c8#64 ([] : List (List (BitVec 8))) [14, 15, 2, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [mL] [m4L, mL] [] hc

/-- `a4 < s3 >> 1`: `iy = a4`. -/
theorem m4_step (v : Abi) (outp : Array String) (sp ua adp ix' c a4 h : Nat) (j9 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hlt : a4 < h) (hh : h < 2 ^ 31) (ha4 : a4 < 2 ^ 31) :
    Triple (At 0x800071c0#64 ((14, BitVec.ofNat 64 a4) :: (15, BitVec.ofNat 64 h) ::
        mL sp ua adp ix' c (BitVec.ofNat 64 h) j9 j10 j11) M (kF v) outp)
      (At 0x800071c8#64 (m4L sp ua adp ix' c a4 j9 j10 j11) (writeLog M []) (kF v) outp) := by
  sq_ctx
  seg_step sqM4 0x800071c8#64 ([] : List (List (BitVec 8))) [14, 15, 2, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [mL] [m4L, mL] [] hc

/-- `iy = 0`: an empty half column, back to the head. -/
theorem m5_step (v : Abi) (outp : Array String) (sp ua adp ix' c : Nat) (j9 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hix : ix' < 2 ^ 30) :
    Triple (At 0x800071c8#64 (m4L sp ua adp ix' c 0 j9 j10 j11) M (kF v) outp)
      (At 0x800070a8#64 (qH sp ua adp ix' c (BitVec.ofNat 64 0) j9 j10 j11) (writeLog M []) (kF v) outp) := by
  sq_ctx
  seg_step sqM5 0x800070a8#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [m4L, mL] [qH] [] hc

/-- `iy > 0`: `tx = ix' + 1 - a->used`, `ty = a->used - 1`. -/
theorem m6_step (v : Abi) (outp : Array String) (sp ua adp ix' c iy : Nat) (j9 j10 j11 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hk : KS sp)
    (h24 : bytesT8 M (sp - 2184) = BitVec.ofNat 64 ua) (h32 : bytesT8 M (sp - 2176) = BitVec.ofNat 64 (4 * (ua - 1)))
    (hiy : 0 < iy) (hiy' : iy < 2 ^ 31) (hu : ua ≤ ix') (hix : ix' < 2 * ua) (hua : ua < 2 ^ 30) :
    Triple (At 0x800071c8#64 (m4L sp ua adp ix' c iy j9 j10 j11) M (kF v) outp)
      (At 0x80007114#64 (iS sp ua adp ix' c (ix' + 1 - ua) (ua - 1) iy j9) (writeLog M []) (kF v) outp) := by
  sq_ctx
  have h1 : bytesT8 M (sp - 2208 + 24) = BitVec.ofNat 64 ua := by
    rw [show sp - 2208 + 24 = sp - 2184 by omega]; exact h24
  have h2 : bytesT8 M (sp - 2208 + 32) = BitVec.ofNat 64 (4 * (ua - 1)) := by
    rw [show sp - 2208 + 32 = sp - 2176 by omega]; exact h32
  seg_stepx sqM6 0x80007114#64 [rd8 M (sp - 2208 + 24), rd8 M (sp - 2208 + 32)]
    [2, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [m4L, mL] [iS] [h1, h2] hc

/-! ## The inner loop -/

/-- The inner loop's head `7120`, term `iz`, sum `S`. -/
def iH (sp ua adp ix c tx ty iy iz S : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2208)), (8, BitVec.ofNat 64 (adp + 4 * tx + 4 * iy)), (9, BitVec.ofNat 64 c),
   (18, BitVec.ofNat 64 ix), (19, BitVec.ofNat 64 (2 * ua - 1 - ix)), (20, BitVec.ofNat 64 (sp - 2160)),
   (21, BitVec.ofNat 64 (sp - 2160 + 4 * ix)), (22, BitVec.ofNat 64 (adp + 4 * ix)), (23, BitVec.ofNat 64 adp),
   (24, BitVec.ofNat 64 (2 * ua)), (25, BitVec.ofNat 64 S), (26, BitVec.ofNat 64 (adp + 4 * tx + 4 * iz)),
   (27, BitVec.ofNat 64 (adp + 4 * ty - 4 * iz))]

theorem i0_step (v : Abi) (outp : Array String) (sp ua adp ix c tx ty iy : Nat) (j9 : BitVec 64) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hiy : iy < 2 ^ 30) :
    Triple (At 0x80007114#64 (iS sp ua adp ix c tx ty iy j9) M (kF v) outp)
      (At 0x80007120#64 (iH sp ua adp ix c tx ty iy 0 0) (writeLog M []) (kF v) outp) := by
  sq_ctx
  seg_step sqI0 0x80007120#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [iS] [iH] [] hc

def kI (sp ua adp ix c tx ty iy iz S : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 2208)), (8, BitVec.ofNat 64 (adp + 4 * tx + 4 * iy)), (9, BitVec.ofNat 64 c),
   (18, BitVec.ofNat 64 ix), (19, BitVec.ofNat 64 (2 * ua - 1 - ix)), (20, BitVec.ofNat 64 (sp - 2160)),
   (21, BitVec.ofNat 64 (sp - 2160 + 4 * ix)), (22, BitVec.ofNat 64 (adp + 4 * ix)), (23, BitVec.ofNat 64 adp),
   (24, BitVec.ofNat 64 (2 * ua)), (25, BitVec.ofNat 64 S), (26, BitVec.ofNat 64 (adp + 4 * tx + 4 * (iz + 1))),
   (27, BitVec.ofNat 64 (adp + 4 * ty - 4 * (iz + 1)))]

def jI (sp ua adp ix c tx ty iy iz S x y : Nat) : GRegs :=
  (10, BitVec.ofNat 64 x) :: (11, BitVec.ofNat 64 y) :: kI sp ua adp ix c tx ty iy iz S

def rI (sp ua adp ix c tx ty iy iz S p : Nat) : GRegs := (10, BitVec.ofNat 64 p) :: kI sp ua adp ix c tx ty iy iz S

/-- The loads `a->dp[ty - iz]`, `a->dp[tx + iz]`. -/
theorem l1_step (v : Abi) (outp : Array String) (sp ua adp ix c tx ty iy iz S x y : Nat) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hx : DRead M (adp + 4 * tx + 4 * iz) x)
    (hy : DRead M (adp + 4 * ty - 4 * iz) y) (hb4 : 4 ≤ adp + 4 * ty - 4 * iz) :
    Triple (At 0x80007120#64 (iH sp ua adp ix c tx ty iy iz S) M (kF v) outp)
      (At 0x80007130#64 (jI sp ua adp ix c tx ty iy iz S x y) (writeLog M []) (kF v) outp) := by
  sq_ctx
  have h1 : zero_extend (m := 64) (bytesT4 M (adp + 4 * ty - 4 * iz)) = BitVec.ofNat 64 y := by
    rw [hy.v, zext_ofNat32 _ (by have := hy.lt; omega)]
  have h2 : zero_extend (m := 64) (bytesT4 M (adp + 4 * tx + 4 * iz)) = BitVec.ofNat 64 x := by
    rw [hx.v, zext_ofNat32 _ (by have := hx.lt; omega)]
  seg_step sqL1 0x80007130#64 [rd4 M (adp + 4 * ty - 4 * iz), rd4 M (adp + 4 * tx + 4 * iz)]
    [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [iH] [jI, kI] [h1, h2] hc

theorem l2_step (v : Abi) (outp : Array String) (sp ua adp ix c tx ty iy iz S p : Nat) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hS : S + p < 2 ^ 64) (hi : iz + 1 < iy)
    (ha : adp + 4 * tx + 4 * iy ≤ 2 ^ 32) :
    Triple (At 0x80007134#64 (rI sp ua adp ix c tx ty iy iz S p) M (kF v) outp)
      (At 0x80007120#64 (iH sp ua adp ix c tx ty iy (iz + 1) (S + p)) (writeLog M []) (kF v) outp) := by
  sq_ctx
  seg_step sqL2 0x80007120#64 ([] : List (List (BitVec 8))) [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [rI, kI] [iH] [] hc

theorem l2e_step (v : Abi) (outp : Array String) (sp ua adp ix c tx ty iy iz S p : Nat) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hS : S + p < 2 ^ 64) (hi : iz + 1 = iy) :
    Triple (At 0x80007134#64 (rI sp ua adp ix c tx ty iy iz S p) M (kF v) outp)
      (At 0x8000713c#64 (iH sp ua adp ix c tx ty iy iy (S + p)) (writeLog M []) (kF v) outp) := by
  sq_ctx
  seg_step sqL2e 0x8000713c#64 ([] : List (List (BitVec 8))) [10, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [rI, kI] [iH] [] hc

/-- Double the half column into the carry, back to the head. -/
theorem x_step (v : Abi) (outp : Array String) (sp ua adp ix c tx ty iy S : Nat) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hS : c + 2 * S < 2 ^ 64) :
    Triple (At 0x8000713c#64 (iH sp ua adp ix c tx ty iy iy S) M (kF v) outp)
      (At 0x800070a8#64 (qH sp ua adp ix (c + 2 * S) (BitVec.ofNat 64 (adp + 4 * tx + 4 * iy))
          (BitVec.ofNat 64 S) (BitVec.ofNat 64 (adp + 4 * tx + 4 * iy)) (BitVec.ofNat 64 (adp + 4 * ty - 4 * iy)))
        (writeLog M []) (kF v) outp) := by
  sq_ctx
  seg_step sqX 0x800070a8#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [iH] [qH] [] hc

/-! ## After the last column -/

/-- `b`'s struct, from the saved pointer. -/
structure BFacts (M : Mem) (sp pb ou bdp ua : Nat) : Prop where
  rb : Ram pb 24
  pb_al : pb % 8 = 0
  pb_v : bytesT8 M (sp - 2192) = BitVec.ofNat 64 pb
  pa_v : bytesT8 M (sp - 2168) = BitVec.ofNat 64 (2 * ua)
  ou_v : bytesT4 M pb = BitVec.ofNat 32 ou
  bdp_v : bytesT8 M (pb + 16) = BitVec.ofNat 64 bdp
  ou_lt : ou < 2 ^ 31
  code_b : pb + 24 ≤ sMpSqrFastBase ∨ sMpSqrFastBase + 700 ≤ pb

theorem BFacts.sx {M : Mem} {sp pb ou bdp ua : Nat} (h : BFacts M sp pb ou bdp ua) :
    BitVec.signExtend 64 (bytesT4 M pb) = BitVec.ofNat 64 ou := by
  rw [h.ou_v, signExtend_ofNat32 _ h.ou_lt]

/-- At `7214`: `a0 = pa`, `a1 = a4 = b->dp`, `a2 = b->dp + pa`, `a3 = b`, `a6 = olduse`. -/
def f1L (sp ua adp ix s pb bdp ou : Nat) (j0 j9 j10 j11 : BitVec 64) : GRegs :=
  (10, BitVec.ofNat 64 (2 * ua)) :: (11, BitVec.ofNat 64 bdp) :: (12, BitVec.ofNat 64 (bdp + 4 * (2 * ua))) ::
    (13, BitVec.ofNat 64 pb) :: (14, BitVec.ofNat 64 bdp) :: (16, BitVec.ofNat 64 ou) ::
    sP sp ua adp ix s j0 j9 j10 j11

theorem f1_step (v : Abi) (outp : Array String) (sp ua adp ix s pb bdp ou : Nat) (j0 j9 j10 j11 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hk : KS sp) (hf : BFacts M sp pb ou bdp ua)
    (hua : ua < 2 ^ 30) :
    Triple (At 0x800071ec#64 (sP sp ua adp ix s j0 j9 j10 j11) M (kF v) outp)
      (At 0x80007214#64 (f1L sp ua adp ix s pb bdp ou j0 j9 j10 j11) (writeLog M []) (kF v) outp) := by
  sq_ctx
  have hs := hf.sx
  have h1 : bytesT8 M (sp - 2208 + 16) = BitVec.ofNat 64 pb := by
    rw [show sp - 2208 + 16 = sp - 2192 by omega]; exact hf.pb_v
  have h2 : bytesT8 M (sp - 2208 + 40) = BitVec.ofNat 64 (2 * ua) := by
    rw [show sp - 2208 + 40 = sp - 2168 by omega]; exact hf.pa_v
  seg_step sqF1 0x80007214#64 [rd8 M (sp - 2208 + 16), rd8 M (sp - 2208 + 16), rd8 M (sp - 2208 + 40),
      rd8 M (pb + 16), rd4 M pb]
    [15, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [sP, qH] [f1L, sP, qH] [h1, h2, hf.bdp_v, hs] hc

/-- The copy loop's head `7218`: digit `j`. -/
def cL (sp ua adp ix s bdp ou j : Nat) (j0 j9 j10 j11 : BitVec 64) : GRegs :=
  [(10, BitVec.ofNat 64 (2 * ua)), (11, BitVec.ofNat 64 bdp), (12, BitVec.ofNat 64 (bdp + 4 * (2 * ua))),
   (14, BitVec.ofNat 64 (bdp + 4 * j)), (15, 268435455#64), (16, BitVec.ofNat 64 ou),
   (2, BitVec.ofNat 64 (sp - 2208)), (8, j0), (9, BitVec.ofNat 64 s), (18, BitVec.ofNat 64 ix),
   (19, BitVec.ofNat 64 (2 * ua - 1 - ix)), (20, BitVec.ofNat 64 (sp - 2160 + 4 * j)),
   (21, BitVec.ofNat 64 (sp - 2160 + 4 * ix)), (22, BitVec.ofNat 64 (adp + 4 * ix)), (23, BitVec.ofNat 64 adp),
   (24, BitVec.ofNat 64 (2 * ua)), (25, j9), (26, j10), (27, j11)]

/-- `b->used := pa`. -/
theorem f1b_step (v : Abi) (outp : Array String) (sp ua adp ix s pb bdp ou : Nat) (j0 j9 j10 j11 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hf : BFacts M sp pb ou bdp ua) (hua : ua < 2 ^ 30) :
    Triple (At 0x80007214#64 (f1L sp ua adp ix s pb bdp ou j0 j9 j10 j11) M (kF v) outp)
      (At 0x80007218#64 (cL sp ua adp ix s bdp ou 0 j0 j9 j10 j11) (writeLog M [(pb, 4, BitVec.ofNat 64 (2 * ua))])
        (kF v) outp) := by
  sq_ctx
  seg_step sqF1b 0x80007218#64 ([] : List (List (BitVec 8)))
    [10, 11, 12, 13, 14, 16, 15, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [f1L, sP, qH] [cL] [] hc

/-- The copy: `b->dp[j] := W[j] & MP_MASK`. -/
structure CFacts (M : Mem) (sp bdp ua j w : Nat) : Prop where
  k : KS sp
  rd : Ram (bdp + 4 * j) 4
  al : bdp % 4 = 0
  code_b : bdp + 4 * j + 4 ≤ sMpSqrFastBase ∨ sMpSqrFastBase + 700 ≤ bdp + 4 * j
  j_lt : j < 512
  w_v : bytesT4 M (sp - 2160 + 4 * j) = BitVec.ofNat 32 w
  w_lt : w < 268435456
  hb : bdp + 4 * (2 * ua) ≤ 2 ^ 32

theorem CFacts.sx {M : Mem} {sp bdp ua j w : Nat} (h : CFacts M sp bdp ua j w) :
    BitVec.signExtend 64 (bytesT4 M (sp - 2160 + 4 * j)) = BitVec.ofNat 64 w := by
  rw [h.w_v, signExtend_ofNat32 _ (by have := h.w_lt; omega)]

theorem c_step (v : Abi) (outp : Array String) (sp ua adp ix s bdp ou j w : Nat) (j0 j9 j10 j11 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hf : CFacts M sp bdp ua j w) (hj : j + 1 < 2 * ua) :
    Triple (At 0x80007218#64 (cL sp ua adp ix s bdp ou j j0 j9 j10 j11) M (kF v) outp)
      (At 0x80007218#64 (cL sp ua adp ix s bdp ou (j + 1) j0 j9 j10 j11)
        (writeLog M [(bdp + 4 * j, 4, BitVec.ofNat 64 (w % 268435456))]) (kF v) outp) := by
  sq_ctx
  have hs := hf.sx
  seg_step sqC 0x80007218#64 [rd4 M (sp - 2160 + 4 * j)]
    [10, 11, 12, 14, 15, 16, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [cL] [cL] [hs] hc

theorem ce_step (v : Abi) (outp : Array String) (sp ua adp ix s bdp ou j w : Nat) (j0 j9 j10 j11 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hf : CFacts M sp bdp ua j w) (hj : j + 1 = 2 * ua) :
    Triple (At 0x80007218#64 (cL sp ua adp ix s bdp ou j j0 j9 j10 j11) M (kF v) outp)
      (At 0x80007230#64 (cL sp ua adp ix s bdp ou (j + 1) j0 j9 j10 j11)
        (writeLog M [(bdp + 4 * j, 4, BitVec.ofNat 64 (w % 268435456))]) (kF v) outp) := by
  sq_ctx
  have hs := hf.sx
  seg_step sqCe 0x80007230#64 [rd4 M (sp - 2160 + 4 * j)]
    [10, 11, 12, 14, 15, 16, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [cL] [cL] [hs] hc

/-- The callee-saved registers after the copy. -/
def sAbi (v : Abi) (sp ua adp ix s : Nat) (j0 j9 j10 j11 : BitVec 64) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 2208), s0 := j0,
           s := ⟨BitVec.ofNat 64 s, BitVec.ofNat 64 ix, BitVec.ofNat 64 (2 * ua - 1 - ix),
                 BitVec.ofNat 64 (sp - 2160 + 4 * (2 * ua)), BitVec.ofNat 64 (sp - 2160 + 4 * ix),
                 BitVec.ofNat 64 (adp + 4 * ix), BitVec.ofNat 64 adp, BitVec.ofNat 64 (2 * ua), j9, j10, j11⟩ }

/-- `olduse ≤ pa`: no `memset`. -/
theorem f2t_step (v : Abi) (outp : Array String) (sp ua adp ix s bdp ou : Nat) (j0 j9 j10 j11 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hou : ou ≤ 2 * ua) (hua : 1 ≤ ua) (hua' : ua < 2 ^ 30)
    (hou' : ou < 2 ^ 31) :
    Triple (At 0x80007230#64 (cL sp ua adp ix s bdp ou (2 * ua) j0 j9 j10 j11) M (kF v) outp)
      (At 0x80007258#64 (abiL (sAbi v sp ua adp ix s j0 j9 j10 j11)) (writeLog M []) (kF v) outp) := by
  sq_ctx
  seg_step sqF2t 0x80007258#64 ([] : List (List (BitVec 8)))
    [10, 11, 12, 14, 15, 16, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [cL] [abiL, sAbi, sKeepL] [] hc

/-- `olduse > pa`: set up `memset(b->dp + pa, 0, 4 (olduse - pa))`. -/
theorem f2m_step (v : Abi) (outp : Array String) (sp ua adp ix s bdp ou : Nat) (j0 j9 j10 j11 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hou : 2 * ua < ou) (hua : 1 ≤ ua) (hou' : ou < 2 ^ 31)
    (hb : bdp + 4 * ou ≤ 2 ^ 32) :
    Triple (At 0x80007230#64 (cL sp ua adp ix s bdp ou (2 * ua) j0 j9 j10 j11) M (kF v) outp)
      (At 0x80007254#64 (msL (sAbi v sp ua adp ix s j0 j9 j10 j11) bdp (2 * ua) ou) (writeLog M []) (kF v) outp) := by
  sq_ctx
  seg_step sqF2m 0x80007254#64 ([] : List (List (BitVec 8)))
    [10, 11, 12, 14, 15, 16, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [cL] [msL, abiL, sAbi, sKeepL] [] hc

/-- The callee-saved registers on the `pa = 0` path. -/
def zAbi (v : Abi) (sp pa : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 2208), s0 := BitVec.ofNat 64 pa, s := { v.s with s8 := BitVec.ofNat 64 (2 * 0) } }

/-- At `72bc` (`pa = 0`): `a5 = b`, `a2 = olduse`, `a0 = b->dp`. -/
def z1L (v : Abi) (sp pa pb ou bdp : Nat) : GRegs :=
  (15, BitVec.ofNat 64 pb) :: (12, BitVec.ofNat 64 ou) :: (10, BitVec.ofNat 64 bdp) :: zL v sp pa

/-- `b`'s struct on the `a->used = 0` path. -/
structure ZFacts (M : Mem) (sp pb ou bdp : Nat) : Prop where
  rb : Ram pb 24
  pb_v : bytesT8 M (sp - 2192) = BitVec.ofNat 64 pb
  ou_v : bytesT4 M pb = BitVec.ofNat 32 ou
  bdp_v : bytesT8 M (pb + 16) = BitVec.ofNat 64 bdp
  ou_lt : ou < 2 ^ 31

theorem ZFacts.sx {M : Mem} {sp pb ou bdp : Nat} (h : ZFacts M sp pb ou bdp) :
    BitVec.signExtend 64 (bytesT4 M pb) = BitVec.ofNat 64 ou := by
  rw [h.ou_v, signExtend_ofNat32 _ h.ou_lt]

theorem z_step (v : Abi) (outp : Array String) (sp pa pb ou bdp : Nat) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hk : KS sp) (hf : ZFacts M sp pb ou bdp) :
    Triple (At 0x800072b0#64 (zL v sp pa) M (kF v) outp)
      (At 0x800072bc#64 (z1L v sp pa pb ou bdp) (writeLog M []) (kF v) outp) := by
  sq_ctx
  have hs := hf.sx
  have h1 : bytesT8 M (sp - 2208 + 16) = BitVec.ofNat 64 pb := by
    rw [show sp - 2208 + 16 = sp - 2192 by omega]; exact hf.pb_v
  seg_step sqZ 0x800072bc#64 [rd8 M (sp - 2208 + 16), rd4 M pb, rd8 M (pb + 16)]
    [14, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [zL] [z1L, zL] [h1, hs, hf.bdp_v] hc

/-- The `b->used` store of the `pa = 0` path. -/
structure UFacts (pb : Nat) : Prop where
  rb : Ram pb 24
  pb_al : pb % 8 = 0
  code_b : pb + 24 ≤ sMpSqrFastBase ∨ sMpSqrFastBase + 700 ≤ pb

theorem zt_step (v : Abi) (outp : Array String) (sp pa pb bdp : Nat) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hf : UFacts pb) :
    Triple (At 0x800072bc#64 (z1L v sp pa pb 0 bdp) M (kF v) outp)
      (At 0x80007258#64 (abiL (zAbi v sp pa)) (writeLog M [(pb, 4, 0#64)]) (kF v) outp) := by
  sq_ctx
  seg_step sqZt 0x80007258#64 ([] : List (List (BitVec 8)))
    [15, 12, 10, 14, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [z1L, zL]
    [abiL, zAbi, sKeepL] [] hc

theorem zm_step (v : Abi) (outp : Array String) (sp pa pb ou bdp : Nat) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hf : UFacts pb) (hou : 0 < ou) (hou' : ou < 2 ^ 31) :
    Triple (At 0x800072bc#64 (z1L v sp pa pb ou bdp) M (kF v) outp)
      (At 0x80007254#64 (msL (zAbi v sp pa) bdp 0 ou) (writeLog M [(pb, 4, 0#64)]) (kF v) outp) := by
  sq_ctx
  seg_step sqZm 0x80007254#64 ([] : List (List (BitVec 8)))
    [15, 12, 10, 14, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] kFKeys [z1L, zL]
    [msL, abiL, zAbi, sKeepL] [] hc

theorem gc_step (v : Abi) (outp : Array String) (u : Abi) (sp pb : Nat) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hk : KS sp) (hsp : u.sp = BitVec.ofNat 64 (sp - 2208))
    (hp : bytesT8 M (sp - 2192) = BitVec.ofNat 64 pb) :
    Triple (At 0x80007258#64 (abiL u) M (kF v) outp) (At 0x8000725c#64 (clL u pb) (writeLog M []) (kF v) outp) := by
  sq_ctx
  have h1 : bytesT8 M (sp - 2208 + 16) = BitVec.ofNat 64 pb := by
    rw [show sp - 2208 + 16 = sp - 2192 by omega]; exact hp
  seg_step sqGc 0x8000725c#64 [rd8 M (sp - 2208 + 16)] [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
    kFKeys [abiL, sKeepL] [clL, abiL, sKeepL] [hsp, h1] hc

/-- The saved registers (the slots of `s_mp_mul_digs_fast`'s frame). -/
structure HFacts (M : Mem) (ra s0 : BitVec 64) (v : Abi) (sp : Nat) : Prop where
  k : KS sp
  ra_al : ra.toNat % 4 = 0
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  s1_v : bytesT8 M (sp - 24) = v.s.s1
  s2_v : bytesT8 M (sp - 32) = v.s.s2
  s3_v : bytesT8 M (sp - 40) = v.s.s3
  s4_v : bytesT8 M (sp - 48) = v.s.s4
  s5_v : bytesT8 M (sp - 56) = v.s.s5
  s6_v : bytesT8 M (sp - 64) = v.s.s6
  s7_v : bytesT8 M (sp - 72) = v.s.s7
  s8_v : bytesT8 M (sp - 80) = v.s.s8
  s9_v : bytesT8 M (sp - 88) = v.s.s9
  s10_v : bytesT8 M (sp - 96) = v.s.s10
  s11_v : bytesT8 M (sp - 104) = v.s.s11

theorem h_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hf : HFacts M ra s0 v sp) :
    Triple (At 0x80007260#64 [(2, BitVec.ofNat 64 (sp - 2208))] M (kF v) outp)
      (At ra (rL ra s0 v sp) (writeLog M []) (kF v) outp) := by
  sq_ctx
  have hra := hf.ra_al
  seg_step sqH ra [rd8 M (sp - 8), rd8 M (sp - 16), rd8 M (sp - 24), rd8 M (sp - 32), rd8 M (sp - 40),
      rd8 M (sp - 48), rd8 M (sp - 56), rd8 M (sp - 64), rd8 M (sp - 72), rd8 M (sp - 80), rd8 M (sp - 88),
      rd8 M (sp - 96), rd8 M (sp - 104)]
    [2] kFKeys [] [rL]
    [hf.ra_v, hf.s0_v, hf.s1_v, hf.s2_v, hf.s3_v, hf.s4_v, hf.s5_v, hf.s6_v, hf.s7_v, hf.s8_v, hf.s9_v,
     hf.s10_v, hf.s11_v] hc

end Tom.Machine.Fn.SqrFast
