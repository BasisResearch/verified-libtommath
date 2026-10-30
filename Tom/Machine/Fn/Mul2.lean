import Tom.Machine.Seg.Mul2
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Arr
import Tom.Machine.Kit.Bits
import Tom.Machine.Kit.Shift
import Tom.Machine.Kit.Jal
import Tom.Machine.Fn.Memset

/-!
# `mp_mul_2` on the machine: the segments

`mp_mul_2(a, b)` at `0x80005ca0` (60 instructions). The prologue saves
`s1`, `s0`, `ra`, sets `b->used := a->used` (`mul2E0`/`mul2E1`; the
`mp_grow` branch `a->used ≥ b->alloc` is excluded by the contract, D5); the
loop at `5cec` stores `b[i] := ((a[i] << 1) | r) & MP_MASK` and carries
`r := a[i] >> 27` (`mul2L`, the exit `mul2Le`); a final carry stores
`b[used] := 1` and `++b->used` (`mul2C1`, `mul2C2`), none jumps back
(`mul2N`); at `5d34` the excess digits are zeroed by `memset` if there are
any (`mul2T0`/`mul2T1`); `mul2R` copies the sign and returns `MP_OKAY`.
`s0 = a`, `s1 = b` are locals, so the segments keep `Abi.keepR1` and carry
`s0`, `s1`.
-/


namespace Tom.Machine.Fn.Mul2

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mul2_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpMul2Base = 0x80005ca0 := rfl
   have : mpMul2Code.length = 60 := rfl))

/-! ## Register lists at the join points -/

/-- At the entry (`s0`, `s1` carried). -/
def entry1 (ra s0 s1 : BitVec 64) (sp pa pb : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)]

/-- At the loop head `5cec`, index `i`, carry `r`. -/
def lL (ra : BitVec 64) (sp pa pb bdp ou adp i r : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb),
   (10, BitVec.ofNat 64 bdp), (12, BitVec.ofNat 64 ou), (6, 268435455#64),
   (13, BitVec.ofNat 64 (bdp + 4 * i)), (15, BitVec.ofNat 64 r), (11, BitVec.ofNat 64 i),
   (16, BitVec.ofNat 64 (adp + 4 * i))]

/-- At `5d28`, after the carry digit `b[used] := 1`. -/
def cL (ra : BitVec 64) (sp pa pb bdp ou : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb),
   (10, BitVec.ofNat 64 bdp), (12, BitVec.ofNat 64 ou)]

/-- At `5d34`: `a1 = b->used = n`, `a2 = oldused`. -/
def tL (ra : BitVec 64) (sp pa pb bdp n ou : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb),
   (10, BitVec.ofNat 64 bdp), (11, BitVec.ofNat 64 n), (12, BitVec.ofNat 64 ou)]

/-- At the `memset` call (`5d4c`): `memset(b->dp + n, 0, 4 (oldused - n))`. -/
def msL (ra : BitVec 64) (sp pa pb bdp n ou : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb),
   (10, BitVec.ofNat 64 (bdp + 4 * n)), (11, 0#64), (12, BitVec.ofNat 64 (4 * (ou - n)))]

/-- At `5d50` (after the `memset` call, or instead of it). -/
def rL (sp pa pb : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb)]

/-- The frame stores of the prologue. -/
def frameLog (ra s0 s1 : BitVec 64) (sp : Nat) : List WEntry :=
  [(sp - 24, 8, s1), (sp - 16, 8, s0), (sp - 8, 8, ra)]

/-- At `5cc4`, after the frame stores and the `mp_grow` test. -/
def pL (ra : BitVec 64) (sp pa pb ua : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb),
   (11, BitVec.ofNat 64 ua)]

/-! ## Facts the segments read -/

/-- The prologue: `a->used`, `b->alloc`, the stack frame. -/
structure ProFacts (m : Mem) (sp pa pb ua al : Nat) : Prop where
  ra_ : Ram pa 24
  rb : Ram pb 24
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  ua_v : bytesT4 m pa = BitVec.ofNat 32 ua
  al_v : bytesT4 m (pb + 4) = BitVec.ofNat 32 al
  ua_lt : ua < 2 ^ 31
  al_lt : al < 2 ^ 31
  room : ua < al
  s_a : sp ≤ pa ∨ pa + 24 ≤ sp - 32
  s_b : sp ≤ pb ∨ pb + 24 ≤ sp - 32
  code_s : sp ≤ mpMul2Base ∨ mpMul2Base + 240 ≤ sp - 32

theorem ProFacts.sx {m : Mem} {sp pa pb ua al : Nat} (h : ProFacts m sp pa pb ua al) :
    BitVec.signExtend 64 (bytesT4 m pa) = BitVec.ofNat 64 ua ∧
      BitVec.signExtend 64 (bytesT4 m (pb + 4)) = BitVec.ofNat 64 al :=
  ⟨by rw [h.ua_v, signExtend_ofNat32 _ h.ua_lt], by rw [h.al_v, signExtend_ofNat32 _ h.al_lt]⟩

/-- `b`'s struct at `5cc4`: `oldused`, the digit pointer; `a`'s digit pointer. -/
structure BFacts (M : Mem) (pa pb ou bdp adp : Nat) : Prop where
  ra_ : Ram pa 24
  rb : Ram pb 24
  pb_al : pb % 8 = 0
  ou_v : bytesT4 M pb = BitVec.ofNat 32 ou
  bdp_v : bytesT8 M (pb + 16) = BitVec.ofNat 64 bdp
  adp_v : bytesT8 M (pa + 16) = BitVec.ofNat 64 adp
  ou_lt : ou < 2 ^ 31
  ab : pa + 24 ≤ pb ∨ pb + 4 ≤ pa + 16
  code_b : pb + 24 ≤ mpMul2Base ∨ mpMul2Base + 240 ≤ pb

theorem BFacts.sx {M : Mem} {pa pb ou bdp adp : Nat} (h : BFacts M pa pb ou bdp adp) :
    BitVec.signExtend 64 (bytesT4 M pb) = BitVec.ofNat 64 ou := by
  rw [h.ou_v, signExtend_ofNat32 _ h.ou_lt]

/-! ## The prologue -/

/-- Save `s1`, `s0`, `ra`; `b` has room (`a->used < b->alloc`, so no `mp_grow`). -/
theorem p_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb ua al : Nat) (m : Mem)
    (hc : CodeAt m mpMul2Base mpMul2Code) (hf : ProFacts m sp pa pb ua al) :
    Triple (At 0x80005ca0#64 (entry1 ra s0 s1 sp pa pb) m v.keepR1 outp)
      (At 0x80005cc4#64 (pL ra sp pa pb ua) (writeLog m (frameLog ra s0 s1 sp)) v.keepR1 outp) := by
  mul2_ctx
  have ⟨hua, hal⟩ := hf.sx
  seg_step mul2P 0x80005cc4#64 [rd4 m (pb + 4), rd4 m pa]
    [1, 2, 8, 9, 10, 11] abiKeysR1 [entry1, frameLog] [pL] [hua, hal] hc

/-- `a->used = 0`: `b->used := 0`, no loop, to `5d34` with `n = 0`. -/
theorem e0_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb ou bdp adp : Nat) (M : Mem)
    (hc : CodeAt M mpMul2Base mpMul2Code) (hf : BFacts M pa pb ou bdp adp) :
    Triple (At 0x80005cc4#64 (pL ra sp pa pb 0) M v.keepR1 outp)
      (At 0x80005d34#64 (tL ra sp pa pb bdp 0 ou) (writeLog M [(pb, 4, BitVec.ofNat 64 0)]) v.keepR1 outp) := by
  mul2_ctx
  have hou := hf.sx
  seg_step mul2E0 0x80005d34#64 [rd4 M pb, rd8 M (pb + 16)]
    [1, 2, 8, 9, 11] abiKeysR1 [pL] [tL] [hou, hf.bdp_v] hc

/-- `a->used ≥ 1`: `b->used := a->used`, load the digit pointers, enter the loop at
`i = 0`, `r = 0`. -/
theorem e1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb ua ou bdp adp : Nat)
    (M : Mem) (hc : CodeAt M mpMul2Base mpMul2Code) (hf : BFacts M pa pb ou bdp adp) (h1 : 1 ≤ ua)
    (hua : ua < 2 ^ 31) :
    Triple (At 0x80005cc4#64 (pL ra sp pa pb ua) M v.keepR1 outp)
      (At 0x80005cec#64 (lL ra sp pa pb bdp ou adp 0 0) (writeLog M [(pb, 4, BitVec.ofNat 64 ua)])
        v.keepR1 outp) := by
  mul2_ctx
  have hou := hf.sx
  seg_step mul2E1 0x80005cec#64 [rd4 M pb, rd8 M (pb + 16), rd8 M (pa + 16)]
    [1, 2, 8, 9, 11] abiKeysR1 [pL] [lL] [hou, hf.bdp_v, hf.adp_v] hc

/-! ## The loop -/

/-- One iteration's reads and store: `a[i] = x` and `a->used` (after the
store, so `a`'s struct is off `b`'s digit `i`), the store into `b[i]`. -/
structure LFacts (M : Mem) (pa adp bdp ua i x : Nat) : Prop where
  rx : Ram (adp + 4 * i) 4
  x_v : bytesT4 M (adp + 4 * i) = BitVec.ofNat 32 x
  x_lt : x < 268435456
  ra_ : Ram pa 24
  ua_v : bytesT4 M pa = BitVec.ofNat 32 ua
  ua_lt : ua < 2 ^ 31
  rb : Ram (bdp + 4 * i) 4
  b_al : bdp % 4 = 0
  ab : pa + 24 ≤ bdp + 4 * i ∨ bdp + 4 * i + 4 ≤ pa
  code_b : bdp + 4 * i + 4 ≤ mpMul2Base ∨ mpMul2Base + 240 ≤ bdp + 4 * i

theorem LFacts.sx {M : Mem} {pa adp bdp ua i x : Nat} (h : LFacts M pa adp bdp ua i x) :
    BitVec.signExtend 64 (bytesT4 M (adp + 4 * i)) = BitVec.ofNat 64 x ∧
      BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 ua :=
  ⟨by rw [h.x_v, signExtend_ofNat32 _ (by have := h.x_lt; omega)], by rw [h.ua_v, signExtend_ofNat32 _ h.ua_lt]⟩

/-- The loop's back edge: `b[i] := (2 x + r) mod 2^28`, carry `x / 2^27`. -/
theorem l_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb bdp ou adp ua i r x : Nat)
    (M : Mem) (hc : CodeAt M mpMul2Base mpMul2Code) (hf : LFacts M pa adp bdp ua i x) (hr : r ≤ 1)
    (hi : i + 1 < ua) :
    Triple (At 0x80005cec#64 (lL ra sp pa pb bdp ou adp i r) M v.keepR1 outp)
      (At 0x80005cec#64 (lL ra sp pa pb bdp ou adp (i + 1) (x / 134217728))
        (writeLog M [(bdp + 4 * i, 4, BitVec.ofNat 64 ((2 * x + r) % 268435456))]) v.keepR1 outp) := by
  mul2_ctx
  have ⟨hx, hua⟩ := hf.sx
  have hd := mul2_digit x r hf.x_lt hr
  seg_step mul2L 0x80005cec#64 [rd4 M (adp + 4 * i), rd4 M pa]
    [1, 2, 8, 9, 10, 12, 6, 13, 15, 11, 16] abiKeysR1 [lL] [] [hx, hua, hd] hc

/-- The loop's last iteration (`i + 1 = a->used`), falling out at `5d1c`. -/
theorem le_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb bdp ou adp ua i r x : Nat)
    (M : Mem) (hc : CodeAt M mpMul2Base mpMul2Code) (hf : LFacts M pa adp bdp ua i x) (hr : r ≤ 1)
    (hi : i + 1 = ua) :
    Triple (At 0x80005cec#64 (lL ra sp pa pb bdp ou adp i r) M v.keepR1 outp)
      (At 0x80005d1c#64 (lL ra sp pa pb bdp ou adp (i + 1) (x / 134217728))
        (writeLog M [(bdp + 4 * i, 4, BitVec.ofNat 64 ((2 * x + r) % 268435456))]) v.keepR1 outp) := by
  mul2_ctx
  have ⟨hx, hua⟩ := hf.sx
  have hd := mul2_digit x r hf.x_lt hr
  seg_step mul2Le 0x80005d1c#64 [rd4 M (adp + 4 * i), rd4 M pa]
    [1, 2, 8, 9, 10, 12, 6, 13, 15, 11, 16] abiKeysR1 [lL] [] [hx, hua, hd] hc

/-- `b->used` after the loop. -/
structure UFacts (M : Mem) (pb u : Nat) : Prop where
  rb : Ram pb 24
  u_v : bytesT4 M pb = BitVec.ofNat 32 u
  u_lt : u + 1 < 2 ^ 31

theorem UFacts.sx {M : Mem} {pb u : Nat} (h : UFacts M pb u) :
    BitVec.signExtend 64 (bytesT4 M pb) = BitVec.ofNat 64 u := by
  rw [h.u_v, signExtend_ofNat32 _ (by have := h.u_lt; omega)]

/-- No final carry: back to `5d34` with `n = b->used = a->used`. -/
theorem n_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb bdp ou adp ua : Nat)
    (M : Mem) (hc : CodeAt M mpMul2Base mpMul2Code) (hf : UFacts M pb ua) :
    Triple (At 0x80005d1c#64 (lL ra sp pa pb bdp ou adp ua 0) M v.keepR1 outp)
      (At 0x80005d34#64 (tL ra sp pa pb bdp ua ou) (writeLog M []) v.keepR1 outp) := by
  mul2_ctx
  have hu := hf.sx
  seg_step mul2N 0x80005d34#64 [rd4 M pb]
    [1, 2, 8, 9, 10, 12, 6, 13, 15, 11, 16] abiKeysR1 [lL] [tL] [hu] hc

/-- The store of the carry digit `b[used] := 1`. -/
structure CFacts (bdp ua : Nat) : Prop where
  rb : Ram (bdp + 4 * ua) 4
  b_al : bdp % 4 = 0
  code_b : bdp + 4 * ua + 4 ≤ mpMul2Base ∨ mpMul2Base + 240 ≤ bdp + 4 * ua

/-- A final carry: `b[a->used] := 1`. -/
theorem c1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb bdp ou adp ua : Nat)
    (M : Mem) (hc : CodeAt M mpMul2Base mpMul2Code) (hf : CFacts bdp ua) :
    Triple (At 0x80005d1c#64 (lL ra sp pa pb bdp ou adp ua 1) M v.keepR1 outp)
      (At 0x80005d28#64 (cL ra sp pa pb bdp ou) (writeLog M [(bdp + 4 * ua, 4, BitVec.ofNat 64 1)])
        v.keepR1 outp) := by
  mul2_ctx
  seg_step mul2C1 0x80005d28#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 12, 6, 13, 15, 11, 16] abiKeysR1 [lL] [cL] [] hc

/-- `b`'s struct off the code. -/
structure SFacts (pb : Nat) : Prop where
  rb : Ram pb 24
  pb_al : pb % 8 = 0
  code_b : pb + 24 ≤ mpMul2Base ∨ mpMul2Base + 240 ≤ pb

/-- `++b->used`, to `5d34` with `n = a->used + 1`. -/
theorem c2_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb bdp ou ua : Nat)
    (M : Mem) (hc : CodeAt M mpMul2Base mpMul2Code) (hf : UFacts M pb ua) (hs : SFacts pb) :
    Triple (At 0x80005d28#64 (cL ra sp pa pb bdp ou) M v.keepR1 outp)
      (At 0x80005d34#64 (tL ra sp pa pb bdp (ua + 1) ou) (writeLog M [(pb, 4, BitVec.ofNat 64 (ua + 1))])
        v.keepR1 outp) := by
  mul2_ctx
  have hu := hf.sx
  seg_step mul2C2 0x80005d34#64 [rd4 M pb]
    [1, 2, 8, 9, 10, 12] abiKeysR1 [cL] [tL] [hu] hc

/-- `oldused ≤ n`: no `memset`. -/
theorem t0_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb bdp n ou : Nat)
    (M : Mem) (hc : CodeAt M mpMul2Base mpMul2Code) (hn : n < 2 ^ 31) (hou : ou ≤ n) :
    Triple (At 0x80005d34#64 (tL ra sp pa pb bdp n ou) M v.keepR1 outp)
      (At 0x80005d50#64 (rL sp pa pb) (writeLog M []) v.keepR1 outp) := by
  mul2_ctx
  seg_step mul2T0 0x80005d50#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 12] abiKeysR1 [tL] [rL] [] hc

/-- `n < oldused`: set up `memset(b->dp + n, 0, 4 (oldused - n))`. -/
theorem t1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb bdp n ou : Nat)
    (M : Mem) (hc : CodeAt M mpMul2Base mpMul2Code) (hou : n < ou) (hou' : ou < 2 ^ 31)
    (hb : bdp + 4 * ou ≤ 2 ^ 32) :
    Triple (At 0x80005d34#64 (tL ra sp pa pb bdp n ou) M v.keepR1 outp)
      (At 0x80005d4c#64 (msL ra sp pa pb bdp n ou) (writeLog M []) v.keepR1 outp) := by
  mul2_ctx
  seg_step mul2T1 0x80005d4c#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 12] abiKeysR1 [tL] [msL] [] hc

/-- The epilogue's reads: `a->sign`, the saved registers. -/
structure RFacts (M : Mem) (ra s0 s1 : BitVec 64) (sp pa pb sa : Nat) : Prop where
  ra_ : Ram pa 24
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  sa_v : bytesT4 M (pa + 8) = BitVec.ofNat 32 sa
  sa_lt : sa < 2 ^ 31
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  s1_v : bytesT8 M (sp - 24) = s1
  ra_al : ra.toNat % 4 = 0
  s : SFacts pb
  s_b : sp ≤ pb ∨ pb + 24 ≤ sp - 32

/-- `b->sign := a->sign`, restore `ra`, `s0`, `s1`, `sp`; return `MP_OKAY`. -/
theorem r_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb sa : Nat)
    (M : Mem) (hc : CodeAt M mpMul2Base mpMul2Code) (hf : RFacts M ra s0 s1 sp pa pb sa) :
    Triple (At 0x80005d50#64 (rL sp pa pb) M v.keepR1 outp)
      (At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, 0#64)]
        (writeLog M [(pb + 8, 4, BitVec.ofNat 64 sa)]) v.keepR1 outp) := by
  mul2_ctx
  have hra := hf.ra_al
  have hsa : BitVec.signExtend 64 (bytesT4 M (pa + 8)) = BitVec.ofNat 64 sa := by
    rw [hf.sa_v, signExtend_ofNat32 _ hf.sa_lt]
  have h1 : bytesT8 M (sp - 32 + 24) = ra := by rw [show sp - 32 + 24 = sp - 8 by omega]; exact hf.ra_v
  have h2 : bytesT8 M (sp - 32 + 16) = s0 := by rw [show sp - 32 + 16 = sp - 16 by omega]; exact hf.s0_v
  have h3 : bytesT8 M (sp - 32 + 8) = s1 := by rw [show sp - 32 + 8 = sp - 24 by omega]; exact hf.s1_v
  seg_step mul2R ra [rd4 M (pa + 8), rd8 M (sp - 32 + 24), rd8 M (sp - 32 + 16), rd8 M (sp - 32 + 8)]
    [2, 8, 9] abiKeysR1 [rL] [] [hsa, h1, h2, h3] hc

/-! ## The `memset` call -/

/-- The callee-saved registers `memset` sees: this frame's `sp`, `s0 = a`, `s1 = b`. -/
def calleeAbi (v : Abi) (sp pa pb : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 32), s0 := BitVec.ofNat 64 pa,
           s := { v.s with s1 := BitVec.ofNat 64 pb } }

/-- `memset(b->dp + n, 0, 4 (oldused - n))` at `5d4c`, back at `5d50`. -/
theorem memset_call (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb bdp n ou : Nat) (M : Mem)
    (hc : CodeAt M mpMul2Base mpMul2Code) (hP : Memset.Pre M (bdp + 4 * n) 0 (4 * (ou - n))) :
    Triple (At 0x80005d4c#64 (msL ra sp pa pb bdp n ou) M v.keepR1 outp)
      (fun c => ∃ M', At 0x80005d50#64 (rL sp pa pb) M' v.keepR1 outp c ∧
        Memset.Post M (bdp + 4 * n) (4 * (ou - n)) 0#8 M') := by
  refine Triple.seq (jal_at (pc := 0x80005d4c#64) (w := 0x658030ef#32) (imm := 0x03658#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb),
        (10, BitVec.ofNat 64 (bdp + 4 * n)), (11, 0#64), (12, BitVec.ofNat 64 (4 * (ou - n)))])
      (hc.word (a := (0x80005d4c#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [msL]) (by simp [keysG]) (by simp [Abi.keepR1, keysG])) ?_
  refine Triple.conseq (Memset.correct_zero 0x80005d50#64 (calleeAbi v sp pa pb) outp M _ _ (by decide) hP)
    (fun c h => ?_) (fun c ⟨M', hat, hpost⟩ => ⟨M', hat.reshape ?_ ?_, hpost⟩)
  · have hpc : (0x80005d4c#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x03658#21) = Memset.entry := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [Memset.entryL, Sail.BitVec.addInt]
    · simp [Abi.keep, Abi.keepR1, calleeAbi, sKeepL]
  · simp [rL, Abi.keep, calleeAbi, sKeepL]
  · simp [Abi.keep, Abi.keepR1, calleeAbi, sKeepL]

end Tom.Machine.Fn.Mul2
