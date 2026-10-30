import Tom.Machine.Seg.Div2
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Arr
import Tom.Machine.Kit.Bits
import Tom.Machine.Kit.Shift
import Tom.Machine.Kit.Jal
import Tom.Machine.Fn.Memset
import Tom.Machine.Fn.Clamp

/-!
# `mp_div_2` on the machine: the segments

`mp_div_2(a, b)` at `0x80005134` (54 instructions). The prologue saves
`s0`, `s1`, `ra` (`div2P`; the `mp_grow` branch `b->alloc < a->used` is
excluded by the contract, D5) and sets `b->used := a->used` (`div2E0`,
`div2E1`); the loop at `518c` runs from the top digit down, storing
`b[x] := (a[x] >> 1) | (r << 27)` and carrying `r := a[x] & 1` (`div2L`,
the exit `div2Le`, which reloads `b->used`); at `51b4` the excess digits are
zeroed by `memset` if there are any (`div2T0`/`div2T1`); `div2S` copies the
sign and calls `mp_clamp(b)`; `div2R` returns `MP_OKAY`. `s0 = b`, `s1 = a`
are locals (`Abi.keepR1`).
-/


namespace Tom.Machine.Fn.Div2

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "div2_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpDiv2Base = 0x80005134 := rfl
   have : mpDiv2Code.length = 54 := rfl))

/-! ## Register lists at the join points -/

/-- At the entry (`s0`, `s1` carried). -/
def entry1 (ra s0 s1 : BitVec 64) (sp pa pb : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)]

/-- The frame stores of the prologue. -/
def frameLog (ra s0 s1 : BitVec 64) (sp : Nat) : List WEntry :=
  [(sp - 16, 8, s0), (sp - 24, 8, s1), (sp - 8, 8, ra)]

/-- At `5158`, after the frame stores and the `mp_grow` test. -/
def pL (ra : BitVec 64) (sp pa pb ua : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pb), (9, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 ua)]

/-- At the loop head `518c`, index `x`, carry `r` (the low bit of `a[x + 1]`). -/
def lL (ra : BitVec 64) (sp pa pb bdp ou adp x r : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pb), (9, BitVec.ofNat 64 pa),
   (10, BitVec.ofNat 64 bdp), (12, BitVec.ofNat 64 ou), (11, BitVec.ofNat 64 (adp - 4)),
   (14, BitVec.ofNat 64 (adp + 4 * x)), (16, BitVec.ofNat 64 (bdp + 4 * x)), (15, BitVec.ofNat 64 r)]

/-- At `51b4`: `a1 = b->used = n`, `a2 = oldused`. -/
def tL (ra : BitVec 64) (sp pa pb bdp n ou : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pb), (9, BitVec.ofNat 64 pa),
   (10, BitVec.ofNat 64 bdp), (11, BitVec.ofNat 64 n), (12, BitVec.ofNat 64 ou)]

/-- At the `memset` call (`51cc`): `memset(b->dp + n, 0, 4 (oldused - n))`. -/
def msL (ra : BitVec 64) (sp pa pb bdp n ou : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pb), (9, BitVec.ofNat 64 pa),
   (10, BitVec.ofNat 64 (bdp + 4 * n)), (11, 0#64), (12, BitVec.ofNat 64 (4 * (ou - n)))]

/-- At `51d0` (after the `memset` call, or instead of it), and at `51e0` after `mp_clamp`. -/
def rL (sp pa pb : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pb), (9, BitVec.ofNat 64 pa)]

/-- At the `mp_clamp` call (`51dc`). -/
def cL (sp pa pb : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pb), (9, BitVec.ofNat 64 pa), (10, BitVec.ofNat 64 pb)]

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
  room : ua ≤ al
  s_a : sp ≤ pa ∨ pa + 24 ≤ sp - 32
  s_b : sp ≤ pb ∨ pb + 24 ≤ sp - 32
  code_s : sp ≤ mpDiv2Base ∨ mpDiv2Base + 216 ≤ sp - 32

theorem ProFacts.sx {m : Mem} {sp pa pb ua al : Nat} (h : ProFacts m sp pa pb ua al) :
    BitVec.signExtend 64 (bytesT4 m pa) = BitVec.ofNat 64 ua ∧
      BitVec.signExtend 64 (bytesT4 m (pb + 4)) = BitVec.ofNat 64 al :=
  ⟨by rw [h.ua_v, signExtend_ofNat32 _ h.ua_lt], by rw [h.al_v, signExtend_ofNat32 _ h.al_lt]⟩

/-- `b`'s struct at `5158`: `oldused`, the digit pointer; `a`'s digit pointer. -/
structure BFacts (M : Mem) (pa pb ou bdp adp : Nat) : Prop where
  ra_ : Ram pa 24
  rb : Ram pb 24
  pb_al : pb % 8 = 0
  ou_v : bytesT4 M pb = BitVec.ofNat 32 ou
  bdp_v : bytesT8 M (pb + 16) = BitVec.ofNat 64 bdp
  adp_v : bytesT8 M (pa + 16) = BitVec.ofNat 64 adp
  ou_lt : ou < 2 ^ 31
  ab : pa + 24 ≤ pb ∨ pb + 4 ≤ pa + 16
  code_b : pb + 24 ≤ mpDiv2Base ∨ mpDiv2Base + 216 ≤ pb

theorem BFacts.sx {M : Mem} {pa pb ou bdp adp : Nat} (h : BFacts M pa pb ou bdp adp) :
    BitVec.signExtend 64 (bytesT4 M pb) = BitVec.ofNat 64 ou := by
  rw [h.ou_v, signExtend_ofNat32 _ h.ou_lt]

/-- The digit arrays' bounds. -/
structure DFacts (adp bdp ua : Nat) : Prop where
  ra_d : Ram adp (4 * ua)
  rb_d : Ram bdp (4 * ua)
  ua_lt : ua < 2 ^ 31

/-! ## The prologue -/

/-- Save `s0`, `s1`, `ra`; `b` has room (`a->used ≤ b->alloc`, so no `mp_grow`). -/
theorem p_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb ua al : Nat) (m : Mem)
    (hc : CodeAt m mpDiv2Base mpDiv2Code) (hf : ProFacts m sp pa pb ua al) :
    Triple (At 0x80005134#64 (entry1 ra s0 s1 sp pa pb) m v.keepR1 outp)
      (At 0x80005158#64 (pL ra sp pa pb ua) (writeLog m (frameLog ra s0 s1 sp)) v.keepR1 outp) := by
  div2_ctx
  have ⟨hua, hal⟩ := hf.sx
  seg_step div2P 0x80005158#64 [rd4 m (pb + 4), rd4 m pa]
    [1, 2, 8, 9, 10, 11] abiKeysR1 [entry1, frameLog] [pL] [hua, hal] hc

/-- `a->used = 0`: `b->used := 0`, no loop, to `51b4` with `n = 0`. -/
theorem e0_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb ou bdp adp : Nat) (M : Mem)
    (hc : CodeAt M mpDiv2Base mpDiv2Code) (hf : BFacts M pa pb ou bdp adp) :
    Triple (At 0x80005158#64 (pL ra sp pa pb 0) M v.keepR1 outp)
      (At 0x800051b4#64 (tL ra sp pa pb bdp 0 ou) (writeLog M [(pb, 4, BitVec.ofNat 64 0)]) v.keepR1 outp) := by
  div2_ctx
  have hou := hf.sx
  seg_step div2E0 0x800051b4#64 [rd4 M pb, rd8 M (pb + 16)]
    [1, 2, 8, 9, 11] abiKeysR1 [pL] [tL] [hou, hf.bdp_v] hc

/-- At `5168`: `a->used ≥ 1`, `b->used := a->used` stored. -/
def eL (ra : BitVec 64) (sp pa pb bdp ua ou : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pb), (9, BitVec.ofNat 64 pa),
   (10, BitVec.ofNat 64 bdp), (11, BitVec.ofNat 64 ua), (12, BitVec.ofNat 64 ou)]

/-- `a->used ≥ 1`: `b->used := a->used`. -/
theorem e1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb ua ou bdp adp : Nat)
    (M : Mem) (hc : CodeAt M mpDiv2Base mpDiv2Code) (hf : BFacts M pa pb ou bdp adp) (h1 : 1 ≤ ua)
    (hua : ua < 2 ^ 31) :
    Triple (At 0x80005158#64 (pL ra sp pa pb ua) M v.keepR1 outp)
      (At 0x80005168#64 (eL ra sp pa pb bdp ua ou) (writeLog M [(pb, 4, BitVec.ofNat 64 ua)]) v.keepR1 outp) := by
  div2_ctx
  have hou := hf.sx
  seg_step div2E1 0x80005168#64 [rd4 M pb, rd8 M (pb + 16)]
    [1, 2, 8, 9, 11] abiKeysR1 [pL] [eL] [hou, hf.bdp_v] hc

/-- Load `a`'s digit pointer and enter the loop at the top digit `x = a->used - 1`, `r = 0`. -/
theorem e2_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb ua ou bdp adp : Nat)
    (M : Mem) (hc : CodeAt M mpDiv2Base mpDiv2Code) (ha : Ram pa 24)
    (hadp : bytesT8 M (pa + 16) = BitVec.ofNat 64 adp) (hd : DFacts adp bdp ua) (h1 : 1 ≤ ua) :
    Triple (At 0x80005168#64 (eL ra sp pa pb bdp ua ou) M v.keepR1 outp)
      (At 0x8000518c#64 (lL ra sp pa pb bdp ou adp (ua - 1) 0) (writeLog M []) v.keepR1 outp) := by
  div2_ctx
  seg_step div2E2 0x8000518c#64 [rd8 M (pa + 16)]
    [1, 2, 8, 9, 10, 11, 12] abiKeysR1 [eL] [lL] [hadp] hc

/-! ## The loop -/

/-- One iteration's read `a[x] = d` and store into `b[x]`. -/
structure LFacts (adp bdp ua x d : Nat) (M : Mem) : Prop where
  rd : DFacts adp bdp ua
  x_lt : x < ua
  d_v : bytesT4 M (adp + 4 * x) = BitVec.ofNat 32 d
  d_lt : d < 268435456
  b_al : bdp % 4 = 0
  code_b : bdp + 4 * x + 4 ≤ mpDiv2Base ∨ mpDiv2Base + 216 ≤ bdp + 4 * x

theorem LFacts.sx {adp bdp ua x d : Nat} {M : Mem} (h : LFacts adp bdp ua x d M) :
    BitVec.signExtend 64 (bytesT4 M (adp + 4 * x)) = BitVec.ofNat 64 d := by
  rw [h.d_v, signExtend_ofNat32 _ (by have := h.d_lt; omega)]

/-- The loop's back edge from `x = k + 1`: `b[k + 1] := d / 2 + r 2^27`, carry `d mod 2`. -/
theorem l_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb bdp ou adp ua k r d : Nat)
    (M : Mem) (hc : CodeAt M mpDiv2Base mpDiv2Code) (hf : LFacts adp bdp ua (k + 1) d M) (hr : r ≤ 1) :
    Triple (At 0x8000518c#64 (lL ra sp pa pb bdp ou adp (k + 1) r) M v.keepR1 outp)
      (At 0x8000518c#64 (lL ra sp pa pb bdp ou adp k (d % 2))
        (writeLog M [(bdp + 4 * (k + 1), 4, BitVec.ofNat 64 (d / 2 + 134217728 * r))]) v.keepR1 outp) := by
  div2_ctx
  have hx := hf.sx
  have hd := div2_digit d r hf.d_lt hr
  have h1 := and1_ofNat d
  have := hf.rd.ra_d; have := hf.rd.rb_d; have := hf.x_lt
  seg_step div2L 0x8000518c#64 [rd4 M (adp + 4 * (k + 1))]
    [1, 2, 8, 9, 10, 12, 11, 14, 16, 15] abiKeysR1 [lL] [] [hx, hd, h1] hc

/-- `b->used` (reloaded after the loop's last store into `b[0]`). -/
structure UFacts (M : Mem) (pb bdp u : Nat) : Prop where
  rb : Ram pb 24
  u_v : bytesT4 M pb = BitVec.ofNat 32 u
  u_lt : u < 2 ^ 31
  bb : pb + 24 ≤ bdp ∨ bdp + 4 ≤ pb

theorem UFacts.sx {M : Mem} {pb bdp u : Nat} (h : UFacts M pb bdp u) :
    BitVec.signExtend 64 (bytesT4 M pb) = BitVec.ofNat 64 u := by
  rw [h.u_v, signExtend_ofNat32 _ h.u_lt]

/-- The loop's last iteration (`x = 0`): `b[0] := d / 2 + r 2^27`, reload `b->used`, to `51b4`. -/
theorem le_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb bdp ou adp ua n r d : Nat)
    (M : Mem) (hc : CodeAt M mpDiv2Base mpDiv2Code) (hf : LFacts adp bdp ua 0 d M) (hr : r ≤ 1)
    (hu : UFacts M pb bdp n) :
    Triple (At 0x8000518c#64 (lL ra sp pa pb bdp ou adp 0 r) M v.keepR1 outp)
      (At 0x800051b4#64 (tL ra sp pa pb bdp n ou)
        (writeLog M [(bdp + 4 * 0, 4, BitVec.ofNat 64 (d / 2 + 134217728 * r))]) v.keepR1 outp) := by
  div2_ctx
  have hx := hf.sx
  have hn := hu.sx
  have hd := div2_digit d r hf.d_lt hr
  have := hf.rd.ra_d; have := hf.rd.rb_d; have := hf.x_lt
  seg_step div2Le 0x800051b4#64 [rd4 M (adp + 4 * 0), rd4 M pb]
    [1, 2, 8, 9, 10, 12, 11, 14, 16, 15] abiKeysR1 [lL] [tL] [hx, hn, hd] hc

/-- `oldused ≤ n`: no `memset`. -/
theorem t0_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb bdp n ou : Nat)
    (M : Mem) (hc : CodeAt M mpDiv2Base mpDiv2Code) (hn : n < 2 ^ 31) (hou : ou ≤ n) :
    Triple (At 0x800051b4#64 (tL ra sp pa pb bdp n ou) M v.keepR1 outp)
      (At 0x800051d0#64 (rL sp pa pb) (writeLog M []) v.keepR1 outp) := by
  div2_ctx
  seg_step div2T0 0x800051d0#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 12] abiKeysR1 [tL] [rL] [] hc

/-- `n < oldused`: set up `memset(b->dp + n, 0, 4 (oldused - n))`. -/
theorem t1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb bdp n ou : Nat)
    (M : Mem) (hc : CodeAt M mpDiv2Base mpDiv2Code) (hou : n < ou) (hou' : ou < 2 ^ 31)
    (hb : bdp + 4 * ou ≤ 2 ^ 32) :
    Triple (At 0x800051b4#64 (tL ra sp pa pb bdp n ou) M v.keepR1 outp)
      (At 0x800051cc#64 (msL ra sp pa pb bdp n ou) (writeLog M []) v.keepR1 outp) := by
  div2_ctx
  seg_step div2T1 0x800051cc#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 9, 10, 11, 12] abiKeysR1 [tL] [msL] [] hc

/-- `b`'s struct off the code; `a->sign`. -/
structure SFacts (M : Mem) (pa pb sa : Nat) : Prop where
  ra_ : Ram pa 24
  rb : Ram pb 24
  pb_al : pb % 8 = 0
  code_b : pb + 24 ≤ mpDiv2Base ∨ mpDiv2Base + 216 ≤ pb
  sa_v : bytesT4 M (pa + 8) = BitVec.ofNat 32 sa
  sa_lt : sa < 2 ^ 31

/-- `b->sign := a->sign`; `a0 := b` for `mp_clamp`. -/
theorem s_step (v : Abi) (outp : Array String) (sp pa pb sa : Nat)
    (M : Mem) (hc : CodeAt M mpDiv2Base mpDiv2Code) (hf : SFacts M pa pb sa) :
    Triple (At 0x800051d0#64 (rL sp pa pb) M v.keepR1 outp)
      (At 0x800051dc#64 (cL sp pa pb) (writeLog M [(pb + 8, 4, BitVec.ofNat 64 sa)]) v.keepR1 outp) := by
  div2_ctx
  have hsa : BitVec.signExtend 64 (bytesT4 M (pa + 8)) = BitVec.ofNat 64 sa := by
    rw [hf.sa_v, signExtend_ofNat32 _ hf.sa_lt]
  seg_step div2S 0x800051dc#64 [rd4 M (pa + 8)] [2, 8, 9] abiKeysR1 [rL] [cL] [hsa] hc

/-- The epilogue's reads: the saved registers. -/
structure RFacts (M : Mem) (ra s0 s1 : BitVec 64) (sp : Nat) : Prop where
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  s1_v : bytesT8 M (sp - 24) = s1
  ra_al : ra.toNat % 4 = 0

/-- Restore `ra`, `s0`, `s1`, `sp`; return `MP_OKAY`. -/
theorem r_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb : Nat)
    (M : Mem) (hc : CodeAt M mpDiv2Base mpDiv2Code) (hf : RFacts M ra s0 s1 sp) :
    Triple (At 0x800051e0#64 (rL sp pa pb) M v.keepR1 outp)
      (At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, 0#64)] (writeLog M []) v.keepR1 outp) := by
  div2_ctx
  have hra := hf.ra_al
  have h1 : bytesT8 M (sp - 32 + 24) = ra := by rw [show sp - 32 + 24 = sp - 8 by omega]; exact hf.ra_v
  have h2 : bytesT8 M (sp - 32 + 16) = s0 := by rw [show sp - 32 + 16 = sp - 16 by omega]; exact hf.s0_v
  have h3 : bytesT8 M (sp - 32 + 8) = s1 := by rw [show sp - 32 + 8 = sp - 24 by omega]; exact hf.s1_v
  seg_step div2R ra [rd8 M (sp - 32 + 24), rd8 M (sp - 32 + 16), rd8 M (sp - 32 + 8)]
    [2, 8, 9] abiKeysR1 [rL] [] [h1, h2, h3] hc

/-! ## The calls -/

/-- The callee-saved registers `memset`/`mp_clamp` see: this frame's `sp`, `s0 = b`, `s1 = a`. -/
def calleeAbi (v : Abi) (sp pa pb : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 32), s0 := BitVec.ofNat 64 pb,
           s := { v.s with s1 := BitVec.ofNat 64 pa } }

/-- `memset(b->dp + n, 0, 4 (oldused - n))` at `51cc`, back at `51d0`. -/
theorem memset_call (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb bdp n ou : Nat) (M : Mem)
    (hc : CodeAt M mpDiv2Base mpDiv2Code) (hP : Memset.Pre M (bdp + 4 * n) 0 (4 * (ou - n))) :
    Triple (At 0x800051cc#64 (msL ra sp pa pb bdp n ou) M v.keepR1 outp)
      (fun c => ∃ M', At 0x800051d0#64 (rL sp pa pb) M' v.keepR1 outp c ∧
        Memset.Post M (bdp + 4 * n) (4 * (ou - n)) 0#8 M') := by
  refine Triple.seq (jal_at (pc := 0x800051cc#64) (w := 0x1d8040ef#32) (imm := 0x041d8#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pb), (9, BitVec.ofNat 64 pa),
        (10, BitVec.ofNat 64 (bdp + 4 * n)), (11, 0#64), (12, BitVec.ofNat 64 (4 * (ou - n)))])
      (hc.word (a := (0x800051cc#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [msL]) (by simp [keysG]) (by simp [Abi.keepR1, keysG])) ?_
  refine Triple.conseq (Memset.correct_zero 0x800051d0#64 (calleeAbi v sp pa pb) outp M _ _ (by decide) hP)
    (fun c h => ?_) (fun c ⟨M', hat, hpost⟩ => ⟨M', hat.reshape ?_ ?_, hpost⟩)
  · have hpc : (0x800051cc#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x041d8#21) = Memset.entry := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [Memset.entryL, Sail.BitVec.addInt]
    · simp [Abi.keep, Abi.keepR1, calleeAbi, sKeepL]
  · simp [rL, Abi.keep, calleeAbi, sKeepL]
  · simp [Abi.keep, Abi.keepR1, calleeAbi, sKeepL]

/-- `mp_clamp(b)` at `51dc`, back at `51e0`. -/
theorem clamp_call (v : Abi) (outp : Array String) (sp pa pb bdp : Nat) (cm : MpInt) (M : Mem)
    (hc : CodeAt M mpDiv2Base mpDiv2Code) (hP : Clamp.Pre M pb bdp cm) :
    Triple (At 0x800051dc#64 (cL sp pa pb) M v.keepR1 outp)
      (fun c => ∃ a' M', At 0x800051e0#64 (rL sp pa pb) M' v.keepR1 outp c ∧
        Clamp.Post M pb bdp cm a' M') := by
  refine Triple.seq (jal_at (pc := 0x800051dc#64) (w := 0xdfdff0ef#32) (imm := 0x1ffdfc#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pb), (9, BitVec.ofNat 64 pa),
        (10, BitVec.ofNat 64 pb)])
      (hc.word (a := (0x800051dc#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [cL]) (by simp [keysG]) (by simp [Abi.keepR1, keysG])) ?_
  refine Triple.conseq (Clamp.correct 0x800051e0#64 (calleeAbi v sp pa pb) outp pb bdp cm M (by decide) hP)
    (fun c h => ?_) (fun c ⟨a', M', hat, hpost⟩ => ⟨a', M', hat.reshape ?_ ?_, hpost⟩)
  · have hpc : (0x800051dc#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x1ffdfc#21) = Clamp.entry := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [Sail.BitVec.addInt]
    · simp [Abi.keep, Abi.keepR1, calleeAbi, sKeepL]
  · simp [rL, Abi.keep, calleeAbi, sKeepL]
  · simp [Abi.keep, Abi.keepR1, calleeAbi, sKeepL]

end Tom.Machine.Fn.Div2
