import Tom.Machine.Seg.SAdd
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Arr
import Tom.Machine.Kit.Loop
import Tom.Spec.Indexed
import Tom.Machine.Kit.Jal
import Tom.Machine.Fn.Memset
import Tom.Machine.Fn.Clamp

/-!
# `s_mp_add` on the machine

`s_mp_add(a, b, c)` at `0x8000219c` in `c/tommath-arith.elf` (108
instructions). Join points: `21d4` after the prologue (`t5 = min`,
`t3 = max`, `t6 = x`, the operand with more digits); the loop-1 head `2218`
(digit sums of `a` and `b`); `225c` after it; the loop-2 head `228c` (the
digits of `x` plus the carry); `22c4` (store the carry); the calls of
`memset` (`22e0`) and `mp_clamp` (`22e8`); the epilogue at `22ec`. The
`mp_grow` branch (`max ≥ c->alloc`) is excluded by the contract (D5).
-/


namespace Tom.Machine.Fn.SAdd

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

/-- The context every segment lemma of this file needs: the facts of the
structure hypotheses (`facts_ctx`) and the code's place. -/
macro "sadd_ctx" : tactic => `(tactic|
  (facts_ctx
   have : sMpAddBase = 0x8000219c := rfl
   have : sMpAddCode.length = 108 := rfl))

/-! ## Register lists at the join points -/

/-- Registers at entry. -/
def entryL (ra s0 : BitVec 64) (sp pa pb pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb),
   (12, BitVec.ofNat 64 pc)]

/-- At `21d4`: `min`, `max`, `x`. -/
def j1L (ra : BitVec 64) (sp pa pb pc mn mx xp : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (14, BitVec.ofNat 64 pa),
   (15, BitVec.ofNat 64 pb), (28, BitVec.ofNat 64 mx), (30, BitVec.ofNat 64 mn), (31, BitVec.ofNat 64 xp)]

/-- At the loop-1 head, index `i`, carry `u`. -/
def l1L (ra : BitVec 64) (sp pc cdp ou mn mx xp adp bdp i u : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 cdp),
   (12, BitVec.ofNat 64 ou), (28, BitVec.ofNat 64 mx), (30, BitVec.ofNat 64 mn), (31, BitVec.ofNat 64 xp),
   (11, BitVec.ofNat 64 (cdp + 4 * i)), (13, BitVec.ofNat 64 u), (14, BitVec.ofNat 64 (adp + 4 * i)),
   (16, BitVec.ofNat 64 (bdp + 4 * i)), (6, BitVec.ofNat 64 (adp + 4 * mn)), (29, 268435455#64)]

/-- At `225c`: `t1 = i`, `a0 = cdp + 4i`, carry `u`. -/
def j2L (ra : BitVec 64) (sp pc cdp ou mn mx xp i u : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (6, BitVec.ofNat 64 i),
   (10, BitVec.ofNat 64 (cdp + 4 * i)), (13, BitVec.ofNat 64 u), (12, BitVec.ofNat 64 ou),
   (28, BitVec.ofNat 64 mx), (30, BitVec.ofNat 64 mn), (31, BitVec.ofNat 64 xp)]

/-- At the loop-2 head, index `i`, carry `u` (`x`'s digits at `xdp`). -/
def l2L (ra : BitVec 64) (sp pc cdp ou mn mx xdp i u : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (12, BitVec.ofNat 64 ou),
   (28, BitVec.ofNat 64 mx), (30, BitVec.ofNat 64 mn), (6, BitVec.ofNat 64 mn),
   (10, BitVec.ofNat 64 (cdp + 4 * mn)), (14, BitVec.ofNat 64 (cdp + 4 * i)),
   (11, BitVec.ofNat 64 (xdp + 4 * i)), (13, BitVec.ofNat 64 u), (16, BitVec.ofNat 64 (cdp + 4 * mx)),
   (17, 268435455#64)]

/-- At `22c4`: `a0 = cdp + 4 max`, carry `u`. -/
def j3L (ra : BitVec 64) (sp pc cdp ou mx u : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 (cdp + 4 * mx)),
   (13, BitVec.ofNat 64 u), (12, BitVec.ofNat 64 ou)]

/-- At the `memset` call (`22e0`). -/
def msL (ra : BitVec 64) (sp pc cdp ou mx : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc),
   (10, BitVec.ofNat 64 (cdp + 4 * (mx + 1))), (11, 0#64), (12, BitVec.ofNat 64 (4 * (ou - (mx + 1))))]

/-- At `22e4` (after the `memset` call, or instead of it); `ra` is in the frame. -/
def j4L (sp pc : Nat) : GRegs := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc)]

/-- The frame stores of the prologue. -/
def frameLog (ra s0 : BitVec 64) (sp : Nat) : List WEntry := [(sp - 16, 8, s0), (sp - 8, 8, ra)]

/-! ## Facts the segments read -/

/-- The prologue: the `used` loads and the stack frame. -/
structure ProFacts (m : Mem) (sp pa pb ua ub : Nat) : Prop where
  ra_ : Ram pa 24
  rb : Ram pb 24
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  ua_v : bytesT4 m pa = BitVec.ofNat 32 ua
  ub_v : bytesT4 m pb = BitVec.ofNat 32 ub
  ua_lt : ua < 2 ^ 31
  ub_lt : ub < 2 ^ 31
  code_off : sp ≤ sMpAddBase ∨ sMpAddBase + 432 ≤ sp - 64

theorem ProFacts.sx {m : Mem} {sp pa pb ua ub : Nat} (h : ProFacts m sp pa pb ua ub) :
    BitVec.signExtend 64 (bytesT4 m pa) = BitVec.ofNat 64 ua ∧
      BitVec.signExtend 64 (bytesT4 m pb) = BitVec.ofNat 64 ub :=
  ⟨by rw [h.ua_v, signExtend_ofNat32 _ h.ua_lt], by rw [h.ub_v, signExtend_ofNat32 _ h.ub_lt]⟩

/-- `c`'s struct. -/
structure CFacts (M : Mem) (pc al ou cdp : Nat) : Prop where
  rc : Ram pc 24
  pc_al : pc % 8 = 0
  al_v : bytesT4 M (pc + 4) = BitVec.ofNat 32 al
  ou_v : bytesT4 M pc = BitVec.ofNat 32 ou
  dp_v : bytesT8 M (pc + 16) = BitVec.ofNat 64 cdp
  al_lt : al < 2 ^ 31
  ou_lt : ou < 2 ^ 31
  code_off : pc + 24 ≤ sMpAddBase ∨ sMpAddBase + 432 ≤ pc

theorem CFacts.sx {M : Mem} {pc al ou cdp : Nat} (h : CFacts M pc al ou cdp) :
    BitVec.signExtend 64 (bytesT4 M (pc + 4)) = BitVec.ofNat 64 al ∧
      BitVec.signExtend 64 (bytesT4 M pc) = BitVec.ofNat 64 ou :=
  ⟨by rw [h.al_v, signExtend_ofNat32 _ h.al_lt], by rw [h.ou_v, signExtend_ofNat32 _ h.ou_lt]⟩

/-- The operands' digit pointers, their structs off `c`'s. -/
structure OpFacts (M : Mem) (pa pb pc adp bdp mn : Nat) : Prop where
  ra_ : Ram pa 24
  rb : Ram pb 24
  adp_v : bytesT8 M (pa + 16) = BitVec.ofNat 64 adp
  bdp_v : bytesT8 M (pb + 16) = BitVec.ofNat 64 bdp
  ra_d : Ram adp (4 * mn)
  rb_d : Ram bdp (4 * mn)
  ac : pa + 24 ≤ pc ∨ pc + 24 ≤ pa
  bc : pb + 24 ≤ pc ∨ pc + 24 ≤ pb

/-- A digit read at index `i` of the arrays at `p` (and `q`). -/
structure DRead (M : Mem) (p i x : Nat) : Prop where
  r : Ram (p + 4 * i) 4
  v : bytesT4 M (p + 4 * i) = BitVec.ofNat 32 x
  lt : x < 268435456

/-- A store into `c`'s digit `i`. -/
structure CStore (cdp i : Nat) : Prop where
  rc : Ram (cdp + 4 * i) 4
  al : cdp % 4 = 0
  code_off : cdp + 4 * i + 4 ≤ sMpAddBase ∨ sMpAddBase + 432 ≤ cdp + 4 * i

/-! ## The segments -/

/-- `b->used ≥ a->used`: no swap, `min = a->used`, `x = b`. -/
theorem e0_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc ua ub : Nat) (m : Mem)
    (hc : CodeAt m sMpAddBase sMpAddCode) (hf : ProFacts m sp pa pb ua ub) (hge : ua ≤ ub) :
    Triple (At 0x8000219c#64 (entryL ra s0 sp pa pb pc) m v.keepR outp)
      (At 0x800021d4#64 (j1L ra sp pa pb pc ua ub pb) (writeLog m (frameLog ra s0 sp)) v.keepR outp) := by
  sadd_ctx
  have ⟨hsa, hsb⟩ := hf.sx
  seg_step saddE0 0x800021d4#64 [rd4 m pa, rd4 m pb] [1, 2, 8, 10, 11, 12] abiKeysR
    [entryL, frameLog] [j1L] [hsa, hsb] hc

/-- `b->used < a->used`: swap, `min = b->used`, `x = a`. -/
theorem e1_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc ua ub : Nat) (m : Mem)
    (hc : CodeAt m sMpAddBase sMpAddCode) (hf : ProFacts m sp pa pb ua ub) (hlt : ub < ua) :
    Triple (At 0x8000219c#64 (entryL ra s0 sp pa pb pc) m v.keepR outp)
      (At 0x800021d4#64 (j1L ra sp pa pb pc ub ua pa) (writeLog m (frameLog ra s0 sp)) v.keepR outp) := by
  sadd_ctx
  have ⟨hsa, hsb⟩ := hf.sx
  seg_step saddE1 0x800021d4#64 [rd4 m pa, rd4 m pb] [1, 2, 8, 10, 11, 12] abiKeysR
    [entryL, frameLog] [j1L] [hsa, hsb] hc

/-- At `21e8`, after `c->used := max + 1` (`a2 = olduse`). -/
def jaL (ra : BitVec 64) (sp pa pb pc mn mx xp ou : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (14, BitVec.ofNat 64 pa),
   (15, BitVec.ofNat 64 pb), (28, BitVec.ofNat 64 mx), (30, BitVec.ofNat 64 mn), (31, BitVec.ofNat 64 xp),
   (12, BitVec.ofNat 64 ou)]

/-- `c` has room (`max < c->alloc`, so no `mp_grow`): `c->used := max + 1`. -/
theorem a_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc xp mn mx al ou cdp : Nat)
    (M : Mem) (hc : CodeAt M sMpAddBase sMpAddCode) (hf : CFacts M pc al ou cdp) (hmx : mx < al) :
    Triple (At 0x800021d4#64 (j1L ra sp pa pb pc mn mx xp) M v.keepR outp)
      (At 0x800021e8#64 (jaL ra sp pa pb pc mn mx xp ou)
        (writeLog M [(pc, 4, BitVec.ofNat 64 (mx + 1))]) v.keepR outp) := by
  sadd_ctx
  have ⟨hal, hou⟩ := hf.sx
  seg_step saddA 0x800021e8#64 [rd4 M (pc + 4), rd4 M pc]
    [1, 2, 8, 14, 15, 28, 30, 31] abiKeysR [j1L] [jaL] [hal, hou] hc

/-- `min = 0`: skip loop 1. -/
theorem a0b_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc xp mx ou cdp : Nat)
    (M : Mem) (hc : CodeAt M sMpAddBase sMpAddCode) (hp : Ram pc 24)
    (hdp : bytesT8 M (pc + 16) = BitVec.ofNat 64 cdp) :
    Triple (At 0x800021e8#64 (jaL ra sp pa pb pc 0 mx xp ou) M v.keepR outp)
      (At 0x8000225c#64 (j2L ra sp pc cdp ou 0 mx xp 0 0) (writeLog M []) v.keepR outp) := by
  sadd_ctx
  seg_step saddA0b 0x8000225c#64 [rd8 M (pc + 16)]
    [1, 2, 8, 14, 15, 28, 30, 31, 12] abiKeysR [jaL] [j2L] [hdp] hc

/-- `min ≥ 1`: load the digit pointers, enter loop 1. -/
theorem a1b_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb pc xp mn mx ou cdp adp bdp : Nat)
    (M : Mem) (hc : CodeAt M sMpAddBase sMpAddCode) (hp : Ram pc 24)
    (hdp : bytesT8 M (pc + 16) = BitVec.ofNat 64 cdp) (ho : OpFacts M pa pb pc adp bdp mn)
    (hmn : 1 ≤ mn) (hmn' : mn < 2 ^ 31) :
    Triple (At 0x800021e8#64 (jaL ra sp pa pb pc mn mx xp ou) M v.keepR outp)
      (At 0x80002218#64 (l1L ra sp pc cdp ou mn mx xp adp bdp 0 0) (writeLog M []) v.keepR outp) := by
  sadd_ctx
  seg_step saddA1b 0x80002218#64 [rd8 M (pc + 16), rd8 M (pa + 16), rd8 M (pb + 16)]
    [1, 2, 8, 14, 15, 28, 30, 31, 12] abiKeysR [jaL] [l1L] [hdp, ho.adp_v, ho.bdp_v] hc

/-- Loop 1's back edge: `c->dp[i] := (x + y + u) mod 2^28`, carry `(x + y + u) / 2^28`. -/
theorem l1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx xp adp bdp i u x y : Nat)
    (M : Mem) (hc : CodeAt M sMpAddBase sMpAddCode) (hx : DRead M adp i x) (hy : DRead M bdp i y)
    (hs : CStore cdp i) (hu : u ≤ 1) (hi : i + 1 < mn) (hmn : adp + 4 * mn ≤ 4294967296) :
    Triple (At 0x80002218#64 (l1L ra sp pc cdp ou mn mx xp adp bdp i u) M v.keepR outp)
      (At 0x80002218#64 (l1L ra sp pc cdp ou mn mx xp adp bdp (i + 1) ((x + y + u) / 268435456))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64 ((x + y + u) % 268435456))]) v.keepR outp) := by
  sadd_ctx
  seg_step saddL1 0x80002218#64 [rd4 M (adp + 4 * i), rd4 M (bdp + 4 * i)]
    [1, 2, 8, 10, 12, 28, 30, 31, 11, 13, 14, 16, 6, 29] abiKeysR [l1L] [] [hx.v, hy.v] hc

/-- Loop 1's last iteration (`i + 1 = min`), falling out at `2244`. -/
theorem l1e_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx xp adp bdp i u x y : Nat)
    (M : Mem) (hc : CodeAt M sMpAddBase sMpAddCode) (hx : DRead M adp i x) (hy : DRead M bdp i y)
    (hs : CStore cdp i) (hu : u ≤ 1) (hi : i + 1 = mn) (hmn : adp + 4 * mn ≤ 4294967296) :
    Triple (At 0x80002218#64 (l1L ra sp pc cdp ou mn mx xp adp bdp i u) M v.keepR outp)
      (At 0x80002244#64 (l1L ra sp pc cdp ou mn mx xp adp bdp (i + 1) ((x + y + u) / 268435456))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64 ((x + y + u) % 268435456))]) v.keepR outp) := by
  sadd_ctx
  seg_step saddL1e 0x80002244#64 [rd4 M (adp + 4 * i), rd4 M (bdp + 4 * i)]
    [1, 2, 8, 10, 12, 28, 30, 31, 11, 13, 14, 16, 6, 29] abiKeysR [l1L] [] [hx.v, hy.v] hc

/-- After loop 1 (at `2244`, index `min`): `a0 = cdp + 4 min`, `t1 = min`. -/
theorem l1t_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx xp adp bdp u : Nat)
    (M : Mem) (hc : CodeAt M sMpAddBase sMpAddCode) (hmn : 1 ≤ mn) (hmn' : mn < 2 ^ 31)
    (hcd : cdp + 4 * mn < 4294967296) :
    Triple (At 0x80002244#64 (l1L ra sp pc cdp ou mn mx xp adp bdp mn u) M v.keepR outp)
      (At 0x8000225c#64 (j2L ra sp pc cdp ou mn mx xp mn u) (writeLog M []) v.keepR outp) := by
  sadd_ctx
  seg_step saddL1t 0x8000225c#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 10, 12, 28, 30, 31, 11, 13, 14, 16, 6, 29] abiKeysR [l1L] [j2L] [] hc

/-- `min = max`: no loop 2. -/
theorem b0_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx xp u : Nat)
    (M : Mem) (hc : CodeAt M sMpAddBase sMpAddCode) (he : mn = mx) (hmx : mx < 2 ^ 31)
    (hcd : cdp + 4 * mx < 4294967296) :
    Triple (At 0x8000225c#64 (j2L ra sp pc cdp ou mn mx xp mn u) M v.keepR outp)
      (At 0x800022c4#64 (j3L ra sp pc cdp ou mx u) (writeLog M []) v.keepR outp) := by
  sadd_ctx
  subst he
  seg_step saddB0 0x800022c4#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 6, 10, 13, 12, 28, 30, 31] abiKeysR [j2L] [j3L] [] hc

/-- `x`'s digit pointer. -/
structure XFacts (M : Mem) (xp xdp mx : Nat) : Prop where
  rx : Ram xp 24
  xdp_v : bytesT8 M (xp + 16) = BitVec.ofNat 64 xdp
  rx_d : Ram xdp (4 * mx)

/-- `min < max`: load `x->dp`, enter loop 2 at index `min`. -/
theorem b2_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx xp xdp u : Nat)
    (M : Mem) (hc : CodeAt M sMpAddBase sMpAddCode) (hx : XFacts M xp xdp mx) (hlt : mn < mx)
    (hmx : mx < 2 ^ 31) (hcd : cdp + 4 * mx < 4294967296) :
    Triple (At 0x8000225c#64 (j2L ra sp pc cdp ou mn mx xp mn u) M v.keepR outp)
      (At 0x8000228c#64 (l2L ra sp pc cdp ou mn mx xdp mn u) (writeLog M []) v.keepR outp) := by
  sadd_ctx
  seg_step saddB2 0x8000228c#64 [rd8 M (xp + 16)]
    [1, 2, 8, 6, 10, 13, 12, 28, 30, 31] abiKeysR [j2L] [l2L] [hx.xdp_v] hc

/-- Loop 2's back edge: `c->dp[i] := (d + u) mod 2^28`, carry `(d + u) / 2^28`. -/
theorem l2_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx xdp i u d : Nat)
    (M : Mem) (hc : CodeAt M sMpAddBase sMpAddCode) (hd : DRead M xdp i d) (hs : CStore cdp i)
    (hu : u ≤ 1) (hi : i + 1 < mx) (hcd : cdp + 4 * mx < 4294967296) :
    Triple (At 0x8000228c#64 (l2L ra sp pc cdp ou mn mx xdp i u) M v.keepR outp)
      (At 0x8000228c#64 (l2L ra sp pc cdp ou mn mx xdp (i + 1) ((d + u) / 268435456))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64 ((d + u) % 268435456))]) v.keepR outp) := by
  sadd_ctx
  seg_step saddL2 0x8000228c#64 [rd4 M (xdp + 4 * i)]
    [1, 2, 8, 12, 28, 30, 6, 10, 14, 11, 13, 16, 17] abiKeysR [l2L] [] [hd.v] hc

/-- Loop 2's last iteration (`i + 1 = max`), falling out at `22ac`. -/
theorem l2e_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx xdp i u d : Nat)
    (M : Mem) (hc : CodeAt M sMpAddBase sMpAddCode) (hd : DRead M xdp i d) (hs : CStore cdp i)
    (hu : u ≤ 1) (hi : i + 1 = mx) (hcd : cdp + 4 * mx < 4294967296) :
    Triple (At 0x8000228c#64 (l2L ra sp pc cdp ou mn mx xdp i u) M v.keepR outp)
      (At 0x800022ac#64 (l2L ra sp pc cdp ou mn mx xdp (i + 1) ((d + u) / 268435456))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64 ((d + u) % 268435456))]) v.keepR outp) := by
  sadd_ctx
  seg_step saddL2e 0x800022ac#64 [rd4 M (xdp + 4 * i)]
    [1, 2, 8, 12, 28, 30, 6, 10, 14, 11, 13, 16, 17] abiKeysR [l2L] [] [hd.v] hc

/-- After loop 2: `a0 = cdp + 4 max`. -/
theorem l2t_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx xdp u : Nat)
    (M : Mem) (hc : CodeAt M sMpAddBase sMpAddCode) (hlt : mn < mx) (hmx : mx < 2 ^ 31)
    (hcd : cdp + 4 * mx < 4294967296) :
    Triple (At 0x800022ac#64 (l2L ra sp pc cdp ou mn mx xdp mx u) M v.keepR outp)
      (At 0x800022c4#64 (j3L ra sp pc cdp ou mx u) (writeLog M []) v.keepR outp) := by
  sadd_ctx
  seg_step saddL2t 0x800022c4#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 12, 28, 30, 6, 10, 14, 11, 13, 16, 17] abiKeysR [l2L] [j3L] [] hc

/-- The facts of the carry store and the `olduse` test. -/
structure TailFacts (M : Mem) (pc cdp mx : Nat) : Prop where
  rc : Ram pc 24
  pc_al : pc % 8 = 0
  used_v : bytesT4 M pc = BitVec.ofNat 32 (mx + 1)
  st : CStore cdp mx
  disj : pc + 24 ≤ cdp + 4 * mx ∨ cdp + 4 * mx + 4 ≤ pc
  mx_lt : mx + 1 < 2 ^ 31

theorem TailFacts.sx {M : Mem} {pc cdp mx : Nat} (h : TailFacts M pc cdp mx) :
    BitVec.signExtend 64 (bytesT4 M pc) = BitVec.ofNat 64 (mx + 1) := by
  rw [h.used_v, signExtend_ofNat32 _ h.mx_lt]

/-- Store the carry; `olduse ≤ max + 1`: no `memset`. -/
theorem c0_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mx u : Nat)
    (M : Mem) (hc : CodeAt M sMpAddBase sMpAddCode) (ht : TailFacts M pc cdp mx) (hu : u ≤ 1)
    (hou : ou ≤ mx + 1) :
    Triple (At 0x800022c4#64 (j3L ra sp pc cdp ou mx u) M v.keepR outp)
      (At 0x800022e4#64 (j4L sp pc) (writeLog M [(cdp + 4 * mx, 4, BitVec.ofNat 64 u)]) v.keepR outp) := by
  sadd_ctx
  have := ht.st.rc; have := ht.st.al; have := ht.st.code_off
  have := ram_bounds ht.st.rc
  have hus := ht.sx
  seg_step saddC0 0x800022e4#64 [rd4 M pc] [1, 2, 8, 10, 13, 12] abiKeysR [j3L] [j4L] [hus] hc

/-- Store the carry; `olduse > max + 1`: set up `memset(c->dp + max + 1, 0, …)`. -/
theorem c1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mx u : Nat)
    (M : Mem) (hc : CodeAt M sMpAddBase sMpAddCode) (ht : TailFacts M pc cdp mx) (hu : u ≤ 1)
    (hou : mx + 1 < ou) (hou' : ou < 2 ^ 31) :
    Triple (At 0x800022c4#64 (j3L ra sp pc cdp ou mx u) M v.keepR outp)
      (At 0x800022e0#64 (msL ra sp pc cdp ou mx) (writeLog M [(cdp + 4 * mx, 4, BitVec.ofNat 64 u)])
        v.keepR outp) := by
  sadd_ctx
  have := ht.st.rc; have := ht.st.al; have := ht.st.code_off
  have := ram_bounds ht.st.rc
  have hus := ht.sx
  seg_step saddC1 0x800022e0#64 [rd4 M pc] [1, 2, 8, 10, 13, 12] abiKeysR [j3L] [msL] [hus] hc

/-- `a0 := c` before the `mp_clamp` call (`22e4`). -/
theorem d_step (v : Abi) (outp : Array String) (sp pc : Nat) (M : Mem)
    (hc : CodeAt M sMpAddBase sMpAddCode) :
    Triple (At 0x800022e4#64 (j4L sp pc) M v.keepR outp)
      (At 0x800022e8#64 [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pc)]
        (writeLog M []) v.keepR outp) := by
  sadd_ctx
  seg_step saddD 0x800022e8#64 ([] : List (List (BitVec 8))) [2, 8] abiKeysR [j4L] [] [] hc

/-- The stack frame at the epilogue: the saved `ra` and `s0`. -/
structure FrameFacts (M : Mem) (ra s0 : BitVec 64) (sp : Nat) : Prop where
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  ra_al : ra.toNat % 4 = 0

/-- The epilogue (`22ec`): restore `ra`, `s0`, `sp`; return `MP_OKAY`. -/
theorem r_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M sMpAddBase sMpAddCode) (hf : FrameFacts M ra s0 sp) :
    Triple (At 0x800022ec#64 [(2, BitVec.ofNat 64 (sp - 64))] M v.keepR outp)
      (At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] (writeLog M []) v.keepR outp) := by
  sadd_ctx
  have hra := hf.ra_al
  have h1 : bytesT8 M (sp - 64 + 56) = ra := by rw [show sp - 64 + 56 = sp - 8 by omega]; exact hf.ra_v
  have h2 : bytesT8 M (sp - 64 + 48) = s0 := by rw [show sp - 64 + 48 = sp - 16 by omega]; exact hf.s0_v
  seg_step saddR ra [rd8 M (sp - 64 + 56), rd8 M (sp - 64 + 48)] [2] abiKeysR [] [] [h1, h2] hc

/-! ## The calls -/

/-- The callee-saved registers `memset`/`mp_clamp` see: ours, with this
frame's `sp` and `s0 = c`. -/
def calleeAbi (v : Abi) (sp pc : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 64), s0 := BitVec.ofNat 64 pc }

/-- `memset(c->dp + max + 1, 0, 4 (olduse - max - 1))` at `22e0`, back at `22e4`. -/
theorem memset_call (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mx : Nat) (M : Mem)
    (hc : CodeAt M sMpAddBase sMpAddCode)
    (hP : Memset.Pre M (cdp + 4 * (mx + 1)) 0 (4 * (ou - (mx + 1)))) :
    Triple (At 0x800022e0#64 (msL ra sp pc cdp ou mx) M v.keepR outp)
      (fun c => ∃ M', At 0x800022e4#64 (j4L sp pc) M' v.keepR outp c ∧
        Memset.Post M (cdp + 4 * (mx + 1)) (4 * (ou - (mx + 1))) 0#8 M') := by
  refine Triple.seq (jal_at (pc := 0x800022e0#64) (w := 0x0c4070ef#32) (imm := 0x070c4#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc),
        (10, BitVec.ofNat 64 (cdp + 4 * (mx + 1))), (11, 0#64), (12, BitVec.ofNat 64 (4 * (ou - (mx + 1))))])
      (hc.word (a := (0x800022e0#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [msL]) (by simp [keysG]) (by simp [Abi.keepR, sKeepL, keysG])) ?_
  refine Triple.conseq (Memset.correct_zero 0x800022e4#64 (calleeAbi v sp pc) outp M _ _ (by decide) hP)
    (fun c h => ?_) (fun c ⟨M', hat, hpost⟩ => ⟨M', hat.reshape ?_ ?_, hpost⟩)
  · have hpc : (0x800022e0#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x070c4#21) = Memset.entry := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [Memset.entryL, Sail.BitVec.addInt]
    · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]
  · simp [j4L, Abi.keep, calleeAbi]
  · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]

/-- `mp_clamp(c)` at `22e8`, back at `22ec`. -/
theorem clamp_call (v : Abi) (outp : Array String) (sp pc cdp : Nat) (cm : MpInt) (M : Mem)
    (hc : CodeAt M sMpAddBase sMpAddCode) (hP : Clamp.Pre M pc cdp cm) :
    Triple (At 0x800022e8#64 [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc),
        (10, BitVec.ofNat 64 pc)] M v.keepR outp)
      (fun c => ∃ a' M', At 0x800022ec#64 [(2, BitVec.ofNat 64 (sp - 64))] M' v.keepR outp c ∧
        Clamp.Post M pc cdp cm a' M') := by
  refine Triple.seq (jal_at (pc := 0x800022e8#64) (w := 0x4f1020ef#32) (imm := 0x02cf0#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pc)])
      (hc.word (a := (0x800022e8#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp) (by simp [keysG]) (by simp [Abi.keepR, sKeepL, keysG])) ?_
  refine Triple.conseq (Clamp.correct 0x800022ec#64 (calleeAbi v sp pc) outp pc cdp cm M (by decide) hP)
    (fun c h => ?_) (fun c ⟨a', M', hat, hpost⟩ => ⟨a', M', hat.reshape ?_ ?_, hpost⟩)
  · have hpc : (0x800022e8#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x02cf0#21) = Clamp.entry := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [Sail.BitVec.addInt]
    · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]
  · simp [Abi.keep, calleeAbi]
  · simp [Abi.keep, Abi.keepR, calleeAbi, sKeepL]

end Tom.Machine.Fn.SAdd
