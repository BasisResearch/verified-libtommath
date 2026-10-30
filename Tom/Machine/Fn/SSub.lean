import Tom.Machine.Seg.SSub
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
# `s_mp_sub` on the machine: the segments

`s_mp_sub(a, b, c)` at `0x80004564` in `c/tommath-arith.elf` (95
instructions), for `|a| ≥ |b|` (so `max = a->used`, `min = b->used`).
Join points: the loop-1 head `45c0` (digit differences of `a` and `b`);
`4608` after it (both arms of `blez b->used` meet here); the loop-2 head
`4628` (`a`'s digits minus the borrow); `4660` (the `olduse` test); the calls
of `memset` (`4674`) and `mp_clamp` (`467c`); the epilogue at `4680`. The
`mp_grow` branch (`c->alloc < a->used`) is excluded by the contract (D5).
-/


namespace Tom.Machine.Fn.SSub

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "ssub_ctx" : tactic => `(tactic|
  (facts_ctx
   have : sMpSubBase = 0x80004564 := rfl
   have : sMpSubCode.length = 95 := rfl))

/-! ## Register lists at the join points -/

def entryL (ra s0 : BitVec 64) (sp pa pb pc : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb),
   (12, BitVec.ofNat 64 pc)]

/-- At the loop-1 head, index `i`, borrow `u`. -/
def l1L (ra : BitVec 64) (sp pc cdp ou mn mx adp bdp i u : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 cdp),
   (12, BitVec.ofNat 64 ou), (14, BitVec.ofNat 64 adp), (29, BitVec.ofNat 64 mx), (30, BitVec.ofNat 64 mn),
   (28, BitVec.ofNat 64 (adp + 4 * mn)), (31, 268435455#64), (16, BitVec.ofNat 64 (cdp + 4 * i)),
   (11, BitVec.ofNat 64 (adp + 4 * i)), (17, BitVec.ofNat 64 (bdp + 4 * i)), (13, BitVec.ofNat 64 u)]

/-- At `4608`: `a0 = cdp + 4 min`, `a4 = adp + 4 min`, borrow `u`. -/
def j2L (ra : BitVec 64) (sp pc cdp ou mn mx adp u : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (29, BitVec.ofNat 64 mx),
   (30, BitVec.ofNat 64 mn), (13, BitVec.ofNat 64 u), (12, BitVec.ofNat 64 ou),
   (14, BitVec.ofNat 64 (adp + 4 * mn)), (10, BitVec.ofNat 64 (cdp + 4 * mn))]

/-- At the loop-2 head, index `i`. -/
def l2L (ra : BitVec 64) (sp pc cdp ou mn mx adp i u : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (29, BitVec.ofNat 64 mx),
   (30, BitVec.ofNat 64 mn), (12, BitVec.ofNat 64 ou), (10, BitVec.ofNat 64 (cdp + 4 * mn)),
   (16, BitVec.ofNat 64 (adp + 4 * mx)), (17, 268435455#64), (11, BitVec.ofNat 64 (cdp + 4 * i)),
   (14, BitVec.ofNat 64 (adp + 4 * i)), (13, BitVec.ofNat 64 u)]

/-- At `4660`: `a0 = cdp + 4 max`. -/
def j3L (ra : BitVec 64) (sp pc cdp ou mx : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (12, BitVec.ofNat 64 ou),
   (10, BitVec.ofNat 64 (cdp + 4 * mx))]

/-- At the `memset` call (`4674`): `memset(c->dp + used, 0, 4 (olduse - used))`. -/
def msL (ra : BitVec 64) (sp pc cdp ou mx : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc),
   (10, BitVec.ofNat 64 (cdp + 4 * mx)), (11, 0#64), (12, BitVec.ofNat 64 (4 * (ou - mx)))]

/-- At `4678` (after the `memset` call, or instead of it). -/
def j4L (sp pc : Nat) : GRegs := [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc)]

def frameLog (ra s0 : BitVec 64) (sp : Nat) : List WEntry := [(sp - 16, 8, s0), (sp - 8, 8, ra)]

/-! ## Facts the segments read -/

/-- The prologue: the `used`/`alloc` loads and the stack frame. -/
structure ProFacts (m : Mem) (sp pa pb pc ua ub al : Nat) : Prop where
  ra_ : Ram pa 24
  rb : Ram pb 24
  rc : Ram pc 24
  rs : Ram (sp - 48) 48
  sp_al : sp % 16 = 0
  sp_ge : 48 ≤ sp
  ua_v : bytesT4 m pa = BitVec.ofNat 32 ua
  ub_v : bytesT4 m pb = BitVec.ofNat 32 ub
  al_v : bytesT4 m (pc + 4) = BitVec.ofNat 32 al
  ua_lt : ua < 2 ^ 31
  ub_lt : ub < 2 ^ 31
  al_lt : al < 2 ^ 31
  s_b : sp ≤ pb ∨ pb + 24 ≤ sp - 48
  code_off : sp ≤ sMpSubBase ∨ sMpSubBase + 380 ≤ sp - 48

theorem ProFacts.sx {m : Mem} {sp pa pb pc ua ub al : Nat} (h : ProFacts m sp pa pb pc ua ub al) :
    BitVec.signExtend 64 (bytesT4 m pa) = BitVec.ofNat 64 ua ∧
      BitVec.signExtend 64 (bytesT4 m pb) = BitVec.ofNat 64 ub ∧
      BitVec.signExtend 64 (bytesT4 m (pc + 4)) = BitVec.ofNat 64 al :=
  ⟨by rw [h.ua_v, signExtend_ofNat32 _ h.ua_lt], by rw [h.ub_v, signExtend_ofNat32 _ h.ub_lt],
   by rw [h.al_v, signExtend_ofNat32 _ h.al_lt]⟩

/-- After the prologue: `c->used`, the `used` store, the digit pointers. -/
structure CFacts (m : Mem) (pa pc ou adp cdp : Nat) : Prop where
  ra_ : Ram pa 24
  rc : Ram pc 24
  pc_al : pc % 8 = 0
  ou_v : bytesT4 m pc = BitVec.ofNat 32 ou
  adp_v : bytesT8 m (pa + 16) = BitVec.ofNat 64 adp
  cdp_v : bytesT8 m (pc + 16) = BitVec.ofNat 64 cdp
  ou_lt : ou < 2 ^ 31
  c_a : pc + 4 ≤ pa + 16 ∨ pa + 24 ≤ pc
  code_off : pc + 4 ≤ sMpSubBase ∨ sMpSubBase + 380 ≤ pc

theorem CFacts.sx {m : Mem} {pa pc ou adp cdp : Nat} (h : CFacts m pa pc ou adp cdp) :
    BitVec.signExtend 64 (bytesT4 m pc) = BitVec.ofNat 64 ou := by
  rw [h.ou_v, signExtend_ofNat32 _ h.ou_lt]

/-- A digit read at index `i` of the array at `p`. -/
structure DRead (M : Mem) (p i x : Nat) : Prop where
  r : Ram (p + 4 * i) 4
  v : bytesT4 M (p + 4 * i) = BitVec.ofNat 32 x
  lt : x < 268435456

/-- A store into `c`'s digit `i`. -/
structure CStore (cdp i : Nat) : Prop where
  rc : Ram (cdp + 4 * i) 4
  al : cdp % 4 = 0
  code_off : cdp + 4 * i + 4 ≤ sMpSubBase ∨ sMpSubBase + 380 ≤ cdp + 4 * i

/-! ## The segments -/

/-- At `458c`, after the prologue (`c->alloc ≥ a->used`). -/
def pL (ra : BitVec 64) (sp pa pb pc ua ub : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (29, BitVec.ofNat 64 ua),
   (30, BitVec.ofNat 64 ub), (15, BitVec.ofNat 64 pa), (13, BitVec.ofNat 64 pb)]

/-- The prologue: the frame, `c->alloc ≥ a->used` (no `mp_grow`). -/
theorem p_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String)
    (sp pa pb pc ua ub al : Nat) (m : Mem)
    (hc : CodeAt m sMpSubBase sMpSubCode) (hf : ProFacts m sp pa pb pc ua ub al)
    (hal : ua ≤ al) :
    Triple (At 0x80004564#64 (entryL ra s0 sp pa pb pc) m v.keepR outp)
      (At 0x8000458c#64 (pL ra sp pa pb pc ua ub) (writeLog m (frameLog ra s0 sp)) v.keepR outp) := by
  ssub_ctx
  have ⟨hsa, hsb, hsl⟩ := hf.sx
  seg_step ssubP 0x8000458c#64 [rd4 m pa, rd4 m (pc + 4), rd4 m pb] [1, 2, 8, 10, 11, 12] abiKeysR
    [entryL, frameLog] [pL] [hsa, hsb, hsl] hc

/-- `b->used = 0`: `c->used := a->used`, skip loop 1. -/
theorem e0_step (ra : BitVec 64) (v : Abi) (outp : Array String)
    (sp pa pb pc ua ou adp cdp : Nat) (m : Mem)
    (hc : CodeAt m sMpSubBase sMpSubCode) (hf : CFacts m pa pc ou adp cdp) :
    Triple (At 0x8000458c#64 (pL ra sp pa pb pc ua 0) m v.keepR outp)
      (At 0x80004608#64 (j2L ra sp pc cdp ou 0 ua adp 0)
        (writeLog m [(pc, 4, BitVec.ofNat 64 ua)]) v.keepR outp) := by
  ssub_ctx
  have hso := hf.sx
  seg_step ssubE0 0x80004608#64 [rd4 m pc, rd8 m (pa + 16), rd8 m (pc + 16)]
    [1, 2, 8, 29, 30, 15, 13] abiKeysR [pL] [j2L] [hso, hf.adp_v, hf.cdp_v] hc

/-- `b`'s digit pointer, off the `used` store. -/
structure BFacts (m : Mem) (pb pc bdp : Nat) : Prop where
  rb : Ram pb 24
  bdp_v : bytesT8 m (pb + 16) = BitVec.ofNat 64 bdp
  c_b : pc + 4 ≤ pb + 16 ∨ pb + 24 ≤ pc

/-- `b->used ≥ 1`: `c->used := a->used`, enter loop 1. -/
theorem e1_step (ra : BitVec 64) (v : Abi) (outp : Array String)
    (sp pa pb pc ua ub ou adp bdp cdp : Nat) (m : Mem)
    (hc : CodeAt m sMpSubBase sMpSubCode) (hf : CFacts m pa pc ou adp cdp) (hb : BFacts m pb pc bdp)
    (hub : 1 ≤ ub) (hub' : ub < 2 ^ 31) :
    Triple (At 0x8000458c#64 (pL ra sp pa pb pc ua ub) m v.keepR outp)
      (At 0x800045c0#64 (l1L ra sp pc cdp ou ub ua adp bdp 0 0)
        (writeLog m [(pc, 4, BitVec.ofNat 64 ua)]) v.keepR outp) := by
  ssub_ctx
  have hso := hf.sx
  seg_step ssubE1 0x800045c0#64 [rd4 m pc, rd8 m (pa + 16), rd8 m (pc + 16), rd8 m (pb + 16)]
    [1, 2, 8, 29, 30, 15, 13] abiKeysR [pL] [l1L] [hso, hf.adp_v, hf.cdp_v, hb.bdp_v] hc

/-- Loop 1's back edge: `c->dp[i] := (x - y - u) mod 2^28`; the borrow is bit 31
of the 32-bit difference (`subBorrow_c`). -/
theorem l1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx adp bdp i u x y : Nat)
    (M : Mem) (hc : CodeAt M sMpSubBase sMpSubCode) (hx : DRead M adp i x) (hy : DRead M bdp i y)
    (hs : CStore cdp i) (hu : u ≤ 1) (hi : i + 1 < mn) (hmn : adp + 4 * mn ≤ 4294967296) :
    Triple (At 0x800045c0#64 (l1L ra sp pc cdp ou mn mx adp bdp i u) M v.keepR outp)
      (At 0x800045c0#64 (l1L ra sp pc cdp ou mn mx adp bdp (i + 1)
          ((x + 4294967296 - (y + u)) % 4294967296 / 2147483648))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64 ((x + 268435456 - y - u) % 268435456))]) v.keepR outp) := by
  ssub_ctx
  seg_step ssubL1 0x800045c0#64 [rd4 M (adp + 4 * i), rd4 M (bdp + 4 * i)]
    [1, 2, 8, 10, 12, 14, 29, 30, 28, 31, 16, 11, 17, 13] abiKeysR [l1L] [] [hx.v, hy.v] hc

/-- Loop 1's last iteration (`i + 1 = min`), falling out at `45ec`. -/
theorem l1e_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx adp bdp i u x y : Nat)
    (M : Mem) (hc : CodeAt M sMpSubBase sMpSubCode) (hx : DRead M adp i x) (hy : DRead M bdp i y)
    (hs : CStore cdp i) (hu : u ≤ 1) (hi : i + 1 = mn) (hmn : adp + 4 * mn ≤ 4294967296) :
    Triple (At 0x800045c0#64 (l1L ra sp pc cdp ou mn mx adp bdp i u) M v.keepR outp)
      (At 0x800045ec#64 (l1L ra sp pc cdp ou mn mx adp bdp (i + 1)
          ((x + 4294967296 - (y + u)) % 4294967296 / 2147483648))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64 ((x + 268435456 - y - u) % 268435456))]) v.keepR outp) := by
  ssub_ctx
  seg_step ssubL1e 0x800045ec#64 [rd4 M (adp + 4 * i), rd4 M (bdp + 4 * i)]
    [1, 2, 8, 10, 12, 14, 29, 30, 28, 31, 16, 11, 17, 13] abiKeysR [l1L] [] [hx.v, hy.v] hc

/-- After loop 1 (at `45ec`, index `min`): `a0 = cdp + 4 min`, `a4 = adp + 4 min`. -/
theorem l1t_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx adp bdp u : Nat)
    (M : Mem) (hc : CodeAt M sMpSubBase sMpSubCode) (hmn : 1 ≤ mn) (hmn' : mn < 2 ^ 31)
    (hcd : cdp + 4 * mn < 4294967296) (had : adp + 4 * mn < 4294967296) :
    Triple (At 0x800045ec#64 (l1L ra sp pc cdp ou mn mx adp bdp mn u) M v.keepR outp)
      (At 0x80004608#64 (j2L ra sp pc cdp ou mn mx adp u) (writeLog M []) v.keepR outp) := by
  ssub_ctx
  seg_step ssubL1t 0x80004608#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 10, 12, 14, 29, 30, 28, 31, 16, 11, 17, 13] abiKeysR [l1L] [j2L] [] hc

/-- `min = max`: no loop 2. -/
theorem b0_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx adp u : Nat)
    (M : Mem) (hc : CodeAt M sMpSubBase sMpSubCode) (he : mn = mx) (hmx : mx < 2 ^ 31) :
    Triple (At 0x80004608#64 (j2L ra sp pc cdp ou mn mx adp u) M v.keepR outp)
      (At 0x80004660#64 (j3L ra sp pc cdp ou mx) (writeLog M []) v.keepR outp) := by
  ssub_ctx
  subst he
  seg_step ssubB0 0x80004660#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 29, 30, 13, 12, 14, 10] abiKeysR [j2L] [j3L] [] hc

/-- `min < max`: enter loop 2 at index `min`. -/
theorem b2_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx adp u : Nat)
    (M : Mem) (hc : CodeAt M sMpSubBase sMpSubCode) (hlt : mn < mx) (hmx : mx < 2 ^ 31)
    (had : adp + 4 * mx < 4294967296) :
    Triple (At 0x80004608#64 (j2L ra sp pc cdp ou mn mx adp u) M v.keepR outp)
      (At 0x80004628#64 (l2L ra sp pc cdp ou mn mx adp mn u) (writeLog M []) v.keepR outp) := by
  ssub_ctx
  seg_step ssubB2 0x80004628#64 ([] : List (List (BitVec 8)))
    [1, 2, 8, 29, 30, 13, 12, 14, 10] abiKeysR [j2L] [l2L] [] hc

/-- Loop 2's back edge: `c->dp[i] := (x - u) mod 2^28`. -/
theorem l2_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx adp i u x : Nat)
    (M : Mem) (hc : CodeAt M sMpSubBase sMpSubCode) (hx : DRead M adp i x) (hs : CStore cdp i)
    (hu : u ≤ 1) (hi : i + 1 < mx) (had : adp + 4 * mx ≤ 4294967296) :
    Triple (At 0x80004628#64 (l2L ra sp pc cdp ou mn mx adp i u) M v.keepR outp)
      (At 0x80004628#64 (l2L ra sp pc cdp ou mn mx adp (i + 1)
          ((x + 4294967296 - u) % 4294967296 / 2147483648))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64 ((x + 268435456 - u) % 268435456))]) v.keepR outp) := by
  ssub_ctx
  seg_step ssubL2 0x80004628#64 [rd4 M (adp + 4 * i)] [1, 2, 8, 29, 30, 12, 10, 16, 17, 11, 14, 13] abiKeysR [l2L] [] [hx.v] hc

/-- Loop 2's last iteration (`i + 1 = max`), falling out at `4648`. -/
theorem l2e_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx adp i u x : Nat)
    (M : Mem) (hc : CodeAt M sMpSubBase sMpSubCode) (hx : DRead M adp i x) (hs : CStore cdp i)
    (hu : u ≤ 1) (hi : i + 1 = mx) (had : adp + 4 * mx ≤ 4294967296) :
    Triple (At 0x80004628#64 (l2L ra sp pc cdp ou mn mx adp i u) M v.keepR outp)
      (At 0x80004648#64 (l2L ra sp pc cdp ou mn mx adp (i + 1)
          ((x + 4294967296 - u) % 4294967296 / 2147483648))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64 ((x + 268435456 - u) % 268435456))]) v.keepR outp) := by
  ssub_ctx
  seg_step ssubL2e 0x80004648#64 [rd4 M (adp + 4 * i)] [1, 2, 8, 29, 30, 12, 10, 16, 17, 11, 14, 13] abiKeysR [l2L] [] [hx.v] hc

/-- After loop 2: `a0 = cdp + 4 max`. -/
theorem l2t_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx adp u : Nat)
    (M : Mem) (hc : CodeAt M sMpSubBase sMpSubCode) (hlt : mn < mx) (hmx : mx < 2 ^ 31)
    (hcd : cdp + 4 * mx < 4294967296) :
    Triple (At 0x80004648#64 (l2L ra sp pc cdp ou mn mx adp mx u) M v.keepR outp)
      (At 0x80004660#64 (j3L ra sp pc cdp ou mx) (writeLog M []) v.keepR outp) := by
  ssub_ctx
  seg_step ssubL2t 0x80004660#64 ([] : List (List (BitVec 8))) [1, 2, 8, 29, 30, 12, 10, 16, 17, 11, 14, 13] abiKeysR [l2L] [j3L] [] hc

/-- The `olduse` test's facts: `c->used = max`. -/
structure TailFacts (M : Mem) (pc mx ou : Nat) : Prop where
  rc : Ram pc 24
  pc_al : pc % 8 = 0
  used_v : bytesT4 M pc = BitVec.ofNat 32 mx
  mx_lt : mx < 2 ^ 31
  ou_lt : ou < 2 ^ 31

theorem TailFacts.sx {M : Mem} {pc mx ou : Nat} (h : TailFacts M pc mx ou) :
    BitVec.signExtend 64 (bytesT4 M pc) = BitVec.ofNat 64 mx := by
  rw [h.used_v, signExtend_ofNat32 _ h.mx_lt]

/-- `olduse ≤ max`: no `memset`. -/
theorem c0_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mx : Nat)
    (M : Mem) (hc : CodeAt M sMpSubBase sMpSubCode) (ht : TailFacts M pc mx ou) (hou : ou ≤ mx) :
    Triple (At 0x80004660#64 (j3L ra sp pc cdp ou mx) M v.keepR outp)
      (At 0x80004678#64 (j4L sp pc) (writeLog M []) v.keepR outp) := by
  ssub_ctx
  have hus := ht.sx
  seg_step ssubC0 0x80004678#64 [rd4 M pc] [1, 2, 8, 12, 10] abiKeysR [j3L] [j4L] [hus] hc

/-- `olduse > max`: set up `memset(c->dp + max, 0, 4 (olduse - max))`. -/
theorem c1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mx : Nat)
    (M : Mem) (hc : CodeAt M sMpSubBase sMpSubCode) (ht : TailFacts M pc mx ou) (hou : mx < ou) :
    Triple (At 0x80004660#64 (j3L ra sp pc cdp ou mx) M v.keepR outp)
      (At 0x80004674#64 (msL ra sp pc cdp ou mx) (writeLog M []) v.keepR outp) := by
  ssub_ctx
  have hus := ht.sx
  seg_step ssubC1 0x80004674#64 [rd4 M pc] [1, 2, 8, 12, 10] abiKeysR [j3L] [msL] [hus] hc

/-- `a0 := c` before the `mp_clamp` call (`4678`). -/
theorem d_step (v : Abi) (outp : Array String) (sp pc : Nat) (M : Mem)
    (hc : CodeAt M sMpSubBase sMpSubCode) :
    Triple (At 0x80004678#64 (j4L sp pc) M v.keepR outp)
      (At 0x8000467c#64 [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 pc)]
        (writeLog M []) v.keepR outp) := by
  ssub_ctx
  seg_step ssubD 0x8000467c#64 ([] : List (List (BitVec 8))) [2, 8] abiKeysR [j4L] [] [] hc

/-- The stack frame at the epilogue. -/
structure FrameFacts (M : Mem) (ra s0 : BitVec 64) (sp : Nat) : Prop where
  rs : Ram (sp - 48) 48
  sp_al : sp % 16 = 0
  sp_ge : 48 ≤ sp
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  ra_al : ra.toNat % 4 = 0

/-- The epilogue (`4680`): restore `ra`, `s0`, `sp`; return `MP_OKAY`. -/
theorem r_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M sMpSubBase sMpSubCode) (hf : FrameFacts M ra s0 sp) :
    Triple (At 0x80004680#64 [(2, BitVec.ofNat 64 (sp - 48))] M v.keepR outp)
      (At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] (writeLog M []) v.keepR outp) := by
  ssub_ctx
  have hra := hf.ra_al
  have h1 : bytesT8 M (sp - 48 + 40) = ra := by rw [show sp - 48 + 40 = sp - 8 by omega]; exact hf.ra_v
  have h2 : bytesT8 M (sp - 48 + 32) = s0 := by rw [show sp - 48 + 32 = sp - 16 by omega]; exact hf.s0_v
  seg_step ssubR ra [rd8 M (sp - 48 + 40), rd8 M (sp - 48 + 32)] [2] abiKeysR [] [] [h1, h2] hc

end Tom.Machine.Fn.SSub
