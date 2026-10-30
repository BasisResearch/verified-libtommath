import Tom.Machine.Seg.MpRshd
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.AutoEq
import Tom.Machine.Fn.MpZero
import Vsa.Sim.TripleCat

/-!
# `mp_rshd` on the machine: the segments

`mp_rshd(a, b)` at `0x80001e1c` (37 instructions). `b ≤ 0`: return
(`mrshdN`). `b ≥ a->used`: tail-jump to `mp_zero(a)` (`mrshdZ`). Otherwise
the loop at `1e3c` (`mrshdE` enters it) copies `dp[x + b]` to `dp[x]` and
reloads `used` (`mrshdL`, `mrshdLe`); then the frame (`a`, `b`, `ra`) and
`memset(dp + used - b, 0, 4 b)` at `1e7c` (`mrshdM`; the `blez` before it is
never taken, since the loop leaves `used - x = b > 0`); `mrshdR` reloads the
frame, stores `used -= b` and returns.
-/


namespace Tom.Machine.Fn.MpRshd

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mrshd_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpRshdBase = 0x80001e1c := rfl
   have : mpRshdCode.length = 37 := rfl))

def entry : BitVec 64 := 0x80001e1c#64

/-- The entry: `a0 = a`, `a1 = b`. -/
def entryL (ra s0 : BitVec 64) (sp pa b : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 b)]

/-- The return. -/
def retL (ra s0 : BitVec 64) (sp : Nat) : GRegs := [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0)]

/-- `b = 0`: return. -/
theorem n_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa : Nat) (m : Mem)
    (hc : CodeAt m mpRshdBase mpRshdCode) (hra : ra.toNat % 4 = 0) :
    Triple (At entry (entryL ra s0 sp pa 0) m v.keepR outp) (At ra (retL ra s0 sp) (writeLog m []) v.keepR outp) := by
  mrshd_ctx
  seg_step mrshdN ra ([] : List (List (BitVec 8))) [1, 2, 8, 10, 11] abiKeysR [entry, entryL] [retL] [] hc

/-- The struct reads. -/
structure SFacts (m : Mem) (pa dp u : Nat) : Prop where
  ra_ : Ram pa 24
  u_v : bytesT4 m pa = BitVec.ofNat 32 u
  dp_v : bytesT8 m (pa + 16) = BitVec.ofNat 64 dp
  u_lt : u < 2 ^ 31

theorem SFacts.sx {m : Mem} {pa dp u : Nat} (h : SFacts m pa dp u) :
    BitVec.signExtend 64 (bytesT4 m pa) = BitVec.ofNat 64 u := by rw [h.u_v, signExtend_ofNat32 _ h.u_lt]

/-- `b ≥ used`: tail-jump to `mp_zero(a)`. -/
theorem z_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa dp u b : Nat) (m : Mem)
    (hc : CodeAt m mpRshdBase mpRshdCode) (hf : SFacts m pa dp u) (hb : 0 < b) (hb' : b < 2 ^ 31) (hub : u ≤ b) :
    Triple (At entry (entryL ra s0 sp pa b) m v.keepR outp)
      (At MpZero.entry (entryL ra s0 sp pa b) (writeLog m []) v.keepR outp) := by
  mrshd_ctx
  have hsx := hf.sx
  seg_step mrshdZ MpZero.entry [rd4 m pa] [1, 2, 8, 10, 11] abiKeysR [entry, entryL, MpZero.entry] [] [hsx] hc

/-- At the loop head (`1e3c`), index `x`. -/
def hL (ra s0 : BitVec 64) (sp pa dp b x : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 (dp + 4 * x)), (11, BitVec.ofNat 64 b),
   (14, BitVec.ofNat 64 x), (15, BitVec.ofNat 64 (dp + 4 * (x + b))), (16, BitVec.ofNat 64 pa)]

/-- `0 < b < used`: enter the loop. -/
theorem e_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa dp u b : Nat) (m : Mem)
    (hc : CodeAt m mpRshdBase mpRshdCode) (hf : SFacts m pa dp u) (hb : 0 < b) (hbu : b < u) :
    Triple (At entry (entryL ra s0 sp pa b) m v.keepR outp)
      (At 0x80001e3c#64 (hL ra s0 sp pa dp b 0) (writeLog m []) v.keepR outp) := by
  mrshd_ctx
  have hsx := hf.sx
  seg_step mrshdE 0x80001e3c#64 [rd4 m pa, rd8 m (pa + 16)] [1, 2, 8, 10, 11] abiKeysR [entry, entryL] [hL]
    [hsx, hf.dp_v] hc

/-- One iteration's memory facts: `y = dp[x + b]`, the store at `dp[x]`, `used`. -/
structure LFacts (M : Mem) (pa dp u b x y : Nat) : Prop where
  ra_ : Ram pa 24
  u_v : bytesT4 M pa = BitVec.ofNat 32 u
  u_lt : u < 2 ^ 31
  ry : Ram (dp + 4 * (x + b)) 4
  y_v : bytesT4 M (dp + 4 * (x + b)) = BitVec.ofNat 32 y
  y_lt : y < 2 ^ 31
  rd : Ram (dp + 4 * x) 4
  dp_al : dp % 4 = 0
  d_a : dp + 4 * x + 4 ≤ pa ∨ pa + 4 ≤ dp + 4 * x
  code_off : dp + 4 * x + 4 ≤ mpRshdBase ∨ mpRshdBase + 148 ≤ dp + 4 * x

/-- The loop's back edge (`x + 1 < used - b`). -/
theorem l_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa dp u b x y : Nat) (M : Mem)
    (hc : CodeAt M mpRshdBase mpRshdCode) (hf : LFacts M pa dp u b x y) (hbu : b < u) (hx : x + 1 < u - b) :
    Triple (At 0x80001e3c#64 (hL ra s0 sp pa dp b x) M v.keepR outp)
      (At 0x80001e3c#64 (hL ra s0 sp pa dp b (x + 1)) (writeLog M [(dp + 4 * x, 4, BitVec.ofNat 64 y)])
        v.keepR outp) := by
  mrshd_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 u := by rw [hf.u_v, signExtend_ofNat32 _ hf.u_lt]
  have h2 : BitVec.signExtend 64 (bytesT4 M (dp + 4 * (x + b))) = BitVec.ofNat 64 y := by
    rw [hf.y_v, signExtend_ofNat32 _ hf.y_lt]
  seg_step mrshdL 0x80001e3c#64 [rd4 M (dp + 4 * (x + b)), rd4 M pa] [1, 2, 8, 10, 11, 14, 15, 16] abiKeysR
    [hL] [] [h1, h2] hc

/-- After the loop (`1e5c`). -/
def jL (ra s0 : BitVec 64) (sp pa dp u b : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 (dp + 4 * (u - b))), (11, BitVec.ofNat 64 b),
   (14, BitVec.ofNat 64 (u - b)), (16, BitVec.ofNat 64 pa), (12, BitVec.ofNat 64 u)]

/-- The loop's last iteration (`x + 1 = used - b`). -/
theorem le_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa dp u b x y : Nat) (M : Mem)
    (hc : CodeAt M mpRshdBase mpRshdCode) (hf : LFacts M pa dp u b x y) (hbu : b < u) (hx : x + 1 = u - b) :
    Triple (At 0x80001e3c#64 (hL ra s0 sp pa dp b x) M v.keepR outp)
      (At 0x80001e5c#64 (jL ra s0 sp pa dp u b) (writeLog M [(dp + 4 * x, 4, BitVec.ofNat 64 y)])
        v.keepR outp) := by
  mrshd_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 u := by rw [hf.u_v, signExtend_ofNat32 _ hf.u_lt]
  have h2 : BitVec.signExtend 64 (bytesT4 M (dp + 4 * (x + b))) = BitVec.ofNat 64 y := by
    rw [hf.y_v, signExtend_ofNat32 _ hf.y_lt]
  seg_step mrshdLe 0x80001e5c#64 [rd4 M (dp + 4 * (x + b)), rd4 M pa] [1, 2, 8, 10, 11, 14, 15, 16] abiKeysR
    [hL] [jL] [h1, h2] hc

/-- The frame stores. -/
def frameLog (ra : BitVec 64) (sp pa b : Nat) : List WEntry :=
  [(sp - 24, 8, BitVec.ofNat 64 b), (sp - 8, 8, ra), (sp - 32, 8, BitVec.ofNat 64 pa)]

/-- At the `memset` call (`1e7c`). -/
def msL (ra s0 : BitVec 64) (sp dp u b : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, s0), (10, BitVec.ofNat 64 (dp + 4 * (u - b))), (11, 0#64),
   (12, BitVec.ofNat 64 (4 * b))]

/-- The frame. -/
structure FFacts (sp : Nat) : Prop where
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  code_off : sp ≤ mpRshdBase ∨ mpRshdBase + 148 ≤ sp - 32

/-- The frame, to the `memset` call. -/
theorem m_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa dp u b : Nat) (M : Mem)
    (hc : CodeAt M mpRshdBase mpRshdCode) (hf : FFacts sp) (hb : 0 < b) (hbu : b < u) (hu : u < 2 ^ 31) :
    Triple (At 0x80001e5c#64 (jL ra s0 sp pa dp u b) M v.keepR outp)
      (At 0x80001e7c#64 (msL ra s0 sp dp u b) (writeLog M (frameLog ra sp pa b)) v.keepR outp) := by
  mrshd_ctx
  seg_step mrshdM 0x80001e7c#64 ([] : List (List (BitVec 8))) [1, 2, 8, 10, 11, 14, 16, 12] abiKeysR
    [jL, frameLog] [msL] [] hc

/-- The epilogue's facts. -/
structure RFacts (M : Mem) (ra : BitVec 64) (sp pa u b : Nat) : Prop where
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  ra_al : ra.toNat % 4 = 0
  ra_ : Ram pa 24
  pa_al : pa % 8 = 0
  pa_v : bytesT8 M (sp - 32) = BitVec.ofNat 64 pa
  b_v : bytesT8 M (sp - 24) = BitVec.ofNat 64 b
  ra_v : bytesT8 M (sp - 8) = ra
  u_v : bytesT4 M pa = BitVec.ofNat 32 u
  u_lt : u < 2 ^ 31
  b_le : b ≤ u
  code_off : pa + 24 ≤ mpRshdBase ∨ mpRshdBase + 148 ≤ pa

/-- After `memset`: `used -= b`, restore, return. -/
theorem r_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa u b : Nat) (M : Mem)
    (hc : CodeAt M mpRshdBase mpRshdCode) (hf : RFacts M ra sp pa u b) :
    Triple (At 0x80001e80#64 [(2, BitVec.ofNat 64 (sp - 32)), (8, s0)] M v.keepR outp)
      (At ra (retL ra s0 sp) (writeLog M [(pa, 4, BitVec.ofNat 64 (u - b))]) v.keepR outp) := by
  mrshd_ctx
  have hra := hf.ra_al
  have h1 : bytesT8 M (sp - 32 + 0) = BitVec.ofNat 64 pa := hf.pa_v
  have h2 : bytesT8 M (sp - 32 + 8) = BitVec.ofNat 64 b := by rw [show sp - 32 + 8 = sp - 24 by omega]; exact hf.b_v
  have h3 : bytesT8 M (sp - 32 + 24) = ra := by rw [show sp - 32 + 24 = sp - 8 by omega]; exact hf.ra_v
  have h4 : BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 u := by rw [hf.u_v, signExtend_ofNat32 _ hf.u_lt]
  seg_step_eq mrshdR ra [rd8 M (sp - 32 + 0), rd8 M (sp - 32 + 8), rd8 M (sp - 32 + 24), rd4 M pa] [2, 8]
    abiKeysR [] [retL] [h1, h2, h3, h4] hc

end Tom.Machine.Fn.MpRshd
