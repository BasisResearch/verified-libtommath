import Tom.Layout
import Tom.Machine.Api.Heap
import Tom.Machine.Api.MpAdd
import Tom.Machine.Api.SAdd
import Tom.Machine.Api.SSub
import Tom.Machine.Fn.AddDMain
import Tom.Machine.Fn.AddDPosI
import Tom.Machine.Fn.AllocFree
import Tom.Machine.Fn.AllocMallocR
import Tom.Machine.Fn.AllocRealloc
import Tom.Machine.Fn.BalMulAMainG
import Tom.Machine.Fn.BalMulMainG
import Tom.Machine.Fn.CallocMain
import Tom.Machine.Fn.Clamp
import Tom.Machine.Fn.CmpDMain
import Tom.Machine.Fn.CmpMag
import Tom.Machine.Fn.CmpSMain
import Tom.Machine.Fn.CntLsbMain
import Tom.Machine.Fn.CountBitsMain
import Tom.Machine.Fn.Div2InPlace
import Tom.Machine.Fn.Div2Main
import Tom.Machine.Fn.Div3IMainG
import Tom.Machine.Fn.Div3Main
import Tom.Machine.Fn.Div3NMainG
import Tom.Machine.Fn.DrIsModulusMain
import Tom.Machine.Fn.DrReduceGMainG
import Tom.Machine.Fn.DrReduceMain
import Tom.Machine.Fn.DrSetupMain
import Tom.Machine.Fn.ExchMain
import Tom.Machine.Fn.Expt2GMainG
import Tom.Machine.Fn.Expt2Main
import Tom.Machine.Fn.GrowH
import Tom.Machine.Fn.Invmod
import Tom.Machine.Fn.InvmodFastMainG
import Tom.Machine.Fn.InvmodSlowMainG
import Tom.Machine.Fn.KMulAMainG
import Tom.Machine.Fn.KMulMainG
import Tom.Machine.Fn.KSqrAMainG
import Tom.Machine.Fn.KSqrMainG
import Tom.Machine.Fn.Libgcc
import Tom.Machine.Fn.LibgccSigned
import Tom.Machine.Fn.MemcpyMain
import Tom.Machine.Fn.Memset
import Tom.Machine.Fn.MontNormGMainG
import Tom.Machine.Fn.MontNormMain
import Tom.Machine.Fn.MontRedFastGMainG
import Tom.Machine.Fn.MontRedFastMain
import Tom.Machine.Fn.MontRedGrMainG
import Tom.Machine.Fn.MontRedMainG
import Tom.Machine.Fn.MpAbsGMainG
import Tom.Machine.Fn.MpAbsMain
import Tom.Machine.Fn.MpAddAlias
import Tom.Machine.Fn.MpAddGAMainG
import Tom.Machine.Fn.MpAddGBMainG
import Tom.Machine.Fn.MpAddGMainG
import Tom.Machine.Fn.MpClearMain
import Tom.Machine.Fn.MpClearMultiMain
import Tom.Machine.Fn.MpCopyGMainG
import Tom.Machine.Fn.MpCopyMain
import Tom.Machine.Fn.MpDiv2dMain
import Tom.Machine.Fn.MpDiv2dRGMainG
import Tom.Machine.Fn.MpDiv2dRMainG
import Tom.Machine.Fn.MpDivDIMainG
import Tom.Machine.Fn.MpDivDMainG
import Tom.Machine.Fn.MpDivMainG
import Tom.Machine.Fn.MpDivQMainG
import Tom.Machine.Fn.MpDivRMainG
import Tom.Machine.Fn.MpExptmod
import Tom.Machine.Fn.MpGcdMainG
import Tom.Machine.Fn.MpGrowMain
import Tom.Machine.Fn.MpInitCopyMain
import Tom.Machine.Fn.MpInitMain
import Tom.Machine.Fn.MpInitMultiMain
import Tom.Machine.Fn.MpLshdGMainG
import Tom.Machine.Fn.MpLshdMain
import Tom.Machine.Fn.MpMod2dIMainG
import Tom.Machine.Fn.MpMod2dMain
import Tom.Machine.Fn.MpModMainG
import Tom.Machine.Fn.MpMontSetupMain
import Tom.Machine.Fn.MpMul2dIMainG
import Tom.Machine.Fn.MpMul2dMain
import Tom.Machine.Fn.MpMulmodMainG
import Tom.Machine.Fn.MpReduce2kGMainG
import Tom.Machine.Fn.MpReduce2kLGMainG
import Tom.Machine.Fn.MpReduce2kLMainG
import Tom.Machine.Fn.MpReduce2kMainG
import Tom.Machine.Fn.MpReduceMainG
import Tom.Machine.Fn.MpReduceSetupGMainG
import Tom.Machine.Fn.MpReduceSetupMainG
import Tom.Machine.Fn.MpRshdMain
import Tom.Machine.Fn.MpSetMain
import Tom.Machine.Fn.MpSubAlias
import Tom.Machine.Fn.MpSubGAMainG
import Tom.Machine.Fn.MpSubGBMainG
import Tom.Machine.Fn.MpSubGMainG
import Tom.Machine.Fn.MpSubMain
import Tom.Machine.Fn.MpToRadixMainG
import Tom.Machine.Fn.MpZeroMain
import Tom.Machine.Fn.Mul2HDMainG
import Tom.Machine.Fn.Mul2HMainG
import Tom.Machine.Fn.Mul2Main
import Tom.Machine.Fn.MulDGAMainG
import Tom.Machine.Fn.MulDGMainG
import Tom.Machine.Fn.MulDMain
import Tom.Machine.Fn.MulFastGAMainG
import Tom.Machine.Fn.MulFastGMainG
import Tom.Machine.Fn.MulFastMain
import Tom.Machine.Fn.MulGroupB
import Tom.Machine.Fn.MulHighFastGAMainG
import Tom.Machine.Fn.MulHighFastMain
import Tom.Machine.Fn.ReadRadixMainG
import Tom.Machine.Fn.Reduce2kLMain
import Tom.Machine.Fn.Reduce2kMain
import Tom.Machine.Fn.Reduce2kSetupGrMainG
import Tom.Machine.Fn.Reduce2kSetupLGMainG
import Tom.Machine.Fn.Reduce2kSetupLMainG
import Tom.Machine.Fn.Reduce2kSetupMainG
import Tom.Machine.Fn.ReverseMain
import Tom.Machine.Fn.SAddAlias
import Tom.Machine.Fn.SAddGAMainG
import Tom.Machine.Fn.SAddGBMainG
import Tom.Machine.Fn.SAddGMainG
import Tom.Machine.Fn.SExptFastMainG
import Tom.Machine.Fn.SExptMainG
import Tom.Machine.Fn.SMpMulDigsAGClosed
import Tom.Machine.Fn.SMpMulDigsMainG
import Tom.Machine.Fn.SMpMulHighDigsMainG
import Tom.Machine.Fn.SMpSqrMainG
import Tom.Machine.Fn.SSubAlias
import Tom.Machine.Fn.SSubGAMainG
import Tom.Machine.Fn.SSubGBMainG
import Tom.Machine.Fn.SSubGMainG
import Tom.Machine.Fn.SqrFastHAMainG
import Tom.Machine.Fn.SqrFastHMainG
import Tom.Machine.Fn.SqrFastMain
import Tom.Machine.Fn.SubDMain
import Tom.Machine.Fn.SubDPosI
import Tom.Machine.Fn.ToomMulAMainG
import Tom.Machine.Fn.ToomMulMainG
import Tom.Machine.Fn.ToomSqrAClosed
import Tom.Machine.Fn.ToomSqrClosed
import Tom.Machine.Kit.At
import Tom.Machine.Kit.Frame
import Tom.Machine.Kit.Meet
import Tom.Machine.Kit.MeetHeap
import Tom.Machine.Repr
import Tom.Spec.MpInt
import Tom.Spec.MpIntU
import Vsa.Triple

/-!
# The specifications of libtommath v1.3.0 on RV64I, for review

Generated by `scripts/gen_specs.py` from `experiments/specs.tsv` and the Lean sources; do not edit.
Every theorem below is proved (its proof is the machine proof, named after `:=`), and
`#print axioms` on it shows only `propext`, `Classical.choice` and `Quot.sound`.

For each libtommath function of `c/tommath-arith.elf` (alphabetical): its C prototype, every proved
form of its contract (the most general first: growing destinations, then the forms that assume
the destination has room, called D5 in the sources, then aliasing variants), and the definitions
the statement is made of, copied verbatim from the sources. The newlib/libgcc routines the
functions reach are in the appendix.

## How to read a contract

A contract is a total-correctness `Triple` over the Sail RISC-V model: from every machine state
`At entry …` (the pc at the function's entry, the argument registers, memory `m`), some finite run
reaches a state `At ra …` (returned to the caller) whose memory `M` satisfies the postcondition.
Its parameters `p : P` name the `mp_int`s involved (`p.a`, `p.b`, …, as `MpInt` values: `used`,
`alloc`, `sign` and the digit array) and where they are in memory. A contract `Statement` reads:

    ∀ p m …, ra aligned → Res p →                      -- what the caller must provide
      Sound (lay p) isW → Bundle (lay p) (kind p) m →  -- the regions are disjoint and hold p's mp_ints
      AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) → -- the allocator's heap, regions off its blocks
      Triple (At entry (args p) m …)
        (fun cf => ∃ x M, At ra (rets p x ra) M … cf ∧ Q p x ∧   -- the result x satisfies Q
                         HPost (lay p) ws site (out p x) … m M)  -- only the written regions changed

Most allocating contracts state exactly this (`def Statement : Prop :=` in the sources); below,
`Standard.Statement Res Q (site .s)` abbreviates that verbatim text with the site `.s`:

    ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
      Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
      Triple (At entry ((1, ra) :: args p) m v.keep outp)
        (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
          HPost (lay p) ws .s (out p x) (site' p x) (hin p) (hout p x) m M)

`Res` (or `Pre`) is the precondition: validity of the operands (`MpInt.Valid`), the C's `int`
arithmetic bounds, the stack. `Q` (or `Post`) is the arithmetic postcondition, stated with the
`Tom/Spec` definitions (for `mp_add`: the result's `val` is `val a + val b`). The machine plumbing
(the stack reservation, the register map, the regions) is summarised in one line per contract.
-/

/-! ## The common vocabulary

`MpInt` is the `mp_int` struct with its digit array read as a list; `mag` and `val`
its magnitude (`Nat`) and value (`Int`); `Shape`/`Valid` the representation invariants;
`ShapeU`/`ValidU` the same with the digits at and above `used` unconstrained. `Triple` is
total correctness on the machine, `At` a machine state at a pc with registers and memory.
-/

/-
-- Tom/Spec/MpInt.lean
/-- The radix `2^MP_DIGIT_BIT` (`2^28` for `MP_32BIT`, decision D1). -/
abbrev radix : Nat := 2 ^ Layout.digitBits

/-- `Σ_{i<n} dig i * radix^i`. -/
def natUpTo (dig : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => natUpTo dig n + radix ^ n * dig n

/-- An `mp_int`: the struct's integer fields and its digit array
`dp[0 .. alloc)` as a list. -/
structure MpInt where
  used : Nat
  alloc : Nat
  sign : Nat
  digits : List Nat
  deriving Repr, DecidableEq

/-- Digit `i` of the array (`dp[i]`), `0` past its end. -/
def digit (a : MpInt) (i : Nat) : Nat := a.digits.getD i 0

/-- The structural invariant. -/
structure Shape (a : MpInt) : Prop where
  len : a.digits.length = a.alloc
  used_le : a.used ≤ a.alloc
  alloc_lt : a.alloc < 2 ^ 31
  digit_lt : ∀ i, a.digit i < radix
  high_zero : ∀ i, a.used ≤ i → a.digit i = 0

/-- The full representation invariant. -/
structure Valid (a : MpInt) : Prop extends Shape a where
  top : 0 < a.used → a.digit (a.used - 1) ≠ 0
  sign_ok : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg
  zero_pos : a.used = 0 → a.sign = Layout.mpZpos

/-- The magnitude: `Σ_{i<used} dp[i] * radix^i`. -/
def mag (a : MpInt) : Nat := natUpTo a.digit a.used

/-- The value. -/
def val (a : MpInt) : Int := if a.sign = Layout.mpNeg then -(a.mag : Int) else a.mag

/-- libtommath's `mp_ord` code of a comparison (`MP_LT`, `MP_EQ`, `MP_GT`). -/
def ordCode : Ordering → Int
  | .lt => Layout.mpLt
  | .eq => Layout.mpEq
  | .gt => Layout.mpGt

-- Tom/Spec/MpIntU.lean
/-- `Shape` without `high_zero`. -/
structure ShapeU (a : MpInt) : Prop where
  len : a.digits.length = a.alloc
  used_le : a.used ≤ a.alloc
  alloc_lt : a.alloc < 2 ^ 31
  digit_lt : ∀ i, a.digit i < radix

/-- `Valid` without `high_zero`: the digits at and above `used` arbitrary (below `radix`). -/
structure ValidU (a : MpInt) : Prop extends ShapeU a where
  top : 0 < a.used → a.digit (a.used - 1) ≠ 0
  sign_ok : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg
  zero_pos : a.used = 0 → a.sign = Layout.mpZpos

-- Vsa/Triple.lean
/-- Total-correctness triple over the machine: from every `P`-configuration,
some finite run reaches a `Q`-configuration. -/
def Triple (P Q : Config → Prop) : Prop :=
  ∀ c, P c → ∃ c', Steps c c' ∧ Q c'

-- Tom/Machine/Kit/At.lean
/-- The machine parked at `pc` (see the module doc). -/
structure At (pc : BitVec 64) (L : GRegs) (m : Mem) (keep : GRegs) (outp : Array String)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = m
  pcv : c.σ.regs.get? Register.PC = some pc
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  regs : GHolds c.σ L
  keep : GHolds c.σ keep
  out : c.σ.sailOutput = outp
  pw : c.σ.regs.get? Register.htif_payload_writes = some 0#4
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v
  gprs : AllGprs c.σ

-- Tom/Machine/Repr.lean
/-- `a` at `p`, digits at `dp`. -/
structure MpAt (m : Mem) (p dp : Nat) (a : MpInt) : Prop where
  used : bytesT4 m (p + Layout.offUsed) = BitVec.ofNat 32 a.used
  alloc : bytesT4 m (p + Layout.offAlloc) = BitVec.ofNat 32 a.alloc
  sign : bytesT4 m (p + Layout.offSign) = BitVec.ofNat 32 a.sign
  dpv : bytesT8 m (p + Layout.offDp) = BitVec.ofNat 64 dp
  digits : ∀ i, i < a.alloc → bytesT4 m (dp + Layout.sizeofDigit * i) = BitVec.ofNat 32 (a.digit i)

-- Tom/Machine/Kit/Meet.lean
/-- **A witness bundle**: every region's witness, by its kind. -/
def Bundle (ρ : ι → Iv) (κ : ι → Kind) (m : Mem) : Prop := ∀ r, (κ r).Fits (ρ r) ∧ (κ r).Wit (ρ r) m

-- Tom/Machine/Kit/Frame.lean
/-- The layout is sound for `isW`: `Sep` names are disjoint. -/
def Sound (ρ : ι → Iv) (isW : ι → Bool) : Prop := ∀ r s, Sep isW r s = true → (ρ r).Disj (ρ s)

-- Tom/Machine/Kit/MeetHeap.lean
/-- The heap with the blocks `H`, and `_impure_ptr` (what every allocator call reads). -/
structure AHeap (m : Mem) (H : List (Nat × Nat)) : Prop where
  heap : Heap m H
  imp : ImpureAt m

/-- What an allocating callee leaves, in its names (`site` placed at `J`). -/
structure HPost {R : Type} (lay : R → Iv) (ws : List R) (site : R) (out : R → Kind) (J : Iv)
    (hin hout : List (Nat × Nat)) (m M : Mem) : Prop where
  wit : ∀ r, r ∈ ws → r ≠ site → (out r).Fits (lay r) ∧ (out r).Wit (lay r) M
  wsite : (out site).Fits J ∧ (out site).Wit J M
  place : Place hin (lay site) J
  frame : HFrm lay ws hin m M
  heap : AHeap M hout
  foot : ∀ a, Foot hout a → Foot hin a ∨ (lay site).In a
  off : Off J hout

-- Tom/Machine/Api/Heap.lean
/-- `[a, a + n)` lies off everything the allocator owns or hands out: below its
data or above the arena. -/
def OffHeap (a n : Nat) : Prop := a + n ≤ allocLo ∨ heapEnd ≤ a

-- Tom/Machine/Kit/Frame.lean
/-- `M` equals `m` outside the regions `ws`. -/
def Frm (ρ : ι → Iv) (ws : List ι) (m M : Mem) : Prop := ∀ x, ¬ InAny ρ ws x → M[x]? = m[x]?

-- Tom/Layout.lean
def digitBits : Nat := 28

def mpEq : Int := 0

def mpErr : Int := -1

def mpGt : Int := 1

def mpLt : Int := -1

def mpMask : Nat := 268435455

def mpMem : Int := -2

def mpNeg : Nat := 1

def mpOkay : Int := 0

def mpVal : Int := -3

def mpZpos : Nat := 0

def offAlloc : Nat := 4

def offDp : Nat := 16

def offSign : Nat := 8

def offUsed : Nat := 0

def sizeofDigit : Nat := 4

def sizeofMpInt : Nat := 24

def sizeofSign : Nat := 4

def sizeofUsed : Nat := 4
-/

/-! ## `mp_2expt`

`mp_err mp_2expt(mp_int *a, int b);`
-/

/-- `mp_2expt(a, b)` growing `a`: the allocating contract -/
theorem Specs.mp_2expt_correct : Tom.Machine.Api.Expt2G.Statement :=
  Tom.Machine.Fn.Expt2GG5.correct
/-
Machine plumbing: entry `0x800076d4`; the arguments: `a0 = a`, `a1 = b` (`gp` for the allocator); stack reservation `F = 48 + MpGrow.F`; regions stk aS aD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/Expt2G.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

structure P where  (sp pa adp : Nat); (a : MpInt); (b : Nat); (H : List (Nat × Nat))

/-- What `mp_2expt(a, b)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_zero` and `mp_grow` take a shaped `a`. -/
  sa : p.a.Shape
  /-- The C's `int b`, nonnegative (`bltz` at `76d4`: `MP_VAL` is not covered). -/
  b_lt : p.b < 2 ^ 31
  /-- `a`'s digits are `realloc`'s block: live and nonempty. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.a.alloc < p.b / Layout.digitBits + 1
  | some (q, a') => Ok p q a'

-- Tom/Machine/Api/StdHeap.lean
/-- The stack residue of an allocator call with `F` bytes. -/
structure StkRes (sp F : Nat) : Prop where
  al : sp % 16 = 0
  lo : heapEnd + F ≤ sp
  hi : sp ≤ 0x100000000

-- Tom/Machine/Api/Expt2G.lean
/-- `MP_OKAY`: the value, and where `a`'s digits went (kept or re-placed: a caller that re-places its
own region by this call needs it, `HContract.after` consumes the callee's `HPost.place`). -/
structure Ok (p : P) (q : Nat) (a' : MpInt) : Prop where
  post : Expt2Post (expt2In p.a p.b) p.b a'
  place : Place (hin p) (lay p .aD) ⟨q, 4 * a'.alloc⟩

-- Tom/Machine/Api/Alloc.lean
/-- `__heap_end` (`0x87800000`). -/
abbrev heapEnd : Nat := Vsa.Sim.DlHeap.heapEnd

-- Tom/Spec/Expt2.lean
/-- What `mp_2expt(a, b)` leaves in `a` (`b ≥ 0`, `b / 28 + 1 ≤ a->alloc`): one digit
`2^(b mod 28)` at `b / 28`, the rest zero. -/
structure Expt2Post (a : MpInt) (b : Nat) (a' : MpInt) : Prop where
  alloc : a'.alloc = a.alloc
  len : a'.digits.length = a.alloc
  used : a'.used = b / Layout.digitBits + 1
  sign : a'.sign = Layout.mpZpos
  digit : ∀ j, a'.digit j = if j = b / Layout.digitBits then 2 ^ (b % Layout.digitBits) else 0
theorem Expt2Post.spec {a a' : MpInt} {b : Nat} (hroom : b / Layout.digitBits + 1 ≤ a.alloc)
    (hal : a.alloc < 2 ^ 31) (h : Expt2Post a b a') : a'.Valid ∧ a'.mag = 2 ^ b ∧ a'.val = 2 ^ b := …  -- proved in Tom/Spec/Expt2.lean
theorem Expt2Post.specG {a a' : MpInt} {b : Nat} (ha : a.alloc < 2 ^ 31) (hb : b < 2 ^ 31)
    (h : Expt2Post (expt2In a b) b a') : a'.Valid ∧ a'.mag = 2 ^ b ∧ a'.val = 2 ^ b := …  -- proved in Tom/Spec/Expt2G.lean

-- Tom/Spec/Expt2G.lean
/-- `a` after `mp_zero(a)` and `mp_grow(a, b / 28 + 1)`. -/
def expt2In (a : MpInt) (b : Nat) : MpInt := MpInt.zeroN (max a.alloc (b / Layout.digitBits + 1))

-- Tom/Spec/Init.lean
/-- A zero `mp_int` with `n` digits allocated (`used = 0`, `MP_ZPOS`, all digits zero). -/
def MpInt.zeroN (n : Nat) : MpInt := ⟨0, n, Layout.mpZpos, List.replicate n 0⟩
-/

/-- `mp_2expt`: the standard contract -/
theorem Specs.mp_2expt_correct_room : Tom.Machine.Api.Expt2.Statement :=
  Tom.Machine.Fn.Expt2.correct
/-
Machine plumbing: entry `0x800076d4`; regions stk aS aD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/Expt2.lean
/-- **`mp_2expt` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {b : Nat} {ra s0 : BitVec 64},
    Pre m sp pa adp a b ra →
    Triple (At entry (Fn.Expt2.entryL ra s0 sp pa b) m v.keepR outp) (Ret m v outp sp pa adp a b ra s0)

/-- What `mp_2expt(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  b_lt : b < 2 ^ 31
  room : b / Layout.digitBits + 1 ≤ a.alloc
  rs : Ram (sp - 48) 48
  sp_al : sp % 16 = 0
  sp_ge : 48 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp a) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra s0 : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp a b a' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  expt : Expt2Post a b a'
  frame : Frm (lay sp pa adp a) ws m M

Also used (printed above): `Tom.Expt2Post` (`mp_2expt`)
-/

/-! ## `mp_abs`

`mp_err mp_abs(const mp_int *a, mp_int *b);`

Coverage: contract (growing b: Api.MpAbsG, a != b; the D5 one Fn.MpAbs.correct).
-/

/-- `mp_abs(a, b)` growing `b`: the allocating contract -/
theorem Specs.mp_abs_correct : Tom.Machine.Api.MpAbsG.Statement :=
  Tom.Machine.Fn.MpAbsGG5.correct
/-
Machine plumbing: entry `0x800005cc`; the arguments: `a0 = a`, `a1 = b` (`gp` for the allocator); stack reservation `F = 32 + MpCopyG.F`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/MpAbsG.lean
def Statement : Prop := Standard.Statement Res Q (site .bD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp : Nat); (a b : MpInt); (H : List (Nat × Nat))

/-- What `mp_abs(a, b)` needs: `mp_copy(a, b)`'s (`MpCopyG.Res`) on the deeper stack. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  sa : p.a.Shape
  sb : p.b.Shape
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  apos : 0 < p.a.alloc
  ne : p.pa ≠ p.pb
  bpos : 0 < p.b.alloc
  boff : OffHeap p.pb 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.b.alloc < p.a.used
  | some (_, b') => AbsPost p.a (copyIn p.a p.b) b'

-- Tom/Spec/Set.lean
/-- What `mp_abs(a, b)` leaves in `b`: `a` copied, `sign := MP_ZPOS`. -/
structure AbsPost (a b b' : MpInt) : Prop where
  alloc : b'.alloc = b.alloc
  len : b'.digits.length = b.alloc
  used : b'.used = a.used
  sign : b'.sign = Layout.mpZpos
  digit : ∀ i, b'.digit i = if i < a.used then a.digit i else if i < b.used then 0 else b.digit i
theorem AbsPost.spec {a b b' : MpInt} (ha : a.Valid) (hb : b.Shape) (hroom : a.used ≤ b.alloc)
    (h : AbsPost a b b') : b'.Valid ∧ b'.mag = a.mag ∧ b'.val = a.mag := …  -- proved in Tom/Spec/Set.lean

-- Tom/Spec/CopyGStep.lean
/-- `b` after `mp_copy`'s `mp_grow(b, a->used)`. -/
def copyIn (a b : MpInt) : MpInt := if b.alloc < a.used then b.growTo a.used else b

-- Tom/Spec/Grow6Step.lean
/-- `a` with `n` digits: its digit function on `[0, n)`. -/
def MpInt.growTo (a : MpInt) (n : Nat) : MpInt := MpInt.ofDigits a.used n a.sign a.digit

-- Tom/Spec/Set.lean
/-- The `mp_int` with `used = u`, `alloc = al`, `sign = s` and digits `f` on `[0, al)`. -/
def MpInt.ofDigits (u al s : Nat) (f : Nat → Nat) : MpInt :=
  { used := u, alloc := al, sign := s, digits := (List.range al).map f }

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`)
-/

/-- `mp_abs`: the standard contract -/
theorem Specs.mp_abs_correct_room : Tom.Machine.Api.MpAbs.Statement :=
  Tom.Machine.Fn.MpAbs.correct
/-
Machine plumbing: entry `0x800005cc`.

-- Tom/Machine/Api/MpAbs.lean
/-- **`mp_abs` on the machine** (distinct operands). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    Pre m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.MpAbs.entryL ra s0 sp pa pb) m v.keepR outp) (Ret m v outp sp pa adp pb bdp a b ra s0)

/-- What `mp_abs(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  sa : a.Shape
  sb : b.Shape
  asign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  room : a.used ≤ b.alloc
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp a b) Two.isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ b' M, At ra (Fn.MpAbs.retL ra s0 sp) M v.keepR outp cf ∧ Post m sp pa adp pb bdp a b b' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp : Nat) (a b b' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pb bdp b'
  abs : AbsPost a b b'
  frame : Frm (lay sp pa adp pb bdp a b) Two.ws m M

Also used (printed above): `Tom.AbsPost` (`mp_abs`)
-/

/-- `mp_abs`: the standard contract -/
theorem Specs.mp_abs_correct_alias : Tom.Machine.Api.MpAbs.AliasStatement :=
  Tom.Machine.Fn.MpAbs.alias_correct
/-
Machine plumbing: entry `0x800005cc`.

-- Tom/Machine/Api/MpAbs.lean
/-- **`mp_abs(a, a)` on the machine.** -/
def AliasStatement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {ra s0 : BitVec 64},
    APre m sp pa adp a ra →
    Triple (At entry (Fn.MpAbs.entryL ra s0 sp pa pa) m v.keepR outp)
      (fun cf => ∃ a' M, At ra (Fn.MpAbs.retL ra s0 sp) M v.keepR outp cf ∧ APost m sp pa adp a a' M)

/-- What `mp_abs(a, a)` needs. -/
structure APre (m : Mem) (sp pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (Un.lay 0 sp pa adp a) Un.isW

/-- What it leaves. -/
structure APost (m : Mem) (sp pa adp : Nat) (a a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  abs : AbsPost a a a'
  frame : Frm (Un.lay 0 sp pa adp a) Un.ws m M

Also used (printed above): `Tom.AbsPost` (`mp_abs`)
-/

/-! ## `mp_add`

`mp_err mp_add(const mp_int *a, const mp_int *b, mp_int *c);`
-/

/-- `mp_add(a, b, c)` with growth: the allocating contract -/
theorem Specs.mp_add_correct : Tom.Machine.Api.MpAddG.Statement :=
  Tom.Machine.Fn.MpAddGG5.correct
/-
Machine plumbing: entry `0x80000608`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator); stack reservation `F = 64 + MpGrow.F`; regions stk aS aD bS bD cS cD code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/MpAddG.lean
def Statement : Prop := Standard.Statement Res Q (site .cD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp pc cdp : Nat); (a b c : MpInt); (H : List (Nat × Nat))

/-- What `mp_add(a, b, c)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_cmp_mag` compares the operands' magnitudes (valid operands). -/
  va : p.a.Valid
  vb : p.b.Valid
  /-- `c`'s old digits above the result are zeroed only up to its old `used`. -/
  sc : p.c.Shape
  /-- `mp_grow`'s `int size` (`max(used) + 1`). -/
  size_lt : max p.a.used p.b.used + 1 < 2 ^ 31
  /-- The operands' digit arrays are nonempty (initialised `mp_int`s). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  cpos : 0 < p.c.alloc
  /-- `c`'s struct is off the arena (`mp_grow` reads and writes it). -/
  coff : OffHeap p.pc 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.c.alloc < addSize p.a p.b
  | some (_, x) => AddG p.a p.b (SAddPost p.a p.b (sAddIn p.a p.b (p.c.withSign p.a.sign)) x) (SSubPost p.b p.a (sSubIn p.b (p.c.withSign p.b.sign)) x) (SSubPost p.a p.b (sSubIn p.a (p.c.withSign p.a.sign)) x)

-- Tom/Spec/AddGStep.lean
/-- The size the tail callee grows `c` to (when `c->alloc` is less). -/
def addSize (a b : MpInt) : Nat :=
  if a.sign = b.sign then max a.used b.used + 1 else if a.mag < b.mag then b.used else a.used

/-- What `mp_add` leaves, by branch. -/
structure AddG (a b : MpInt) (S L G : Prop) : Prop where
  same : a.sign = b.sign → S
  lt : a.sign ≠ b.sign → a.mag < b.mag → L
  ge : a.sign ≠ b.sign → ¬ a.mag < b.mag → G
theorem AddG.specA {a b x : MpInt} (ha : a.Valid) (hb : b.Valid)
    (h31 : max a.used b.used + 1 < 2 ^ 31)
    (h : AddG a b (SAddPost (a.withSign a.sign) b (sAddIn (a.withSign a.sign) b (a.withSign a.sign)) x)
      (SSubPost b (a.withSign b.sign) (sSubIn b (a.withSign b.sign)) x)
      (SSubPost (a.withSign a.sign) b (sSubIn (a.withSign a.sign) (a.withSign a.sign)) x)) :
    x.Valid ∧ x.val = a.val + b.val ∧ a.alloc ≤ x.alloc := …  -- proved in Tom/Spec/GrowAStep.lean
theorem AddG.specB {a b x : MpInt} (ha : a.Valid) (hb : b.Valid)
    (h31 : max a.used b.used + 1 < 2 ^ 31)
    (h : AddG a b (SAddPost a (b.withSign a.sign) (sAddIn a (b.withSign a.sign) (b.withSign a.sign)) x)
      (SSubPost (b.withSign b.sign) a (sSubIn (b.withSign b.sign) (b.withSign b.sign)) x)
      (SSubPost a (b.withSign a.sign) (sSubIn a (b.withSign a.sign)) x)) :
    x.Valid ∧ x.val = a.val + b.val ∧ b.alloc ≤ x.alloc := …  -- proved in Tom/Spec/GrowAStep.lean
theorem AddG.spec {a b c x : MpInt} (ha : a.Valid) (hb : b.Valid) (hc : c.Shape)
    (h31 : max a.used b.used + 1 < 2 ^ 31)
    (h : AddG a b (SAddPost a b (sAddIn a b (c.withSign a.sign)) x)
      (SSubPost b a (sSubIn b (c.withSign b.sign)) x) (SSubPost a b (sSubIn a (c.withSign a.sign)) x)) :
    x.Valid ∧ x.val = a.val + b.val ∧ c.alloc ≤ x.alloc := …  -- proved in Tom/Spec/GrowHStep.lean

-- Tom/Spec/Ops.lean
/-- What `s_mp_add(a, b, c)` leaves in `c` when `c` has room
(`c->alloc ≥ max + 1`, so `mp_grow` is not called): the carry chain's
digits, zeros above, `used` clamped from `max + 1`, the sign reset if the
sum is zero; `alloc` unchanged. -/
structure SAddPost (a b c c' : MpInt) : Prop where
  alloc : c'.alloc = c.alloc
  len : c'.digits.length = c.alloc
  digit : c'.digit = addDigits a b
  used : c'.used = clampUsed (addDigits a b) (max a.used b.used + 1)
  sign : c'.sign = if c'.used = 0 then Layout.mpZpos else c.sign
theorem SAddPost.spec {a b c c' : MpInt} (ha : a.Shape) (hb : b.Shape)
    (hroom : max a.used b.used + 1 ≤ c.alloc) (hc : c.alloc < 2 ^ 31)
    (hsign : c.sign = Layout.mpZpos ∨ c.sign = Layout.mpNeg) (h : SAddPost a b c c') :
    c'.Valid ∧ c'.mag = a.mag + b.mag := …  -- proved in Tom/Spec/Ops.lean

-- Tom/Spec/SAddGStep.lean
/-- The destination `s_mp_add(a, b, c)` writes. -/
def sAddIn (a b c : MpInt) : MpInt :=
  if c.alloc < max a.used b.used + 1 then c.growTo (max a.used b.used + 1) else c

-- Tom/Spec/Signed.lean
/-- `c` with its sign field overwritten (`c->sign = s`). -/
def MpInt.withSign (c : MpInt) (s : Nat) : MpInt := { c with sign := s }

-- Tom/Spec/Sub.lean
/-- What `s_mp_sub(a, b, c)` leaves in `c` when `b->used ≤ a->used` and `c`
has room (`c->alloc ≥ a->used`, so `mp_grow` is not called): the borrow
chain's digits, zeros above (the loop writes `c[0 .. max)`,
`MP_ZERO_DIGITS` clears `c[max .. olduse)`, and `c`'s shape gives zeros
above `olduse`), `used` clamped from `a->used`, the sign reset if the
difference is zero; `alloc` unchanged. `c.sign` is the sign at entry (which
`mp_add`/`mp_sub` set just before the call). -/
structure SSubPost (a b c c' : MpInt) : Prop where
  alloc : c'.alloc = c.alloc
  len : c'.digits.length = c.alloc
  digit : c'.digit = subDigits a b
  used : c'.used = clampUsed (subDigits a b) a.used
  sign : c'.sign = if c'.used = 0 then Layout.mpZpos else c.sign
theorem SSubPost.spec {a b c c' : MpInt} (ha : a.Shape) (hb : b.Shape) (hmag : b.mag ≤ a.mag)
    (hroom : a.used ≤ c.alloc) (hc : c.alloc < 2 ^ 31)
    (hsign : c.sign = Layout.mpZpos ∨ c.sign = Layout.mpNeg) (h : SSubPost a b c c') :
    c'.Valid ∧ c'.mag = a.mag - b.mag := …  -- proved in Tom/Spec/Sub.lean

-- Tom/Spec/SSubGStep.lean
/-- The destination `s_mp_sub(a, b, c)` writes. -/
def sSubIn (a c : MpInt) : MpInt :=
  if c.alloc < a.used then c.growTo a.used else c

-- Tom/Spec/Ops.lean
/-- The digits `s_mp_add(a, b, c)` writes: the carry chain of the used
digits, as a digit function (zero past `max(used) + 1`). -/
def addDigits (a b : MpInt) (i : Nat) : Nat :=
  (addCarry (a.digits.take a.used) (b.digits.take b.used) 0).getD i 0

-- Tom/Spec/Algo.lean
/-- `used` after `mp_clamp`'s loop: strip zero digits from the top. -/
def clampUsed (dig : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if dig n = 0 then clampUsed dig n else n + 1

-- Tom/Spec/Sub.lean
/-- The digits `s_mp_sub(a, b, c)` writes: the borrow chain over `a`'s used
digits, as a digit function (zero from `a->used` on). -/
def subDigits (a b : MpInt) (i : Nat) : Nat :=
  (subBorrow (a.digits.take a.used) (b.digits.take b.used) 0).getD i 0

-- Tom/Spec/Algo.lean
/-- The digit loop of `s_mp_add` on the used digits of its two operands,
then the carry digit. -/
def addCarry : List Nat → List Nat → Nat → List Nat
  | [], [], u => [u]
  | x :: xs, [], u => (x + u) % radix :: addCarry xs [] ((x + u) / radix)
  | [], y :: ys, u => (y + u) % radix :: addCarry [] ys ((y + u) / radix)
  | x :: xs, y :: ys, u => (x + y + u) % radix :: addCarry xs ys ((x + y + u) / radix)

-- Tom/Spec/Sub.lean
/-- The digit loops of `s_mp_sub` on the used digits of `a` and `b`: one
output digit per digit of `a`, `b`'s digits read as `0` past its end (the
second loop). No final borrow digit. -/
def subBorrow : List Nat → List Nat → Nat → List Nat
  | [], _, _ => []
  | x :: xs, ys, u =>
    (x + radix - ys.headD 0 - u) % radix :: subBorrow xs ys.tail (if x < ys.headD 0 + u then 1 else 0)

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.MpInt.ofDigits` (`mp_abs`)
-/

/-- `mp_add(a, b, a)` with growth: the allocating contract -/
theorem Specs.mp_add_correct_ca : Tom.Machine.Api.MpAddGA.Statement :=
  Tom.Machine.Fn.MpAddGAG5.correct
/-
Machine plumbing: entry `0x80000608`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator); stack reservation `F = 64 + MpGrow.F`; regions stk aS aD bS bD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MpAddGA.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp : Nat); (a b : MpInt); (H : List (Nat × Nat))

/-- What `mp_add(a, b, a)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_cmp_mag` compares the operands' magnitudes (valid operands). -/
  va : p.a.Valid
  vb : p.b.Valid
  /-- `mp_grow`'s `int size` (`max(used) + 1`). -/
  size_lt : max p.a.used p.b.used + 1 < 2 ^ 31
  /-- The operands' digit arrays are nonempty (initialised `mp_int`s). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- `a`'s struct is off the arena (`mp_grow` reads and writes it). -/
  coff : OffHeap p.pa 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.a.alloc < addSize p.a p.b
  | some (_, x) => AddG p.a p.b (SAddPost (p.a.withSign p.a.sign) p.b (sAddIn (p.a.withSign p.a.sign) p.b (p.a.withSign p.a.sign)) x) (SSubPost p.b (p.a.withSign p.b.sign) (sSubIn p.b (p.a.withSign p.b.sign)) x) (SSubPost (p.a.withSign p.a.sign) p.b (sSubIn (p.a.withSign p.a.sign) (p.a.withSign p.a.sign)) x)

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.addSize` (`mp_add`), `Tom.AddG` (`mp_add`), `Tom.SAddPost` (`mp_add`), `Tom.MpInt.withSign` (`mp_add`), `Tom.sAddIn` (`mp_add`), `Tom.SSubPost` (`mp_add`), `Tom.sSubIn` (`mp_add`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.addDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.subDigits` (`mp_add`), `Tom.addCarry` (`mp_add`), `Tom.MpInt.ofDigits` (`mp_abs`), `Tom.subBorrow` (`mp_add`)
-/

/-- `mp_add(a, b, b)` with growth: the allocating contract -/
theorem Specs.mp_add_correct_cb : Tom.Machine.Api.MpAddGB.Statement :=
  Tom.Machine.Fn.MpAddGBG5.correct
/-
Machine plumbing: entry `0x80000608`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator); stack reservation `F = 64 + MpGrow.F`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/MpAddGB.lean
def Statement : Prop := Standard.Statement Res Q (site .bD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp : Nat); (a b : MpInt); (H : List (Nat × Nat))

/-- What `mp_add(a, b, b)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_cmp_mag` compares the operands' magnitudes (valid operands). -/
  va : p.a.Valid
  vb : p.b.Valid
  /-- `mp_grow`'s `int size` (`max(used) + 1`). -/
  size_lt : max p.a.used p.b.used + 1 < 2 ^ 31
  /-- The operands' digit arrays are nonempty (initialised `mp_int`s). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- `b`'s struct is off the arena (`mp_grow` reads and writes it). -/
  coff : OffHeap p.pb 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.b.alloc < addSize p.a p.b
  | some (_, x) => AddG p.a p.b (SAddPost p.a (p.b.withSign p.a.sign) (sAddIn p.a (p.b.withSign p.a.sign) (p.b.withSign p.a.sign)) x) (SSubPost (p.b.withSign p.b.sign) p.a (sSubIn (p.b.withSign p.b.sign) (p.b.withSign p.b.sign)) x) (SSubPost p.a (p.b.withSign p.a.sign) (sSubIn p.a (p.b.withSign p.a.sign)) x)

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.addSize` (`mp_add`), `Tom.AddG` (`mp_add`), `Tom.SAddPost` (`mp_add`), `Tom.MpInt.withSign` (`mp_add`), `Tom.sAddIn` (`mp_add`), `Tom.SSubPost` (`mp_add`), `Tom.sSubIn` (`mp_add`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.addDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.subDigits` (`mp_add`), `Tom.addCarry` (`mp_add`), `Tom.MpInt.ofDigits` (`mp_abs`), `Tom.subBorrow` (`mp_add`)
-/

namespace Tom.Machine.Api.MpAdd
open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Bin
/-- `mp_add`: the standard contract -/
theorem _root_.Specs.mp_add_correct_room {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat}
    {a b c : MpInt} {ra s0 : BitVec 64} (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Triple (At entry (Fn.SSub.entryL ra s0 sp pa pb pc) m v.keepR outp)
      (Ret m v outp sp pa adp pb bdp pc cdp a b c ra s0) :=
  Tom.Machine.Api.MpAdd.correct hP
end Tom.Machine.Api.MpAdd
/-
-- Tom/Machine/Api/MpAdd.lean
/-- What `mp_add(a, b, c)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  rc : MpAt m pc cdp c
  va : a.Valid
  vb : b.Valid
  sc : c.Shape
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  gc : MpGeom pc cdp c.alloc
  room : max a.used b.used + 1 ≤ c.alloc
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp pc cdp a b c) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp pc cdp a b c c' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp pc cdp : Nat) (a b c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  add : AddPost a b c c'
  frame : Frm (lay sp pa adp pb bdp pc cdp a b c) ws m M

-- Tom/Spec/Signed.lean
/-- What `mp_add(a, b, c)` leaves in `c`, by the branch it takes. -/
structure AddPost (a b c c' : MpInt) : Prop where
  same : a.sign = b.sign → SAddPost a b (c.withSign a.sign) c'
  lt : a.sign ≠ b.sign → cmpMag a b = .lt → SSubPost b a (c.withSign b.sign) c'
  ge : a.sign ≠ b.sign → cmpMag a b ≠ .lt → SSubPost a b (c.withSign a.sign) c'
theorem AddPost.spec {a b c c' : MpInt} (ha : a.Valid) (hb : b.Valid)
    (hroom : max a.used b.used + 1 ≤ c.alloc) (hc : c.alloc < 2 ^ 31) (h : AddPost a b c c') :
    c'.Valid ∧ c'.val = a.val + b.val := …  -- proved in Tom/Spec/Signed.lean

-- Tom/Spec/Algo.lean
/-- `mp_cmp_mag`: compare `used`, then the digits from the top. -/
def cmpMag (a b : MpInt) : Ordering :=
  if a.used > b.used then .gt else if a.used < b.used then .lt else cmpTop a.digit b.digit a.used

/-- The digit loop of `mp_cmp_mag`: compare digits `n - 1` down to `0`. -/
def cmpTop (da db : Nat → Nat) : Nat → Ordering
  | 0 => .eq
  | n + 1 => if da n > db n then .gt else if da n < db n then .lt else cmpTop da db n

Also used (printed above): `Tom.SAddPost` (`mp_add`), `Tom.MpInt.withSign` (`mp_add`), `Tom.SSubPost` (`mp_add`), `Tom.addDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.subDigits` (`mp_add`), `Tom.addCarry` (`mp_add`), `Tom.subBorrow` (`mp_add`)
-/

/-- `mp_add` in place: the standard contracts -/
theorem Specs.mp_add_correct_room_ca : Tom.Machine.Api.MpAddAlias.StatementCA :=
  Tom.Machine.Fn.MpAdd.correctCA
/-
Machine plumbing: entry `0x80000608`; regions stk aS aD bS bD code.

-- Tom/Machine/Api/MpAddAlias.lean
/-- **`mp_add(a, b, a)` on the machine.** -/
def StatementCA : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    PreCA m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.SSub.entryL ra s0 sp pa pb pa) m v.keepR outp)
      (RetCA m v outp sp pa adp pb bdp a b ra s0)

/-- What `mp_add(a, b, a)` needs. -/
structure PreCA (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop
    extends Base m 64 sp pa adp pb bdp a b ra where
  va : a.Valid
  vb : b.Valid
  room : max a.used b.used + 1 ≤ a.alloc
  lay : Sound (lay sp pa adp pb bdp a b) isWA

def RetCA (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostCA m sp pa adp pb bdp a b a' M

-- Tom/Machine/Api/BinA.lean
/-- What every in-place contract needs (stack depth `F`): the operands in
memory, the stack, the code. -/
structure Base (m : Mem) (F sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  rs : Ram (sp - F) F
  sp_al : sp % 16 = 0
  sp_ge : F ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m

/-- `c = a`: the stack and `a` written. -/
def isWA : R → Bool
  | .stk | .aS | .aD => true
  | _ => false

-- Tom/Machine/Api/MpAddAlias.lean
/-- What `mp_add(a, b, a)` leaves: `a'` at `a`. -/
structure PostCA (m : Mem) (sp pa adp pb bdp : Nat) (a b a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  add : AddPost a b a a'
  frame : Frm (lay sp pa adp pb bdp a b) wsA m M

-- Tom/Machine/Api/BinA.lean
def wsA : List R := [.stk, .aS, .aD]

Also used (printed above): `Tom.AddPost` (`mp_add`), `Tom.SAddPost` (`mp_add`), `Tom.MpInt.withSign` (`mp_add`), `Tom.cmpMag` (`mp_add`), `Tom.SSubPost` (`mp_add`), `Tom.addDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.cmpTop` (`mp_add`), `Tom.subDigits` (`mp_add`), `Tom.addCarry` (`mp_add`), `Tom.subBorrow` (`mp_add`)
-/

/-- `mp_add` in place: the standard contracts -/
theorem Specs.mp_add_correct_room_cb : Tom.Machine.Api.MpAddAlias.StatementCB :=
  Tom.Machine.Fn.MpAdd.correctCB
/-
Machine plumbing: entry `0x80000608`; regions stk aS aD bS bD code.

-- Tom/Machine/Api/MpAddAlias.lean
/-- **`mp_add(a, b, b)` on the machine.** -/
def StatementCB : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    PreCB m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.SSub.entryL ra s0 sp pa pb pb) m v.keepR outp)
      (RetCB m v outp sp pa adp pb bdp a b ra s0)

/-- What `mp_add(a, b, b)` needs. -/
structure PreCB (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop
    extends Base m 64 sp pa adp pb bdp a b ra where
  va : a.Valid
  vb : b.Valid
  room : max a.used b.used + 1 ≤ b.alloc
  lay : Sound (lay sp pa adp pb bdp a b) isWB

def RetCB (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ b' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostCB m sp pa adp pb bdp a b b' M

-- Tom/Machine/Api/BinA.lean
/-- `c = b`: the stack and `b` written. -/
def isWB : R → Bool
  | .stk | .bS | .bD => true
  | _ => false

-- Tom/Machine/Api/MpAddAlias.lean
/-- What `mp_add(a, b, b)` leaves: `b'` at `b`. -/
structure PostCB (m : Mem) (sp pa adp pb bdp : Nat) (a b b' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pb bdp b'
  add : AddPost a b b b'
  frame : Frm (lay sp pa adp pb bdp a b) wsB m M

-- Tom/Machine/Api/BinA.lean
def wsB : List R := [.stk, .bS, .bD]

Also used (printed above): `Tom.Machine.Api.BinA.Base` (`mp_add`), `Tom.AddPost` (`mp_add`), `Tom.SAddPost` (`mp_add`), `Tom.MpInt.withSign` (`mp_add`), `Tom.cmpMag` (`mp_add`), `Tom.SSubPost` (`mp_add`), `Tom.addDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.cmpTop` (`mp_add`), `Tom.subDigits` (`mp_add`), `Tom.addCarry` (`mp_add`), `Tom.subBorrow` (`mp_add`)
-/

/-! ## `mp_add_d`

`mp_err mp_add_d(const mp_int *a, mp_digit b, mp_int *c);`
-/

/-- `mp_add_d`: the standard contract -/
theorem Specs.mp_add_d_correct : Tom.Machine.Api.AddD.Statement :=
  Tom.Machine.Fn.AddD.correct
/-
Machine plumbing: entry `0x80004e30`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/AddD.lean
/-- **`mp_add_d` on the machine** (stack depth 128: its frame and `mp_sub_d`'s). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat} {c : MpInt}
    {ra s0 : BitVec 64}, Pre 128 m sp pa adp pc cdp a b c ra →
    Triple (At entry (entryL ra s0 sp pa b pc) m v.keepR outp) (Ret 128 m v outp sp pa adp pc cdp a b c ra s0)

/-- What `mp_add_d(a, b, c)` needs, with a stack of depth `F`. -/
structure Pre (F : Nat) (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt) (ra : BitVec 64) :
    Prop where
  ra_ : MpAt m pa adp a
  rc : MpAt m pc cdp c
  va : a.Valid
  sc : c.Shape
  hb : b < radix
  ga : MpGeom pa adp a.alloc
  gc : MpGeom pc cdp c.alloc
  room : a.used + 1 ≤ c.alloc
  rs : Ram (sp - F) F
  sp_al : sp % 16 = 0
  sp_ge : F ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay F sp pa adp pc cdp a c) isW

def Ret (F : Nat) (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat)
    (c : MpInt) (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post F m sp pa adp pc cdp a b c c' M

/-- What it leaves. -/
structure Post (F : Nat) (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c c' : MpInt) (M : Mem) :
    Prop where
  repr : MpAt M pc cdp c'
  addd : AddDPost a b c c'
  frame : Frm (lay F sp pa adp pc cdp a c) ws m M

-- Tom/Spec/Digit.lean
/-- What `mp_add_d(a, b, c)` leaves in `c`, by the branch it takes. -/
structure AddDPost (a : MpInt) (b : Nat) (c c' : MpInt) : Prop where
  pos : a.sign = Layout.mpZpos → DRes c c' (addDDigits a b) (a.used + 1) Layout.mpZpos
  big : a.sign = Layout.mpNeg → ¬ AddDSmall a b → DRes c c' (subDDigits a b) a.used Layout.mpNeg
  small : a.sign = Layout.mpNeg → AddDSmall a b → DRes c c' (smallDigits a b) 1 Layout.mpZpos
theorem AddDPost.spec {a c c' : MpInt} {b : Nat} (ha : a.Valid) (hb : b < radix)
    (hroom : a.used + 1 ≤ c.alloc) (hc : c.alloc < 2 ^ 31) (h : AddDPost a b c c') :
    c'.Valid ∧ c'.val = a.val + b := …  -- proved in Tom/Spec/Digit.lean

/-- What a branch leaves in `c`: the digits `dig`, `used` clamped from `n`,
the sign `s` unless the result is zero; `alloc` unchanged. -/
structure DRes (c c' : MpInt) (dig : Nat → Nat) (n s : Nat) : Prop where
  alloc : c'.alloc = c.alloc
  len : c'.digits.length = c.alloc
  digit : c'.digit = dig
  used : c'.used = clampUsed dig n
  sign : c'.sign = if c'.used = 0 then Layout.mpZpos else s
theorem DRes.spec {c c' : MpInt} {dig : Nat → Nat} {n s : Nat} (h : DRes c c' dig n s)
    (hlt : ∀ i, dig i < radix) (hhi : ∀ i, n ≤ i → dig i = 0) (hn : n ≤ c.alloc)
    (hc : c.alloc < 2 ^ 31) (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg) :
    c'.Valid ∧ c'.mag = natUpTo dig n ∧
      c'.val = if s = Layout.mpNeg then -(natUpTo dig n : Int) else natUpTo dig n := …  -- proved in Tom/Spec/Digit.lean

/-- `mp_add_d`'s digits for `a ≥ 0`: the loop's sums below `a->used`, the
final carry at `a->used`, zero above. -/
def addDDigits (a : MpInt) (b : Nat) (i : Nat) : Nat :=
  if i < a.used then (a.digit i + addDCarry a b i) % radix
  else if i = a.used then addDCarry a b i else 0

/-- `mp_add_d`'s test for its negative small branch (`a < 0` and `|a| < b`). -/
def AddDSmall (a : MpInt) (b : Nat) : Prop := a.used ≤ 1 ∧ a.digit 0 < b

/-- `mp_sub_d`'s digits for `a ≥ b ≥ 0`: the loop's differences below
`a->used`, zero above. -/
def subDDigits (a : MpInt) (b : Nat) (i : Nat) : Nat :=
  if i < a.used then (a.digit i + radix - subDBorrow a b i) % radix else 0

/-- The single digit of the small branches: `b - a[0]`. -/
def smallDigits (a : MpInt) (b : Nat) (i : Nat) : Nat := if i = 0 then b - a.digit 0 else 0

/-- The carry into position `i` of `mp_add_d`'s loop (`mu`, from `mu = b`). -/
def addDCarry (a : MpInt) (b : Nat) : Nat → Nat := carryChain a.digit (fun _ => 0) b

/-- The borrow into position `i` of `mp_sub_d`'s loop (`mu`, from `mu = b`). -/
def subDBorrow (a : MpInt) (b : Nat) : Nat → Nat := borrowChain a.digit (fun _ => 0) b

-- Tom/Spec/Indexed.lean
/-- The carry into position `i` of a digit-by-digit addition of `dx` and
`dy` with carry-in `u`. -/
def carryChain (dx dy : Nat → Nat) (u : Nat) : Nat → Nat
  | 0 => u
  | i + 1 => (dx i + dy i + carryChain dx dy u i) / radix

/-- The borrow into position `i` of a digit-by-digit subtraction of `dy`
from `dx` with borrow-in `u`. -/
def borrowChain (dx dy : Nat → Nat) (u : Nat) : Nat → Nat
  | 0 => u
  | i + 1 => if dx i < dy i + borrowChain dx dy u i then 1 else 0

Also used (printed above): `Tom.clampUsed` (`mp_add`)
-/

/-- `mp_add_d`: the standard contract -/
theorem Specs.mp_add_d_correct_inplace_pos : Tom.Machine.Api.AddD.StatementInPlacePos :=
  Tom.Machine.Fn.AddD.correct_inplace_pos
/-
Machine plumbing: entry `0x80004e30`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/AddD.lean
/-- **`mp_add_d(a, b, a)` on the machine for `a ≥ 0`** (any stack depth `F ≥ 64`). -/
def StatementInPlacePos : Prop :=
  ∀ {F : Nat} {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {b : Nat}
    {ra s0 : BitVec 64}, 64 ≤ F → PreI F m sp pa adp a b ra → a.sign = Layout.mpZpos →
    Triple (At entry (entryL ra s0 sp pa b pa) m v.keepR outp) (RetI F m v outp sp pa adp a b ra s0)

/-- What `mp_add_d(a, b, a)` needs, with a stack of depth `F`. -/
structure PreI (F : Nat) (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  va : a.Valid
  hb : b < radix
  ga : MpGeom pa adp a.alloc
  room : a.used + 1 ≤ a.alloc
  rs : Ram (sp - F) F
  sp_al : sp % 16 = 0
  sp_ge : F ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (layI F sp pa adp a) Un.isW

def RetI (F : Nat) (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (b : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostI F m sp pa adp a b a' M

/-- The regions of the in-place call (`Api/Un.lean`: `a` written). -/
abbrev layI (F sp pa adp : Nat) (a : MpInt) := Un.lay F sp pa adp a

/-- What it leaves. -/
structure PostI (F : Nat) (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  addd : AddDPost a b a a'
  frame : Frm (layI F sp pa adp a) Un.ws m M

Also used (printed above): `Tom.AddDPost` (`mp_add_d`), `Tom.DRes` (`mp_add_d`), `Tom.addDDigits` (`mp_add_d`), `Tom.AddDSmall` (`mp_add_d`), `Tom.subDDigits` (`mp_add_d`), `Tom.smallDigits` (`mp_add_d`), `Tom.clampUsed` (`mp_add`), `Tom.addDCarry` (`mp_add_d`), `Tom.subDBorrow` (`mp_add_d`), `Tom.carryChain` (`mp_add_d`), `Tom.borrowChain` (`mp_add_d`)
-/

/-! ## `mp_clamp`

`void mp_clamp(mp_int *a);`
-/

namespace Tom.Machine.Fn.Clamp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg
/-- **`mp_clamp` on the machine.** From its entry with `a0 = p`, the return
address `ra` and the callee-saved registers `v`, the machine runs `mp_clamp`
to `ra`, keeping `v`, with `a'` at `p` such that `ClampPost a a'`
(`ClampPost.spec`: `a'` valid, `mag a' = mag a`), only `used`/`sign` written,
and the code intact. -/
theorem _root_.Specs.mp_clamp_correct (ra : BitVec 64) (v : Abi) (outp : Array String) (p dp : Nat) (a : MpInt)
    (m : Mem) (hra : ra.toNat % 4 = 0) (hP : PreU m p dp a) :
    Triple (At entry [(1, ra), (10, BitVec.ofNat 64 p)] m v.keep outp)
      (Ret ra v outp m p dp a) :=
  Tom.Machine.Fn.Clamp.correctU ra v outp p dp a m hra hP
end Tom.Machine.Fn.Clamp
/-
-- Tom/Machine/Fn/Clamp.lean
/-- `Pre` with `a` only `ShapeU`: the code reads `dp[i]` for `i < used` only, so the digits at
and above `used` may be stale. -/
structure PreU (m : Mem) (p dp : Nat) (a : MpInt) : Prop where
  repr : MpAt m p dp a
  shape : a.ShapeU
  geom : MpGeom p dp a.alloc
  code : CodeAt m mpClampBase mpClampCode
  code_off : p + 24 ≤ mpClampBase ∨ mpClampBase + 64 ≤ p

/-- The return state. -/
def Ret (ra : BitVec 64) (v : Abi) (outp : Array String) (m : Mem) (p dp : Nat) (a : MpInt)
    (c : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (10, BitVec.ofNat 64 p)] M v.keep outp c ∧ Post m p dp a a' M

/-- What it leaves: `a'` at `p` with `ClampPost a a'`, the code, and memory
unchanged outside `used`/`alloc`/`sign`. -/
structure Post (m : Mem) (p dp : Nat) (a a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M p dp a'
  clamp : ClampPost a a'
  code : CodeAt M mpClampBase mpClampCode
  frame : ∀ x, x < p ∨ p + 12 ≤ x → M[x]? = m[x]?

-- Tom/Spec/Ops.lean
/-- What `mp_clamp(a)` leaves: the digits and `alloc` unchanged, `used`
lowered past the zero top digits, the sign reset when the result is zero. -/
structure ClampPost (a a' : MpInt) : Prop where
  digits : a'.digits = a.digits
  alloc : a'.alloc = a.alloc
  used : a'.used = clampUsed a.digit a.used
  sign : a'.sign = if a'.used = 0 then Layout.mpZpos else a.sign
theorem ClampPost.spec {a a' : MpInt} (hs : a.Shape)
    (hsign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg) (h : ClampPost a a') :
    a'.Valid ∧ a'.mag = a.mag := …  -- proved in Tom/Spec/Ops.lean

Also used (printed above): `Tom.clampUsed` (`mp_add`)
-/

namespace Tom.Machine.Fn.Clamp
open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg
/-- `mp_clamp` on the machine, against the specification: the returned
`mp_int` is valid and has the same magnitude (and so, by its sign, the same
value, `ClampPost.spec`). -/
theorem _root_.Specs.mp_clamp_correct_valid (ra : BitVec 64) (v : Abi) (outp : Array String) (p dp : Nat) (a : MpInt)
    (m : Mem) (hra : ra.toNat % 4 = 0) (hP : Pre m p dp a)
    (hsign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg) :
    Triple (At entry [(1, ra), (10, BitVec.ofNat 64 p)] m v.keep outp)
      (fun c => ∃ a' M, At ra [(1, ra), (10, BitVec.ofNat 64 p)] M v.keep outp c ∧
        MpAt M p dp a' ∧ a'.Valid ∧ a'.mag = a.mag) :=
  Tom.Machine.Fn.Clamp.correct_spec ra v outp p dp a m hra hP hsign
end Tom.Machine.Fn.Clamp
/-
-- Tom/Machine/Fn/Clamp.lean
/-- What `mp_clamp(a)` needs: `a` at `p` with its digits at `dp`, shaped,
the code in memory, and the struct off the code. -/
structure Pre (m : Mem) (p dp : Nat) (a : MpInt) : Prop where
  repr : MpAt m p dp a
  shape : a.Shape
  geom : MpGeom p dp a.alloc
  code : CodeAt m mpClampBase mpClampCode
  code_off : p + 24 ≤ mpClampBase ∨ mpClampBase + 64 ≤ p
-/

/-! ## `mp_clear`

`void mp_clear(mp_int *a);`
-/

/-- `mp_clear`: the standard contract -/
theorem Specs.mp_clear_correct : Tom.Machine.Api.MpClear.Statement :=
  Tom.Machine.Fn.MpClear.correct
/-
Machine plumbing: stack reservation `F = 32 + depth`.

-- Tom/Machine/Api/MpClear.lean
/-- **`mp_clear` on the machine**, `a` live. -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp pa adp : Nat} {a : MpInt}
    {ra : BitVec 64}, Pre m v H sp pa adp a ra →
    Triple (At Fn.MpClear.entry (entryL ra pa) m v.keep outp)
      (Ret m v outp H sp pa adp a ra)

/-- What `mp_clear(a)` needs, `a` live. -/
structure Pre (m : Mem) (v : Abi) (H : List (Nat × Nat)) (sp pa adp : Nat) (a : MpInt)
    (ra : BitVec 64) : Prop where
  repr : MpAt m pa adp a
  heap : Heap m (digBlk adp a :: H)
  st : Ram pa 24
  st_al : pa % 8 = 0
  soff : OffHeap pa 24
  ctx : ACtx m v sp F
  ra_al : ra.toNat % 4 = 0
  lay : Sound (lay sp pa adp a) Un.isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (H : List (Nat × Nat)) (sp pa adp : Nat) (a : MpInt)
    (ra : BitVec 64) (c : Vsa.Machine.Config) : Prop :=
  ∃ M, At ra [(1, ra)] M v.keep outp c ∧ Post m H sp pa adp a M

-- Tom/Machine/Api/Alloc.lean
/-- **The heap invariant** (`pShape (fun a => (m[a]?).getD 0) H`): the
blocks start at distinct addresses, and `m` read totally on `Foot H` is a
well-formed dlmalloc state with exactly the blocks `H` in use. -/
structure Heap (m : Mem) (H : List (Nat × Nat)) : Prop where
  starts : (H.map Prod.fst).Nodup
  shape : ∃ m', Shape m H m'

-- Tom/Machine/Api/Heap.lean
/-- **What an allocating function needs of its caller** besides its operands:
the code, `_impure_ptr`, `gp`, and a 16-aligned stack of `F` bytes (its own
frame and the allocator's) above the arena and below 4 GiB. -/
structure ACtx (m : Mem) (v : Abi) (sp F : Nat) : Prop where
  img : Img m
  impure : ImpureAt m
  gp : v.gp = gpV
  sp_v : v.sp = BitVec.ofNat 64 sp
  sp_al : sp % 16 = 0
  sp_lo : heapEnd + F ≤ sp
  sp_hi : sp ≤ 0x100000000

-- Tom/Machine/Api/MpClear.lean
/-- What it leaves. -/
structure Post (m : Mem) (H : List (Nat × Nat)) (sp pa adp : Nat) (a : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa 0 cleared
  heap : Heap M H
  frame : HFrm (lay sp pa adp a) Un.ws H m M

-- Tom/Machine/Api/Alloc.lean
/-- A witness memory for `Heap`. -/
structure Shape (m : Mem) (H : List (Nat × Nat)) (m' : Mem) : Prop where
  agree : Agree H m m'
  wit : ∃ top brk chunks bins, HeapWit m' H top brk chunks bins

/-- `_impure_ptr` holds `&_impure_data`. -/
def ImpureAt (m : Mem) : Prop := ∀ i b, impureBytes[i]? = some b → m[impurePtr + i]? = some b

-- Tom/Machine/Api/MpClear.lean
/-- A cleared `mp_int`: every field zero, no digits. -/
abbrev cleared : MpInt := MpInt.cleared

-- Tom/Machine/Api/Heap.lean
/-- **The frame of an allocating call**: `M` equals `m` outside the named
regions `ws` and the allocator's footprint for the blocks `H` it leaves alone. -/
def HFrm (ρ : ι → Iv) (ws : List ι) (H : List (Nat × Nat)) (m M : Mem) : Prop :=
  Keep (fun x => InAny ρ ws x ∨ Foot H x) m M

-- Tom/Machine/Api/Alloc.lean
/-- `m'` holds `m`'s total reads on the footprint. -/
def Agree (H : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ a, Foot H a → m'[a]? = some ((m[a]?).getD 0)

/-- dlmalloc's invariant in a memory `m'` (`PHeapAt`): the chunk walk,
bins and globals of `Vsa.Sim.DlHeap.HeapAt`, every live block inside a chunk
in use (`exact`: at its payload start), top room, a page-aligned break, the
`binblocks` map in 32 bits. -/
structure HeapWit (m' : Mem) (H : List (Nat × Nat)) (top brk : Nat)
    (chunks : List DlHeap.Chunk) (bins : Nat → List Nat) : Prop where
  heap : DlHeap.HeapAt m' H (fun e => e ∈ H) top brk chunks bins
  top_room : top + 16 ≤ brk
  brk_page : brk % 4096 = 0
  bb_lt : ∀ bb, read64 m' DlHeap.binblocksAddr = some bb → bb < 2 ^ 32

/-- Its contents: `&_impure_data` (`0x800190c8`), little-endian. -/
def impureBytes : List (BitVec 8) := [0xc8, 0x90, 0x01, 0x80, 0, 0, 0, 0]

/-- `_impure_ptr`, the word the wrappers load (`.data`, never written). -/
def impurePtr : Nat := 0x80019510

-- Tom/Spec/Init.lean
/-- A cleared `mp_int` (`mp_clear`): every field zero, no digits. -/
def MpInt.cleared : MpInt := ⟨0, 0, 0, []⟩

-- Tom/Machine/Api/Alloc.lean
/-- `M` equals `m` outside `W`. -/
def Keep (W : Nat → Prop) (m M : Mem) : Prop := ∀ a, ¬ W a → M[a]? = m[a]?

/-- **The allocator's bytes** with live blocks `H` (`heapFoot`): its
globals and the arena outside the blocks. -/
def Foot (H : List (Nat × Nat)) (a : Nat) : Prop :=
  Global a ∨ (heapStart ≤ a ∧ a < heapEnd ∧ ∀ e ∈ H, ¬ InBlk e a)

/-- The allocator's static data (`allocGlobal`, relocated): `__malloc_av_`,
`_impure_data._errno`, `__malloc_sbrk_base` and `__malloc_trim_threshold`,
`brk.0` to `__malloc_top_pad`, `errno`, `__malloc_current_mallinfo`. -/
def Global (a : Nat) : Prop :=
  (0x800188a0 ≤ a ∧ a < 0x800190b0) ∨ (0x800190c8 ≤ a ∧ a < 0x800190cc) ∨
  (0x80019500 ≤ a ∧ a < 0x80019510) ∨ (0x80019530 ≤ a ∧ a < 0x80019550) ∨
  (0x80019558 ≤ a ∧ a < 0x8001955c) ∨ (0x800195b8 ≤ a ∧ a < 0x80019608)

/-- `_end`: the first byte `_sbrk` hands out (`0x80019d10`). -/
abbrev heapStart : Nat := Vsa.Sim.DlHeap.heapStart

/-- Byte `a` lies in the block `e = (p, n)`. -/
def InBlk (e : Nat × Nat) (a : Nat) : Prop := e.1 ≤ a ∧ a < e.1 + e.2

Also used (printed above): `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`)
-/

/-- `mp_clear`: the standard contract -/
theorem Specs.mp_clear_correct_null : Tom.Machine.Api.MpClear.NullStatement :=
  Tom.Machine.Fn.MpClear.correct_null
/-
Machine plumbing: stack reservation `F = 32 + depth`.

-- Tom/Machine/Api/MpClear.lean
/-- **`mp_clear` of a cleared `mp_int`** (`a->dp == NULL`): nothing written. -/
def NullStatement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {pa : Nat} {ra : BitVec 64},
    bytesT8 m (pa + 16) = 0#64 → Ram pa 24 → Img m → ra.toNat % 4 = 0 →
    Triple (At Fn.MpClear.entry (entryL ra pa) m v.keep outp)
      (At ra [(1, ra)] m v.keep outp)
-/

/-! ## `mp_clear_multi`

`void mp_clear_multi(mp_int *mp, ...);`
-/

/-- `mp_clear_multi`: the standard contract -/
theorem Specs.mp_clear_multi_correct : Tom.Machine.Api.MpClearMulti.Statement :=
  Tom.Machine.Fn.MpClearMulti.correct
/-
Machine plumbing: the argument list: the pointers and the terminating `NULL`; stack reservation `F = 96 + MpClear.F`.

-- Tom/Machine/Api/MpClearMulti.lean
/-- **`mp_clear_multi` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp : Nat} {xs : List Arg}
    {ra : BitVec 64}, Pre m v H sp xs ra →
    Triple (At Fn.MpClearMulti.entry ((1, ra) :: argRegs 0 (args (ptrs xs))) m v.keep outp)
      (Ret m v outp H sp xs ra)

-- Tom/Machine/Api/Multi.lean
/-- An `mp_int` argument: struct, digits, value. -/
abbrev Arg := Nat × Nat × MpInt

-- Tom/Machine/Api/MpClearMulti.lean
/-- What `mp_clear_multi(xs…, NULL)` needs. -/
structure Pre (m : Mem) (v : Abi) (H : List (Nat × Nat)) (sp : Nat) (xs : List Arg) (ra : BitVec 64) : Prop where
  live : ∀ x ∈ xs, MpAt m x.1 x.2.1 x.2.2
  heap : Heap m (blocks xs ++ H)
  bpw : (blocks xs).Pairwise fun e e' => Disj e.1 e.2 e'.1 e'.2
  st : Structs (ptrs xs) (sp - F) (F + argLen (xs.length + 1))
  sargs : StackArgs m sp (args (ptrs xs))
  args_hi : sp + argLen (xs.length + 1) ≤ 0x100000000
  ctx : ACtx m v sp F
  ra_al : ra.toNat % 4 = 0

-- Tom/Machine/Api/Multi.lean
/-- `a0..a7` hold the first eight arguments. -/
def argRegs : Nat → List Nat → GRegs
  | _, [] => []
  | i, x :: xs => if i < 8 then (10 + i, BitVec.ofNat 64 x) :: argRegs (i + 1) xs else []

/-- The struct pointers. -/
def ptrs (xs : List Arg) : List Nat := xs.map (·.1)

-- Tom/Machine/Api/MpClearMulti.lean
def Ret (m : Mem) (v : Abi) (outp : Array String) (H : List (Nat × Nat)) (sp : Nat) (xs : List Arg)
    (ra : BitVec 64) (c : Vsa.Machine.Config) : Prop :=
  ∃ M, At ra [(1, ra)] M v.keep outp c ∧ Post m H sp xs M

-- Tom/Machine/Api/Multi.lean
/-- The digit blocks. -/
def blocks (xs : List Arg) : List (Nat × Nat) := xs.map fun x => digBlk x.2.1 x.2.2

/-- The structs of the arguments. -/
structure Structs (ps : List Nat) (lo len : Nat) : Prop where
  ram : ∀ p ∈ ps, Ram p 24
  al : ∀ p ∈ ps, p % 8 = 0
  off : ∀ p ∈ ps, OffHeap p 24
  pw : ps.Pairwise fun p q => Disj p 24 q 24
  stk : ∀ p ∈ ps, Disj p 24 lo len
  code : ∀ p ∈ ps, Disj p 24 textBase textLen

/-- The bytes of stack arguments for `n` arguments. -/
def argLen (n : Nat) : Nat := 8 * (n - 8)

/-- Arguments from the ninth on lie on the caller's stack at `sp`. -/
def StackArgs (m : Mem) (sp : Nat) (xs : List Nat) : Prop :=
  ∀ j (h : j < xs.length), 8 ≤ j → bytesT8 m (sp + 8 * (j - 8)) = BitVec.ofNat 64 xs[j]

-- Tom/Machine/Api/MpClearMulti.lean
/-- What it leaves. -/
structure Post (m : Mem) (H : List (Nat × Nat)) (sp : Nat) (xs : List Arg) (M : Mem) : Prop where
  cleared : ∀ x ∈ xs, MpAt M x.1 0 MpInt.cleared
  heap : Heap M H
  frame : Keep (W xs H sp) m M

/-- What it may write: the stack, the structs and blocks, the footprint. -/
def W (xs : List Arg) (H : List (Nat × Nat)) (sp : Nat) (a : Nat) : Prop :=
  Stk sp F a ∨ (∃ x ∈ xs, InBlk (x.1, 24) a ∨ InBlk (digBlk x.2.1 x.2.2) a) ∨ Foot H a

-- Tom/Machine/Api/Alloc.lean
/-- The stack window `[sp - F, sp)`. -/
def Stk (sp F a : Nat) : Prop := sp - F ≤ a ∧ a < sp

Also used (printed above): `Tom.Machine.Api.Alloc.Heap` (`mp_clear`), `Tom.Machine.Api.Heap.ACtx` (`mp_clear`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.Machine.Api.Alloc.ImpureAt` (`mp_clear`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.MpInt.cleared` (`mp_clear`), `Tom.Machine.Api.Alloc.Keep` (`mp_clear`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.impureBytes` (`mp_clear`), `Tom.Machine.Api.Alloc.impurePtr` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`)
-/

/-! ## `mp_cmp`

`mp_ord mp_cmp(const mp_int *a, const mp_int *b);`
-/

/-- `mp_cmp`: the standard contract -/
theorem Specs.mp_cmp_correct : Tom.Machine.Api.CmpS.Statement :=
  Tom.Machine.Fn.CmpS.correct
/-
Machine plumbing: entry `0x800006ec`.

-- Tom/Machine/Api/CmpS.lean
/-- **`mp_cmp` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {pa adp pb bdp : Nat} {a b : MpInt} {ra : BitVec 64},
    Pre m pa adp pb bdp a b ra →
    Triple (At entry (Fn.CmpS.entryL ra pa pb) m v.keep outp) (Ret m v outp a b ra)

/-- What `mp_cmp(a, b)` needs. -/
structure Pre (m : Mem) (pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  va : a.Valid
  vb : b.Valid
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  ra_al : ra.toNat % 4 = 0
  img : Img m

/-- Back at `ra` with the result in `a0`, memory unchanged. -/
def Ret (m : Mem) (v : Abi) (outp : Array String) (a b : MpInt) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  At ra [(1, ra), (10, BitVec.ofInt 64 (ordCode (cmpS a b)))] m v.keep outp cf

-- Tom/Spec/Cmp.lean
/-- `mp_cmp(a, b)` as the C states it. -/
def cmpS (a b : MpInt) : Ordering :=
  if a.sign ≠ b.sign then (if a.sign = Layout.mpNeg then .lt else .gt)
  else if a.sign = Layout.mpNeg then cmpMag b a else cmpMag a b

Also used (printed above): `Tom.cmpMag` (`mp_add`), `Tom.cmpTop` (`mp_add`)
-/

/-! ## `mp_cmp_d`

`mp_ord mp_cmp_d(const mp_int *a, mp_digit b);`
-/

/-- `mp_cmp_d`: the standard contract -/
theorem Specs.mp_cmp_d_correct : Tom.Machine.Api.CmpD.Statement :=
  Tom.Machine.Fn.CmpD.correct
/-
Machine plumbing: entry `0x80000728`.

-- Tom/Machine/Api/CmpD.lean
/-- **`mp_cmp_d` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {pa adp : Nat} {a : MpInt} {b : Nat} {ra : BitVec 64},
    Pre m pa adp a b ra →
    Triple (At entry (Fn.CmpD.entryL ra pa b) m v.keep outp) (Ret m v outp a b ra)

/-- What `mp_cmp_d(a, b)` needs. -/
structure Pre (m : Mem) (pa adp : Nat) (a : MpInt) (b : Nat) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  va : a.Valid
  ga : MpGeom pa adp a.alloc
  alloc_pos : 1 ≤ a.alloc
  db : b < radix
  ra_al : ra.toNat % 4 = 0
  img : Img m

/-- Back at `ra` with the result in `a0`, memory unchanged. -/
def Ret (m : Mem) (v : Abi) (outp : Array String) (a : MpInt) (b : Nat) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  At ra [(1, ra), (10, BitVec.ofInt 64 (ordCode (cmpD a b)))] m v.keep outp cf

-- Tom/Spec/Cmp.lean
/-- `mp_cmp_d(a, b)` as the C states it. -/
def cmpD (a : MpInt) (b : Nat) : Ordering :=
  if a.sign = Layout.mpNeg then .lt
  else if 1 < a.used then .gt
  else compare (a.digit 0) b
-/

/-! ## `mp_cmp_mag`

`mp_ord mp_cmp_mag(const mp_int *a, const mp_int *b);`
-/

namespace Tom.Machine.Fn.CmpMag
open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg
/-- **`mp_cmp_mag` of two shaped integers**: `a0` is the structural comparison `cmpMag a b`
(`used` first, then the digits from the top), `compare |a| |b|` only when both are valid. -/
theorem _root_.Specs.mp_cmp_mag_correct (ra : BitVec 64) (v : Abi) (outp : Array String) (pa adp pb bdp : Nat)
    (a b : MpInt) (m : Mem) (hra : ra.toNat % 4 = 0) (hP : PreS m pa adp pb bdp a b) :
    Triple (At entry (entryL ra pa pb) m v.keep outp)
      (At ra (retL ra (res (cmpMag a b))) m v.keep outp) :=
  Tom.Machine.Fn.CmpMag.correctS ra v outp pa adp pb bdp a b m hra hP
end Tom.Machine.Fn.CmpMag
/-
-- Tom/Machine/Fn/CmpMag.lean
/-- `mp_cmp_mag`'s loop reads only the shape (digits below `2^28`, `used ≤ alloc < 2^31`): `Pre`
with `Shape` operands (`mp_div`'s step 3.2 compares `t1` with `t2 = [x[i-2], x[i-1], x[i]]`,
`used = 3` and not clamped, `Tom/Spec/DivKnuth.lean` `cmpMag_three`). -/
structure PreS (m : Mem) (pa adp pb bdp : Nat) (a b : MpInt) : Prop where
  ra : MpAt m pa adp a
  rb : MpAt m pb bdp b
  sa : a.Shape
  sb : b.Shape
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  code : CodeAt m mpCmpMagBase mpCmpMagCode

/-- The result register for an ordering. -/
def res (o : Ordering) : BitVec 64 := BitVec.ofInt 64 (ordCode o)

Also used (printed above): `Tom.cmpMag` (`mp_add`), `Tom.cmpTop` (`mp_add`)
-/

namespace Tom.Machine.Fn.CmpMag
open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg
/-- **`mp_cmp_mag` on the machine.** From its entry with `a0 = pa`, `a1 = pb`,
the machine returns to `ra`, keeping the callee-saved registers and memory,
with `a0` the `mp_ord` code of `compare |a| |b|`. -/
theorem _root_.Specs.mp_cmp_mag_correct_valid (ra : BitVec 64) (v : Abi) (outp : Array String) (pa adp pb bdp : Nat)
    (a b : MpInt) (m : Mem) (hra : ra.toNat % 4 = 0) (hP : Pre m pa adp pb bdp a b) :
    Triple (At entry (entryL ra pa pb) m v.keep outp)
      (At ra (retL ra (BitVec.ofInt 64 (ordCode (compare a.mag b.mag)))) m v.keep outp) :=
  Tom.Machine.Fn.CmpMag.correct ra v outp pa adp pb bdp a b m hra hP
end Tom.Machine.Fn.CmpMag
/-
-- Tom/Machine/Fn/CmpMag.lean
/-- What `mp_cmp_mag(a, b)` needs: both `mp_int`s valid, in memory with their
geometry, and the code in memory. -/
structure Pre (m : Mem) (pa adp pb bdp : Nat) (a b : MpInt) : Prop where
  ra : MpAt m pa adp a
  rb : MpAt m pb bdp b
  va : a.Valid
  vb : b.Valid
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  code : CodeAt m mpCmpMagBase mpCmpMagCode
-/

/-! ## `mp_cnt_lsb`

`int mp_cnt_lsb(const mp_int *a);`
-/

/-- `mp_cnt_lsb`: the standard contract -/
theorem Specs.mp_cnt_lsb_correct : Tom.Machine.Api.CntLsb.Statement :=
  Tom.Machine.Fn.CntLsb.correct
/-
Machine plumbing: entry `0x80005054`.

-- Tom/Machine/Api/CntLsb.lean
/-- **`mp_cnt_lsb` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {pa adp : Nat} {a : MpInt} {ra : BitVec 64},
    Pre m pa adp a ra →
    Triple (At entry (Fn.CntLsb.entryL ra pa) m v.keep outp) (Ret m v outp a ra)

structure Pre (m : Mem) (pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  va : a.Valid
  ga : MpGeom pa adp a.alloc
  bits : Layout.digitBits * a.used < 2 ^ 31
  ra_al : ra.toNat % 4 = 0
  img : Img m

def Ret (m : Mem) (v : Abi) (outp : Array String) (a : MpInt) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  At ra [(1, ra), (10, BitVec.ofNat 64 (cntLsb a))] m v.keep outp cf

-- Tom/Spec/Bits.lean
/-- `mp_cnt_lsb(a)` as the C states it. -/
def cntLsb (a : MpInt) : Nat :=
  if a.used = 0 then 0
  else Layout.digitBits * firstNz a.digit a.used +
    (if a.digit (firstNz a.digit a.used) % 2 = 1 then 0 else lsbInner (a.digit (firstNz a.digit a.used)))

/-- The index of the lowest nonzero digit below `n` (`n` if none). -/
def firstNz (dig : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if firstNz dig n < n then firstNz dig n else if dig n ≠ 0 then n else n + 1

/-- The C's nibble loop: `x += lnz[q & 15]; q >>= 4` while the nibble was zero. -/
def lsbInner (q : Nat) : Nat :=
  if q % 16 = 0 ∧ q ≠ 0 then 4 + lsbInner (q / 16) else lnzTab (q % 16)

/-- `lnz` of `bn_mp_cnt_lsb.c`: the trailing zeros of a nibble (`4` for `0`). -/
def lnzTab (j : Nat) : Nat := [4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0].getD j 0
-/

/-! ## `mp_copy`

`mp_err mp_copy(const mp_int *a, mp_int *b);`
-/

/-- `mp_copy(a, b)` growing `b`: the allocating contract -/
theorem Specs.mp_copy_correct : Tom.Machine.Api.MpCopyG.Statement :=
  Tom.Machine.Fn.MpCopyGG5.correct
/-
Machine plumbing: entry `0x800007e0`; the arguments: `a0 = a`, `a1 = b` (`gp` for the allocator); stack reservation `F = 32 + MpGrow.F`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/MpCopyG.lean
def Statement : Prop := Standard.Statement Res Q (site .bD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp : Nat); (a b : MpInt); (H : List (Nat × Nat))

/-- What `mp_copy(a, b)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The loop reads `a`'s digits below `used`, `memset` zeroes `b`'s old digits up to `used`. -/
  sa : p.a.Shape
  sb : p.b.Shape
  /-- `b->sign := a->sign` (an `int` word). -/
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  /-- `a`'s digits: an initialised `mp_int`'s, nonempty. -/
  apos : 0 < p.a.alloc
  /-- Distinct (`a == b` returns at once, D6). -/
  ne : p.pa ≠ p.pb
  /-- `b`'s digits are `realloc`'s block: live and nonempty. -/
  bpos : 0 < p.b.alloc
  boff : OffHeap p.pb 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.b.alloc < p.a.used
  | some (_, b') => CopyPost p.a (copyIn p.a p.b) b'

-- Tom/Spec/Set.lean
/-- What `mp_copy(a, b)` leaves in `b` (distinct operands, `a->used ≤ b->alloc`). -/
structure CopyPost (a b b' : MpInt) : Prop where
  alloc : b'.alloc = b.alloc
  len : b'.digits.length = b.alloc
  used : b'.used = a.used
  sign : b'.sign = a.sign
  digit : ∀ i, b'.digit i = if i < a.used then a.digit i else if i < b.used then 0 else b.digit i
theorem CopyPost.specG {a b b' : MpInt} (ha : a.Valid) (hb : b.Shape) (h : CopyPost a (copyIn a b) b') :
    b'.Valid ∧ b'.mag = a.mag ∧ b'.val = a.val := …  -- proved in Tom/Spec/CopyGStep.lean
theorem CopyPost.valid {a b b' : MpInt} (ha : a.Valid) (hb : b.Shape) (hroom : a.used ≤ b.alloc)
    (h : CopyPost a b b') : b'.Valid ∧ b'.mag = a.mag := …  -- proved in Tom/Spec/Set.lean
theorem CopyPost.spec {a b b' : MpInt} (ha : a.Valid) (hb : b.Shape) (hroom : a.used ≤ b.alloc)
    (h : CopyPost a b b') : b'.Valid ∧ b'.mag = a.mag ∧ b'.val = a.val := …  -- proved in Tom/Spec/Set.lean

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.copyIn` (`mp_abs`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.MpInt.ofDigits` (`mp_abs`)
-/

/-- `mp_copy`: the standard contract -/
theorem Specs.mp_copy_correct_room : Tom.Machine.Api.MpCopy.Statement :=
  Tom.Machine.Fn.MpCopy.correct
/-
Machine plumbing: entry `0x800007e0`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/MpCopy.lean
/-- **`mp_copy` on the machine** (distinct operands). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    Pre m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.MpCopy.entryL ra s0 sp pa pb) m v.keepR outp) (Ret m v outp sp pa adp pb bdp a b ra s0)

/-- What `mp_copy(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  sa : a.Shape
  sb : b.Shape
  asign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  room : a.used ≤ b.alloc
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp a b) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ b' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp a b b' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp : Nat) (a b b' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pb bdp b'
  copy : CopyPost a b b'
  frame : Frm (lay sp pa adp pb bdp a b) ws m M

Also used (printed above): `Tom.CopyPost` (`mp_copy`)
-/

/-- `mp_copy`: the standard contract -/
theorem Specs.mp_copy_correct_alias : Tom.Machine.Api.MpCopy.AliasStatement :=
  Tom.Machine.Fn.MpCopy.alias_correct
/-
Machine plumbing: entry `0x800007e0`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/MpCopy.lean
/-- **`mp_copy(a, a)` on the machine**: `MP_OKAY`, nothing written. -/
def AliasStatement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa : Nat} {ra s0 : BitVec 64},
    ra.toNat % 4 = 0 → Img m →
    Triple (At entry (Fn.MpCopy.entryL ra s0 sp pa pa) m v.keepR outp)
      (At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] m v.keepR outp)
-/

/-! ## `mp_count_bits`

`int mp_count_bits(const mp_int *a);`
-/

/-- `mp_count_bits`: the standard contract -/
theorem Specs.mp_count_bits_correct : Tom.Machine.Api.CountBits.Statement :=
  Tom.Machine.Fn.CountBits.correct
/-
Machine plumbing: entry `0x800050f0`.

-- Tom/Machine/Api/CountBits.lean
/-- **`mp_count_bits` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {pa adp : Nat} {a : MpInt} {ra : BitVec 64},
    Pre m pa adp a ra →
    Triple (At entry (Fn.CountBits.entryL ra pa) m v.keep outp) (Ret m v outp a ra)

/-- What `mp_count_bits(a)` needs. -/
structure Pre (m : Mem) (pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  va : a.Valid
  ga : MpGeom pa adp a.alloc
  bits : Layout.digitBits * a.used < 2 ^ 31
  ra_al : ra.toNat % 4 = 0
  img : Img m

/-- Back at `ra` with the result in `a0`, memory unchanged. -/
def Ret (m : Mem) (v : Abi) (outp : Array String) (a : MpInt) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  At ra [(1, ra), (10, BitVec.ofNat 64 (countBits a))] m v.keep outp cf

-- Tom/Spec/Bits.lean
/-- `mp_count_bits(a)` as the C states it. -/
def countBits (a : MpInt) : Nat :=
  if a.used = 0 then 0 else Layout.digitBits * (a.used - 1) + bitLen (a.digit (a.used - 1))

/-- The number of bits of `q`: how often `q >>= 1` runs before `q = 0`. -/
def bitLen (q : Nat) : Nat := if q = 0 then 0 else Nat.log2 q + 1
-/

/-! ## `mp_div`

`mp_err mp_div(const mp_int *a, const mp_int *b, mp_int *c, mp_int *d);`

Coverage: contract (c, d non-NULL).
-/

/-- `mp_div(a, b, c, d)`: the allocating contract, `c` and `d` non-NULL -/
theorem Specs.mp_div_correct : Tom.Machine.Api.MpDiv.Statement :=
  Tom.Machine.Fn.MpDivG5.correct
/-
Machine plumbing: entry `0x80000898`; the arguments: `a0 = a`, `a1 = b`, `a2 = c`, `a3 = d` (`gp` for the allocator); stack reservation `F = 272 + MpInitCopy.F`; regions stk aS aD bS bD cS cD dS dD code; written [.stk, .cS, .cD, .dS, .dD].

-- Tom/Machine/Api/MpDiv.lean
/-- **`mp_div(a, b, c, d)` on the machine**, `c`, `d` non-NULL, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        Post2 (lay p) ws .cD .dD (out p x) (siteC p x) (siteD p x) (hin p) (hout p x) m M)

structure P where  (sp pa adp pb bdp pc cdp pd ddp : Nat); (a b c d : MpInt); (H : List (Nat × Nat))

/-- What `mp_div(a, b, c, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_cmp_mag`, `mp_init_copy` and the long division read `a`, `b` as valid integers. -/
  va : p.a.Valid
  vb : p.b.Valid
  /-- `b ≠ 0`: the `MP_VAL` return (`8a8`) is not covered. -/
  bnz : 0 < p.b.used
  /-- `mp_count_bits(&y)` is an `int` (`Std.cntBits`). -/
  bits : Layout.digitBits * p.b.used < 2 ^ 31
  /-- `mp_init_size(&q, a->used + 2)` and every `int` index of the loops (`i ≤ a->used`,
  `x.used ≤ a->used + 1`, byte offsets `4 i`) fit. -/
  au : p.a.used + 3 < 2 ^ 30
  /-- D5 for the small case: `mp_copy(a, d)` does not call `mp_grow`. -/
  droom : p.a.used ≤ p.d.alloc
  /-- `c`'s old digits are freed by `mp_clear(&q)` after the exchange: a live, nonempty block. -/
  cpos : 0 < p.c.alloc
  /-- `d`'s old digits are freed by `mp_clear(&x)` after the exchange: a live, nonempty block. -/
  dpos : 0 < p.d.alloc
  /-- `c != NULL`: the branches at `974` and `b64` are taken the non-NULL way. -/
  cnn : p.pc ≠ 0
  /-- `d != NULL`: the branches at `960` and `b90` are taken the non-NULL way. -/
  dnn : p.pd ≠ 0
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24
  doff : OffHeap p.pd 24
  /-- `mp_zero(c)` in the small case (`Std.mpZero`: the `memset` over `c->alloc` digits). -/
  csh : p.c.Shape
  /-- `mp_copy(a, d)` in the small case zeroes `d`'s digits only up to the old `d->used`: the
  ones above must be zero already for `d' = a` (`DivRem.small`; refutable without). -/
  dsh : p.d.Shape
  /-- `mp_init_copy(&x, a)` copies from a live block (`MpInitCopy.Pre.live`), nonempty. -/
  ablk : digBlk p.adp p.a ∈ p.H
  apos : 0 < p.a.alloc
  /-- `mp_init_copy(&y, b)` copies from a live block. -/
  bblk : digBlk p.bdp p.b ∈ p.H

/-- What `c` and `d` hold, with the case the code took. -/
def Q (p : P) : Out → Prop
  | .mem => p.b.mag ≤ p.a.mag
  | .small c' d' => p.a.mag < p.b.mag ∧ DivQuot p.a p.b p.c c' ∧ DivRem p.a p.b p.d d'
  | .big _ c' _ d' => p.b.mag ≤ p.a.mag ∧ DivQuot p.a p.b p.c c' ∧ DivRem p.a p.b p.d d'

/-- What an allocating function with two re-placed sites `sc`, `sd` leaves (`HPost` with a
second site): the written regions but the sites witnessed in place, each site at its new
placement, the two placements apart, the frame from the entry, the heap after, and the
allocator's footprint grown only by the sites' old blocks. -/
structure Post2 {R : Type} (lay : R → Iv) (ws : List R) (sc sd : R) (out : R → Kind) (Jc Jd : Iv)
    (hin hout : List (Nat × Nat)) (m M : Mem) : Prop where
  wit : ∀ r, r ∈ ws → r ≠ sc → r ≠ sd → (out r).Fits (lay r) ∧ (out r).Wit (lay r) M
  wsc : (out sc).Fits Jc ∧ (out sc).Wit Jc M
  wsd : (out sd).Fits Jd ∧ (out sd).Wit Jd M
  placec : Place hin (lay sc) Jc
  placed : Place hin (lay sd) Jd
  sep : Jc.Disj Jd
  frame : HFrm lay ws hin m M
  heap : AHeap M hout
  foot : ∀ a, Foot hout a → Foot hin a ∨ (lay sc).In a ∨ (lay sd).In a
  offc : Off Jc hout
  offd : Off Jd hout

/-- Where `c`'s digits are after. -/
def siteC (p : P) : Out → Iv
  | .big qc c' _ _ => ⟨qc, 4 * c'.alloc⟩
  | _ => lay p .cD

/-- Where `d`'s digits are after. -/
def siteD (p : P) : Out → Iv
  | .big _ _ qd d' => ⟨qd, 4 * d'.alloc⟩
  | _ => lay p .dD

/-- What `mp_div` returns: `MP_MEM`, the copy/zero case in place, or the long division with
`c'` at `q`'s block `qc` and `d'` at `x`'s block `qd`. -/
inductive Out
  | mem
  | small (c' d' : MpInt)
  | big (qc : Nat) (c' : MpInt) (qd : Nat) (d' : MpInt)

-- Tom/Spec/Div.lean
/-- What `mp_div(a, b, c, d)` (`b ≠ 0`) leaves in `c` (non-`NULL`). -/
structure DivQuot (a b c c' : MpInt) : Prop where
  small : a.mag < b.mag → ClampedTo c' c.alloc (fun _ => 0) 0 Layout.mpZpos
  big : b.mag ≤ a.mag → DivBigQuot a b c'
theorem DivQuot.spec {a b c c' : MpInt} (ha : a.Valid) (hb : b.Valid) (hb0 : 0 < b.used)
    (hau : a.used + 2 < 2 ^ 31) (hc : c.alloc < 2 ^ 31) (h : DivQuot a b c c') :
    c'.Valid ∧ c'.mag = a.mag / b.mag ∧ c'.val = a.val.tdiv b.val := …  -- proved in Tom/Spec/Div.lean

/-- What `mp_div(a, b, c, d)` (`b ≠ 0`) leaves in `d` (non-`NULL`). -/
structure DivRem (a b d d' : MpInt) : Prop where
  small : a.mag < b.mag → ClampedTo d' d.alloc a.digit a.used a.sign
  big : b.mag ≤ a.mag → DivBigRem a b d'
theorem DivRem.spec {a b d d' : MpInt} (ha : a.Valid) (hb : b.Valid) (hb0 : 0 < b.used)
    (hroom : a.used ≤ d.alloc) (hd : d.alloc < 2 ^ 31) (h : DivRem a b d d') :
    d'.Valid ∧ d'.mag = a.mag % b.mag ∧ d'.val = a.val.tmod b.val := …  -- proved in Tom/Spec/Div.lean

-- Tom/Spec/Div2d.lean
/-- An `mp_int` with digit function `f`, `used` clamped from `n`, sign `s` unless it
is zero (`mp_clamp`), and `al` digits allocated. -/
structure ClampedTo (c' : MpInt) (al : Nat) (f : Nat → Nat) (n s : Nat) : Prop where
  alloc : c'.alloc = al
  len : c'.digits.length = al
  digit : c'.digit = f
  used : c'.used = clampUsed f n
  sign : c'.sign = if c'.used = 0 then Layout.mpZpos else s
theorem ClampedTo.spec {c' : MpInt} {al n s : Nat} {f : Nat → Nat} (h : ClampedTo c' al f n s)
    (hf : ∀ i, f i < radix) (hz : ∀ i, n ≤ i → f i = 0) (hn : n ≤ al) (hal : al < 2 ^ 31)
    (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg) :
    c'.Valid ∧ c'.mag = natUpTo f n ∧
      c'.val = if s = Layout.mpNeg then -(natUpTo f n : Int) else natUpTo f n := …  -- proved in Tom/Spec/Div2d.lean
theorem ClampedTo.spec_natDigit {c' : MpInt} {al n s N : Nat} (h : ClampedTo c' al (natDigit N) n s)
    (hN : N < radix ^ n) (hn : n ≤ al) (hal : al < 2 ^ 31) (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg) :
    c'.Valid ∧ c'.mag = N ∧ c'.val = if s = Layout.mpNeg then -(N : Int) else N := …  -- proved in Tom/Spec/Div2d.lean

-- Tom/Spec/Div.lean
/-- The quotient of the big case: `q` (`a->used + 2` digits from `mp_init_size`, the
digits of `|a| / |b|`), clamped, with the sign `neg` written after `mp_exch`. -/
structure DivBigQuot (a b c' : MpInt) : Prop where
  alloc : c'.alloc = max 3 (a.used + 2)
  len : c'.digits.length = max 3 (a.used + 2)
  digit : c'.digit = natDigit (a.mag / b.mag)
  used : c'.used = clampUsed (natDigit (a.mag / b.mag)) (a.used + 2)
  sign : c'.sign = divSign a.sign b.sign

/-- The remainder of the big case: `x` after `mp_div_2d(&x, norm, &x, NULL)`. -/
structure DivBigRem (a b d' : MpInt) : Prop where
  valid : d'.Valid
  mag : d'.mag = a.mag % b.mag
  sign : d'.sign = if d'.used = 0 then Layout.mpZpos else a.sign

-- Tom/Spec/Div2d.lean
/-- Digit `j` of `N` in base `radix`. -/
def natDigit (N j : Nat) : Nat := N / radix ^ j % radix

-- Tom/Spec/Div.lean
/-- The sign `mp_div` gives the quotient. -/
def divSign (sa sb : Nat) : Nat := if sa = sb then Layout.mpZpos else Layout.mpNeg

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Heap.HFrm` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.Alloc.Keep` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`), `Tom.clampUsed` (`mp_add`)
-/

/-- `mp_div(a, b, a, NULL)`: the quotient in place of the dividend -/
theorem Specs.mp_div_correct_quot_inplace : Tom.Machine.Api.MpDivQ.Statement :=
  Tom.Machine.Fn.MpDivQG5.correct
/-
Machine plumbing: entry `0x80000898`; the arguments: `a0 = a`, `a1 = b`, `a2 = a`, `a3 = NULL`; stack reservation `F = 272 + MpInitCopy.F`; regions stk aS aD bS bD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MpDivQ.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp : Nat); (a b : MpInt); (H : List (Nat × Nat))

/-- What `mp_div(a, b, a, NULL)` needs (`Api.MpDiv.Res` with `c = a`, without `d`'s fields). -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_cmp_mag`, `mp_init_copy` and the long division read `a`, `b` as valid integers. -/
  va : p.a.Valid
  vb : p.b.Valid
  /-- `b ≠ 0`: the `MP_VAL` return is not covered. -/
  bnz : 0 < p.b.used
  /-- `mp_count_bits(&y)` is an `int`. -/
  bits : Layout.digitBits * p.b.used < 2 ^ 31
  /-- `mp_init_size(&q, a->used + 2)` and the loops' `int` indices fit. -/
  au : p.a.used + 3 < 2 ^ 30
  /-- `a`'s old digits are freed by `mp_clear(&q)` after the exchange: a nonempty block (live: the
  front of `hin`). -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  /-- `mp_init_copy(&y, b)` copies from a live block. -/
  bblk : digBlk p.bdp p.b ∈ p.H

/-- What `a` holds, -/
def Q (p : P) : Out → Prop
  | .mem => p.b.mag ≤ p.a.mag
  | .ok _ a' => DivQuot p.a p.b p.a a' ∧ 0 < a'.alloc

/-- `MP_MEM`, the zero in place, or the quotient at `q`'s block `qa`. -/
inductive Out
  | mem
  | ok (q : Nat) (a' : MpInt)

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.DivQuot` (`mp_div`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.ClampedTo` (`mp_div`), `Tom.DivBigQuot` (`mp_div`), `Tom.clampUsed` (`mp_add`), `Tom.natDigit` (`mp_div`), `Tom.divSign` (`mp_div`)
-/

/-- `mp_div(a, b, NULL, d)`: the remainder only -/
theorem Specs.mp_div_correct_rem : Tom.Machine.Api.MpDivR.Statement :=
  Tom.Machine.Fn.MpDivRG5.correct
/-
Machine plumbing: entry `0x80000898`; the arguments: `a0 = a`, `a1 = b`, `a2 = NULL`, `a3 = d`; stack reservation `F = 272 + MpInitCopy.F`; regions stk aS aD bS bD dS dD code; written [.stk, .dS, .dD].

-- Tom/Machine/Api/MpDivR.lean
def Statement : Prop := Standard.Statement Res Q (site .dD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp pd ddp : Nat); (a b d : MpInt); (H : List (Nat × Nat))

/-- What `mp_div(a, b, NULL, d)` needs (`Api.MpDiv.Res` without `c`'s fields). -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_cmp_mag`, `mp_init_copy` and the long division read `a`, `b` as valid integers. -/
  va : p.a.Valid
  vb : p.b.Valid
  /-- `b ≠ 0`: the `MP_VAL` return is not covered. -/
  bnz : 0 < p.b.used
  /-- `mp_count_bits(&y)` is an `int`. -/
  bits : Layout.digitBits * p.b.used < 2 ^ 31
  /-- `mp_init_size(&q, a->used + 2)` and the loops' `int` indices fit. -/
  au : p.a.used + 3 < 2 ^ 30
  /-- D5 for the small case only: `mp_copy(a, d)` does not call `mp_grow`. -/
  droom : p.a.mag < p.b.mag → p.a.used ≤ p.d.alloc
  /-- `d`'s old digits are freed by `mp_clear(&x)` after the exchange: a live, nonempty block. -/
  dpos : 0 < p.d.alloc
  /-- `d != NULL`: the branches at `960` and `b90` are taken the non-NULL way. -/
  dnn : p.pd ≠ 0
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  doff : OffHeap p.pd 24
  /-- `mp_copy(a, d)` zeroes `d`'s digits only up to the old `d->used`. -/
  dsh : p.d.Shape
  /-- `mp_init_copy(&x, a)`, `mp_init_copy(&y, b)` copy from live blocks. -/
  ablk : digBlk p.adp p.a ∈ p.H
  apos : 0 < p.a.alloc
  bblk : digBlk p.bdp p.b ∈ p.H

/-- What `d` holds, -/
def Q (p : P) : Out → Prop
  | .mem => p.b.mag ≤ p.a.mag
  | .ok _ d' => DivRem p.a p.b p.d d' ∧ 0 < d'.alloc

/-- `MP_MEM`, the copy in place, or the remainder at `x`'s block `qd`. -/
inductive Out
  | mem
  | ok (q : Nat) (d' : MpInt)

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.DivRem` (`mp_div`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.ClampedTo` (`mp_div`), `Tom.DivBigRem` (`mp_div`), `Tom.clampUsed` (`mp_add`)
-/

/-! ## `mp_div_2`

`mp_err mp_div_2(const mp_int *a, mp_int *b);`
-/

/-- `mp_div_2`: the standard contract -/
theorem Specs.mp_div_2_correct : Tom.Machine.Api.Div2.Statement :=
  Tom.Machine.Fn.Div2.correct
/-
Machine plumbing: entry `0x80005134`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/Div2.lean
/-- **`mp_div_2` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat}
    {a b : MpInt} {ra s0 : BitVec 64}, Pre m sp pa adp pb bdp a b ra →
    Triple (At entry (entryL ra s0 sp pa pb) m v.keepR outp)
      (Ret m v outp sp pa adp pb bdp a b ra s0)

/-- What `mp_div_2(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  va : a.Valid
  sb : b.Shape
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  room : a.used ≤ b.alloc
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp a b) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ b' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp a b b' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp : Nat) (a b b' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pb bdp b'
  div2 : Div2Post a b b'
  frame : Frm (lay sp pa adp pb bdp a b) ws m M

-- Tom/Spec/Shift.lean
/-- What `mp_div_2(a, b)` leaves in `b` when `b` has room
(`b->alloc ≥ a->used`, so `mp_grow` is not called): the shifted digits,
`used` clamped from `a->used`, `a`'s sign reset if the result is zero. -/
structure Div2Post (a b b' : MpInt) : Prop where
  alloc : b'.alloc = b.alloc
  len : b'.digits.length = b.alloc
  digit : b'.digit = div2Digits a
  used : b'.used = clampUsed (div2Digits a) a.used
  sign : b'.sign = if b'.used = 0 then Layout.mpZpos else a.sign
theorem Div2Post.spec {a b b' : MpInt} (ha : a.Valid) (hroom : a.used ≤ b.alloc)
    (hb : b.alloc < 2 ^ 31) (h : Div2Post a b b') :
    b'.Valid ∧ b'.mag = a.mag / 2 ∧ b'.val = a.val.tdiv 2 := …  -- proved in Tom/Spec/Shift.lean

/-- The C's digit `x` of `mp_div_2`: `a[x] >> 1` with the low bit of
`a[x + 1]` as its top bit (`r << (MP_DIGIT_BIT - 1)`). -/
def div2Digits (a : MpInt) (i : Nat) : Nat := a.digit i / 2 + 2 ^ 27 * (a.digit (i + 1) % 2)

Also used (printed above): `Tom.clampUsed` (`mp_add`)
-/

/-- `mp_div_2`: the standard contract -/
theorem Specs.mp_div_2_correct_inplace : Tom.Machine.Api.Div2.StatementInPlace :=
  Tom.Machine.Fn.Div2.correct_inplace
/-
Machine plumbing: entry `0x80005134`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/Div2.lean
/-- **`mp_div_2(a, a)` on the machine.** -/
def StatementInPlace : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {ra s0 : BitVec 64},
    PreI m sp pa adp a ra →
    Triple (At entry (entryL ra s0 sp pa pa) m v.keepR outp) (RetI m v outp sp pa adp a ra s0)

/-- What `mp_div_2(a, a)` needs. -/
structure PreI (m : Mem) (sp pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  va : a.Valid
  ga : MpGeom pa adp a.alloc
  room : a.used ≤ a.alloc
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (layI sp pa adp a) Un.isW

def RetI (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostI m sp pa adp a a' M

/-- The regions of the in-place call (`Api/Un.lean`: `a` written). -/
abbrev layI (sp pa adp : Nat) (a : MpInt) := Un.lay 32 sp pa adp a

/-- What it leaves. -/
structure PostI (m : Mem) (sp pa adp : Nat) (a a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  div2 : Div2Post a a a'
  frame : Frm (layI sp pa adp a) Un.ws m M

Also used (printed above): `Tom.Div2Post` (`mp_div_2`), `Tom.div2Digits` (`mp_div_2`), `Tom.clampUsed` (`mp_add`)
-/

/-! ## `mp_div_2d`

`mp_err mp_div_2d(const mp_int *a, int b, mp_int *c, mp_int *d);`
-/

/-- `mp_div_2d(a, b, c, NULL)`: the standard contracts -/
theorem Specs.mp_div_2d_correct : Tom.Machine.Api.MpDiv2d.Statement :=
  Tom.Machine.Fn.MpDiv2d.correct
/-
Machine plumbing: entry `0x8000520c`.

-- Tom/Machine/Api/MpDiv2d.lean
/-- **`mp_div_2d(a, b, c, NULL)` on the machine** (distinct operands). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat} {c : MpInt}
    {ra s0 : BitVec 64}, Pre m sp pa adp pc cdp a b c ra →
    Triple (At entry (Fn.MpDiv2d.entryL ra s0 sp pa b pc) m v.keepR outp)
      (Ret m v outp sp pa adp pc cdp a b c ra s0)

/-- What `mp_div_2d(a, b, c, NULL)` needs (distinct operands). -/
structure Pre (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rc : MpAt m pc cdp c
  va : a.Valid
  sc : c.Shape
  ga : MpGeom pa adp a.alloc
  gc : MpGeom pc cdp c.alloc
  b_lt : b < 2 ^ 31
  room : a.used ≤ c.alloc
  rs : Ram (sp - 96) 96
  sp_al : sp % 16 = 0
  sp_ge : 96 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pc cdp a c) Two.isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pc cdp a b c c' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  div : Div2dPost a b c c'
  frame : Frm (lay sp pa adp pc cdp a c) Two.ws m M

-- Tom/Spec/Div2d.lean
/-- What `mp_div_2d(a, sh, c, NULL)` leaves in `c` when `c->alloc ≥ a->used` (D5):
the shifted digits, `used` clamped from `a->used - D`, `a`'s sign unless zero. (With
`d != NULL` it also leaves `Mod2dPost a sh d d'` in `d`.) The in-place call
`mp_div_2d(x, sh, x, NULL)` (in `mp_div`) leaves the same state with `c = a`. -/
def Div2dPost (a : MpInt) (sh : Nat) (c c' : MpInt) : Prop :=
  ClampedTo c' c.alloc (div2dDigit a sh) (a.used - sh / Layout.digitBits) a.sign
theorem Div2dPost.spec {a c c' : MpInt} {sh : Nat} (ha : a.Valid) (hroom : a.used ≤ c.alloc)
    (hc : c.alloc < 2 ^ 31) (h : Div2dPost a sh c c') :
    c'.Valid ∧ c'.mag = a.mag / 2 ^ sh ∧
      c'.val = if a.sign = Layout.mpNeg then -((a.mag / 2 ^ sh : Nat) : Int) else (a.mag / 2 ^ sh : Nat) := …  -- proved in Tom/Spec/Div2d.lean

/-- Digit `j` of `mp_div_2d(a, sh, c, NULL)`: after `mp_rshd(c, D)` digit `j` is
`a[j + D]`; the bit loop shifts it right by `d` and ORs in the low `d` bits of the
digit above, shifted up by `28 - d`. -/
def div2dDigit (a : MpInt) (sh j : Nat) : Nat :=
  a.digit (j + sh / Layout.digitBits) / 2 ^ (sh % Layout.digitBits) +
    a.digit (j + sh / Layout.digitBits + 1) % 2 ^ (sh % Layout.digitBits) *
      2 ^ (Layout.digitBits - sh % Layout.digitBits)

Also used (printed above): `Tom.ClampedTo` (`mp_div`), `Tom.clampUsed` (`mp_add`)
-/

/-- `mp_div_2d(a, b, c, NULL)`: the standard contracts -/
theorem Specs.mp_div_2d_correct_inplace : Tom.Machine.Api.MpDiv2d.StatementInPlace :=
  Tom.Machine.Fn.MpDiv2d.correct_inplace
/-
Machine plumbing: entry `0x8000520c`.

-- Tom/Machine/Api/MpDiv2d.lean
/-- **`mp_div_2d(a, b, a, NULL)` on the machine** (in place). -/
def StatementInPlace : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {b : Nat} {ra s0 : BitVec 64},
    PreI m sp pa adp a b ra →
    Triple (At entry (Fn.MpDiv2d.entryL ra s0 sp pa b pa) m v.keepR outp) (RetI m v outp sp pa adp a b ra s0)

/-- What `mp_div_2d(a, b, a, NULL)` needs. -/
structure PreI (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  va : a.Valid
  ga : MpGeom pa adp a.alloc
  b_lt : b < 2 ^ 31
  rs : Ram (sp - 96) 96
  sp_al : sp % 16 = 0
  sp_ge : 96 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (layI sp pa adp a) Un.isW

def RetI (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (b : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostI m sp pa adp a b a' M

abbrev layI (sp pa adp : Nat) (a : MpInt) := Un.lay 96 sp pa adp a

/-- What it leaves. -/
structure PostI (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  div : Div2dPost a b a a'
  frame : Frm (layI sp pa adp a) Un.ws m M

Also used (printed above): `Tom.Div2dPost` (`mp_div_2d`), `Tom.ClampedTo` (`mp_div`), `Tom.div2dDigit` (`mp_div_2d`), `Tom.clampUsed` (`mp_add`)
-/

/-- `mp_div_2d(a, b, c, a)` growing `c`: the allocating contract -/
theorem Specs.mp_div_2d_correct_rem : Tom.Machine.Api.MpDiv2dRG.Statement :=
  Tom.Machine.Fn.MpDiv2dRGG5.correct
/-
Machine plumbing: entry `0x8000520c`; the arguments: `a0 = a`, `a1 = b`, `a2 = c`, `a3 = d = a` (`gp` for the allocator); stack reservation `F = 64 + MpCopyG.F`; regions stk aS aD cS cD code; written [.stk, .aS, .aD, .cS, .cD].

-- Tom/Machine/Api/MpDiv2dRG.lean
def Statement : Prop := Standard.Statement Res Q (site .cD)  -- the standard shape (top of file)

structure P where  (sp pa adp pc cdp : Nat); (a : MpInt); (b : Nat); (c : MpInt); (H : List (Nat × Nat))

/-- What `mp_div_2d(a, b, c, a)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  sc : p.c.Shape
  /-- `b > 0`: the shifting path. -/
  b_pos : 0 < p.b
  /-- The C's `int b`. -/
  b_lt : p.b < 2 ^ 31
  /-- `mp_mod_2d`'s `a->used * MP_DIGIT_BIT` does not overflow. -/
  bits : Layout.digitBits * p.a.used < 2 ^ 31
  /-- `a`, `c` distinct, nonempty digit arrays (`c`'s: `realloc`'s block). -/
  ne : p.pa ≠ p.pc
  apos : 0 < p.a.alloc
  cpos : 0 < p.c.alloc
  coff : OffHeap p.pc 24

def Q (p : P) : X → Prop
  | none => p.c.alloc < p.a.used
  | some (_, a', c') => Ok p a' c'

/-- `MP_MEM` (`none`), or `MP_OKAY` with `a'` in place and `c'`'s digits at `q`. -/
abbrev X := Option (Nat × MpInt × MpInt)

/-- `MP_OKAY`: the remainder in `a`, the quotient in `c`. -/
structure Ok (p : P) (a' c' : MpInt) : Prop where
  mod : Mod2dPost p.a p.b p.a a'
  div : Div2dPost p.a p.b (copyIn p.a p.c) c'

-- Tom/Spec/Div2d.lean
/-- What `mp_mod_2d(a, sh, c)` leaves in `c` when `c->alloc ≥ a->used` (D5): the
masked digits, `used` clamped from `a->used`, `a`'s sign unless zero. (For `sh = 0`
the C calls `mp_zero(c)`; for `sh ≥ 28 * a->used` it is `mp_copy(a, c)`: both are
this state.) -/
def Mod2dPost (a : MpInt) (sh : Nat) (c c' : MpInt) : Prop :=
  ClampedTo c' c.alloc (mod2dDigit a sh) a.used a.sign
theorem Mod2dPost.spec {a c c' : MpInt} {sh : Nat} (ha : a.Valid) (hroom : a.used ≤ c.alloc)
    (hc : c.alloc < 2 ^ 31) (h : Mod2dPost a sh c c') :
    c'.Valid ∧ c'.mag = a.mag % 2 ^ sh ∧
      c'.val = if a.sign = Layout.mpNeg then -((a.mag % 2 ^ sh : Nat) : Int) else (a.mag % 2 ^ sh : Nat) := …  -- proved in Tom/Spec/Div2d.lean

/-- Digit `j` of `mp_mod_2d(a, sh, c)`: `a`'s digits below `D`, digit `D` masked with
`2^d - 1`, zero above. -/
def mod2dDigit (a : MpInt) (sh j : Nat) : Nat :=
  if j < sh / Layout.digitBits then a.digit j
  else if j = sh / Layout.digitBits then a.digit j % 2 ^ (sh % Layout.digitBits) else 0

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Div2dPost` (`mp_div_2d`), `Tom.copyIn` (`mp_abs`), `Tom.ClampedTo` (`mp_div`), `Tom.div2dDigit` (`mp_div_2d`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.clampUsed` (`mp_add`), `Tom.MpInt.ofDigits` (`mp_abs`)
-/

/-- `mp_div_2d(a, b, c, d)` with `d != NULL`: the standard contract (`d = a`) -/
theorem Specs.mp_div_2d_correct_rem_room : Tom.Machine.Api.MpDiv2dR.Statement :=
  Tom.Machine.Fn.MpDiv2dRG5.correct
/-
Machine plumbing: entry `0x8000520c`; stack reservation `F = 112`.

-- Tom/Machine/Api/MpDiv2dR.lean
/-- **`mp_div_2d(a, b, c, a)` on the machine** (`d = a`, distinct from `c`). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat} {c : MpInt}
    {ra s0 : BitVec 64}, Pre m sp pa adp pc cdp a b c ra →
    Triple (At entry (entryL ra s0 sp pa b pc) m v.keepR outp) (Ret m v outp sp pa adp pc cdp a b c ra s0)

/-- What `mp_div_2d(a, b, c, a)` needs. -/
structure Pre (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rc : MpAt m pc cdp c
  va : a.Valid
  sc : c.Shape
  ga : MpGeom pa adp a.alloc
  gc : MpGeom pc cdp c.alloc
  /-- `b > 0`: the shifting path. Both callers pass `p = mp_count_bits(n)` of a nonzero
  modulus; `b ≤ 0` (`mp_copy(a, c)`, `mp_zero(d)`) is not covered. -/
  b_pos : 0 < b
  /-- The C's `int b`. -/
  b_lt : b < 2 ^ 31
  /-- `mp_mod_2d`'s `a->used * MP_DIGIT_BIT` does not overflow (`Api.MpMod2dI`). -/
  bits : Layout.digitBits * a.used < 2 ^ 31
  /-- D5: `mp_copy(a, c)` does not call `mp_grow`. -/
  room : a.used ≤ c.alloc
  rs : Ram (sp - 112) 112
  sp_al : sp % 16 = 0
  sp_ge : 112 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pc cdp a c) Two.isW2

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pc cdp a b c a' c' M

-- Tom/Machine/Api/Two.lean
def isW2 : R → Bool
  | .code => false
  | _ => true

-- Tom/Machine/Api/MpDiv2dR.lean
/-- What it leaves: the quotient in `c`, the remainder in `a`. -/
structure Post (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c a' c' : MpInt) (M : Mem) : Prop where
  reprA : MpAt M pa adp a'
  reprC : MpAt M pc cdp c'
  div : Div2dPost a b c c'
  mod : Mod2dPost a b a a'
  frame : Frm (lay sp pa adp pc cdp a c) Two.ws2 m M

-- Tom/Machine/Api/Two.lean
def ws2 : List R := [.stk, .aS, .aD, .bS, .bD]

Also used (printed above): `Tom.Div2dPost` (`mp_div_2d`), `Tom.Mod2dPost` (`mp_div_2d`), `Tom.ClampedTo` (`mp_div`), `Tom.div2dDigit` (`mp_div_2d`), `Tom.mod2dDigit` (`mp_div_2d`), `Tom.clampUsed` (`mp_add`)
-/

/-! ## `mp_div_d`

`mp_err mp_div_d(const mp_int *a, mp_digit b, mp_int *c, mp_digit *d);`

Coverage: contract (c != a).
-/

/-- `mp_div_d(a, b, c, d)`: the allocating contract -/
theorem Specs.mp_div_d_correct : Tom.Machine.Api.MpDivD.Statement :=
  Tom.Machine.Fn.MpDivDG5.correct
/-
Machine plumbing: entry `0x80005388`; stack reservation `F = 688`; regions stk aS aD cS cD dS code; written [.stk, .cS, .cD, .dS].

-- Tom/Machine/Api/MpDivD.lean
def Statement : Prop := Standard.Statement Res Q (site .cD)  -- the standard shape (top of file)

structure P where  (sp pa adp pc cdp pd : Nat); (a c : MpInt); (v : Nat); (H : List (Nat × Nat))

/-- What `mp_div_d(a, b, c, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  sc : p.c.Shape
  apos : 0 < p.a.alloc
  cpos : 0 < p.c.alloc
  aoff : OffHeap p.pa 24
  coff : OffHeap p.pc 24
  /-- `c != NULL`: the `c == NULL` paths (`mp_mod_d`, not in the image) are not covered. They
  need `s_mp_div_3` with `c = NULL` and the branches that
  skip `mp_copy`/`mp_div_2d`/`mp_clamp`/`mp_exch`. -/
  c_nn : p.pc ≠ 0
  /-- `d != NULL`: the `d == NULL` branches (`53a4`, `5540`, `54d8`) are not covered; the
  image's only caller (`mp_to_radix`) passes `&d`. -/
  d_nn : p.pd ≠ 0
  d_al : p.pd % 4 = 0
  doff : OffHeap p.pd 4
  /-- `b` is a digit: the power-of-two scan stops at `MP_DIGIT_BIT` (`b = 2^29` would shift
  by 28), and the long division's `w * 2^28 + a[i]` fits an `mp_word` for `b ≤ 2^32`. -/
  v_lt : p.v < radix
  /-- D5: `mp_copy(a, c)` and `mp_div_2d(a, k, c, NULL)` do not call `mp_grow`. -/
  room : p.a.used ≤ p.c.alloc

/-- `c` after (non-`NULL`; `DivDQuot`, by path) and nothing on `MP_VAL`/`MP_MEM`. -/
def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (_, c') => DivDQuot p.a p.v p.c c'

-- Tom/Spec/DivD.lean
/-- What `mp_div_d(a, v, c, d)` leaves in `c` (non-`NULL`), by path. The copy path
assumes `c->alloc ≥ a->used` (D5). -/
structure DivDQuot (a : MpInt) (v : Nat) (c c' : MpInt) : Prop where
  copy : (v = 1 ∨ a.used = 0) → ClampedTo c' c.alloc a.digit a.used a.sign
  pow2 : v ≠ 1 → a.used ≠ 0 → v &&& (v - 1) = 0 → Div2dPost a (Nat.log2 v) c c'
  long : v ≠ 1 → a.used ≠ 0 → v &&& (v - 1) ≠ 0 → DivLongQuot a v c'
theorem DivDQuot.spec {a c c' : MpInt} {v : Nat} (ha : a.Valid) (hv : 0 < v)
    (hroom : a.used ≤ c.alloc) (hc : c.alloc < 2 ^ 31) (h : DivDQuot a v c c') :
    c'.Valid ∧ c'.mag = a.mag / v ∧ c'.val = a.val.tdiv v := …  -- proved in Tom/Spec/DivD.lean

/-- What the long division (`s_mp_div_3`, or `mp_div_d`'s loop) leaves in `c`. -/
def DivLongQuot (a : MpInt) (v : Nat) (c' : MpInt) : Prop :=
  ClampedTo c' (max 3 a.used) (divDDigit a v) a.used a.sign
theorem DivLongQuot.spec {a c' : MpInt} {v : Nat} (ha : a.Valid) (hv : 0 < v) (h : DivLongQuot a v c') :
    c'.Valid ∧ c'.mag = a.mag / v ∧ c'.val = a.val.tdiv v := …  -- proved in Tom/Spec/DivD.lean

/-- The quotient digits of the long division of `a` by `v`. -/
def divDDigit (a : MpInt) (v : Nat) (i : Nat) : Nat := if i < a.used then ldQ a.digit v a.used i else 0

/-- The quotient digit at position `i`: `(w * radix + a[i]) / v` with `w` the
remainder carried in. -/
def ldQ (da : Nat → Nat) (v n i : Nat) : Nat := (ldR da v n (i + 1) * radix + da i) / v

/-- The remainder carried into position `i`. -/
def ldR (da : Nat → Nat) (v n i : Nat) : Nat := ldV da n i % v

/-- The value of the digits from position `i` up (of `n`). -/
def ldV (da : Nat → Nat) (n i : Nat) : Nat := natUpTo (fun j => da (i + j)) (n - i)

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.ClampedTo` (`mp_div`), `Tom.Div2dPost` (`mp_div_2d`), `Tom.clampUsed` (`mp_add`), `Tom.div2dDigit` (`mp_div_2d`)
-/

/-- `mp_div_d(a, b, a, d)` in place: the allocating contract -/
theorem Specs.mp_div_d_correct_inplace : Tom.Machine.Api.MpDivDI.Statement :=
  Tom.Machine.Fn.MpDivDIG5.correct
/-
Machine plumbing: entry `0x80005388`; stack reservation `F = 688`; regions stk aS aD dS code; written [.stk, .aS, .aD, .dS].

-- Tom/Machine/Api/MpDivDI.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

structure P where  (sp pa adp pd : Nat); (a : MpInt); (v : Nat); (H : List (Nat × Nat))

/-- What `mp_div_d(a, b, a, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  /-- `b ≥ 2` (`mp_to_radix`'s `radix ≥ 2`): `b = 0` returns `MP_VAL` and `b = 1` tail-calls
  `mp_copy(a, a)`, whose `a == b` return has no contract here. -/
  v_ge : 2 ≤ p.v
  /-- `a != 0` (`mp_to_radix` divides while `t != 0`): `a == 0` tail-calls `mp_copy(a, a)`. -/
  u_pos : 0 < p.a.used
  /-- `d != NULL`: the image's only caller passes `&d`. -/
  d_nn : p.pd ≠ 0
  d_al : p.pd % 4 = 0
  doff : OffHeap p.pd 4
  /-- `b` is a digit: the power-of-two scan stops at `MP_DIGIT_BIT`, and the long division's
  `w * 2^28 + a[i]` fits an `mp_word`. -/
  v_lt : p.v < radix

/-- `a` after: `DivDQuot a b a a'` (by path), nothing on `MP_MEM`. -/
def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (_, a') => DivDQuot p.a p.v p.a a'

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.DivDQuot` (`mp_div_d`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.ClampedTo` (`mp_div`), `Tom.Div2dPost` (`mp_div_2d`), `Tom.DivLongQuot` (`mp_div_d`), `Tom.clampUsed` (`mp_add`), `Tom.div2dDigit` (`mp_div_2d`), `Tom.divDDigit` (`mp_div_d`), `Tom.ldQ` (`mp_div_d`), `Tom.ldR` (`mp_div_d`), `Tom.ldV` (`mp_div_d`)
-/

/-! ## `mp_dr_is_modulus`

`mp_bool mp_dr_is_modulus(const mp_int *a);`
-/

/-- `mp_dr_is_modulus`: the standard contract -/
theorem Specs.mp_dr_is_modulus_correct : Tom.Machine.Api.DrIsModulus.Statement :=
  Tom.Machine.Fn.DrIsModulus.correct
/-
Machine plumbing: entry `0x80005594`.

-- Tom/Machine/Api/DrIsModulus.lean
/-- **`mp_dr_is_modulus` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {pa adp : Nat} {a : MpInt} {ra : BitVec 64},
    Pre m pa adp a ra →
    Triple (At entry (Fn.DrIsModulus.entryL ra pa) m v.keep outp) (Ret m v outp a ra)

/-- What `mp_dr_is_modulus(a)` needs. -/
structure Pre (m : Mem) (pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  ra_al : ra.toNat % 4 = 0
  img : Img m

def Ret (m : Mem) (v : Abi) (outp : Array String) (a : MpInt) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  At ra [(1, ra), (10, BitVec.ofNat 64 (if IsDrModulus a then 1 else 0))] m v.keep outp cf

-- Tom/Spec/ModShape.lean
/-- `mp_dr_is_modulus(a)`: at least two digits, all but the lowest `MP_MASK`. -/
def IsDrModulus (a : MpInt) : Prop := 2 ≤ a.used ∧ ∀ i, 1 ≤ i → i < a.used → a.digit i = Layout.mpMask
-/

/-! ## `mp_dr_reduce`

`mp_err mp_dr_reduce(mp_int *x, const mp_int *n, mp_digit k);`
-/

/-- `mp_dr_reduce(x, n, k)` growing `x`: the allocating contract -/
theorem Specs.mp_dr_reduce_correct : Tom.Machine.Api.DrReduceG.Statement :=
  Tom.Machine.Fn.DrReduceGG5.correct
/-
Machine plumbing: entry `0x800055e4`; the arguments: `a0 = a`, `a1 = n`, `a2 = d` (`gp` for the allocator); stack reservation `F = 128 + MpGrow.F`; regions stk aS aD nS nD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/DrReduceG.lean
/-- **`mp_dr_reduce(x, n, k)` on the machine, growing `x`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) MpReduce2k.isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: MpReduce2k.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) MpReduce2k.ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

-- Tom/Machine/Api/MpReduce2k.lean
structure P where  (sp pa adp pn ndp d : Nat); (a n : MpInt); (H : List (Nat × Nat))

-- Tom/Machine/Api/DrReduceG.lean
/-- What `mp_dr_reduce(x, n, k)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  vn : p.n.Valid
  /-- `n ≠ 0`: at least one digit, and a loop that ends. -/
  npos : 0 < p.n.mag
  /-- `k` an `mp_digit` (`mp_dr_setup`). -/
  d_lt : p.d < radix
  /-- The C asks for `x ≤ (n - 1)^2`; the fold needs `x < radix^(2 m)`. -/
  x_lt : p.a.mag < radix ^ (2 * p.n.used)
  /-- `x`'s digits are `realloc`'s block: live and nonempty. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  noff : OffHeap p.pn 24

def Q (p : P) (x : X) : Prop := ReduxG.Out p (lay p .aD) (DrReducePost p.a p.n p.d) x

abbrev X := ReduxG.X

-- Tom/Machine/Api/ReduxG.lean
/-- What `x` holds after: shaped, live, placed (inside the old block `L` or a fresh one); on
`MP_OKAY` the reduction `post`. -/
structure Out (p : P) (L : Iv) (post : MpInt → Prop) (x : X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) L (site' p x)
  post : x.1 = true → post x.2.2

-- Tom/Spec/Reduce.lean
/-- What `mp_dr_reduce(x, n, k)` leaves in `x` (`x->alloc ≥ 2 n->used`, no `mp_grow`):
the fold-and-subtract loop of `drFold`, valid, the sign of `x` (reset if zero). The digit
loop (`drRow`, `drPass_val`) is the fold when `x->used ≤ 2 n->used`. -/
structure DrReducePost (x n : MpInt) (k : Nat) (x' : MpInt) : Prop where
  valid : x'.Valid
  mag : x'.mag = redLoop (drFold n.used k) n.mag (x.mag + 1) x.mag
  sign : x'.sign = if x'.used = 0 then Layout.mpZpos else x.sign
theorem DrReducePost.spec {x n x' : MpInt} {k : Nat} (hn : 0 < n.mag) (hk : n.mag + k = radix ^ n.used)
    (hx : x.mag < radix ^ (2 * n.used)) (h : DrReducePost x n k x') : x'.Valid ∧ x'.mag = x.mag % n.mag := …  -- proved in Tom/Spec/Reduce.lean

-- Tom/Machine/Api/ReduxG.lean
/-- `(ok, q, x')`: `x'`'s digits at `q`. -/
abbrev X : Type := Bool × Nat × MpInt

-- Tom/Spec/Reduce.lean
/-- `top: a = fold(a); if (a ≥ n) { a -= n; goto top; }` with fuel. -/
def redLoop (fold : Nat → Nat) (n : Nat) : Nat → Nat → Nat
  | 0, a => a
  | fuel + 1, a => if n ≤ fold a then redLoop fold n fuel (fold a - n) else fold a

/-- A pass computes `x mod radix^m + k * (x / radix^m mod radix^m)`. -/
def drFold (m k x : Nat) : Nat := x % radix ^ m + k * (x / radix ^ m % radix ^ m)

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`)
-/

/-- `mp_dr_reduce`: the standard contract -/
theorem Specs.mp_dr_reduce_correct_room : Tom.Machine.Api.DrReduce.Statement :=
  Tom.Machine.Fn.DrReduce.correct
/-
Machine plumbing: entry `0x800055e4`.

-- Tom/Machine/Api/DrReduce.lean
/-- **`mp_dr_reduce` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp px xdp pn ndp : Nat} {x n : MpInt} {k : Nat} {ra s0 : BitVec 64},
    Pre m sp px xdp pn ndp x n k ra →
    Triple (At entry (entryL ra s0 sp px pn k) m v.keepR outp) (Ret m v outp sp px xdp pn ndp x n k ra s0)

/-- What `mp_dr_reduce(x, n, k)` needs. -/
structure Pre (m : Mem) (sp px xdp pn ndp : Nat) (x n : MpInt) (k : Nat) (ra : BitVec 64) : Prop where
  rx : MpAt m px xdp x
  rn : MpAt m pn ndp n
  vx : x.Valid
  vn : n.Valid
  gx : MpGeom px xdp x.alloc
  gn : MpGeom pn ndp n.alloc
  n_pos : 0 < n.mag
  k_lt : k < radix
  x_lt : x.mag < radix ^ (2 * n.used)
  room : 2 * n.used ≤ x.alloc
  rs : Ram (sp - 176) 176
  sp_al : sp % 16 = 0
  sp_ge : 176 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp px xdp pn ndp x n) Two.isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp px xdp pn ndp : Nat) (x n : MpInt) (k : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ x' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp px xdp pn ndp x n k x' M

/-- What it leaves. -/
structure Post (m : Mem) (sp px xdp pn ndp : Nat) (x n : MpInt) (k : Nat) (x' : MpInt) (M : Mem) : Prop where
  repr : MpAt M px xdp x'
  dr : DrReducePost x n k x'
  /-- No `mp_grow` (D5): `x`'s digits stay in place. -/
  alloc : x'.alloc = x.alloc
  frame : Frm (lay sp px xdp pn ndp x n) Two.ws m M

Also used (printed above): `Tom.Reduce.DrReducePost` (`mp_dr_reduce`), `Tom.Reduce.redLoop` (`mp_dr_reduce`), `Tom.Reduce.drFold` (`mp_dr_reduce`)
-/

/-! ## `mp_dr_setup`

`void mp_dr_setup(const mp_int *a, mp_digit *d);`
-/

/-- `mp_dr_setup`: the standard contract -/
theorem Specs.mp_dr_setup_correct : Tom.Machine.Api.DrSetup.Statement :=
  Tom.Machine.Fn.DrSetup.correct
/-
Machine plumbing: entry `0x8000578c`; regions dW aS aD code.

-- Tom/Machine/Api/DrSetup.lean
/-- **`mp_dr_setup` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {pa adp pd : Nat} {a : MpInt} {ra : BitVec 64},
    Pre m pa adp pd a ra →
    Triple (At entry (Fn.DrSetup.entryL ra pa pd) m v.keep outp) (Ret m v outp pa adp pd a ra)

/-- What `mp_dr_setup(a, d)` needs. -/
structure Pre (m : Mem) (pa adp pd : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  alloc_pos : 1 ≤ a.alloc
  rd : Ram pd 4
  pd_al : pd % 4 = 0
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay pd pa adp a) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (pa adp pd : Nat) (a : MpInt) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ M, At ra [(1, ra)] M v.keep outp cf ∧ Post m pa adp pd a M

/-- What it leaves. -/
structure Post (m : Mem) (pa adp pd : Nat) (a : MpInt) (M : Mem) : Prop where
  res : bytesT4 M pd = BitVec.ofNat 32 (drSetupDigit a)
  frame : Frm (lay pd pa adp a) [R.dW] m M

-- Tom/Spec/ModShape.lean
/-- `mp_dr_setup(a, &d)`: `d = 2^MP_DIGIT_BIT - dp[0]`. -/
def drSetupDigit (a : MpInt) : Nat := radix - a.digit 0
-/

/-! ## `mp_exch`

`void mp_exch(mp_int *a, mp_int *b);`
-/

/-- `mp_exch`: the standard contract -/
theorem Specs.mp_exch_correct : Tom.Machine.Api.Exch.Statement :=
  Tom.Machine.Fn.Exch.correct
/-
Machine plumbing: entry `0x80000e60`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/Exch.lean
/-- **`mp_exch` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra : BitVec 64},
    Pre m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.Exch.entryL ra pa pb) m v.keep outp) (Ret m v outp sp pa adp pb bdp a b ra)

/-- What `mp_exch(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  sgn : a.sign < 2 ^ 31
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp a b) isW2

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ M, At ra [(1, ra)] M v.keep outp cf ∧ Post m sp pa adp pb bdp a b M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (M : Mem) : Prop where
  ra_ : MpAt M pa bdp b
  rb : MpAt M pb adp a
  frame : Frm (lay sp pa adp pb bdp a b) [R.aS, R.bS] m M

Also used (printed above): `Tom.Machine.Api.Two.isW2` (`mp_div_2d`)
-/

/-! ## `mp_exptmod`

`mp_err mp_exptmod(const mp_int *G, const mp_int *X, const mp_int *P, mp_int *Y);`

Coverage: contract (P > 1, P->used < 79 with room 2 P->used + 1; DR moduli with a nonzero low digit; 2k moduli exact within MP_PREC; X < 0 without caps: mp_invmod, mp_abs growing).
-/

/-- `mp_exptmod(G, X, P, Y)`: the allocating contract -/
theorem Specs.mp_exptmod_correct : Tom.Machine.Api.MpExptmod.Statement :=
  Tom.Machine.Fn.MpExptmod.correct
/-
Machine plumbing: entry `0x80000e94`; the arguments: `a0 = G`, `a1 = X`, `a2 = P`, `a3 = Y`; stack reservation `F = if p.x.sign = Layout.mpNeg then 96 + Fn p.n else Fd p`; regions stk gS gD xS xD nS nD yS yD ks ts kc tc code; written [.stk, .yS, .yD].

-- Tom/Machine/Api/MpExptmod.lean
/-- **`mp_exptmod(G, X, P, Y)` on the machine.** -/
def Statement : Prop := Spec Res

/-- A run from `entry` with residue `Res'`. -/
def Spec (Res' : P → Prop) : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res' p →
    Sound (lay (F p) p) isW → Bundle (lay (F p) p) (kind p) m → AHeap m (hin p) →
    (∀ r, Off (lay (F p) p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay (F p) p) ws .yD (out p x) (site' (F p) p x) (hin p) (hout p x) m M)

structure Res (p : P) : Prop extends Base (F p) p where
  arith : Arith p.n p.x

-- Tom/Machine/Api/Exptmod.lean
structure P where  (sp pg gdp px xdp pn ndp py ydp : Nat); (g x n y : MpInt); (mode : Nat); (H : List (Nat × Nat))

-- Tom/Machine/Api/MpExptmod.lean
/-- `MP_MEM` (`Y` as it was), or `ExptmodPost`. -/
def Q (p : P) : Out → Prop
  | .err r => r = Layout.mpMem ∨ ExptmodPost p.g p.x p.n p.y p.y r
  | .ok _ y' => ExptmodPost p.g p.x p.n p.y y' Layout.mpOkay

-- Tom/Machine/Api/Exptmod.lean
/-- What both workers need beyond their arithmetic: the stack, the operands valid and their
structs off the arena, `Y` live (its block is freed), the blocks `mp_mod`'s `mp_div` copies
(`G`'s and `P`'s) live, `redmode` an `int`, the C's `int` arithmetic on the sizes. -/
structure Base (F : Nat) (p : P) : Prop where
  stk : StkRes p.sp F
  vg : p.g.Valid
  vx : p.x.Valid
  vn : p.n.Valid
  sy : p.y.Shape
  /-- `P` positive (`mp_exptmod` returns `MP_VAL` before for a negative modulus). -/
  nz : p.n.sign = Layout.mpZpos
  /-- `mp_count_bits(X)`, `mp_count_bits(P)` are `int`s; `digidx = X->used - 1`. -/
  xbits : Layout.digitBits * p.x.used < 2 ^ 31
  nbits : Layout.digitBits * p.n.used < 2 ^ 31
  /-- `mp_mod(G, P, ·)`'s `mp_div` sizes (`Api/MpMod.lean` `au`). -/
  gu : p.g.used + p.n.used + 3 < 2 ^ 30
  mode : p.mode < 2 ^ 31
  gpos : 0 < p.g.alloc
  xpos : 0 < p.x.alloc
  npos : 0 < p.n.alloc
  ypos : 0 < p.y.alloc
  goff : OffHeap p.pg 24
  xoff : OffHeap p.px 24
  noff : OffHeap p.pn 24
  yoff : OffHeap p.py 24
  gblk : digBlk p.gdp p.g ∈ p.H
  nblk : digBlk p.ndp p.n ∈ p.H

-- Tom/Machine/Api/MpExptmod.lean
/-- The arithmetic the workers need for the mode the dispatch picks. -/
structure Arith (n x : MpInt) : Prop where
  gt1 : 1 < n.mag
  bits : Layout.digitBits * (2 * n.used + 1) < 2 ^ 31
  r2k : isReduce2k n = 1 → SMpExptmodFast.Exact2k n

-- Tom/Machine/Api/Exptmod.lean
/-- An error `r` (`Y` as it was), or `MP_OKAY` with `Y'`'s digits at `q` (`res`'s block). -/
inductive Out
  | err (r : Int)
  | ok (q : Nat) (y' : MpInt)

-- Tom/Spec/Exptmod.lean
/-- What `mp_exptmod(G, X, P, Y)` leaves (allocations not failing): `MP_VAL` for a negative
modulus; for a negative exponent, `mp_invmod(G, P, &tmpG)` and then the nonnegative case for
`tmpG` and `|X|` (`mp_abs`); otherwise the nonnegative case. -/
structure ExptmodPost (G X P Y Y' : MpInt) (ret : Int) : Prop where
  pneg : P.sign = Layout.mpNeg → ret = Layout.mpVal ∧ Y' = Y
  xpos : P.sign ≠ Layout.mpNeg → X.sign ≠ Layout.mpNeg → ExptmodNNPost G X P Y Y' ret
  xneg : P.sign ≠ Layout.mpNeg → X.sign = Layout.mpNeg →
    ∃ Gi0 Gi : MpInt, ∃ r1 : Int, InvmodPost G P Gi0 Gi r1 ∧ (r1 ≠ Layout.mpOkay → ret = r1 ∧ Y' = Y) ∧
      (r1 = Layout.mpOkay → ExptmodNNPost Gi (X.withSign Layout.mpZpos) P Y Y' ret)
theorem ExptmodPost.spec_nonneg {G X P Y Y' : MpInt} {ret : Int} (hX : X.Shape) (hP : P.Valid)
    (hPs : P.sign ≠ Layout.mpNeg) (hP1 : 1 < P.mag) (hXs : X.sign ≠ Layout.mpNeg) (hbug : ¬ Lossy2k P)
    (h : ExptmodPost G X P Y Y' ret) : ret = Layout.mpOkay ∧ Y'.Valid ∧ Y'.val = G.val ^ X.mag % P.val := …  -- proved in Tom/Spec/Exptmod.lean
theorem ExptmodPost.spec_neg {G X P Y Y' : MpInt} {ret : Int} (hG : G.Valid) (hX : X.Shape) (hP : P.Valid)
    (hPs : P.sign ≠ Layout.mpNeg) (hP1 : 1 < P.mag) (hXs : X.sign = Layout.mpNeg) (hbug : ¬ Lossy2k P)
    (hg : Nat.gcd (invmodRem G P) P.mag = 1) (hsg : 0 ≤ G.val ∨ P.mag % 2 = 0)
    (h : ExptmodPost G X P Y Y' ret) :
    ret = Layout.mpOkay ∧ Y'.Valid ∧ (Y'.val * G.val ^ X.mag) % P.val = 1 := …  -- proved in Tom/Spec/Exptmod.lean
theorem ExptmodPost.spec_neg_odd {G X P Y Y' : MpInt} {ret : Int} (hG : G.Valid) (hX : X.Shape) (hP : P.Valid)
    (hPs : P.sign ≠ Layout.mpNeg) (hP1 : 1 < P.mag) (hXs : X.sign = Layout.mpNeg) (hbug : ¬ Lossy2k P)
    (hg : Nat.gcd (invmodRem G P) P.mag = 1) (hneg : G.val < 0) (hodd : P.mag % 2 = 1)
    (h : ExptmodPost G X P Y Y' ret) :
    ret = Layout.mpOkay ∧ Y'.Valid ∧ (Y'.val * (-G.val) ^ X.mag) % P.val = 1 := …  -- proved in Tom/Spec/Exptmod.lean

-- Tom/Spec/ModShape.lean
/-- `mp_reduce_is_2k(a)` as the C states it (`MP_YES = 1`, `MP_NO = 0`): every bit from
`MP_DIGIT_BIT` up to `mp_count_bits(a)` set. -/
def isReduce2k (a : MpInt) : Nat :=
  if a.used = 0 then 0 else if a.used = 1 then 1
  else if (∀ ix, ix < countBits a → Layout.digitBits ≤ ix →
      (a.digit (ix / Layout.digitBits)).testBit (ix % Layout.digitBits) = true) then 1 else 0

-- Tom/Machine/Api/Exptmod.lean
/-- The non-lossy `mp_reduce_2k_setup` (`Exptmod.Lossy2k`'s negation for an `is2k` modulus):
its digit is the true `d` of `P = 2^p - d` (`Api.MpReduce2k.Res.hd`). -/
def Exact2k (n : MpInt) : Prop :=
  n.mag + (2 ^ Mont.nbits n.mag - n.mag) % radix = 2 ^ Mont.nbits n.mag

-- Tom/Spec/Exptmod.lean
/-- The nonnegative-exponent part of `mp_exptmod(G, X, P, Y)` (`P ≥ 0`, `X ≥ 0`): the
dispatch, by branch. Errors leave `Y` as it was. -/
structure ExptmodNNPost (G X P Y Y' : MpInt) (ret : Int) : Prop where
  l2k : is2kL P = true → ret = Layout.mpOkay ∧ SExptmodPost G X P Y'
  fast : is2kL P = false → (P.mag % 2 = 1 ∨ drMode P ≠ 0) →
    ret = Layout.mpOkay ∧ SExptmodFastPost G X P Y' (drMode P)
  zero : is2kL P = false → P.mag % 2 = 0 → drMode P = 0 → P.mag = 0 → ret = Layout.mpVal ∧ Y' = Y
  barrett : is2kL P = false → P.mag % 2 = 0 → drMode P = 0 → 0 < P.mag →
    ret = Layout.mpOkay ∧ SExptmodPost G X P Y'
theorem ExptmodNNPost.spec {G X P Y Y' : MpInt} {ret : Int} (hX : X.Shape) (hP : P.Valid)
    (hPs : P.sign ≠ Layout.mpNeg) (hP1 : 1 < P.mag) (hbug : ¬ Lossy2k P) (h : ExptmodNNPost G X P Y Y' ret) :
    ret = Layout.mpOkay ∧ Y'.Valid ∧ Y'.val = G.val ^ X.mag % P.val := …  -- proved in Tom/Spec/Exptmod.lean

-- Tom/Spec/Gcd.lean
/-- What `mp_invmod(a, b, c)` leaves, by the branch it takes. -/
structure InvmodPost (a b c c' : MpInt) (ret : Int) : Prop where
  bad : (b.sign = Layout.mpNeg ∨ b.mag ≤ 1) → InvmodErr c c' ret
  fast : b.sign ≠ Layout.mpNeg → 1 < b.mag → b.mag % 2 = 1 → InvmodFastPost a b c c' ret
  slow : b.sign ≠ Layout.mpNeg → 1 < b.mag → b.mag % 2 = 0 → InvmodSlowPost a b c c' ret
theorem InvmodPost.spec_ok {a b c c' : MpInt} {ret : Int} (ha : a.Valid)
    (hb1 : 1 < b.val) (hg : Nat.gcd (invmodRem a b) b.mag = 1)
    (hsg : 0 ≤ a.val ∨ b.mag % 2 = 0) (h : InvmodPost a b c c' ret) :
    ret = Layout.mpOkay ∧ c'.Valid ∧ 0 ≤ c'.val ∧ c'.val < b.val ∧ (a.val * c'.val) % b.val = 1 := …  -- proved in Tom/Spec/Gcd.lean
theorem InvmodPost.spec_neg_odd {a b c c' : MpInt} {ret : Int} (ha : a.Valid)
    (hb1 : 1 < b.val) (hg : Nat.gcd (invmodRem a b) b.mag = 1)
    (hneg : a.val < 0) (ho : b.mag % 2 = 1) (h : InvmodPost a b c c' ret) :
    ret = Layout.mpOkay ∧ c'.Valid ∧ -b.val < c'.val ∧ c'.val < 0 ∧ (a.val * -c'.val) % b.val = 1 ∧
      (a.val * c'.val + 1) % b.val = 0 := …  -- proved in Tom/Spec/Gcd.lean
theorem InvmodPost.spec_err {a b c c' : MpInt} {ret : Int}
    (hbad : b.sign = Layout.mpNeg ∨ b.mag ≤ 1 ∨ Nat.gcd (invmodRem a b) b.mag ≠ 1)
    (h : InvmodPost a b c c' ret) : ret = Layout.mpVal ∧ c' = c := …  -- proved in Tom/Spec/Gcd.lean

-- Tom/Spec/Mont.lean
/-- `mp_count_bits` by meaning: `0` for `0`, else `⌊log2 m⌋ + 1`. -/
def nbits (m : Nat) : Nat := if m = 0 then 0 else Nat.log2 m + 1

-- Tom/Spec/Exptmod.lean
/-- `mp_reduce_is_2k_l(a)`: one digit, or at least half of the digits are `MP_MASK`. -/
def is2kL (a : MpInt) : Bool :=
  a.used != 0 && (a.used == 1 || decide ((List.range a.used).countP (fun i => a.digit i == radix - 1) ≥ a.used / 2))

/-- What `s_mp_exptmod(G, X, P, Y, redmode)` leaves in `Y` (`redmode` 0 or 1, `X ≥ 0`,
`P > 0`, allocations not failing): the window loop with every product reduced modulo `P`,
`M[1] = G mod P`, `res = 1`. -/
structure SExptmodPost (G X P Y' : MpInt) : Prop where
  valid : Y'.Valid
  mag : Y'.mag = winRes (redP P.mag) X (base G P) 1
  sign : Y'.sign = Layout.mpZpos
theorem SExptmodPost.spec {G X P Y' : MpInt} (hX : X.Shape) (hPs : P.sign ≠ Layout.mpNeg) (hP : 1 < P.mag)
    (h : SExptmodPost G X P Y') :
    Y'.Valid ∧ Y'.mag = base G P ^ X.mag % P.mag ∧ Y'.val = G.val ^ X.mag % P.val := …  -- proved in Tom/Spec/Exptmod.lean

/-- `s_mp_exptmod_fast`'s `redmode` as `mp_exptmod` picks it. -/
def drMode (a : MpInt) : Nat := if drIsMod a then 1 else if is2k a then 2 else 0

/-- What `s_mp_exptmod_fast(G, X, P, Y, redmode)` leaves in `Y` (`X ≥ 0`, `P > 0`,
allocations not failing), by `redmode`. -/
structure SExptmodFastPost (G X P Y' : MpInt) (redmode : Nat) : Prop where
  valid : Y'.Valid
  sign : Y'.sign = Layout.mpZpos
  mont : redmode = 0 → Y'.mag =
    redMont P (winRes (redMont P) X ((base G P * (radix ^ P.used % P.mag)) % P.mag) (radix ^ P.used % P.mag))
  dr : redmode = 1 → Y'.mag = winRes (redDrC P) X (base G P) 1
  r2k : redmode = 2 → Y'.mag = winRes (red2kC P) X (base G P) 1
theorem SExptmodFastPost.spec_mont {G X P Y' : MpInt} (hX : X.Shape) (hP : P.Shape) (hPs : P.sign ≠ Layout.mpNeg)
    (hodd : P.mag % 2 = 1) (hP1 : 1 < P.mag) (h : SExptmodFastPost G X P Y' 0) :
    Y'.Valid ∧ Y'.val = G.val ^ X.mag % P.val := …  -- proved in Tom/Spec/Exptmod.lean
theorem SExptmodFastPost.spec_dr {G X P Y' : MpInt} (hX : X.Shape) (hP : P.Shape) (hPs : P.sign ≠ Layout.mpNeg)
    (hP1 : 1 < P.mag) (hk : P.mag + (radix - P.digit 0) = radix ^ P.used) (h : SExptmodFastPost G X P Y' 1) :
    Y'.Valid ∧ Y'.val = G.val ^ X.mag % P.val := …  -- proved in Tom/Spec/Exptmod.lean
theorem SExptmodFastPost.spec_2k {G X P Y' : MpInt} (hX : X.Shape) (hPs : P.sign ≠ Layout.mpNeg)
    (hP1 : 1 < P.mag) (hd : P.mag + (2 ^ nbits P.mag - P.mag) % radix = 2 ^ nbits P.mag)
    (h : SExptmodFastPost G X P Y' 2) : Y'.Valid ∧ Y'.val = G.val ^ X.mag % P.val := …  -- proved in Tom/Spec/Exptmod.lean

-- Tom/Spec/Gcd.lean
/-- An `MP_VAL` exit: `c` untouched. -/
structure InvmodErr (c c' : MpInt) (ret : Int) : Prop where
  ret : ret = Layout.mpVal
  same : c' = c

/-- What `s_mp_invmod_fast(a, b, c)` leaves (`b` positive): on `MP_VAL`
(`fastRes = none`) `c` untouched; otherwise `c` is `D` normalised
into `[0, b)` (an `mp_int` from `mp_add`/`mp_sub`: shaped and clamped) with
its sign then overwritten by `a->sign`. -/
structure InvmodFastPost (a b c c' : MpInt) (ret : Int) : Prop where
  err : Gcd.fastRes b.mag (invmodRem a b) = none → InvmodErr c c' ret
  ret_ok : ∀ d, Gcd.fastRes b.mag (invmodRem a b) = some d → ret = Layout.mpOkay
  shape : ∀ d, Gcd.fastRes b.mag (invmodRem a b) = some d → c'.Shape
  top : ∀ d, Gcd.fastRes b.mag (invmodRem a b) = some d → 0 < c'.used → c'.digit (c'.used - 1) ≠ 0
  mag : ∀ d, Gcd.fastRes b.mag (invmodRem a b) = some d → c'.mag = d.toNat
  sign : ∀ d, Gcd.fastRes b.mag (invmodRem a b) = some d → c'.sign = a.sign

/-- What `s_mp_invmod_slow(a, b, c)` leaves (`b` positive and even, the case
`mp_invmod` calls): on `MP_VAL` `c` untouched; otherwise `C` normalised into
`[0, b)`, valid. -/
structure InvmodSlowPost (a b c c' : MpInt) (ret : Int) : Prop where
  err : Gcd.slowRes (invmodRem a b) b.mag = none → InvmodErr c c' ret
  ret_ok : ∀ d, Gcd.slowRes (invmodRem a b) b.mag = some d → ret = Layout.mpOkay
  valid : ∀ d, Gcd.slowRes (invmodRem a b) b.mag = some d → c'.Valid
  val : ∀ d, Gcd.slowRes (invmodRem a b) b.mag = some d → c'.val = d

-- Tom/Spec/Exptmod.lean
/-- The window loop of `s_mp_exptmod(_fast)` over the digits of `X`, with the table built from
`m1` by `red` and the result register starting at `res0`. -/
def winRes (red : Nat → Nat) (X : MpInt) (m1 res0 : Nat) : Nat :=
  finish red (table red m1 (wsize X)) (wsize X)
    (runDigits red (table red m1 (wsize X)) (wsize X) X.digit X.used (start res0))

/-- Reduction modulo `P`: what `mp_reduce`, `mp_reduce_2k_l`, `mp_dr_reduce` and a non-lossy
`mp_reduce_2k` compute on the loop's products. -/
def redP (P : Nat) : Nat → Nat := fun v => v % P

/-- `mp_dr_is_modulus(a)`: at least two digits, all above the lowest `MP_MASK`. -/
def drIsMod (a : MpInt) : Bool :=
  decide (2 ≤ a.used) && (List.range a.used).all (fun i => i == 0 || a.digit i == radix - 1)

/-- `mp_reduce_is_2k(a)`: one digit, or every bit from `MP_DIGIT_BIT` up to the top is set. -/
def is2k (a : MpInt) : Bool :=
  a.used != 0 && (a.used == 1 ||
    (List.range (nbits a.mag)).all (fun i => decide (i < Layout.digitBits) || a.mag.testBit i))

/-- Montgomery reduction with `rho` from `mp_montgomery_setup`. -/
def redMont (P : MpInt) : Nat → Nat := fun v => redc v P.mag (setupRho (P.digit 0)) P.used

/-- `mp_dr_reduce` with `k` from `mp_dr_setup`. -/
def redDrC (P : MpInt) : Nat → Nat := fun v => redLoop (drFold P.used (radix - P.digit 0)) P.mag (v + 1) v

/-- `mp_reduce_2k` with `d` from `mp_reduce_2k_setup`. -/
def red2kC (P : MpInt) : Nat → Nat := fun v =>
  redLoop (fold2k (nbits P.mag) ((2 ^ nbits P.mag - P.mag) % radix)) P.mag (v + 1) v

-- Tom/Spec/Gcd.lean
/-- The result of `s_mp_invmod_fast` on `x = b`, `y = a mod b`, before the
sign is set: `none` for `MP_VAL` (`b` even, `x` or `y` zero, `v ≠ 1`). -/
def fastRes (x y : Nat) : Option Int :=
  if x % 2 = 0 then none
  else if x = 0 ∨ y = 0 then none
  else if (fastTop x (fastInit x y)).v = 1 then some (norm x (fastTop x (fastInit x y)).D)
  else none

/-- `y = a mod b` (`mp_mod(a, b, &y)`), as a `Nat` (`b > 0`). -/
def invmodRem (a b : MpInt) : Nat := (a.val % b.val).toNat

/-- The result of `s_mp_invmod_slow` on `x = a mod b`, `y = b`: `none` for
`MP_VAL` (both even, or `v ≠ 1` at the end), else the normalised `C`. -/
def slowRes (x y : Nat) : Option Int :=
  if x % 2 = 0 ∧ y % 2 = 0 then none
  else if (slowTop x y (slowInit x y)).v = 1 then some (norm y (slowTop x y (slowInit x y)).C)
  else none

-- Tom/Spec/Exptmod.lean
/-- The window size from `mp_count_bits(X)`. -/
def wsize (X : MpInt) : Nat := winSize (nbits X.mag)

-- Tom/Spec/Gcd.lean
def fastTop (x : Nat) (s : FastSt) : FastSt :=
  if h : 0 < s.u ∧ 0 < s.v ∧ (fastPass x s).u ≠ 0 then fastTop x (fastPass x s) else fastPass x s

/-- `u = x, v = y, B = 0, D = 1`. -/
def fastInit (x y : Nat) : FastSt := ⟨x, y, 0, 1⟩

/-- The two loops. -/
def norm (b : Nat) (X : Int) : Int := subDown b (addUp b X)

/-- `top: … if (!MP_IS_ZERO(&u)) goto top;` (guard on `u`, `v` positive not
in the C, where it is an invariant). -/
def slowTop (x y : Nat) (s : SlowSt) : SlowSt :=
  if h : 0 < s.u ∧ 0 < s.v ∧ (slowPass x y s).u ≠ 0 then slowTop x y (slowPass x y s) else slowPass x y s

/-- Step 3: `u = x, v = y, A = 1, B = 0, C = 0, D = 1`. -/
def slowInit (x y : Nat) : SlowSt := ⟨x, y, 1, 0, 0, 1⟩

/-- The values of `u, v, B, D` in `s_mp_invmod_fast`. -/
structure FastSt where
  u : Nat
  v : Nat
  B : Int
  D : Int

def fastPass (x : Nat) (s : FastSt) : FastSt := fastSub (fastLoopV x (fastLoopU x s))

/-- `while (mp_cmp_mag(X, b) != MP_LT) X -= b`, on a nonnegative `X`
(where `|X| ≥ b` is `X ≥ b`; the guard `0 < b` is not in the C). -/
def subDown (b : Nat) (X : Int) : Int := if h : (b : Int) ≤ X ∧ 0 < b then subDown b (X - b) else X

/-- `while (X < 0) X += b` (the guard `0 < b` is not in the C). -/
def addUp (b : Nat) (X : Int) : Int := if h : X < 0 ∧ 0 < b then addUp b (X + b) else X

/-- The values of `u, v, A, B, C, D` in `s_mp_invmod_slow`. -/
structure SlowSt where
  u : Nat
  v : Nat
  A : Int
  B : Int
  C : Int
  D : Int

/-- One pass from `top:` to the test `if (!MP_IS_ZERO(&u)) goto top`. -/
def slowPass (x y : Nat) (s : SlowSt) : SlowSt := slowSub (slowLoopV x y (slowLoopU x y s))

/-- Step 6: `u ≥ v`: `u -= v, B -= D`; else `v -= u, D -= B`. -/
def fastSub (s : FastSt) : FastSt :=
  if s.v ≤ s.u then { s with u := s.u - s.v, B := s.B - s.D } else { s with v := s.v - s.u, D := s.D - s.B }

def fastLoopV (x : Nat) (s : FastSt) : FastSt :=
  if h : s.v ≠ 0 ∧ s.v % 2 = 0 then fastLoopV x (fastHalfV x s) else s

def fastLoopU (x : Nat) (s : FastSt) : FastSt :=
  if h : s.u ≠ 0 ∧ s.u % 2 = 0 then fastLoopU x (fastHalfU x s) else s

/-- Step 6: `u ≥ v` (`mp_cmp(&u, &v) != MP_LT`): `u -= v, A -= C, B -= D`;
else `v -= u, C -= A, D -= B`. -/
def slowSub (s : SlowSt) : SlowSt :=
  if s.v ≤ s.u then { s with u := s.u - s.v, A := s.A - s.C, B := s.B - s.D }
  else { s with v := s.v - s.u, C := s.C - s.A, D := s.D - s.B }

/-- Step 5's loop `while (MP_IS_EVEN(&v))` (guard `v ≠ 0` not in the C). -/
def slowLoopV (x y : Nat) (s : SlowSt) : SlowSt :=
  if h : s.v ≠ 0 ∧ s.v % 2 = 0 then slowLoopV x y (slowHalfV x y s) else s

/-- Step 4's loop `while (MP_IS_EVEN(&u))` (guard `u ≠ 0` not in the C). -/
def slowLoopU (x y : Nat) (s : SlowSt) : SlowSt :=
  if h : s.u ≠ 0 ∧ s.u % 2 = 0 then slowLoopU x y (slowHalfU x y s) else s

/-- One pass of step 5: `v /= 2`; if `D` odd, `D -= x`; `D /= 2`. -/
def fastHalfV (x : Nat) (s : FastSt) : FastSt :=
  { s with v := s.v / 2, D := (if s.D % 2 = 1 then s.D - x else s.D) / 2 }

/-- One pass of step 4: `u /= 2`; if `B` odd, `B -= x`; `B /= 2`. -/
def fastHalfU (x : Nat) (s : FastSt) : FastSt :=
  { s with u := s.u / 2, B := (if s.B % 2 = 1 then s.B - x else s.B) / 2 }

/-- One pass of step 5 (`v` even): the same on `v, C, D`. -/
def slowHalfV (x y : Nat) (s : SlowSt) : SlowSt :=
  if s.C % 2 = 1 ∨ s.D % 2 = 1 then { s with v := s.v / 2, C := (s.C + y) / 2, D := (s.D - x) / 2 }
  else { s with v := s.v / 2, C := s.C / 2, D := s.D / 2 }

/-- One pass of step 4 (`u` even): `u /= 2`; if `A` or `B` is odd,
`A += y, B -= x`; then `A /= 2, B /= 2`. -/
def slowHalfU (x y : Nat) (s : SlowSt) : SlowSt :=
  if s.A % 2 = 1 ∨ s.B % 2 = 1 then { s with u := s.u / 2, A := (s.A + y) / 2, B := (s.B - x) / 2 }
  else { s with u := s.u / 2, A := s.A / 2, B := s.B / 2 }

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.countBits` (`mp_count_bits`), `Tom.bitLen` (`mp_count_bits`)
-/

/-! ## `mp_gcd`

`mp_err mp_gcd(const mp_int *a, const mp_int *b, mp_int *c);`

Coverage: contract.
-/

/-- `mp_gcd(a, b, c)`: the allocating contract (over `Kit/MeetHeap.lean`) -/
theorem Specs.mp_gcd_correct : Tom.Machine.Api.MpGcd.Statement :=
  Tom.Machine.Fn.MpGcdG5.correct
/-
Machine plumbing: entry `0x8000105c`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator); stack reservation `F = 96 + MpInitCopy.F`; regions stk aS aD bS bD cS cD code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/MpGcd.lean
def Statement : Prop := Standard.Statement Res Q (site .cD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp pc cdp : Nat); (a b c : MpInt); (H : List (Nat × Nat))

/-- What `mp_gcd(a, b, c)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_init_copy` copies valid operands; `mp_cnt_lsb` and the loop read their values. -/
  va : p.a.Valid
  vb : p.b.Valid
  /-- `mp_abs` and `mp_mul_2d` write a shaped `c`. -/
  sc : p.c.Shape
  /-- `mp_cnt_lsb`'s `int` count (`28 used < 2^31`, `Api/CntLsb.lean`); the shifts stay below it. -/
  abits : Layout.digitBits * p.a.used < 2 ^ 31
  bbits : Layout.digitBits * p.b.used < 2 ^ 31
  /-- D5: `mp_abs`'s `mp_copy` and `mp_mul_2d(&u, k, c)` (`|u| 2^k ≤ min(|a|, |b|)`) do not grow `c`. -/
  room : max p.a.used p.b.used + 1 ≤ p.c.alloc
  /-- `mp_init_copy` reads the sources' digit blocks: live and nonempty (`IcRes`). -/
  ablk : digBlk p.adp p.a ∈ p.H
  bblk : digBlk p.bdp p.b ∈ p.H
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- The structs lie off the arena (`IcRes`: the source's). -/
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24

/-- The gcd, and `c`'s allocation kept; a leaked block is fresh. -/
def Q (p : P) : Out → Prop
  | .ok c' => GcdPost p.a p.b c' ∧ c'.alloc = p.c.alloc
  | .memU => True
  | .memV q => Fresh p.H q (4 * initPrec p.a.used)

/-- The outcome: `c'` on success; `MP_MEM` from the first `mp_init_copy`; `MP_MEM`
from the second, with `u`'s block `q` leaked. -/
inductive Out
  | ok (c' : MpInt)
  | memU
  | memV (q : Nat)

-- Tom/Spec/Gcd.lean
/-- What `mp_gcd(a, b, c)` leaves in `c`: a valid, nonnegative `mp_int` whose
magnitude is the C's computation `gcdC |a| |b|`. -/
structure GcdPost (a b c' : MpInt) : Prop where
  valid : c'.Valid
  mag : c'.mag = Gcd.gcdC a.mag b.mag
  sign : c'.sign = Layout.mpZpos
theorem GcdPost.spec {a b c' : MpInt} (h : GcdPost a b c') :
    c'.Valid ∧ c'.mag = Nat.gcd a.mag b.mag ∧ c'.val = (Nat.gcd a.mag b.mag : Int) := …  -- proved in Tom/Spec/Gcd.lean
theorem GcdPost.spec_int {a b c' : MpInt} (h : GcdPost a b c') : c'.val = (Int.gcd a.val b.val : Int) := …  -- proved in Tom/Spec/Gcd.lean

-- Tom/Machine/Api/Alloc.lean
/-- **A fresh block** `(p, n)` for the live blocks `H` (`FreshBlock`, with
the alignment `malloc` returns). -/
structure Fresh (H : List (Nat × Nat)) (p n : Nat) : Prop where
  nz : p ≠ 0
  al : p % 16 = 0
  lo : heapStart ≤ p
  hi : p + n ≤ heapEnd
  disj : ∀ e ∈ H, ∀ a, InBlk (p, n) a → ¬ InBlk e a

-- Tom/Spec/Init.lean
/-- The precision `mp_init_size(a, size)` allocates. -/
def initPrec (size : Nat) : Nat := max minPrec size

-- Tom/Spec/Gcd.lean
/-- What `mp_gcd(a, b, c)` computes, as the C does: `|b|` if `a = 0`, `|a|`
if `b = 0`, else the loop on the odd parts, shifted back by the common power
of two. -/
def gcdC (m n : Nat) : Nat :=
  if m = 0 then n else if n = 0 then m
  else gcdLoop (oddPart m) (oddPart n) * 2 ^ min (lsb m) (lsb n)

-- Tom/Spec/Init.lean
/-- `MP_MIN_PREC` for `MP_32BIT` (`tommath_private.h`): `(64 + 28 - 1) / 28`. -/
def minPrec : Nat := (64 + Layout.digitBits - 1) / Layout.digitBits

-- Tom/Spec/Gcd.lean
/-- The loop of `mp_gcd` from `(u, v)`. The guard `u = 0` is not in the C
(where `u` stays odd); it makes the model total. -/
def gcdLoop (u v : Nat) : Nat :=
  if h : v = 0 then u else if hu : u = 0 then v else gcdLoop (gcdStep u v).1 (gcdStep u v).2

/-- `n` with its trailing zero bits shifted out. -/
def oddPart (n : Nat) : Nat := n / 2 ^ lsb n

/-- The number of trailing zero bits of `n` (`0` for `n = 0`, as `mp_cnt_lsb`). -/
def lsb (n : Nat) : Nat := if h : n ≠ 0 ∧ n % 2 = 0 then lsb (n / 2) + 1 else 0

/-- One pass of `mp_gcd`'s `while (!MP_IS_ZERO(&v))` body: swap so that
`u ≤ v` (`mp_cmp_mag(&u, &v) == MP_GT`), `v = v - u` (`s_mp_sub`), then
`v = v / 2 ^ cnt_lsb(v)` (`mp_div_2d`). -/
def gcdStep (u v : Nat) : Nat × Nat :=
  if v < u then (v, oddPart (u - v)) else (u, oddPart (v - u))

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`)
-/

/-! ## `mp_grow`

`mp_err mp_grow(mp_int *a, int size);`

Coverage: contract (all paths).
-/

/-- `mp_grow`: the standard contract, all paths -/
theorem Specs.mp_grow_correct : Tom.Machine.Api.MpGrow.Statement :=
  Tom.Machine.Fn.MpGrowR.correct
/-
Machine plumbing: stack reservation `F = 32 + depth`.

-- Tom/Machine/Api/MpGrow.lean
/-- **`mp_grow(a, size)` on the machine** (`0 ≤ size < 2^31`), all paths. -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp p dp : Nat} {a : MpInt}
    {size : Nat} {ra : BitVec 64}, Pre m v H sp p dp a size ra →
    Triple (At Fn.MpGrowR.entry (entryL ra p (BitVec.ofNat 64 size)) m v.keep outp)
      (Ret m v outp H sp p dp a size ra)

/-- What `mp_grow(a, size)` needs. -/
structure Pre (m : Mem) (v : Abi) (H : List (Nat × Nat)) (sp p dp : Nat) (a : MpInt) (size : Nat)
    (ra : BitVec 64) : Prop where
  repr : MpAt m p dp a
  shape : a.Shape
  heap : Heap m (digBlk dp a :: H)
  st : Ram p 24
  st_al : p % 8 = 0
  soff : OffHeap p 24
  size_lt : size < 2 ^ 31
  ctx : ACtx m v sp F
  ra_al : ra.toNat % 4 = 0
  lay : Sound (lay sp p dp a) Un.isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (H : List (Nat × Nat)) (sp p dp : Nat) (a : MpInt)
    (size : Nat) (ra : BitVec 64) (c : Vsa.Machine.Config) : Prop :=
  ∃ r M, At ra [(1, ra), (10, r)] M v.keep outp c ∧ Post m M H sp p dp a size r

/-- **What it leaves**, with result `r`. -/
inductive Post (m M : Mem) (H : List (Nat × Nat)) (sp p dp : Nat) (a : MpInt) (size : Nat) :
    BitVec 64 → Prop
  /-- `size ≤ a->alloc`: nothing changed. -/
  | keep (hle : size ≤ a.alloc) (same : M = m) : Post m M H sp p dp a size 0#64
  /-- Reallocated: `a'` at the fresh block `q`. -/
  | ok {q : Nat} {a' : MpInt} (hlt : a.alloc < size) (fresh : Fresh H q (4 * size))
      (heap : Heap M ((q, 4 * size) :: H)) (repr : MpAt M p q a') (grow : GrowPost a size a')
      (frame : HFrm (lay sp p dp a) Un.ws H m M) : Post m M H sp p dp a size 0#64
  /-- `realloc` failed: the heap and `a` as they were. -/
  | mem (hlt : a.alloc < size) (heap : Heap M (digBlk dp a :: H)) (repr : MpAt M p dp a)
      (frame : HFrm (lay sp p dp a) Un.ws H m M) : Post m M H sp p dp a size memBV

-- Tom/Spec/Init.lean
/-- **What `mp_grow(a, size)` leaves when it reallocates** (`a->alloc < size`):
`alloc = size`, the old digits below the old `alloc`, zeros above; `used` and
`sign` as they were. -/
structure GrowPost (a : MpInt) (size : Nat) (a' : MpInt) : Prop where
  used : a'.used = a.used
  sign : a'.sign = a.sign
  alloc : a'.alloc = size
  len : a'.digits.length = size
  low : ∀ i, i < a.alloc → a'.digit i = a.digit i
  high : ∀ i, a.alloc ≤ i → a'.digit i = 0
theorem GrowPost.spec {a a' : MpInt} {size : Nat} (ha : a.Shape) (hs : a.alloc < size)
    (h2 : size < 2 ^ 31) (h : GrowPost a size a') :
    a'.Shape ∧ a'.mag = a.mag ∧ a'.val = a.val ∧ (a.Valid → a'.Valid) := …  -- proved in Tom/Spec/Init.lean

Also used (printed above): `Tom.Machine.Api.Alloc.Heap` (`mp_clear`), `Tom.Machine.Api.Heap.ACtx` (`mp_clear`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.Machine.Api.Alloc.ImpureAt` (`mp_clear`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.Alloc.Fresh` (`mp_gcd`), `Tom.Machine.Api.Heap.HFrm` (`mp_clear`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.impureBytes` (`mp_clear`), `Tom.Machine.Api.Alloc.impurePtr` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`), `Tom.Machine.Api.Alloc.Keep` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`)
-/

/-- `mp_grow`: the standard contract, all paths -/
theorem Specs.mp_grow_correct_val : Tom.Machine.Api.MpGrow.ValStatement :=
  Tom.Machine.Fn.MpGrowR.correct_val
/-
Machine plumbing: stack reservation `F = 32 + depth`.

-- Tom/Machine/Api/MpGrow.lean
/-- **`mp_grow(a, size)` with `size < 0`**: `MP_VAL`, nothing written. -/
def ValStatement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {p : Nat} {size ra : BitVec 64},
    Img m → ra.toNat % 4 = 0 → zopz0zI_s size 0#64 = true →
    Triple (At Fn.MpGrowR.entry (entryL ra p size) m v.keep outp)
      (At ra [(1, ra), (10, 0xfffffffffffffffd#64)] m v.keep outp)
-/

/-! ## `mp_init`

`mp_err mp_init(mp_int *a);`

Coverage: contract.
-/

/-- `mp_init`, `mp_init_size`: the standard contracts -/
theorem Specs.mp_init_correct : Tom.Machine.Api.MpInit.Statement :=
  Tom.Machine.Fn.MpInit.init_correct
/-
Machine plumbing: regions stk aS code; written [.stk, .aS].

-- Tom/Machine/Api/MpInit.lean
/-- **`mp_init(a)` on the machine** (`MP_PREC = 32` digits). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp pa : Nat} {ra : BitVec 64},
    Pre m v H sp pa Finit ra →
    Triple (At Fn.MpInit.initEntry (initL ra pa) m v.keep outp)
      (Ret m v outp H sp pa Finit defPrec ra)

/-- What `mp_init_size(a, ·)`/`mp_init(a)` need: the heap, `a`'s struct (RAM,
aligned, off the allocator), the call context with stack depth `F`. -/
structure Pre (m : Mem) (v : Abi) (H : List (Nat × Nat)) (sp pa F : Nat) (ra : BitVec 64) : Prop where
  heap : Heap m H
  st : Ram pa 24
  st_al : pa % 8 = 0
  soff : OffHeap pa 24
  ctx : ACtx m v sp F
  ra_al : ra.toNat % 4 = 0
  lay : Sound (lay F sp pa) isW

/-- The stack depth of `mp_init`: its 16-byte frame and `calloc`'s. -/
abbrev Finit : Nat := 16 + callocDepth

/-- The entry of `mp_init`: `ra`, `a0 = a`. -/
def initL (ra : BitVec 64) (pa : Nat) : GRegs := [(1, ra), (10, BitVec.ofNat 64 pa)]

def Ret (m : Mem) (v : Abi) (outp : Array String) (H : List (Nat × Nat)) (sp pa F n : Nat) (ra : BitVec 64)
    (c : Vsa.Machine.Config) : Prop :=
  ∃ r M, At ra [(1, ra), (10, r)] M v.keep outp c ∧ Post m M H sp pa F n r

-- Tom/Spec/Init.lean
/-- `MP_PREC` (`tommath.h`, not `MP_LOW_MEM`). -/
def defPrec : Nat := 32

-- Tom/Machine/Api/Alloc.lean
/-- The stack depth of `calloc`: `_calloc_r`'s frame (32) and `_malloc_r`'s `depth`. -/
def callocDepth : Nat := 544

-- Tom/Machine/Api/MpInit.lean
/-- **What they leave** with `n` digits requested and result `r`. -/
inductive Post (m M : Mem) (H : List (Nat × Nat)) (sp pa F n : Nat) : BitVec 64 → Prop
  | ok {q : Nat} (fresh : Fresh H q (4 * n)) (heap : Heap M ((q, 4 * n) :: H))
      (live : MpLive M ((q, 4 * n) :: H) pa q (MpInt.zeroN n)) (frame : HFrm (lay F sp pa) ws H m M) :
      Post m M H sp pa F n 0#64
  | mem (heap : Heap M H) (dp : bytesT8 M (pa + 16) = 0#64) (frame : HFrm (lay F sp pa) ws H m M) :
      Post m M H sp pa F n memBV

-- Tom/Machine/Api/Heap.lean
/-- **An `mp_int` on the heap**: `a` at `p`, its digits the live block
`(dp, 4 * a.alloc)` of `H`, its struct off the allocator. -/
structure MpLive (m : Mem) (H : List (Nat × Nat)) (p dp : Nat) (a : MpInt) : Prop where
  repr : MpAt m p dp a
  blk : digBlk dp a ∈ H
  soff : OffHeap p 24

Also used (printed above): `Tom.Machine.Api.Alloc.Heap` (`mp_clear`), `Tom.Machine.Api.Heap.ACtx` (`mp_clear`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.Machine.Api.Alloc.ImpureAt` (`mp_clear`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.Alloc.Fresh` (`mp_gcd`), `Tom.MpInt.zeroN` (`mp_2expt`), `Tom.Machine.Api.Heap.HFrm` (`mp_clear`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.impureBytes` (`mp_clear`), `Tom.Machine.Api.Alloc.impurePtr` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`), `Tom.Machine.Api.Alloc.Keep` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`)
-/

/-! ## `mp_init_copy`

`mp_err mp_init_copy(mp_int *a, const mp_int *b);`
-/

/-- `mp_init_copy`: the standard contract -/
theorem Specs.mp_init_copy_correct : Tom.Machine.Api.MpInitCopy.Statement :=
  Tom.Machine.Fn.MpInitCopy.correct
/-
Machine plumbing: stack reservation `F = 48 + MpInit.Fsize`; regions stk aS bS bD code; written [.stk, .aS].

-- Tom/Machine/Api/MpInitCopy.lean
/-- **`mp_init_copy(a, b)` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp pa pb bdp : Nat} {b : MpInt}
    {ra : BitVec 64}, Pre m v H sp pa pb bdp b ra →
    Triple (At Fn.MpInitCopy.entry (entryL ra pa pb) m v.keep outp)
      (Ret m v outp H sp pa pb bdp b ra)

/-- What `mp_init_copy(a, b)` needs. -/
structure Pre (m : Mem) (v : Abi) (H : List (Nat × Nat)) (sp pa pb bdp : Nat) (b : MpInt)
    (ra : BitVec 64) : Prop where
  heap : Heap m H
  st : Ram pa 24
  st_al : pa % 8 = 0
  soff : OffHeap pa 24
  live : MpLive m H pb bdp b
  vb : b.Valid
  apos : 0 < b.alloc
  gb : MpGeom pb bdp b.alloc
  ctx : ACtx m v sp F
  ra_al : ra.toNat % 4 = 0
  lay : Sound (lay F sp pa pb bdp b) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (H : List (Nat × Nat)) (sp pa pb bdp : Nat) (b : MpInt)
    (ra : BitVec 64) (c : Vsa.Machine.Config) : Prop :=
  ∃ r M, At ra [(1, ra), (10, r)] M v.keep outp c ∧ Post m M H sp pa pb bdp b (initPrec b.used) r

/-- **What it leaves** with result `r` (`n` digits allocated). -/
inductive Post (m M : Mem) (H : List (Nat × Nat)) (sp pa pb bdp : Nat) (b : MpInt) (n : Nat) :
    BitVec 64 → Prop
  | ok {q : Nat} {a' : MpInt} (fresh : Fresh H q (4 * n)) (heap : Heap M ((q, 4 * n) :: H))
      (live : MpLive M ((q, 4 * n) :: H) pa q a') (copy : CopyPost b (MpInt.zeroN n) a')
      (frame : HFrm (lay F sp pa pb bdp b) ws H m M) : Post m M H sp pa pb bdp b n 0#64
  | mem (heap : Heap M H) (dp : bytesT8 M (pa + 16) = 0#64) (frame : HFrm (lay F sp pa pb bdp b) ws H m M) :
      Post m M H sp pa pb bdp b n MpInit.memBV

Also used (printed above): `Tom.Machine.Api.Alloc.Heap` (`mp_clear`), `Tom.Machine.Api.Heap.MpLive` (`mp_init`), `Tom.Machine.Api.Heap.ACtx` (`mp_clear`), `Tom.initPrec` (`mp_gcd`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.Machine.Api.Alloc.ImpureAt` (`mp_clear`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.Alloc.Fresh` (`mp_gcd`), `Tom.CopyPost` (`mp_copy`), `Tom.MpInt.zeroN` (`mp_2expt`), `Tom.Machine.Api.Heap.HFrm` (`mp_clear`), `Tom.minPrec` (`mp_gcd`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.impureBytes` (`mp_clear`), `Tom.Machine.Api.Alloc.impurePtr` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`), `Tom.Machine.Api.Alloc.Keep` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`)
-/

/-! ## `mp_init_multi`

`mp_err mp_init_multi(mp_int *mp, ...);`
-/

/-- `mp_init_multi`: the standard contract -/
theorem Specs.mp_init_multi_correct : Tom.Machine.Api.MpInitMulti.Statement :=
  Tom.Machine.Fn.MpInitMulti.correct
/-
Machine plumbing: the argument list: the pointers and the terminating `NULL`; stack reservation `F = 112 + MpInit.Finit`.

-- Tom/Machine/Api/MpInitMulti.lean
/-- **`mp_init_multi` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp : Nat} {xs : List Nat}
    {ra : BitVec 64}, Pre m v H sp xs ra →
    Triple (At Fn.MpInitMulti.entry ((1, ra) :: argRegs 0 (args xs)) m v.keep outp) (Ret m v outp H sp xs ra)

/-- What `mp_init_multi(xs…, NULL)` needs. -/
structure Pre (m : Mem) (v : Abi) (H : List (Nat × Nat)) (sp : Nat) (xs : List Nat) (ra : BitVec 64) : Prop where
  heap : Heap m H
  st : Structs xs (sp - F) (F + argLen (xs.length + 1))
  sargs : StackArgs m sp (args xs)
  args_hi : sp + argLen (xs.length + 1) ≤ 0x100000000
  len : xs.length + 1 < 2 ^ 31
  ctx : ACtx m v sp F
  ra_al : ra.toNat % 4 = 0

def Ret (m : Mem) (v : Abi) (outp : Array String) (H : List (Nat × Nat)) (sp : Nat) (xs : List Nat)
    (ra : BitVec 64) (c : Vsa.Machine.Config) : Prop :=
  ∃ r M, At ra [(1, ra), (10, r)] M v.keep outp c ∧ Post m M H sp xs r

/-- **What it leaves**, with result `r`. -/
inductive Post (m M : Mem) (H : List (Nat × Nat)) (sp : Nat) (xs : List Nat) : BitVec 64 → Prop
  | ok (ys : List Multi.Arg) (hp : ptrs ys = xs) (zero : ∀ y ∈ ys, y.2.2 = MpInt.zeroN defPrec)
      (live : ∀ y ∈ ys, MpAt M y.1 y.2.1 y.2.2) (heap : Heap M (blocks ys ++ H)) (apart : Apart ys H)
      (frame : Keep (W xs H sp) m M) : Post m M H sp xs 0#64
  | mem (k : Nat) (hk : k < xs.length) (cleared : ∀ i (h : i < k), MpAt M (xs[i]'(by omega)) 0 MpInt.cleared)
      (dp : bytesT8 M (xs[k] + 16) = 0#64) (heap : Heap M H) (frame : Keep (W xs H sp) m M) :
      Post m M H sp xs MpInit.memBV

/-- The blocks of `ys` are apart from each other and from `H`'s. -/
structure Apart (ys : List Multi.Arg) (H : List (Nat × Nat)) : Prop where
  pw : (blocks ys).Pairwise fun e e' => Disj e.1 e.2 e'.1 e'.2
  off : ∀ e ∈ blocks ys, ∀ e' ∈ H, ∀ a, InBlk e a → ¬ InBlk e' a

/-- What it may write: the stack, the structs, the footprint. -/
def W (xs : List Nat) (H : List (Nat × Nat)) (sp : Nat) (a : Nat) : Prop :=
  Stk sp F a ∨ (∃ p ∈ xs, InBlk (p, 24) a) ∨ Foot H a

Also used (printed above): `Tom.Machine.Api.Multi.argRegs` (`mp_clear_multi`), `Tom.Machine.Api.Alloc.Heap` (`mp_clear`), `Tom.Machine.Api.Multi.Structs` (`mp_clear_multi`), `Tom.Machine.Api.Multi.argLen` (`mp_clear_multi`), `Tom.Machine.Api.Multi.StackArgs` (`mp_clear_multi`), `Tom.Machine.Api.Heap.ACtx` (`mp_clear`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.Machine.Api.Alloc.ImpureAt` (`mp_clear`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.Multi.Arg` (`mp_clear_multi`), `Tom.Machine.Api.Multi.ptrs` (`mp_clear_multi`), `Tom.MpInt.zeroN` (`mp_2expt`), `Tom.defPrec` (`mp_init`), `Tom.Machine.Api.Multi.blocks` (`mp_clear_multi`), `Tom.Machine.Api.Alloc.Keep` (`mp_clear`), `Tom.MpInt.cleared` (`mp_clear`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.impureBytes` (`mp_clear`), `Tom.Machine.Api.Alloc.impurePtr` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`), `Tom.Machine.Api.Alloc.Stk` (`mp_clear_multi`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`)
-/

/-! ## `mp_init_size`

`mp_err mp_init_size(mp_int *a, int size);`

Coverage: contract.
-/

/-- `mp_init`, `mp_init_size`: the standard contracts -/
theorem Specs.mp_init_size_correct : Tom.Machine.Api.MpInit.SizeStatement :=
  Tom.Machine.Fn.MpInit.size_correct
/-
Machine plumbing: regions stk aS code; written [.stk, .aS].

-- Tom/Machine/Api/MpInit.lean
/-- **`mp_init_size(a, size)` on the machine** (`0 ≤ size < 2^31`). -/
def SizeStatement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp pa size : Nat} {ra : BitVec 64},
    Pre m v H sp pa Fsize ra → size < 2 ^ 31 →
    Triple (At Fn.MpInit.sizeEntry (sizeL ra pa (BitVec.ofNat 64 size)) m v.keep outp)
      (Ret m v outp H sp pa Fsize (initPrec size) ra)

/-- The stack depth of `mp_init_size`: its 32-byte frame and `calloc`'s. -/
abbrev Fsize : Nat := 32 + callocDepth

/-- The entry of `mp_init_size`: `ra`, `a0 = a`, `a1 = size`. -/
def sizeL (ra : BitVec 64) (pa : Nat) (size : BitVec 64) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 pa), (11, size)]

Also used (printed above): `Tom.Machine.Api.MpInit.Pre` (`mp_init`), `Tom.Machine.Api.MpInit.Ret` (`mp_init`), `Tom.initPrec` (`mp_gcd`), `Tom.Machine.Api.Alloc.Heap` (`mp_clear`), `Tom.Machine.Api.Heap.ACtx` (`mp_clear`), `Tom.Machine.Api.Alloc.callocDepth` (`mp_init`), `Tom.Machine.Api.MpInit.Post` (`mp_init`), `Tom.minPrec` (`mp_gcd`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.Machine.Api.Alloc.ImpureAt` (`mp_clear`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.Alloc.Fresh` (`mp_gcd`), `Tom.Machine.Api.Heap.MpLive` (`mp_init`), `Tom.MpInt.zeroN` (`mp_2expt`), `Tom.Machine.Api.Heap.HFrm` (`mp_clear`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.impureBytes` (`mp_clear`), `Tom.Machine.Api.Alloc.impurePtr` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`), `Tom.Machine.Api.Alloc.Keep` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`)
-/

/-! ## `mp_invmod`

`mp_err mp_invmod(const mp_int *a, const mp_int *b, mp_int *c);`

Coverage: contract (b of any size: Api.MpInvmodG, the workers' mp_copy growing their temporaries; its assembly MpInvmodG5 over the two workers' proofs; the D5 Api.MpInvmod.Statement derived, Fn.Invmod.correct by MpInvmodG.Statement.d5).
-/

/-- `mp_invmod`, `s_mp_invmod_fast`, `s_mp_invmod_slow`: the allocating contracts -/
theorem Specs.mp_invmod_correct : Tom.Machine.Api.MpInvmodG.Statement :=
  Tom.Machine.Fn.Invmod.correctG
/-
Machine plumbing: the arguments: `a0 = a`, `a1 = b`, `a2 = c`; stack reservation `F = 1232`; regions stk aS aD bS bD cS cD code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/Invmod.lean
/-- **`mp_invmod(a, b, c)` on the machine, `b` of any size** (no D5 room). -/
def Statement : Prop := Spec MpInvmod.entry BaseG MpInvmod.Q

/-- A run of one of the three from `entry`, with residue `Res` and outcome `Q`. -/
def Spec (entry : BitVec 64) (Res : P → Prop) (Q : P → Out → Prop) : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

/-- `Base` without the D5 room: every `mp_copy` into a temporary grows it. -/
structure BaseG (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  vb : p.b.Valid
  /-- `mp_mod(a, b, ·)` (`Api/MpMod.lean`): `mp_div`'s sizes. -/
  au : p.a.used + 3 < 2 ^ 30
  /-- `c` is live: `mp_clear_multi` frees its old block after the exchange. -/
  cpos : 0 < p.c.alloc
  /-- `mp_mod`'s `mp_div` copies from the operands' live nonempty blocks. -/
  ablk : digBlk p.adp p.a ∈ p.H
  bblk : digBlk p.bdp p.b ∈ p.H
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- The structs lie off the arena. -/
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24

/-- `MP_MEM`, or what `InvmodPost` says. -/
def Q (p : P) : Out → Prop
  | .err r => r = Layout.mpMem ∨ InvmodPost p.a p.b p.c p.c r
  | .ok _ c' => InvmodPost p.a p.b p.c c' Layout.mpOkay

structure P where  (sp pa adp pb bdp pc cdp : Nat); (a b c : MpInt); (H : List (Nat × Nat))

/-- An error `r` (`c` as it was), or `MP_OKAY` with `c'`'s digits at `q`. -/
inductive Out
  | err (r : Int)
  | ok (q : Nat) (c' : MpInt)

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.InvmodPost` (`mp_exptmod`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.InvmodErr` (`mp_exptmod`), `Tom.InvmodFastPost` (`mp_exptmod`), `Tom.InvmodSlowPost` (`mp_exptmod`), `Tom.Gcd.fastRes` (`mp_exptmod`), `Tom.invmodRem` (`mp_exptmod`), `Tom.Gcd.slowRes` (`mp_exptmod`), `Tom.Gcd.fastTop` (`mp_exptmod`), `Tom.Gcd.fastInit` (`mp_exptmod`), `Tom.Gcd.norm` (`mp_exptmod`), `Tom.Gcd.slowTop` (`mp_exptmod`), `Tom.Gcd.slowInit` (`mp_exptmod`), `Tom.Gcd.FastSt` (`mp_exptmod`), `Tom.Gcd.fastPass` (`mp_exptmod`), `Tom.Gcd.subDown` (`mp_exptmod`), `Tom.Gcd.addUp` (`mp_exptmod`), `Tom.Gcd.SlowSt` (`mp_exptmod`), `Tom.Gcd.slowPass` (`mp_exptmod`), `Tom.Gcd.fastSub` (`mp_exptmod`), `Tom.Gcd.fastLoopV` (`mp_exptmod`), `Tom.Gcd.fastLoopU` (`mp_exptmod`), `Tom.Gcd.slowSub` (`mp_exptmod`), `Tom.Gcd.slowLoopV` (`mp_exptmod`), `Tom.Gcd.slowLoopU` (`mp_exptmod`), `Tom.Gcd.fastHalfV` (`mp_exptmod`), `Tom.Gcd.fastHalfU` (`mp_exptmod`), `Tom.Gcd.slowHalfV` (`mp_exptmod`), `Tom.Gcd.slowHalfU` (`mp_exptmod`)
-/

/-- `mp_invmod`, `s_mp_invmod_fast`, `s_mp_invmod_slow`: the allocating contracts -/
theorem Specs.mp_invmod_correct_room : Tom.Machine.Api.MpInvmod.Statement :=
  Tom.Machine.Fn.Invmod.correct
/-
Machine plumbing: entry `0x8000150c`; the arguments: `a0 = a`, `a1 = b`, `a2 = c`; stack reservation `F = 1232`; regions stk aS aD bS bD cS cD code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/Invmod.lean
/-- **`mp_invmod(a, b, c)` on the machine.** -/
def Statement : Prop := Spec entry Base Q

/-- What all three need. -/
structure Base (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  vb : p.b.Valid
  /-- D5: `mp_copy(b, &x)` into a fresh temporary does not grow it (`InvmodFastStep.Env.room`). -/
  room : p.b.used ≤ defPrec
  /-- `mp_mod(a, b, ·)` (`Api/MpMod.lean`): `mp_div`'s sizes. -/
  au : p.a.used + 3 < 2 ^ 30
  /-- `c` is live: `mp_clear_multi` frees its old block after the exchange. -/
  cpos : 0 < p.c.alloc
  /-- `mp_mod`'s `mp_div` copies from the operands' live nonempty blocks. -/
  ablk : digBlk p.adp p.a ∈ p.H
  bblk : digBlk p.bdp p.b ∈ p.H
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- The structs lie off the arena. -/
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24

Also used (printed above): `Tom.Machine.Api.Invmod.Spec` (`mp_invmod`), `Tom.Machine.Api.MpInvmod.Q` (`mp_invmod`), `Tom.Machine.Api.Invmod.P` (`mp_invmod`), `Tom.Machine.Api.Invmod.Out` (`mp_invmod`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.defPrec` (`mp_init`), `Tom.InvmodPost` (`mp_exptmod`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.InvmodErr` (`mp_exptmod`), `Tom.InvmodFastPost` (`mp_exptmod`), `Tom.InvmodSlowPost` (`mp_exptmod`), `Tom.Gcd.fastRes` (`mp_exptmod`), `Tom.invmodRem` (`mp_exptmod`), `Tom.Gcd.slowRes` (`mp_exptmod`), `Tom.Gcd.fastTop` (`mp_exptmod`), `Tom.Gcd.fastInit` (`mp_exptmod`), `Tom.Gcd.norm` (`mp_exptmod`), `Tom.Gcd.slowTop` (`mp_exptmod`), `Tom.Gcd.slowInit` (`mp_exptmod`), `Tom.Gcd.FastSt` (`mp_exptmod`), `Tom.Gcd.fastPass` (`mp_exptmod`), `Tom.Gcd.subDown` (`mp_exptmod`), `Tom.Gcd.addUp` (`mp_exptmod`), `Tom.Gcd.SlowSt` (`mp_exptmod`), `Tom.Gcd.slowPass` (`mp_exptmod`), `Tom.Gcd.fastSub` (`mp_exptmod`), `Tom.Gcd.fastLoopV` (`mp_exptmod`), `Tom.Gcd.fastLoopU` (`mp_exptmod`), `Tom.Gcd.slowSub` (`mp_exptmod`), `Tom.Gcd.slowLoopV` (`mp_exptmod`), `Tom.Gcd.slowLoopU` (`mp_exptmod`), `Tom.Gcd.fastHalfV` (`mp_exptmod`), `Tom.Gcd.fastHalfU` (`mp_exptmod`), `Tom.Gcd.slowHalfV` (`mp_exptmod`), `Tom.Gcd.slowHalfU` (`mp_exptmod`)
-/

/-! ## `mp_lshd`

`mp_err mp_lshd(mp_int *a, int b);`
-/

/-- `mp_lshd(a, k)` with growth: the allocating contract -/
theorem Specs.mp_lshd_correct : Tom.Machine.Api.MpLshdG.Statement :=
  Tom.Machine.Fn.MpLshdGG5.correct
/-
Machine plumbing: entry `0x800015b8`; the arguments: `a0 = a`, `a1 = k` (`gp` for the allocator); stack reservation `F = 32 + MpGrow.F`; regions stk aS aD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MpLshdG.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

structure P where  (sp pa adp : Nat); (a : MpInt); (k : Nat); (H : List (Nat × Nat))

/-- What `mp_lshd(a, k)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The shift reads `a`'s digits below `used` and `alloc` (`mp_grow` keeps them). -/
  sa : p.a.Shape
  /-- The C's `int b`, nonnegative. -/
  k_lt : p.k < 2 ^ 31
  /-- `mp_grow(a, a->used + b)`'s `int size` (`addw` at `15d8`). -/
  size_lt : p.a.used + p.k < 2 ^ 31
  /-- `a`'s digits are `realloc`'s block: live and nonempty. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.a.alloc < p.a.used + p.k
  | some (_, a') => LshdPost (lshdIn p.a p.k) p.k a'

-- Tom/Spec/DigitShift.lean
/-- What `mp_lshd(a, k)` leaves, by branch (`a->alloc ≥ a->used + k`). -/
structure LshdPost (a : MpInt) (k : Nat) (a' : MpInt) : Prop where
  noop : k = 0 ∨ a.used = 0 → a' = a
  shift : 0 < k → 0 < a.used → LshdShift a k a'
theorem LshdPost.spec {a a' : MpInt} {k : Nat} (ha : a.Valid) (hroom : a.used + k ≤ a.alloc)
    (h : LshdPost a k a') : a'.Valid ∧ a'.mag = a.mag * radix ^ k := …  -- proved in Tom/Spec/DigitShift.lean

-- Tom/Spec/Grow6Step.lean
/-- What `mp_lshd(a, k)` shifts. -/
def lshdIn (a : MpInt) (k : Nat) : MpInt :=
  if a.alloc < a.used + k ∧ 0 < k ∧ 0 < a.used then a.growTo (a.used + k) else a

-- Tom/Spec/DigitShift.lean
/-- The shifting branch of `mp_lshd(a, k)` (`0 < k`, `0 < used`). -/
structure LshdShift (a : MpInt) (k : Nat) (a' : MpInt) : Prop where
  alloc : a'.alloc = a.alloc
  len : a'.digits.length = a.alloc
  used : a'.used = a.used + k
  sign : a'.sign = a.sign
  digit : ∀ i, a'.digit i = if i < k then 0 else if i < a.used + k then a.digit (i - k) else a.digit i
theorem LshdShift.spec {a a' : MpInt} {k : Nat} (ha : a.Valid) (hroom : a.used + k ≤ a.alloc)
    (hu : 0 < a.used) (h : LshdShift a k a') : a'.Valid ∧ a'.mag = a.mag * radix ^ k := …  -- proved in Tom/Spec/DigitShift.lean

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.MpInt.ofDigits` (`mp_abs`)
-/

/-- `mp_lshd`: the standard contract -/
theorem Specs.mp_lshd_correct_room : Tom.Machine.Api.MpLshd.Statement :=
  Tom.Machine.Fn.MpLshd.correct
/-
Machine plumbing: entry `0x800015b8`; regions stk aS aD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MpLshd.lean
/-- **`mp_lshd` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {b : Nat} {ra s0 : BitVec 64},
    Pre m sp pa adp a b ra →
    Triple (At entry (Fn.MpLshd.entryL ra s0 sp pa b) m v.keepR outp) (Ret m v outp sp pa adp a b ra s0)

/-- What `mp_lshd(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  b_lt : b < 2 ^ 31
  room : a.used + b ≤ a.alloc
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp a) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra s0 : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra (Fn.MpLshd.retL ra s0 sp) M v.keepR outp cf ∧ Post m sp pa adp a b a' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  lshd : LshdPost a b a'
  frame : Frm (lay sp pa adp a) ws m M

Also used (printed above): `Tom.LshdPost` (`mp_lshd`), `Tom.LshdShift` (`mp_lshd`)
-/

/-! ## `mp_mod`

`mp_err mp_mod(const mp_int *a, const mp_int *b, mp_int *c);`

Coverage: contract.
-/

/-- `mp_mod(a, b, c)`: the allocating contract -/
theorem Specs.mp_mod_correct : Tom.Machine.Api.MpMod.Statement :=
  Tom.Machine.Fn.MpModG5.correct
/-
Machine plumbing: entry `0x80001680`; the arguments: `a0 = a`, `a1 = b`, `a2 = c`; stack reservation `F = 80 + MpDivR.F`; regions stk aS aD bS bD cS cD code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/MpMod.lean
def Statement : Prop := Standard.Statement Res Q (site .cD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp pc cdp : Nat); (a b c : MpInt); (H : List (Nat × Nat))

/-- What `mp_mod(a, b, c)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_div` reads `a`, `b` as valid integers. -/
  va : p.a.Valid
  vb : p.b.Valid
  /-- `b ≠ 0`: `mp_div`'s `MP_VAL` is not covered. -/
  bnz : 0 < p.b.used
  /-- `mp_div`'s `mp_count_bits(&y)` is an `int`. -/
  bits : Layout.digitBits * p.b.used < 2 ^ 31
  /-- `mp_div`'s `mp_init_size(&q, a->used + 2)` and its loops' indices fit. -/
  au : p.a.used + 3 < 2 ^ 30
  /-- `mp_add(b, &t, c)`: `c`'s old digits above the sum are zeroed only up to its old `used`. -/
  sc : p.c.Shape
  /-- `mp_add`'s `mp_grow` size (`t->used ≤ b->used`). -/
  bsize : p.b.used + 1 < 2 ^ 31
  /-- `c`'s digits: the block `mp_clear(&t)` frees after the exchange, `mp_add`'s `realloc`'s. -/
  cpos : 0 < p.c.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24
  /-- `mp_div`'s `mp_init_copy(&x, a)`, `mp_init_copy(&y, b)` copy from live nonempty blocks. -/
  ablk : digBlk p.adp p.a ∈ p.H
  apos : 0 < p.a.alloc
  bblk : digBlk p.bdp p.b ∈ p.H

/-- What `c` holds. -/
def Q (p : P) : Out → Prop
  | .mem c' => c' = { p.c with sign := c'.sign }
  | .ok _ c' => ModPost p.a p.b c'

/-- `MP_MEM` (`c`'s header after), or `MP_OKAY` with `c'`'s digits at `q`. -/
inductive Out
  | mem (c' : MpInt)
  | ok (q : Nat) (c' : MpInt)

-- Tom/Spec/Div.lean
/-- What `mp_mod(a, b, c)` leaves in `c` (`b ≠ 0`): with `t = a.tmod b` (the
remainder `mp_div` leaves, `DivRem.spec`), `t` itself when it is zero or has `b`'s
sign (`a`'s sign when nonzero), else `b + t` (`mp_add`, `AddPost.spec`). -/
structure ModPost (a b c' : MpInt) : Prop where
  keep : (a.mag % b.mag = 0 ∨ a.sign = b.sign) → HasVal c' (a.val.tmod b.val)
  add : ¬ (a.mag % b.mag = 0 ∨ a.sign = b.sign) → HasVal c' (b.val + a.val.tmod b.val)
theorem ModPost.spec {a b c' : MpInt} (ha : a.Valid) (hb : b.Valid) (hb0 : 0 < b.used) (h : ModPost a b c') :
    HasVal c' (a.val.fmod b.val) := …  -- proved in Tom/Spec/Div.lean

/-- A valid `mp_int` with value `v`. -/
structure HasVal (x : MpInt) (v : Int) : Prop where
  valid : x.Valid
  val : x.val = v

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`)
-/

/-! ## `mp_mod_2d`

`mp_err mp_mod_2d(const mp_int *a, int b, mp_int *c);`
-/

/-- `mp_mod_2d`: the standard contract -/
theorem Specs.mp_mod_2d_correct : Tom.Machine.Api.MpMod2d.Statement :=
  Tom.Machine.Fn.MpMod2d.correct
/-
Machine plumbing: entry `0x800057a4`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/MpMod2d.lean
/-- **`mp_mod_2d` on the machine** (distinct operands). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat} {c : MpInt}
    {ra s0 : BitVec 64}, Pre m sp pa adp pc cdp a b c ra →
    Triple (At entry (Fn.MpMod2d.entryL ra s0 sp pa b pc) m v.keepR outp)
      (Ret m v outp sp pa adp pc cdp a b c ra s0)

/-- What `mp_mod_2d(a, b, c)` needs. -/
structure Pre (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rc : MpAt m pc cdp c
  va : a.Valid
  sc : c.Shape
  ga : MpGeom pa adp a.alloc
  gc : MpGeom pc cdp c.alloc
  b_lt : b < 2 ^ 31
  bits : Layout.digitBits * a.used < 2 ^ 31
  room : a.used ≤ c.alloc
  rs : Ram (sp - 80) 80
  sp_al : sp % 16 = 0
  sp_ge : 80 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pc cdp a c) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pc cdp a b c c' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  mod : Mod2dPost a b c c'
  frame : Frm (lay sp pa adp pc cdp a c) ws m M

Also used (printed above): `Tom.Mod2dPost` (`mp_div_2d`), `Tom.ClampedTo` (`mp_div`), `Tom.mod2dDigit` (`mp_div_2d`), `Tom.clampUsed` (`mp_add`)
-/

/-- `mp_mod_2d(a, b, a)`: the in-place contract -/
theorem Specs.mp_mod_2d_correct_inplace : Tom.Machine.Api.MpMod2dI.Statement :=
  Tom.Machine.Fn.MpMod2dIG5.correct
/-
Machine plumbing: entry `0x800057a4`.

-- Tom/Machine/Api/MpMod2dI.lean
/-- **`mp_mod_2d(a, b, a)` on the machine** (in place). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {b : Nat} {ra s0 : BitVec 64},
    Pre m sp pa adp a b ra →
    Triple (At entry (Fn.MpMod2d.entryL ra s0 sp pa b pa) m v.keepR outp) (Ret m v outp sp pa adp a b ra s0)

/-- What `mp_mod_2d(a, b, a)` needs. -/
structure Pre (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  va : a.Valid
  ga : MpGeom pa adp a.alloc
  /-- `b > 0`: `mp_div_2d` calls `mp_mod_2d` only on its shifting path (`b ≤ 0` copies and
  zeroes `d` itself), so the `b ≤ 0` branch (`mp_zero`) is not needed here. -/
  b_pos : 0 < b
  /-- The C's `int b`. -/
  b_lt : b < 2 ^ 31
  /-- The C's `a->used * MP_DIGIT_BIT` does not overflow (as `Api.MpMod2d`). -/
  bits : Layout.digitBits * a.used < 2 ^ 31
  rs : Ram (sp - 48) 48
  sp_al : sp % 16 = 0
  sp_ge : 48 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp a) Un.isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (b : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp a b a' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  mod : Mod2dPost a b a a'
  frame : Frm (lay sp pa adp a) Un.ws m M

Also used (printed above): `Tom.Mod2dPost` (`mp_div_2d`), `Tom.ClampedTo` (`mp_div`), `Tom.mod2dDigit` (`mp_div_2d`), `Tom.clampUsed` (`mp_add`)
-/

/-! ## `mp_montgomery_calc_normalization`

`mp_err mp_montgomery_calc_normalization(mp_int *a, const mp_int *b);`
-/

/-- `mp_montgomery_calc_normalization(a, b)` growing `a`: the allocating contract -/
theorem Specs.mp_montgomery_calc_normalization_correct : Tom.Machine.Api.MontNormG.Statement :=
  Tom.Machine.Fn.MontNormGG5.correct
/-
Machine plumbing: entry `0x800058b4`; the arguments: `a0 = a`, `a1 = b` (`gp` for the allocator); stack reservation `F = 656`; regions stk aS aD bS bD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MontNormG.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp : Nat); (a b : MpInt); (H : List (Nat × Nat))

/-- What `mp_montgomery_calc_normalization(a, b)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_2expt` zeroes and grows `a`; `mp_set` writes it. -/
  sa : p.a.Shape
  /-- `b` a Montgomery modulus. -/
  vb : p.b.Valid
  odd : p.b.mag % 2 = 1
  gt1 : 1 < p.b.mag
  /-- The C's `int`s: `mp_count_bits(b)` and the exponent `28 (b->used - 1) + bits - 1`. -/
  bits : Layout.digitBits * p.b.used < 2 ^ 31
  /-- `a`'s digits are `realloc`'s block: live and nonempty. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

def Q (p : P) (x : X) : Prop := Out p x

/-- `(ok, q, a')`: `a'`'s digits at `q`. -/
abbrev X : Type := ReduxG.X

/-- What `a` holds after: shaped, live, placed (inside the old block or a fresh one); on `MP_OKAY`
`Mont.NormPost b a'`. -/
structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) (lay p .aD) (site' p x)
  post : x.1 = true → Mont.NormPost p.b x.2.2

-- Tom/Spec/Mont.lean
/-- What `mp_montgomery_calc_normalization(a, b)` leaves in `a` (allocation not failing):
`2^normE0` doubled `normCnt` times with one conditional subtraction each. -/
structure NormPost (b a' : MpInt) : Prop where
  valid : a'.Valid
  mag : a'.mag = normLoop b.mag (2 ^ normE0 b) (normCnt b)
  sign : a'.sign = Layout.mpZpos
theorem NormPost.spec {b a' : MpInt} (hb : b.Valid) (hodd : b.mag % 2 = 1) (h1 : 1 < b.mag)
    (h : NormPost b a') : a'.Valid ∧ a'.mag = radix ^ b.used % b.mag ∧ a'.val = (radix ^ b.used % b.mag : Nat) := …  -- proved in Tom/Spec/Mont.lean

def normLoop (b : Nat) : Nat → Nat → Nat
  | a, 0 => a
  | a, k + 1 => normLoop b (normStep b a) k

/-- The start of `mp_montgomery_calc_normalization(a, b)`: the exponent `e` of the first
`a = 2^e` (`mp_2expt` for `b->used > 1`, `mp_set(a, 1)` else) and the number of doublings
(`for (x = bits - 1; x < MP_DIGIT_BIT; x++)`), with `bits = mp_count_bits(b) % MP_DIGIT_BIT`
(set to `1` in the one-digit case). -/
def normE0 (b : MpInt) : Nat :=
  if 1 < b.used then (b.used - 1) * Layout.digitBits + nbits b.mag % Layout.digitBits - 1 else 0

def normCnt (b : MpInt) : Nat :=
  if 1 < b.used then Layout.digitBits + 1 - nbits b.mag % Layout.digitBits else Layout.digitBits

/-- One pass: `mp_mul_2(a, a)`, then `s_mp_sub(a, b, a)` unless `mp_cmp_mag(a, b) == MP_LT`. -/
def normStep (b a : Nat) : Nat := if b ≤ 2 * a then 2 * a - b else 2 * a

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.ReduxG.X` (`mp_dr_reduce`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Mont.nbits` (`mp_exptmod`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`)
-/

/-- `mp_montgomery_calc_normalization`: the standard contract -/
theorem Specs.mp_montgomery_calc_normalization_correct_room : Tom.Machine.Api.MontNorm.Statement :=
  Tom.Machine.Fn.MontNorm.correct
/-
Machine plumbing: entry `0x800058b4`; regions stk aS aD bS bD code.

-- Tom/Machine/Api/MontNorm.lean
/-- **`mp_montgomery_calc_normalization` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    Pre m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.MontNorm.entryL ra s0 sp pa pb) m v.keepR outp) (Ret m v outp sp pa adp pb bdp a b ra s0)

/-- What `mp_montgomery_calc_normalization(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  sa : a.Shape
  vb : b.Valid
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  odd : b.mag % 2 = 1
  gt1 : 1 < b.mag
  bits : Layout.digitBits * b.used < 2 ^ 31
  room : b.used + 1 ≤ a.alloc
  rs : Ram (sp - 112) 112
  sp_al : sp % 16 = 0
  sp_ge : 112 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp a b) isWA

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra s0 : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp a b a' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp : Nat) (a b a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  norm : Mont.NormPost b a'
  alloc : a'.alloc = a.alloc
  frame : Frm (lay sp pa adp pb bdp a b) wsA m M

Also used (printed above): `Tom.Machine.Api.BinA.isWA` (`mp_add`), `Tom.Mont.NormPost` (`mp_montgomery_calc_normalization`), `Tom.Machine.Api.BinA.wsA` (`mp_add`), `Tom.Mont.normLoop` (`mp_montgomery_calc_normalization`), `Tom.Mont.normE0` (`mp_montgomery_calc_normalization`), `Tom.Mont.normCnt` (`mp_montgomery_calc_normalization`), `Tom.Mont.normStep` (`mp_montgomery_calc_normalization`), `Tom.Mont.nbits` (`mp_exptmod`)
-/

/-! ## `mp_montgomery_reduce`

`mp_err mp_montgomery_reduce(mp_int *x, const mp_int *n, mp_digit rho);`

Coverage: contract.
-/

/-- `mp_montgomery_reduce(x, n, rho)` growing `x`: the allocating contract -/
theorem Specs.mp_montgomery_reduce_correct : Tom.Machine.Api.MontRedGr.Statement :=
  Tom.Machine.Fn.MontRedGrG5.correct
/-
Machine plumbing: entry `0x800059e0`; the arguments: `a0 = a`, `a1 = n`, `a2 = d` (`gp` for the allocator); stack reservation `F = 4800`; regions stk aS aD nS nD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MontRedGr.lean
/-- **`mp_montgomery_reduce(x, n, rho)` on the machine, growing `x`**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) MpReduce2k.isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: MpReduce2k.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) MpReduce2k.ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

/-- What `mp_montgomery_reduce(x, n, rho)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  vn : p.n.Valid
  /-- `rho` from `mp_montgomery_setup(n, &rho)`: `n rho ≡ -1 (mod radix)`. -/
  rho_ok : (p.n.mag * p.d + 1) % radix = 0
  rho_lt : p.d < radix
  /-- REDC's input range: `|x| < |n| R`. -/
  x_lt : p.a.mag < p.n.mag * radix ^ p.n.used
  /-- `x`'s digits are `realloc`'s block: live and nonempty. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  noff : OffHeap p.pn 24

def Q (p : P) (x : X) : Prop := ReduxG.Out p (lay p .aD) (MontRedFastGStep.RedcV p.a p.n p.d) x

abbrev X := ReduxG.X

-- Tom/Spec/MontRedFastGStep.lean
/-- What a growing Montgomery reduction leaves in `x`: `RedcPost` without the block (`x` may have been
re-placed): valid, `redc |x| |n| rho n->used`, `x`'s sign unless zero. -/
structure RedcV (x n : MpInt) (rho : Nat) (x' : MpInt) : Prop where
  valid : x'.Valid
  mag : x'.mag = redc x.mag n.mag rho n.used
  sign : x'.sign = if x'.used = 0 then Layout.mpZpos else x.sign
theorem RedcV.spec {x n x' : MpInt} {rho : Nat} (hrho : (n.mag * rho + 1) % radix = 0)
    (hx : x.mag < n.mag * radix ^ n.used) (h : RedcV x n rho x') :
    x'.Valid ∧ x'.mag < n.mag ∧ (x'.mag * radix ^ n.used) % n.mag = x.mag % n.mag := …  -- proved in Tom/Spec/MontRedFastGStep.lean

Also used (printed above): `Tom.Machine.Api.MpReduce2k.P` (`mp_dr_reduce`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.ReduxG.Out` (`mp_dr_reduce`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.ReduxG.X` (`mp_dr_reduce`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`)
-/

/-- `mp_montgomery_reduce`: the standard contract -/
theorem Specs.mp_montgomery_reduce_correct_room : Tom.Machine.Api.MontRed.Statement :=
  Tom.Machine.Fn.MontRedG5.correct
/-
Machine plumbing: entry `0x800059e0`; stack reservation `F = 4256`.

-- Tom/Machine/Api/MontRed.lean
/-- **`mp_montgomery_reduce` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp px xdp pn ndp : Nat} {x n : MpInt} {rho : Nat}
    {ra s0 : BitVec 64}, Pre m sp px xdp pn ndp x n rho ra →
    Triple (At entry (entryL ra s0 sp px pn rho) m v.keepR outp) (Ret m v outp sp px xdp pn ndp x n rho ra s0)

/-- What `mp_montgomery_reduce(x, n, rho)` needs. -/
structure Pre (m : Mem) (sp px xdp pn ndp : Nat) (x n : MpInt) (rho : Nat) (ra : BitVec 64) : Prop where
  rx : MpAt m px xdp x
  rn : MpAt m pn ndp n
  vx : x.Valid
  vn : n.Valid
  gx : MpGeom px xdp x.alloc
  gn : MpGeom pn ndp n.alloc
  /-- `rho` from `mp_montgomery_setup(n, &rho)`: `n rho ≡ -1 (mod radix)` (`SetupPost.spec`). -/
  rho_ok : (n.mag * rho + 1) % radix = 0
  /-- `rho` is an `mp_digit` (`setupRho_lt`). -/
  rho_lt : rho < radix
  /-- REDC's input range: `|x| < |n| R` (every caller reduces a product of two residues). -/
  x_lt : x.mag < n.mag * radix ^ n.used
  /-- D5: `x->alloc ≥ digs = 2 n->used + 1`, so neither path calls `mp_grow`. -/
  room : 2 * n.used + 1 ≤ x.alloc
  rs : Ram (sp - 4256) 4256
  sp_al : sp % 16 = 0
  sp_ge : 4256 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp px xdp pn ndp x n) Two.isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp px xdp pn ndp : Nat) (x n : MpInt) (rho : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ x' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp px xdp pn ndp x n rho x' M

/-- What it leaves. -/
structure Post (m : Mem) (sp px xdp pn ndp : Nat) (x n : MpInt) (rho : Nat) (x' : MpInt) (M : Mem) : Prop where
  repr : MpAt M px xdp x'
  redc : RedcPost x n rho x'
  frame : Frm (lay sp px xdp pn ndp x n) Two.ws m M

-- Tom/Spec/Mont.lean
/-- The REDC result for `n->used = nu` rows. -/
def redc (x n rho nu : Nat) : Nat := montOut (redcT x n rho nu / radix ^ nu) n

/-- What `mp_montgomery_reduce(x, n, rho)` and `s_mp_montgomery_reduce_fast(x, n, rho)`
leave in `x` (with `x->alloc ≥ 2 n->used + 1`, resp. `≥ n->used + 1`, so no `mp_grow`, D5;
the fast one also needs `x->used ≤ MP_WARRAY`, else `MP_VAL` and `x` unchanged): the REDC
result `redc |x| |n| rho n->used`, valid, the sign of `x` (reset if zero). The rows
(`slowRows_spec` resp. `fastRows_spec`, `fastTail_val`, `fastOut_val`) give `T / R`; `mp_clamp`,
`mp_rshd` (slow) and the conditional `s_mp_sub` give `montOut`. -/
structure RedcPost (x n : MpInt) (rho : Nat) (x' : MpInt) : Prop where
  valid : x'.Valid
  alloc : x'.alloc = x.alloc
  mag : x'.mag = redc x.mag n.mag rho n.used
  sign : x'.sign = if x'.used = 0 then Layout.mpZpos else x.sign
theorem RedcPost.spec {x n x' : MpInt} {rho : Nat} (hrho : (n.mag * rho + 1) % radix = 0)
    (hx : x.mag < n.mag * radix ^ n.used) (h : RedcPost x n rho x') :
    x'.Valid ∧ x'.mag < n.mag ∧ (x'.mag * radix ^ n.used) % n.mag = x.mag % n.mag := …  -- proved in Tom/Spec/Mont.lean

/-- The final conditional subtraction (`if mp_cmp_mag(x, n) != MP_LT then s_mp_sub`). -/
def montOut (t n : Nat) : Nat := if n ≤ t then t - n else t

/-- The running value after `j` rows: row `j` adds `mu_j * n * radix^j`. -/
def redcT (x n rho : Nat) : Nat → Nat
  | 0 => x
  | j + 1 => redcT x n rho j + redcMu rho (redcT x n rho j) j * n * radix ^ j

/-- `mu = x->dp[ix] * rho mod radix`, the digit `j` of the running value `T`. -/
def redcMu (rho T j : Nat) : Nat := T / radix ^ j % radix * rho % radix
-/

/-! ## `mp_montgomery_setup`

`mp_err mp_montgomery_setup(const mp_int *n, mp_digit *rho);`

Coverage: contract.
-/

/-- `mp_montgomery_setup`: the standard contract -/
theorem Specs.mp_montgomery_setup_correct : Tom.Machine.Api.MpMontSetup.Statement :=
  Tom.Machine.Fn.MpMontSetup.correct
/-
Machine plumbing: regions stk nS nD rho code; written [.stk, .rho].

-- Tom/Machine/Api/MpMontSetup.lean
/-- **`mp_montgomery_setup` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp p dp rp : Nat} {n : MpInt} {ra : BitVec 64},
    Pre m v sp p dp rp n ra →
    Triple (At Fn.MpMontSetup.entry (entryL ra p rp) m v.keep outp) (Ret m v outp sp p dp rp n ra)

/-- What `mp_montgomery_setup(n, rho)` needs. -/
structure Pre (m : Mem) (v : Abi) (sp p dp rp : Nat) (n : MpInt) (ra : BitVec 64) : Prop where
  repr : MpAt m p dp n
  shape : n.Shape
  apos : 0 < n.alloc
  gn : MpGeom p dp n.alloc
  rr : Ram rp 4
  r_al : rp % 4 = 0
  rs : Ram (sp - 48) 48
  sp_al : sp % 16 = 0
  sp_ge : 48 ≤ sp
  sp_v : v.sp = BitVec.ofNat 64 sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp p dp rp n) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp p dp rp : Nat) (n : MpInt) (ra : BitVec 64)
    (c : Vsa.Machine.Config) : Prop :=
  ∃ ret rho M, At ra [(1, ra), (10, BitVec.ofInt 64 ret)] M v.keep outp c ∧ Post m sp p dp rp n ret rho M

/-- What it leaves with result `ret`: `*rho` holds `rho`. -/
structure Post (m : Mem) (sp p dp rp : Nat) (n : MpInt) (ret : Int) (rho : Nat) (M : Mem) : Prop where
  rho_v : bytesT4 M rp = BitVec.ofNat 32 rho
  setup : SetupPost n ret rho
  frame : Frm (lay sp p dp rp n) ws m M

-- Tom/Spec/Mont.lean
/-- What `mp_montgomery_setup(n, &rho)` leaves: `MP_VAL` and nothing written for an
even `n->dp[0]`; otherwise `MP_OKAY` and `rho = setupRho n->dp[0]`. -/
structure SetupPost (n : MpInt) (ret : Int) (rho : Nat) : Prop where
  even : n.digit 0 % 2 = 0 → ret = Layout.mpVal
  odd : n.digit 0 % 2 = 1 → ret = Layout.mpOkay ∧ rho = setupRho (n.digit 0)
theorem SetupPost.spec {n : MpInt} {ret : Int} {rho : Nat} (hn : n.Shape) (h : SetupPost n ret rho)
    (hodd : n.mag % 2 = 1) :
    ret = Layout.mpOkay ∧ rho < radix ∧ (n.mag * rho + 1) % radix = 0 := …  -- proved in Tom/Spec/Mont.lean

/-- `*rho = (mp_digit)(((mp_word)1 << MP_DIGIT_BIT) - x) & MP_MASK`: the subtraction in
`uint64_t`, the cast to `uint32_t`, the mask. -/
def setupRho (b : Nat) : Nat := (2 ^ 28 + 2 ^ 64 - setupX b) % 2 ^ 64 % 2 ^ 32 &&& Layout.mpMask

/-- `x` after the three Newton steps of `MP_32BIT` (`mod 2^8`, `2^16`, `2^32`). -/
def setupX (b : Nat) : Nat := newton b (newton b (newton b (setupX0 b)))

/-- One Newton step `x *= 2u - (b * x)` in `uint32_t`. -/
def newton (b x : Nat) : Nat := x * ((2 + 2 ^ 32 - b * x % 2 ^ 32) % 2 ^ 32) % 2 ^ 32

/-- The start `x = (((b + 2u) & 4u) << 1) + b` (no wrap: `b < 2^28`). -/
def setupX0 (b : Nat) : Nat := (((b + 2) &&& 4) <<< 1) + b
-/

/-! ## `mp_mul`

`mp_err mp_mul(const mp_int *a, const mp_int *b, mp_int *c);`

Coverage: contract (both shapes, no premises; operands with stale digits above used: MulGroupB.mulCorrectU).
-/

/-- `mp_mul(a, b, c)`, `c` distinct from `a` and `b`: the allocating contract -/
theorem Specs.mp_mul_correct : Tom.Machine.Api.MpMul.StatementU :=
  Tom.Machine.Fn.MulGroupB.mulCorrectU
/-
Machine plumbing: entry `0x800018a8`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator and the cut-offs); stack reservation `F = Fm (μ p.a p.b)`; regions stk aS aD bS bD cS cD kc tc code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/MpMul.lean
/-- The contract for operands with stale digits above `used`. -/
def StatementU : Prop := ∀ p : P, SpecR ResU p

structure P where  (sp pa adp pb bdp pc cdp : Nat); (a b c : MpInt); (H : List (Nat × Nat))

/-- The contract at one `p`, for a residue `Rs` (`Api/MulRec.lean` adds the induction hypothesis). -/
def SpecR (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

/-- `Res` with the operands only `ValidU` (digits at and above `used` arbitrary): what the group
proves (`Api/MulRec.lean`), since `s_mp_balance_mul` multiplies a left-over slice with stale digits. -/
structure ResU (p : P) : Prop where
  stk : StkRes p.sp (F p)
  va : p.a.ValidU
  vb : p.b.ValidU
  sc : p.c.Shape
  csign : p.c.sign = Layout.mpZpos ∨ p.c.sign = Layout.mpNeg
  uab : μ p.a p.b < 2 ^ 30
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  cpos : 0 < p.c.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24

def Q (p : P) : X → Prop
  | (ok, _, c') => Out p ok c'

/-- The recursion's measure. -/
def μ (a b : MpInt) : Nat := a.used + b.used

/-- The result: `MP_OKAY`?, `c'`'s digits at `q`, `c'`. -/
abbrev X : Type := Bool × Nat × MpInt

/-- What `c` holds after. -/
structure Out (p : P) (ok : Bool) (c' : MpInt) : Prop where
  shape : c'.Shape
  sign : c'.sign = Layout.mpZpos ∨ c'.sign = Layout.mpNeg
  pos : 0 < c'.alloc
  /-- `MP_OKAY`: the product (`Tom/Spec/MulAlgo.lean`). -/
  post : ok = true → MulPost p.a p.b c'

-- Tom/Spec/MulAlgo.lean
/-- What `mp_mul(a, b, c)` leaves in `c` (whichever algorithm the cut-offs choose): `c` valid
holding `a·b`; the C sets `c->sign := (c->used > 0) ? neg : MP_ZPOS`. -/
structure MulPost (a b c' : MpInt) : Prop where
  valid : c'.Valid
  val : c'.val = a.val * b.val

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`)
-/

/-- `mp_mul(a, b, c)`, `c` distinct from `a` and `b`: the allocating contract -/
theorem Specs.mp_mul_correct_valid : Tom.Machine.Api.MpMul.Statement :=
  Tom.Machine.Fn.MulGroupB.mulCorrect.1
/-
Machine plumbing: entry `0x800018a8`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator and the cut-offs); stack reservation `F = Fm (μ p.a p.b)`; regions stk aS aD bS bD cS cD kc tc code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/MpMul.lean
/-- **`mp_mul(a, b, c)` on the machine**, as an allocating contract. -/
def Statement : Prop := ∀ p : P, Spec p

def Spec (p : P) : Prop := SpecR Res p

/-- What `mp_mul(a, b, c)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp (F p)
  /-- The algorithms read the operands' values; karatsuba's halves are valid because `a`, `b` are. -/
  va : p.a.Valid
  vb : p.b.Valid
  /-- `c` is written (grown, or exchanged with a temporary and freed): shaped. -/
  sc : p.c.Shape
  /-- `s_mp_mul_digs_fast` keeps `c`'s sign word for a nonzero result (`Api/SMpMulDigs.lean` `csign`). -/
  csign : p.c.sign = Layout.mpZpos ∨ p.c.sign = Layout.mpNeg
  /-- The C's `int` sums (`digs = a->used + b->used + 1`, `MulFast.Cond.uab`). -/
  uab : μ p.a p.b < 2 ^ 30
  /-- Nonempty digit arrays (`HContract.pos`); `c`'s is a live block that may be freed. -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  cpos : 0 < p.c.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24

Also used (printed above): `Tom.Machine.Api.MpMul.P` (`mp_mul`), `Tom.Machine.Api.MpMul.SpecR` (`mp_mul`), `Tom.Machine.Api.MpMul.Q` (`mp_mul`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MpMul.μ` (`mp_mul`), `Tom.Machine.Api.MpMul.X` (`mp_mul`), `Tom.Machine.Api.MpMul.Out` (`mp_mul`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.MulPost` (`mp_mul`)
-/

/-- `mp_mul(a, b, a)`: the in-place contract -/
theorem Specs.mp_mul_correct_inplace : Tom.Machine.Api.MpMulA.Statement :=
  Tom.Machine.Fn.MulGroupB.mulCorrect.2
/-
Machine plumbing: entry `0x800018a8`; the arguments: `a0 = a2 = a`, `a1 = b`; stack reservation `F = Fm (μ p.a p.b)`; regions stk aS aD bS bD kc tc code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MpMulA.lean
/-- **`mp_mul(a, b, a)` on the machine.** -/
def Statement : Prop := ∀ p : P, Spec p

structure P where  (sp pa adp pb bdp : Nat); (a b : MpInt); (H : List (Nat × Nat))

def Spec (p : P) : Prop := SpecR Res p

def SpecR (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

/-- `Api.MpMul.Res` with `c = a` (`a` valid, hence shaped with a sign). -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp (F p)
  va : p.a.Valid
  vb : p.b.Valid
  uab : μ p.a p.b < 2 ^ 30
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

def Q (p : P) : X → Prop
  | (ok, _, a') => Out p ok a'

structure Out (p : P) (ok : Bool) (a' : MpInt) : Prop where
  shape : a'.Shape
  sign : a'.sign = Layout.mpZpos ∨ a'.sign = Layout.mpNeg
  pos : 0 < a'.alloc
  post : ok = true → MulPost p.a p.b a'

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MpMul.μ` (`mp_mul`), `Tom.Machine.Api.MpMul.X` (`mp_mul`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.MulPost` (`mp_mul`)
-/

/-- The multiplication group's recursion -/
theorem Specs.mp_mul_below : ∀ n, Tom.Machine.Api.MulRec.MulBelow n :=
  Tom.Machine.Fn.MulGroupB.mulBelow
/-
-- Tom/Machine/Api/MulRec.lean
/-- **The induction hypothesis**: both contracts below measure `n`. -/
def MulBelow (n : Nat) : Prop := ∀ k, k < n → MulAt k

/-- Both `mp_mul` contracts at measure `n`. -/
def MulAt (n : Nat) : Prop :=
  (∀ p : MpMul.P, MpMul.μ p.a p.b = n → MpMul.SpecR MpMul.ResU p) ∧
    (∀ p : MpMulA.P, MpMul.μ p.a p.b = n → MpMulA.Spec p)

Also used (printed above): `Tom.Machine.Api.MpMul.P` (`mp_mul`), `Tom.Machine.Api.MpMul.μ` (`mp_mul`), `Tom.Machine.Api.MpMul.SpecR` (`mp_mul`), `Tom.Machine.Api.MpMul.ResU` (`mp_mul`), `Tom.Machine.Api.MpMulA.P` (`mp_mul`), `Tom.Machine.Api.MpMulA.Spec` (`mp_mul`), `Tom.Machine.Api.MpMul.Q` (`mp_mul`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MpMulA.SpecR` (`mp_mul`), `Tom.Machine.Api.MpMulA.Res` (`mp_mul`), `Tom.Machine.Api.MpMul.X` (`mp_mul`), `Tom.Machine.Api.MpMul.Out` (`mp_mul`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.MpMulA.Q` (`mp_mul`), `Tom.MulPost` (`mp_mul`), `Tom.Machine.Api.MpMulA.Out` (`mp_mul`)
-/

/-! ## `mp_mul_2`

`mp_err mp_mul_2(const mp_int *a, mp_int *b);`
-/

/-- `mp_mul_2(a, b)` with growth, `b` distinct: the allocating contract -/
theorem Specs.mp_mul_2_correct : Tom.Machine.Api.Mul2HD.Statement :=
  Tom.Machine.Fn.Mul2HDG5.correct
/-
Machine plumbing: entry `0x80005ca0`; the arguments: `a0 = a`, `a1 = b` (`gp` for the allocator); stack reservation `F = 576`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/Mul2HD.lean
def Statement : Prop := Standard.Statement Res Q (site .bD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp : Nat); (a b : MpInt); (H : List (Nat × Nat))

structure Res (p : P) : Prop where
  stk : StkRes p.sp 576
  va : p.a.Valid
  /-- `mp_grow` and the `memset` read `b`'s header (`b` shaped; its sign is overwritten). -/
  sb : p.b.Shape
  /-- `a->used + 1` is an `int` (`mp_grow`'s size). -/
  ua : p.a.used + 1 < 2 ^ 30
  /-- The operands' digit arrays are nonempty (initialised `mp_int`s). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- `b`'s struct is off the arena (`mp_grow` reads and writes it). -/
  boff : OffHeap p.pb 24

def Q (p : P) (x : X) : Prop := Out p x

-- Tom/Machine/Api/MpSqr.lean
/-- The result: `MP_OKAY`?, `b'`'s digits at `q`, `b'`. -/
abbrev X : Type := Bool × Nat × MpInt

-- Tom/Machine/Api/Mul2HD.lean
/-- What `b` holds after: shaped, live, placed, grown only; on `MP_OKAY` `2 a`. -/
structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) (lay p .bD) (site' p x)
  grow : p.b.alloc ≤ x.2.2.alloc
  valid : x.1 = true → x.2.2.Valid
  val : x.1 = true → x.2.2.val = 2 * p.a.val

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`)
-/

/-- `mp_mul_2(a, a)` with growth: the allocating contract (a named premise) -/
theorem Specs.mp_mul_2_correct_inplace : Tom.Machine.Api.Mul2H.Statement :=
  Tom.Machine.Fn.Mul2HG5.correct
/-
Machine plumbing: entry `0x80005ca0`; the arguments: `a0 = a1 = a` (`gp` for the allocator); stack reservation `F = 576`; regions stk aS aD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/Mul2H.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

structure P where  (sp pa adp : Nat); (a : MpInt); (H : List (Nat × Nat))

structure Res (p : P) : Prop where
  stk : StkRes p.sp 576
  va : p.a.Valid
  /-- `a->used + 1` is an `int` (`mp_grow`'s size). -/
  ua : p.a.used + 1 < 2 ^ 30
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

def Q (p : P) (x : X) : Prop := Out p x

/-- What `a` holds after: shaped, live, placed, grown only; on `MP_OKAY` doubled. -/
structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) (lay p .aD) (site' p x)
  grow : p.a.alloc ≤ x.2.2.alloc
  valid : x.1 = true → x.2.2.Valid
  val : x.1 = true → x.2.2.val = 2 * p.a.val

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MpSqr.X` (`mp_mul_2`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`)
-/

/-- `mp_mul_2`: the standard contract -/
theorem Specs.mp_mul_2_correct_room : Tom.Machine.Api.Mul2.Statement :=
  Tom.Machine.Fn.Mul2.correct
/-
Machine plumbing: entry `0x80005ca0`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/Mul2.lean
/-- **`mp_mul_2` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat}
    {a b : MpInt} {ra s0 : BitVec 64}, Pre m sp pa adp pb bdp a b ra →
    Triple (At entry (entryL ra s0 sp pa pb) m v.keepR outp)
      (Ret m v outp sp pa adp pb bdp a b ra s0)

/-- What `mp_mul_2(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  va : a.Valid
  sb : b.Shape
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  room : a.used + 1 ≤ b.alloc
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp a b) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ b' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp a b b' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp : Nat) (a b b' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pb bdp b'
  mul2 : Mul2Post a b b'
  frame : Frm (lay sp pa adp pb bdp a b) ws m M

-- Tom/Spec/Shift.lean
/-- What `mp_mul_2(a, b)` leaves in `b` when `b` has room
(`b->alloc ≥ a->used + 1`, so `mp_grow` is not called): the digits of
`a + a`, `used` the operand's plus the final carry, `a`'s sign. -/
structure Mul2Post (a b b' : MpInt) : Prop where
  alloc : b'.alloc = b.alloc
  len : b'.digits.length = b.alloc
  digit : b'.digit = addDigits a a
  used : b'.used = a.used + addCarryAt a a a.used
  sign : b'.sign = a.sign
theorem Mul2Post.spec {a b b' : MpInt} (ha : a.Valid) (hroom : a.used + 1 ≤ b.alloc)
    (hb : b.alloc < 2 ^ 31) (h : Mul2Post a b b') :
    b'.Valid ∧ b'.mag = 2 * a.mag ∧ b'.val = 2 * a.val := …  -- proved in Tom/Spec/Shift.lean

-- Tom/Spec/Indexed.lean
/-- The carry into position `i` of `s_mp_add(a, b, c)`. -/
def addCarryAt (a b : MpInt) : Nat → Nat := carryChain a.digit b.digit 0

Also used (printed above): `Tom.addDigits` (`mp_add`), `Tom.addCarry` (`mp_add`), `Tom.carryChain` (`mp_add_d`)
-/

/-! ## `mp_mul_2d`

`mp_err mp_mul_2d(const mp_int *a, int b, mp_int *c);`
-/

/-- `mp_mul_2d`: the standard contract -/
theorem Specs.mp_mul_2d_correct : Tom.Machine.Api.MpMul2d.Statement :=
  Tom.Machine.Fn.MpMul2d.correct
/-
Machine plumbing: entry `0x80001758`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/MpMul2d.lean
/-- **`mp_mul_2d` on the machine** (distinct operands). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat} {c : MpInt}
    {ra s0 : BitVec 64}, Pre m sp pa adp pc cdp a b c ra →
    Triple (At entry (Fn.MpMul2d.entryL ra s0 sp pa b pc) m v.keepR outp)
      (Ret m v outp sp pa adp pc cdp a b c ra s0)

/-- What `mp_mul_2d(a, b, c)` needs. -/
structure Pre (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rc : MpAt m pc cdp c
  va : a.Valid
  sc : c.Shape
  ga : MpGeom pa adp a.alloc
  gc : MpGeom pc cdp c.alloc
  b_lt : b < 2 ^ 31
  room : a.used + b / Layout.digitBits + 1 ≤ c.alloc
  rs : Ram (sp - 80) 80
  sp_al : sp % 16 = 0
  sp_ge : 80 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pc cdp a c) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pc cdp a b c c' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  mul : Mul2dPost a b c c'
  frame : Frm (lay sp pa adp pc cdp a c) ws m M

-- Tom/Spec/Div2d.lean
/-- What `mp_mul_2d(a, sh, c)` leaves in `c` when `c->alloc ≥ a->used + D + 1` (no
`mp_grow`, D5): the shifted digits, `used` clamped from `a->used + D + 1`, `a`'s sign
unless zero. (The C's `used` is `a->used + D`, plus one if the last carry is
nonzero, then `mp_clamp`: the same.) The in-place call `mp_mul_2d(x, sh, x)` (in
`mp_div`) leaves the same state with `c = a`. -/
def Mul2dPost (a : MpInt) (sh : Nat) (c c' : MpInt) : Prop :=
  ClampedTo c' c.alloc (mul2dDigit a sh) (a.used + sh / Layout.digitBits + 1) a.sign
theorem Mul2dPost.spec {a c c' : MpInt} {sh : Nat} (ha : a.Valid)
    (hroom : a.used + sh / Layout.digitBits + 1 ≤ c.alloc) (hc : c.alloc < 2 ^ 31) (h : Mul2dPost a sh c c') :
    c'.Valid ∧ c'.mag = a.mag * 2 ^ sh ∧ c'.val = a.val * 2 ^ sh := …  -- proved in Tom/Spec/Div2d.lean

/-- Digit `j` of `mp_mul_2d(a, sh, c)`: after `mp_lshd(c, D)` digit `j` is
`a[j - D]` (zero below `D`); the bit loop keeps its low `28 - d` bits shifted up by `d`
and ORs in the carry from the digit below; the last carry is the digit at
`a->used + D`. -/
def mul2dDigit (a : MpInt) (sh j : Nat) : Nat :=
  (if sh / Layout.digitBits ≤ j then shlLo (sh % Layout.digitBits) (a.digit (j - sh / Layout.digitBits))
    else 0) +
  (if sh / Layout.digitBits < j then shlHi (sh % Layout.digitBits) (a.digit (j - sh / Layout.digitBits - 1))
    else 0)

/-- The low part of `e << d` kept in the digit (`(*tmpc << d) & MP_MASK`). -/
def shlLo (d e : Nat) : Nat := e * 2 ^ d % radix

/-- The carry `(*tmpc >> (28 - d)) & mask`: the top `d` bits of `e`. -/
def shlHi (d e : Nat) : Nat := e * 2 ^ d / radix

Also used (printed above): `Tom.ClampedTo` (`mp_div`), `Tom.clampUsed` (`mp_add`)
-/

/-- `mp_mul_2d(a, b, a)`: the in-place allocating contract -/
theorem Specs.mp_mul_2d_correct_inplace : Tom.Machine.Api.MpMul2dI.Statement :=
  Tom.Machine.Fn.MpMul2dIG5.correct
/-
Machine plumbing: entry `0x80001758`; the arguments: `a0 = a`, `a1 = b`, `a2 = a` (`gp` for the allocator); stack reservation `F = 48 + MpGrow.F`; regions stk aS aD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MpMul2dI.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

structure P where  (sp pa adp : Nat); (a : MpInt); (b : Nat); (H : List (Nat × Nat))

/-- What `mp_mul_2d(a, b, a)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The shift reads `a`'s digits below `used` and `alloc` (`mp_grow` keeps them). -/
  sa : p.a.Shape
  /-- The C's `int b`, nonnegative (`bltz` at `1758`: `MP_VAL` is not covered). -/
  b_lt : p.b < 2 ^ 31
  /-- `mp_grow(a, a->used + b / 28 + 1)`'s `int size` (`addw`/`addiw` at `179c`, `1884`). -/
  size_lt : p.a.used + p.b / 28 + 1 < 2 ^ 31
  /-- `a`'s digits are `realloc`'s block: live and nonempty. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.a.alloc < p.a.used + p.b / 28 + 1
  | some (_, a') => Mul2dPost p.a p.b (mul2dIn p.a p.b) a'

-- Tom/Spec/Grow6Step.lean
/-- What `mp_mul_2d(a, b, a)` shifts. -/
def mul2dIn (a : MpInt) (b : Nat) : MpInt :=
  if a.alloc < a.used + b / 28 + 1 then a.growTo (a.used + b / 28 + 1) else a

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Mul2dPost` (`mp_mul_2d`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.ClampedTo` (`mp_div`), `Tom.mul2dDigit` (`mp_mul_2d`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.clampUsed` (`mp_add`), `Tom.shlLo` (`mp_mul_2d`), `Tom.shlHi` (`mp_mul_2d`), `Tom.MpInt.ofDigits` (`mp_abs`)
-/

/-! ## `mp_mul_d`

`mp_err mp_mul_d(const mp_int *a, mp_digit b, mp_int *c);`
-/

/-- `mp_mul_d(a, b, c)` with growth: the allocating contract -/
theorem Specs.mp_mul_d_correct : Tom.Machine.Api.MulDG.Statement :=
  Tom.Machine.Fn.MulDGG5.correct
/-
Machine plumbing: entry `0x800019fc`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator); stack reservation `F = 80 + MpGrow.F`; regions stk aS aD cS cD code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/MulDG.lean
def Statement : Prop := Standard.Statement Res Q (site .cD)  -- the standard shape (top of file)

structure P where  (sp pa adp pc cdp : Nat); (a : MpInt); (b : Nat); (c : MpInt); (H : List (Nat × Nat))

/-- What `mp_mul_d(a, b, c)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The row reads `a`'s digits below `used`. -/
  sa : p.a.Shape
  /-- `a`'s digit array is nonempty (an initialised `mp_int`; the region is then off the arena by
  its own bytes). -/
  apos : 0 < p.a.alloc
  /-- `c->sign = a->sign` is stored as a word (`sw` at `1a40`). -/
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  /-- `c`'s old digits above the result are zeroed only up to its old `used`. -/
  sc : p.c.Shape
  /-- `b` is an `mp_digit` (the products stay below `2^56`). -/
  hb : p.b < radix
  /-- `mp_grow(c, a->used + 1)`'s `int size` (`addiw` at `1b1c`). -/
  size_lt : p.a.used + 1 < 2 ^ 31
  /-- `c`'s digits are `realloc`'s block: live and nonempty. -/
  cpos : 0 < p.c.alloc
  coff : OffHeap p.pc 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.c.alloc < p.a.used + 1
  | some (_, c') => MulDPost p.a p.b (mulDIn p.a p.c) c'

-- Tom/Spec/Mul.lean
/-- What `mp_mul_d(a, b, c)` leaves in `c` when `c->alloc ≥ a->used + 1` (no
`mp_grow`, D5): the row's digits, `used` clamped from `a->used + 1`, `a`'s sign
(reset if zero), `alloc` unchanged. -/
structure MulDPost (a : MpInt) (b : Nat) (c c' : MpInt) : Prop where
  alloc : c'.alloc = c.alloc
  len : c'.digits.length = c.alloc
  digit : c'.digit = mulDDigit a b
  used : c'.used = clampUsed (mulDDigit a b) (a.used + 1)
  sign : c'.sign = if c'.used = 0 then Layout.mpZpos else a.sign
theorem MulDPost.spec {a c c' : MpInt} {b : Nat} (ha : a.Valid) (hb : b < radix)
    (hroom : a.used + 1 ≤ c.alloc) (hc : c.alloc < 2 ^ 31) (h : MulDPost a b c c') :
    c'.Valid ∧ c'.mag = a.mag * b ∧ c'.val = a.val * b := …  -- proved in Tom/Spec/Mul.lean

-- Tom/Spec/Grow6Step.lean
/-- The destination `mp_mul_d(a, b, c)` writes. -/
def mulDIn (a c : MpInt) : MpInt :=
  if c.alloc < a.used + 1 then c.growTo (a.used + 1) else c

-- Tom/Spec/Mul.lean
/-- The digits `mp_mul_d(a, b, c)` leaves: the carry chain of the row, the last
carry at `a.used`, zero above. -/
def mulDDigit (a : MpInt) (b : Nat) (i : Nat) : Nat :=
  if i < a.used then combaD (mulDCol a b) i else if i = a.used then combaW (mulDCol a b) a.used else 0

/-- Digit `k` (`W[ix] = _W & MP_MASK`). -/
def combaD (cl : Nat → Nat) (k : Nat) : Nat := (combaW cl k + cl k) % radix

/-- The row `a * b` for a digit `b`: column `i` is `a.digit i * b`. -/
def mulDCol (a : MpInt) (b : Nat) (i : Nat) : Nat := a.digit i * b

/-- The carry into column `k` (`_W` before the column's terms). -/
def combaW (cl : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (combaW cl k + cl k) / radix

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.clampUsed` (`mp_add`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.MpInt.ofDigits` (`mp_abs`)
-/

/-- `mp_mul_d(a, b, a)` in place, growing `a`: the allocating contract -/
theorem Specs.mp_mul_d_correct_inplace : Tom.Machine.Api.MulDGA.Statement :=
  Tom.Machine.Fn.MulDGAG5.correct
/-
Machine plumbing: entry `0x800019fc`; the arguments: `a0 = a`, `a1 = b`, `a2 = a` (`gp` for the allocator); stack reservation `F = 80 + MpGrow.F`; regions stk aS aD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MulDGA.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

structure P where  (sp pa adp : Nat); (a : MpInt); (b : Nat); (H : List (Nat × Nat))

/-- What `mp_mul_d(a, b, a)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  sa : p.a.Shape
  apos : 0 < p.a.alloc
  /-- `c->sign = a->sign` is stored as a word. -/
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  /-- `b` is an `mp_digit`. -/
  hb : p.b < radix
  /-- `mp_grow(a, a->used + 1)`'s `int size`. -/
  size_lt : p.a.used + 1 < 2 ^ 31
  aoff : OffHeap p.pa 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.a.alloc < p.a.used + 1
  | some (_, a') => MulDPost p.a p.b (mulDIn p.a p.a) a'

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.MulDPost` (`mp_mul_d`), `Tom.mulDIn` (`mp_mul_d`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.mulDDigit` (`mp_mul_d`), `Tom.clampUsed` (`mp_add`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.combaD` (`mp_mul_d`), `Tom.mulDCol` (`mp_mul_d`), `Tom.combaW` (`mp_mul_d`), `Tom.MpInt.ofDigits` (`mp_abs`)
-/

/-- `mp_mul_d`: the standard contracts -/
theorem Specs.mp_mul_d_correct_room : Tom.Machine.Api.MulD.Statement :=
  Tom.Machine.Fn.MulD.correct
/-
Machine plumbing: entry `0x800019fc`.

-- Tom/Machine/Api/MulD.lean
/-- **`mp_mul_d` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp b : Nat}
    {a c : MpInt} {ra s0 : BitVec 64}, Pre m sp pa adp pc cdp a b c ra →
    Triple (At entry (entryL ra s0 sp pa b pc) m v.keepR outp)
      (Ret m v outp sp pa adp pc cdp a b c ra s0)

/-- What `mp_mul_d(a, b, c)` needs. -/
structure Pre (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt) (ra : BitVec 64) :
    Prop where
  ra_ : MpAt m pa adp a
  rc : MpAt m pc cdp c
  sa : a.Shape
  asign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg
  sc : c.Shape
  hb : b < radix
  ga : MpGeom pa adp a.alloc
  gc : MpGeom pc cdp c.alloc
  room : a.used + 1 ≤ c.alloc
  rs : Ram (sp - 80) 80
  sp_al : sp % 16 = 0
  sp_ge : 80 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pc cdp a c) Two.isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pc cdp a b c c' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  muld : MulDPost a b c c'
  frame : Frm (lay sp pa adp pc cdp a c) Two.ws m M

Also used (printed above): `Tom.MulDPost` (`mp_mul_d`), `Tom.mulDDigit` (`mp_mul_d`), `Tom.clampUsed` (`mp_add`), `Tom.combaD` (`mp_mul_d`), `Tom.mulDCol` (`mp_mul_d`), `Tom.combaW` (`mp_mul_d`)
-/

/-- `mp_mul_d`: the standard contracts -/
theorem Specs.mp_mul_d_correct_room_inplace : Tom.Machine.Api.MulD.StatementInPlace :=
  Tom.Machine.Fn.MulD.correct_inplace
/-
Machine plumbing: entry `0x800019fc`.

-- Tom/Machine/Api/MulD.lean
/-- **`mp_mul_d(a, b, a)` on the machine.** -/
def StatementInPlace : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp b : Nat}
    {a : MpInt} {ra s0 : BitVec 64}, PreI m sp pa adp a b ra →
    Triple (At entry (entryL ra s0 sp pa b pa) m v.keepR outp)
      (RetI m v outp sp pa adp a b ra s0)

/-- What `mp_mul_d(a, b, a)` needs. -/
structure PreI (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  asign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg
  hb : b < radix
  ga : MpGeom pa adp a.alloc
  room : a.used + 1 ≤ a.alloc
  rs : Ram (sp - 80) 80
  sp_al : sp % 16 = 0
  sp_ge : 80 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (layI sp pa adp a) Un.isW

def RetI (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (b : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostI m sp pa adp a b a' M

abbrev layI (sp pa adp : Nat) (a : MpInt) := Un.lay 80 sp pa adp a

structure PostI (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  muld : MulDPost a b a a'
  frame : Frm (layI sp pa adp a) Un.ws m M

Also used (printed above): `Tom.MulDPost` (`mp_mul_d`), `Tom.mulDDigit` (`mp_mul_d`), `Tom.clampUsed` (`mp_add`), `Tom.combaD` (`mp_mul_d`), `Tom.mulDCol` (`mp_mul_d`), `Tom.combaW` (`mp_mul_d`)
-/

/-! ## `mp_mulmod`

`mp_err mp_mulmod(const mp_int *a, const mp_int *b, const mp_int *c, mp_int *d);`

Coverage: contract (Res.mul := Fn.MulGroupB.mulCorrect.1).
-/

/-- `mp_mulmod(a, b, c, d)`: the allocating contract -/
theorem Specs.mp_mulmod_correct : Tom.Machine.Api.MpMulmod.Statement :=
  Tom.Machine.Fn.MpMulmodG5.correct
/-
Machine plumbing: entry `0x80005d90`; the arguments: `a0 = a`, `a1 = b`, `a2 = c`, `a3 = d`; stack reservation `F = 2864 + 8 * (p.a.used + p.b.used)`; regions stk aS aD bS bD cS cD dS dD kc tc code; written [.stk, .dS, .dD].

-- Tom/Machine/Api/MpMulmod.lean
def Statement : Prop := Standard.Statement Res Q (site .dD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp pc cdp pd ddp : Nat); (a b c d : MpInt); (H : List (Nat × Nat))

/-- What `mp_mulmod(a, b, c, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp (2864 + 8 * (p.a.used + p.b.used))
  /-- `mp_mul`'s contract (proved conditionally on the mp_mul group's gaps). -/
  mul : MpMul.Statement
  /-- `mp_mul` reads valid operands. -/
  va : p.a.Valid
  vb : p.b.Valid
  /-- `mp_mul`'s `int` sums; `mp_mod`'s `mp_div` needs `t->used + 3 < 2^30` (`t->used ≤ a->used + b->used`). -/
  uab : p.a.used + p.b.used + 3 < 2 ^ 30
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- The modulus: valid, positive (`MulmodPost` is stated for `c > 0`; `mp_div`'s `b ≠ 0`). -/
  vc : p.c.Valid
  c0 : 0 < p.c.used
  cz : p.c.sign = Layout.mpZpos
  /-- `mp_mod`'s `mp_div` (`mp_count_bits` an `int`) and `mp_add` (`c->used + 1`). -/
  cbits : Layout.digitBits * p.c.used < 2 ^ 31
  /-- `mp_mod(&t, c, d)` writes `d`: shaped, a live nonempty block. -/
  sd : p.d.Shape
  dpos : 0 < p.d.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24
  doff : OffHeap p.pd 24
  /-- `mp_mod`'s `mp_div` copies `c` (`mp_init_copy(&y, c)`) from a live block. -/
  cblk : digBlk p.cdp p.c ∈ p.H

/-- What `d` holds. -/
def Q (p : P) : Out → Prop
  | .mem d' => d' = { p.d with sign := d'.sign }
  | .ok _ d' => Reduce.MulmodPost p.a p.b p.c d'

/-- `MP_MEM` (`d`'s header after), or `MP_OKAY` with `d'`'s digits at `q`. -/
inductive Out
  | mem (d' : MpInt)
  | ok (q : Nat) (d' : MpInt)

-- Tom/Spec/Reduce.lean
/-- What `mp_mulmod(a, b, c, d)` leaves in `d` (`mp_mul(a, b, &t)`, `mp_mod(&t, c, d)`), `c > 0`:
the value of `a * b` modulo `c` in `[0, c)`. -/
structure MulmodPost (a b c d' : MpInt) : Prop where
  valid : d'.Valid
  val : d'.val = (a.val * b.val) % c.val
theorem MulmodPost.spec {a b c d' : MpInt} (hc : 0 < c.val) (h : MulmodPost a b c d') :
    d'.Valid ∧ 0 ≤ d'.val ∧ d'.val < c.val ∧ d'.val = (a.val * b.val) % c.val := …  -- proved in Tom/Spec/Reduce.lean

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MpMul.Statement` (`mp_mul`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.MpMul.P` (`mp_mul`), `Tom.Machine.Api.MpMul.Spec` (`mp_mul`), `Tom.Machine.Api.MpMul.SpecR` (`mp_mul`), `Tom.Machine.Api.MpMul.Res` (`mp_mul`), `Tom.Machine.Api.MpMul.Q` (`mp_mul`), `Tom.Machine.Api.MpMul.μ` (`mp_mul`), `Tom.Machine.Api.MpMul.X` (`mp_mul`), `Tom.Machine.Api.MpMul.Out` (`mp_mul`), `Tom.MulPost` (`mp_mul`)
-/

/-! ## `mp_read_radix`

`mp_err mp_read_radix(mp_int *a, const char *str, int radix);`

Coverage: contract.
-/

/-- `mp_read_radix(a, str, radix)`: the standard contract -/
theorem Specs.mp_read_radix_correct : Tom.Machine.Api.ReadRadix.Statement :=
  Tom.Machine.Fn.ReadRadixG5.correct
/-
Machine plumbing: entry `0x80001b4c`; stack reservation `F = 160`; regions stk aS aD str code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/ReadRadix.lean
/-- **`mp_read_radix` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pstr radix : Nat} {a : MpInt} {s : List Nat}
    {ra s0 : BitVec 64}, Pre m sp pa adp pstr a s radix ra →
    Triple (At entry (entryL ra s0 sp pa pstr radix) m v.keepR outp)
      (Ret m v outp sp pa adp pstr a s radix ra s0)

/-- What `mp_read_radix(a, str, radix)` needs. -/
structure Pre (m : Mem) (sp pa adp pstr : Nat) (a : MpInt) (s : List Nat) (radix : Nat) (ra : BitVec 64) :
    Prop where
  ra_ : MpAt m pa adp a
  /-- `mp_zero(a)`'s requirement (`Std.mpZero`'s `Res`); `a`'s value is overwritten. -/
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  str : StrAt m pstr s
  /-- The C's `int radix`, nonnegative: the rows (`rradixg`) take `a2` as a natural number
  below `2^31` (`bltu`/`blt`/`bge` on its sign extension); a negative radix is not covered. -/
  rx_lt : radix < 2 ^ 31
  /-- No `mp_grow` (D5): after `k ≤ |s|` digits `a < radix^k ≤ 2^(6k)`, so `a->used + 1 ≤ a->alloc`
  before each `mp_mul_d(a, radix, a)` and `mp_add_d(a, y, a)`. -/
  room : 6 * s.length ≤ Layout.digitBits * (a.alloc - 1)
  rs : Ram (sp - F) F
  sp_al : sp % 16 = 0
  sp_ge : F ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pstr a s) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pstr : Nat) (a : MpInt) (s : List Nat) (radix : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofInt 64 (readRet radix s))] M
      v.keepR outp cf ∧
    Post m sp pa adp pstr a s radix a' M

/-- `str` holds the bytes `s` before its first NUL. -/
structure StrAt (m : Mem) (pstr : Nat) (s : List Nat) : Prop where
  ram : Ram pstr (s.length + 1)
  /-- Byte `i` of the string. -/
  bytes : ∀ i (h : i < s.length), bytesT1 m (pstr + i) = BitVec.ofNat 8 s[i]
  /-- Every byte before the NUL is a nonzero byte. -/
  byte : ∀ c ∈ s, 0 < c ∧ c < 256
  nul : bytesT1 m (pstr + s.length) = 0#8

-- Tom/Spec/Radix.lean
/-- The return code of `mp_read_radix(a, s, radix)`. -/
def readRet (radix : Int) (s : List Nat) : Int :=
  if radixOk radix then
    (if readEndOk (readLoop radix.toNat (readSign s).2 0).2 then Layout.mpOkay else Layout.mpVal)
  else Layout.mpVal

-- Tom/Machine/Api/ReadRadix.lean
/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pstr : Nat) (a : MpInt) (s : List Nat) (radix : Nat) (a' : MpInt) (M : Mem) :
    Prop where
  repr : MpAt M pa adp a'
  /-- Neither callee reallocates (D5). -/
  alloc : a'.alloc = a.alloc
  read : ReadRadixPost (radix : Int) s a' (readRet radix s)
  frame : Frm (lay sp pa adp pstr a s) ws m M

-- Tom/Spec/Radix.lean
/-- The radix is in `2..64`. -/
def radixOk (radix : Int) : Prop := 2 ≤ radix ∧ radix ≤ 64

/-- The loop stopped at NUL, `'\r'` or `'\n'`. -/
def readEndOk : List Nat → Bool
  | [] => true
  | c :: _ => c == 13 || c == 10

/-- The digit loop: per character, `a = a * radix + y` until NUL (`[]`) or a
character `charVal` rejects. Returns the value and the characters from the
stopping one on. -/
def readLoop (r : Nat) : List Nat → Nat → Nat × List Nat
  | [], acc => (acc, [])
  | c :: cs, acc => (charVal r c).elim (acc, c :: cs) (fun y => readLoop r cs (acc * r + y))

/-- The leading `'-'`: the sign to set and the rest of the string. -/
def readSign : List Nat → Nat × List Nat
  | 45 :: t => (Layout.mpNeg, t)
  | s => (Layout.mpZpos, s)

/-- What `mp_read_radix(a, str, radix)` leaves, where `s` is the bytes of
`str` before its first NUL (all nonzero): `a` valid with the magnitude of the
loop model, the sign of the leading `'-'` when nonzero, and the return code. -/
structure ReadRadixPost (radix : Int) (s : List Nat) (a' : MpInt) (ret : Int) : Prop where
  code : ret = readRet radix s
  valid : a'.Valid
  mag : a'.mag = readMag radix s
  sign : a'.sign = if a'.mag = 0 then Layout.mpZpos else (readSign s).1
theorem ReadRadixPost.spec {radix : Int} {s : List Nat} {a' : MpInt} {ret : Int}
    (h : ReadRadixPost radix s a' ret) : a'.Valid ∧ a'.val = readVal radix s ∧ ret = readRet radix s := …  -- proved in Tom/Spec/Radix.lean

/-- The value of character `c` in radix `r`, or `none` where the loop stops. -/
def charVal (r c : Nat) : Option Nat :=
  if rmapRevSz < posOf (foldCh r c) then none
  else if revAt (posOf (foldCh r c)) = 255 ∨ r ≤ revAt (posOf (foldCh r c)) then none
  else some (revAt (posOf (foldCh r c)))

/-- `mp_s_rmap_reverse_sz`. -/
def rmapRevSz : Nat := 88

/-- `pos = (unsigned)(ch - '(')`. -/
@[irreducible] def posOf (ch : Nat) : Nat := (ch + 2 ^ 32 - 40) % 2 ^ 32

/-- `ch = (radix <= 36) ? MP_TOUPPER(c) : c`. -/
@[irreducible] def foldCh (r c : Nat) : Nat := if r ≤ 36 then toUpper c else c

/-- `mp_s_rmap_reverse[pos]` for `pos ≤ 88` as the image reads it (index 88 is
the byte past the table). -/
@[irreducible] def revAt (pos : Nat) : Nat := (rmapRev ++ [rmapRevPast]).getD pos 255

/-- `MP_TOUPPER` on a byte. -/
@[irreducible] def toUpper (c : Nat) : Nat := if 97 ≤ c ∧ c ≤ 122 then c - 32 else c

/-- `mp_s_rmap_reverse` (88 bytes, indexed by `ch - '('`). -/
@[irreducible] def rmapRev : List Nat :=
  [255, 255, 255, 62, 255, 255, 255, 63, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 255, 255, 255, 255, 255,
   255, 255, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
   32, 33, 34, 35, 255, 255, 255, 255, 255, 255, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
   49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 255, 255, 255, 255, 255]

/-- The byte the image holds just past `mp_s_rmap_reverse` (`0x80017d18`). -/
def rmapRevPast : Nat := 44
-/

/-! ## `mp_reduce`

`mp_err mp_reduce(mp_int *x, const mp_int *m, const mp_int *mu);`

Coverage: contract (Barrett: 0 < um < 255, x->used ≤ 2 um, mu->used = um + 1; x grown in place).
Coverage: contract (Barrett at any size: 0 < um with MP_DIGIT_BIT (um + 1) and MP_DIGIT_BIT x->used ints, x->used ≤ 2 um, mu->used = um + 1; x grown in place; both multipliers on either path, SMpMulDigsAGClosed).
-/

/-- `mp_reduce(x, m, mu)`: the allocating contract -/
theorem Specs.mp_reduce_correct : Tom.Machine.Api.MpReduce.Statement :=
  Tom.Machine.Fn.MpReduceG5.correct
/-
Machine plumbing: entry `0x8000620c`; the arguments: `a0 = x`, `a1 = m`, `a2 = mu`; stack reservation `F = 2816`; regions stk xS xD nS nD uS uD code; written [.stk, .xS, .xD].

-- Tom/Machine/Api/MpReduce.lean
def Statement : Prop := Standard.Statement Res Q (site .xD)  -- the standard shape (top of file)

structure P where  (sp px xdp pn ndp pu udp : Nat); (x n mu : MpInt); (H : List (Nat × Nat))

/-- What `mp_reduce(x, m, mu)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  vx : p.x.Valid
  xz : p.x.sign = Layout.mpZpos
  vn : p.n.Valid
  nz : p.n.sign = Layout.mpZpos
  vmu : p.mu.Valid
  muz : p.mu.sign = Layout.mpZpos
  k1 : 0 < p.n.used
  /-- The C's `int` arithmetic: `MP_DIGIT_BIT * (um + 1)` (`mp_mod_2d`'s bit count; it also puts `um`
  below `2^27`, so `s_mp_mul_high_digs` is called, not `mp_mul`). Both multipliers on either path
  (`Api/SMpMulDigsAG.lean`). -/
  bits : Layout.digitBits * (p.n.used + 1) < 2 ^ 31
  /-- `mp_mod_2d(x, ·, x)`'s `x->used * MP_DIGIT_BIT`, an `int`. -/
  xbits : Layout.digitBits * p.x.used < 2 ^ 31
  /-- Barrett's range `x < radix^(2 um)`, in digits. -/
  xu : p.x.used ≤ 2 * p.n.used
  /-- Barrett's `mu = ⌊radix^(2 um) / m⌋` lies in `[radix^um, radix^(um+1)]`: `um + 1` digits, or
  `um + 2` for `m = radix^(um-1)` (`mp_reduce_setup`'s, `ReduceSetupPost`). -/
  mul : p.n.used ≤ p.mu.used
  muh : p.mu.used ≤ p.n.used + 2
  xpos : 0 < p.x.alloc
  npos : 0 < p.n.alloc
  upos : 0 < p.mu.alloc
  xoff : OffHeap p.px 24
  noff : OffHeap p.pn 24
  uoff : OffHeap p.pu 24

def Q (p : P) (x : X) : Prop := Out p x

/-- What `x` holds after: shaped, live, placed, grown only; on `MP_OKAY` Barrett's result. -/
structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) (lay p .xD) (site' p x)
  grow : p.x.alloc ≤ x.2.2.alloc
  valid : x.1 = true → x.2.2.Valid
  post : x.1 = true → ReducePost p.x p.n p.mu x.2.2

-- Tom/Spec/Reduce.lean
/-- What `mp_reduce(x, m, mu)` leaves in `x` (for `x ≥ 0`, allocations not failing). -/
structure ReducePost (x m mu x' : MpInt) : Prop where
  valid : x'.Valid
  mag : x'.mag = barrett x m mu
  sign : x'.sign = Layout.mpZpos
theorem ReducePost.spec {x m mu x' : MpInt} (hx : x.Shape) (hm : m.Valid) (hmuS : mu.Shape) (hk : 0 < m.used)
    (hmu : mu.mag = radix ^ (2 * m.used) / m.mag) (hxb : x.mag < radix ^ (2 * m.used)) (h : ReducePost x m mu x') :
    x'.Valid ∧ x'.mag = x.mag % m.mag ∧ x'.val = ((x.mag % m.mag : Nat) : Int) := …  -- proved in Tom/Spec/Reduce.lean

/-- `mp_reduce`'s result: `barrettR`, then `while (mp_cmp(x, m) != MP_LT) s_mp_sub(x, m, x)`. -/
def barrett (x m mu : MpInt) : Nat :=
  redLoop id m.mag (barrettR x.mag m.mag m.used (barrettQ3 x m mu) + 1)
    (barrettR x.mag m.mag m.used (barrettQ3 x m mu))

/-- The remainder before the final subtractions: `mp_mod_2d(x, MP_DIGIT_BIT * (um + 1), x)`,
`s_mp_mul_digs(&q, m, &q, um + 1)` (`q3 * m mod radix^(um+1)`), `mp_sub(x, &q, x)`, and
`radix^(um+1)` added back (`mp_set`, `mp_lshd`, `mp_add`) if that is negative. -/
def barrettR (x m k q3 : Nat) : Nat :=
  (x % radix ^ (k + 1) + radix ^ (k + 1) - q3 * m % radix ^ (k + 1)) % radix ^ (k + 1)

/-- The quotient estimate `q3` of `mp_reduce`: `q1 * mu` in full (`mp_mul`, when
`um > 2^(MP_DIGIT_BIT - 1)`) or its columns from `um` on (`s_mp_mul_high_digs(&q, mu, &q, um)`),
then `mp_rshd(&q, um + 1)`. -/
def barrettQ3 (x m mu : MpInt) : Nat :=
  if 2 ^ 27 < m.used then (x.mag / radix ^ (m.used - 1)) * mu.mag / radix ^ (m.used + 1)
  else highProd (q1Digit x m.used) mu.digit (q1Used x m.used) mu.used m.used / radix ^ (m.used + 1)

/-- `Σ_{i + j ≥ digs} a_i b_j radix^(i+j)`. -/
def highProd (da db : Nat → Nat) (ua ub digs : Nat) : Nat := natUpTo (highCol da db ua ub digs) (ua + ub)

/-- The digits of `q1 = ⌊x / radix^(k-1)⌋` (`mp_init_copy(&q, x); mp_rshd(&q, um - 1)`). -/
def q1Digit (x : MpInt) (k i : Nat) : Nat := x.digit (k - 1 + i)

def q1Used (x : MpInt) (k : Nat) : Nat := x.used - (k - 1)

/-- Column `k` of `a * b` if `k ≥ digs`, else `0`. -/
def highCol (da db : Nat → Nat) (ua ub digs k : Nat) : Nat := if digs ≤ k then col da db ua ub k else 0

-- Tom/Spec/Mul.lean
/-- Column `k` of the product of `da` (`ua` digits) and `db` (`ub` digits). -/
def col (da db : Nat → Nat) (ua ub k : Nat) : Nat :=
  sumTo (fun i => if i ≤ k ∧ k - i < ub then da i * db (k - i) else 0) ua

/-- `Σ_{i<n} f i`. -/
def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MpSqr.X` (`mp_mul_2`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Reduce.redLoop` (`mp_dr_reduce`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`)
-/

/-! ## `mp_reduce_2k`

`mp_err mp_reduce_2k(mp_int *a, const mp_int *n, mp_digit d);`

Coverage: contract.
-/

/-- `mp_reduce_2k(a, n, d)` with `a` and `q` growing: the allocating contract -/
theorem Specs.mp_reduce_2k_correct : Tom.Machine.Api.MpReduce2kG.Statement :=
  Tom.Machine.Fn.MpReduce2kGG5.correct
/-
Machine plumbing: entry `0x80005e48`; the arguments: `a0 = a`, `a1 = n`, `a2 = d` (`gp` for the allocator); stack reservation `F = 736`; regions stk aS aD nS nD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MpReduce2kG.lean
/-- **`mp_reduce_2k(a, n, d)` on the machine, `a` and `q` growing**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) MpReduce2k.isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: MpReduce2k.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) MpReduce2k.ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

/-- What `mp_reduce_2k(a, n, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  vn : p.n.Valid
  /-- `n ≠ 0`: `p > 0` and a loop that ends. -/
  npos : 0 < p.n.mag
  /-- `d` an `mp_digit`. -/
  d_lt : p.d < radix
  /-- `n = 2^p - d`, `p = mp_count_bits(n)` (`mp_reduce_2k_setup`). -/
  hd : p.n.mag + p.d = 2 ^ nbits p.n.mag
  /-- `mp_count_bits(n)`'s `int` result. -/
  bits : Layout.digitBits * p.n.used < 2 ^ 31
  /-- `mp_div_2d`'s `mp_mod_2d(a, p, a)`: `a->used * MP_DIGIT_BIT` does not overflow. -/
  abits : Layout.digitBits * p.a.used < 2 ^ 31
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  noff : OffHeap p.pn 24

def Q (p : P) (x : X) : Prop := ReduxG.Out p (lay p .aD) (Reduce2kPost p.a p.n p.d) x

abbrev X := ReduxG.X

-- Tom/Spec/Reduce.lean
/-- What `mp_reduce_2k(a, n, d)` (`d` an `mp_digit`) and `mp_reduce_2k_l(a, n, d)`
(`d = |d|`) leave in `a`: the fold-and-subtract loop with `p = mp_count_bits(n)`, valid,
the sign of `a` or `MP_ZPOS`. No pass sets `a`'s sign (`mp_mod_2d(a, p, a)`, `s_mp_add(a, &q, a)`,
`s_mp_sub(a, n, a)` work on magnitudes), but each ends in `mp_clamp`, which resets it when the
value is zero *in the middle of the loop*: for `a < 0` with `|a| mod 2^p = 0` the sign is
`MP_ZPOS` from `mp_mod_2d` on, also when the fold `d·(|a| / 2^p)` is nonzero (e.g. `|a| = 2^p`
leaves `|a'| = d`, sign `MP_ZPOS`). So the sign is `a`'s or `MP_ZPOS`, and `MP_ZPOS` for `a ≥ 0`
(`spec_val`). -/
structure Reduce2kPost (a n : MpInt) (d : Nat) (a' : MpInt) : Prop where
  valid : a'.Valid
  mag : a'.mag = redLoop (fold2k (nbits n.mag) d) n.mag (a.mag + 1) a.mag
  sign : a'.sign = Layout.mpZpos ∨ a'.sign = a.sign
theorem Reduce2kPost.spec {a n a' : MpInt} {d : Nat} (hn : 0 < n.mag) (hd : n.mag + d = 2 ^ nbits n.mag)
    (h : Reduce2kPost a n d a') : a'.Valid ∧ a'.mag = a.mag % n.mag := …  -- proved in Tom/Spec/Reduce.lean
theorem Reduce2kPost.spec_val {a n a' : MpInt} {d : Nat} (hn : 0 < n.mag)
    (hd : n.mag + d = 2 ^ nbits n.mag) (hpos : a.sign = Layout.mpZpos) (h : Reduce2kPost a n d a') :
    a'.val = ((a.mag % n.mag : Nat) : Int) := …  -- proved in Tom/Spec/Reduce.lean

/-- One pass of `mp_reduce_2k(_l)`: `mp_div_2d(a, p, &q, a)` (`q = a / 2^p`, `a = a mod 2^p`),
`q *= d` (`mp_mul_d`, skipped for `d == 1`; `mp_mul` for `_l`), `s_mp_add(a, &q, a)`. -/
def fold2k (p d a : Nat) : Nat := a % 2 ^ p + d * (a / 2 ^ p)

Also used (printed above): `Tom.Machine.Api.MpReduce2k.P` (`mp_dr_reduce`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Mont.nbits` (`mp_exptmod`), `Tom.Machine.Api.ReduxG.Out` (`mp_dr_reduce`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.ReduxG.X` (`mp_dr_reduce`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.Reduce.redLoop` (`mp_dr_reduce`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`)
-/

/-- `mp_reduce_2k(a, n, d)`: the allocating contract (fresh set; over `Kit/MeetHeap.lean`) -/
theorem Specs.mp_reduce_2k_correct_room : Tom.Machine.Api.MpReduce2k.Statement :=
  Tom.Machine.Fn.MpReduce2kG5.correct
/-
Machine plumbing: entry `0x80005e48`; the arguments: `a0 = a`, `a1 = n`, `a2 = d` (`gp` for the allocator); stack reservation `F = 96 + MpInit.Finit`; regions stk aS aD nS nD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MpReduce2k.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

/-- What `mp_reduce_2k(a, n, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_div_2d`'s `a` (`Api.MpDiv2d`), `s_mp_add`'s and `s_mp_sub`'s operand. -/
  va : p.a.Valid
  vn : p.n.Valid
  /-- `n ≠ 0`: `p > 0` (`mp_div_2d`'s shifting path) and a loop that ends. -/
  npos : 0 < p.n.mag
  /-- `d` an `mp_digit` (`mp_mul_d(&q, d, &q)`). -/
  d_lt : p.d < radix
  /-- `n = 2^p - d`, `p = mp_count_bits(n)` (`mp_reduce_2k_setup` for an `mp_reduce_is_2k`
  modulus): the fold keeps the residue and does not grow `a`, so the loop terminates. -/
  hd : p.n.mag + p.d = 2 ^ nbits p.n.mag
  /-- `mp_count_bits(n)`'s `int` result (`Std.cntBits`). -/
  bits : Layout.digitBits * p.n.used < 2 ^ 31
  /-- D5 for `a`: `s_mp_add(a, &q, a)` has room (`max(used) + 1 ≤ alloc`) on every pass. -/
  aroom : p.a.used + 1 ≤ p.a.alloc
  /-- D5 for `q` (`mp_init`'s `MP_PREC = 32` digits): `mp_copy(a, &q)` in `mp_div_2d` and
  `mp_mul_d(&q, d, &q)` do not call `mp_grow`. -/
  qroom : p.a.used + 1 ≤ defPrec
  aoff : OffHeap p.pa 24
  noff : OffHeap p.pn 24

def Q (p : P) : Option MpInt → Prop
  | none => True
  | some a' => Red p a'

/-- What `a` holds after. -/
structure Red (p : P) (a' : MpInt) : Prop where
  red : Reduce2kPost p.a p.n p.d a'
  /-- Not reallocated (D5). -/
  alloc : a'.alloc = p.a.alloc

Also used (printed above): `Tom.Machine.Api.MpReduce2k.P` (`mp_dr_reduce`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Mont.nbits` (`mp_exptmod`), `Tom.defPrec` (`mp_init`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Reduce.Reduce2kPost` (`mp_reduce_2k`), `Tom.Reduce.redLoop` (`mp_dr_reduce`), `Tom.Reduce.fold2k` (`mp_reduce_2k`)
-/

/-! ## `mp_reduce_2k_l`

`mp_err mp_reduce_2k_l(mp_int *a, const mp_int *n, const mp_int *d);`

Coverage: contract (D5: a->used ≤ MP_PREC, d on the comba path).
-/

/-- `mp_reduce_2k_l(a, n, d)` with `a` and `q` growing: the allocating contract -/
theorem Specs.mp_reduce_2k_l_correct : Tom.Machine.Api.MpReduce2kLG.Statement :=
  Tom.Machine.Fn.MpReduce2kLGG5.correct
/-
Machine plumbing: entry `0x80005f70`; the arguments: `a0 = a`, `a1 = n`, `a2 = d` (`gp` for the allocator); stack reservation `F = 2872 + 8 * (p.a.used + p.n.used)`; regions stk aS aD nS nD dS dD kc tc code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MpReduce2kLG.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

-- Tom/Machine/Api/MpReduce2kL.lean
structure P where  (sp pa adp pn ndp pd ddp : Nat); (a n d : MpInt); (H : List (Nat × Nat))

-- Tom/Machine/Api/MpReduce2kLG.lean
/-- What `mp_reduce_2k_l(a, n, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp (F (p := p))
  va : p.a.Valid
  vn : p.n.Valid
  vd : p.d.Valid
  /-- `n ≠ 0`: `p > 0` and a loop that ends. -/
  npos : 0 < p.n.mag
  /-- `n = 2^p - |d|`, `p = mp_count_bits(n)` (`mp_reduce_2k_setup_l`). -/
  hd : p.n.mag + p.d.mag = 2 ^ nbits p.n.mag
  /-- `mp_count_bits(n)`'s `int` result. -/
  bits : Layout.digitBits * p.n.used < 2 ^ 31
  /-- `mp_div_2d`'s `mp_mod_2d(a, p, a)`: `a->used * MP_DIGIT_BIT` does not overflow. -/
  abits : Layout.digitBits * p.a.used < 2 ^ 31
  /-- `s_mp_add`'s `mp_grow(a, max + 1)`'s `int`. -/
  usz : p.a.used + 1 < 2 ^ 31
  apos : 0 < p.a.alloc
  dpos : 0 < p.d.alloc
  aoff : OffHeap p.pa 24
  noff : OffHeap p.pn 24
  doff : OffHeap p.pd 24

def Q (p : P) (x : X) : Prop := Out p x

/-- `(ok, q, a')`: `a'`'s digits at `q`. -/
abbrev X : Type := Bool × Nat × MpInt

/-- What `a` holds after: shaped, live, placed; on `MP_OKAY` the reduction. -/
structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) (lay p .aD) (site' p x)
  post : x.1 = true → Reduce2kPost p.a p.n p.d.mag x.2.2

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Mont.nbits` (`mp_exptmod`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.Reduce.Reduce2kPost` (`mp_reduce_2k`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Reduce.redLoop` (`mp_dr_reduce`), `Tom.Reduce.fold2k` (`mp_reduce_2k`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`)
-/

/-- `mp_reduce_2k_l(a, n, d)`: the allocating contract -/
theorem Specs.mp_reduce_2k_l_correct_room : Tom.Machine.Api.MpReduce2kL.Statement :=
  Tom.Machine.Fn.MpReduce2kLG5.correct
/-
Machine plumbing: entry `0x80005f70`; the arguments: `a0 = a`, `a1 = n`, `a2 = d` (`gp` for the allocator); stack reservation `F = 6952`; regions stk aS aD nS nD dS dD kc tc code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MpReduce2kL.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

/-- What `mp_reduce_2k_l(a, n, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  vn : p.n.Valid
  vd : p.d.Valid
  /-- `n ≠ 0`: `p > 0` and a loop that ends. -/
  npos : 0 < p.n.mag
  /-- `n = 2^p - |d|`, `p = mp_count_bits(n)` (`mp_reduce_2k_setup_l`). -/
  hd : p.n.mag + p.d.mag = 2 ^ nbits p.n.mag
  /-- `mp_count_bits(n)`'s `int` result. -/
  bits : Layout.digitBits * p.n.used < 2 ^ 31
  /-- D5 for `a`: `s_mp_add(a, &q, a)` has room on every pass. -/
  aroom : p.a.used + 1 ≤ p.a.alloc
  /-- D5 for `q` (`mp_init`'s `MP_PREC = 32` digits): `mp_copy(a, &q)` in `mp_div_2d`. -/
  qroom : p.a.used ≤ defPrec
  /-- `mp_mul(&q, d, &q)` on the comba path (`MpMulAF.Small`). -/
  dsmall : defPrec + p.d.used + 1 < 512
  dpos : 0 < p.d.alloc
  aoff : OffHeap p.pa 24
  noff : OffHeap p.pn 24
  doff : OffHeap p.pd 24

def Q (p : P) : X → Prop
  | (true, a') => Red p a'
  | (false, a') => a'.Shape ∧ a'.alloc = p.a.alloc

/-- After: `(ok, a')`, `a` in place. -/
abbrev X : Type := Bool × MpInt

/-- What `a` holds after. -/
structure Red (p : P) (a' : MpInt) : Prop where
  red : Reduce2kPost p.a p.n p.d.mag a'
  /-- Not reallocated (D5). -/
  alloc : a'.alloc = p.a.alloc

Also used (printed above): `Tom.Machine.Api.MpReduce2kL.P` (`mp_reduce_2k_l`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Mont.nbits` (`mp_exptmod`), `Tom.defPrec` (`mp_init`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Reduce.Reduce2kPost` (`mp_reduce_2k`), `Tom.Reduce.redLoop` (`mp_dr_reduce`), `Tom.Reduce.fold2k` (`mp_reduce_2k`)
-/

/-! ## `mp_reduce_2k_setup`

`mp_err mp_reduce_2k_setup(const mp_int *a, mp_digit *d);`

Coverage: contract.
-/

/-- `mp_reduce_2k_setup(a, &d)` growing `tmp`: the contract -/
theorem Specs.mp_reduce_2k_setup_correct : Tom.Machine.Api.Reduce2kSetupGr.Statement :=
  Tom.Machine.Fn.Reduce2kSetupGrG5.correct
/-
Machine plumbing: stack reservation `F = 80 + Expt2G.F`; regions stk aS aD dD code; written Reduce2kSetup.ws.

-- Tom/Machine/Api/Reduce2kSetupGr.lean
/-- **`mp_reduce_2k_setup(a, &d)` on the machine, `tmp` growing.** -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .dD (out p x) (lay p .dD) (hin p) (hin p) m M)

-- Tom/Machine/Api/Reduce2kSetup.lean
structure P where  (sp pa adp pd : Nat); (a : MpInt); (d : Cell); (H : List (Nat × Nat))

-- Tom/Machine/Api/Reduce2kSetupGr.lean
/-- What `mp_reduce_2k_setup(a, &d)` needs: `Reduce2kSetup.Res` without the room. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  /-- `mp_count_bits`'s `int` result. -/
  bits : Layout.digitBits * p.a.used < 2 ^ 31
  apos : 0 < p.a.alloc

abbrev Q := Reduce2kSetup.Q

-- Tom/Machine/Api/Reduce2kSetup.lean
/-- One `mp_digit` in memory, as a digit array of length one. -/
structure Cell where
  v : Nat

def Q (p : P) : Option Nat → Prop
  | none => True
  | some x => Setup2kPost p.a x

-- Tom/Spec/Reduce.lean
/-- What `mp_reduce_2k_setup(a, &d)` leaves: the low digit of `2^p - |a|`
(`mp_2expt`, `s_mp_sub`, `tmp.dp[0]`). -/
structure Setup2kPost (a : MpInt) (d : Nat) : Prop where
  val : d = (2 ^ nbits a.mag - a.mag) % radix
theorem Setup2kPost.spec {a : MpInt} {d : Nat} (h : Setup2kPost a d) (hs : 2 ^ nbits a.mag - a.mag < radix) :
    a.mag + d = 2 ^ nbits a.mag := …  -- proved in Tom/Spec/Reduce.lean

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`)
-/

/-- `mp_reduce_2k_setup(a, &d)`: the contract (over `Kit/MeetHeap.lean`) -/
theorem Specs.mp_reduce_2k_setup_correct_room : Tom.Machine.Api.Reduce2kSetup.Statement :=
  Tom.Machine.Fn.Reduce2kSetupG5.correct
/-
Machine plumbing: entry `0x80006088`; the arguments: `a0 = a`, `a1 = d` (`gp` for the allocator); stack reservation `F = 80 + MpInit.Finit`; regions stk aS aD dD code; written [.stk, .dD].

-- Tom/Machine/Api/Reduce2kSetup.lean
/-- **`mp_reduce_2k_setup(a, &d)` on the machine.** The site is `d`'s cell, kept in place. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .dD (out p x) (lay p .dD) (hin p) (hin p) m M)

/-- What `mp_reduce_2k_setup(a, &d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_count_bits` and `s_mp_sub` read `a` (`mp_reduce_2k`'s callers pass a valid modulus). -/
  va : p.a.Valid
  /-- `mp_count_bits`'s `int` result (`Std.cntBits`). -/
  bits : Layout.digitBits * p.a.used < 2 ^ 31
  /-- D5: `mp_2expt(&tmp, p)` stays in `tmp`'s `MP_PREC` digits (its `mp_grow` does not
  reallocate): `|a| < 2^896`. -/
  room : countBits p.a / Layout.digitBits + 1 ≤ defPrec
  /-- A nonempty digit array (`HContract.pos`: an empty region inside the arena is not off it). -/
  apos : 0 < p.a.alloc

Also used (printed above): `Tom.Machine.Api.Reduce2kSetup.P` (`mp_reduce_2k_setup`), `Tom.Machine.Api.Reduce2kSetup.Q` (`mp_reduce_2k_setup`), `Tom.Machine.Api.Reduce2kSetup.Cell` (`mp_reduce_2k_setup`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.countBits` (`mp_count_bits`), `Tom.defPrec` (`mp_init`), `Tom.Reduce.Setup2kPost` (`mp_reduce_2k_setup`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.bitLen` (`mp_count_bits`)
-/

/-! ## `mp_reduce_2k_setup_l`

`mp_err mp_reduce_2k_setup_l(const mp_int *a, mp_int *d);`

Coverage: contract.
-/

/-- `mp_reduce_2k_setup_l(a, d)` growing `d`: the allocating contract -/
theorem Specs.mp_reduce_2k_setup_l_correct : Tom.Machine.Api.Reduce2kSetupLG.Statement :=
  Tom.Machine.Fn.Reduce2kSetupLGG5.correct
/-
Machine plumbing: entry `0x80006174`; the arguments: `a0 = a`, `a1 = d` (`gp` for the allocator); stack reservation `F = 80 + Expt2G.F`; regions stk aS aD dS dD code; written [.stk, .dS, .dD].

-- Tom/Machine/Api/Reduce2kSetupLG.lean
def Statement : Prop := Standard.Statement Res Q (site .dD)  -- the standard shape (top of file)

-- Tom/Machine/Api/Reduce2kSetupL.lean
structure P where  (sp pa adp pd ddp : Nat); (a d : MpInt); (H : List (Nat × Nat))

-- Tom/Machine/Api/Reduce2kSetupLG.lean
/-- What `mp_reduce_2k_setup_l(a, d)` needs: `Api/Reduce2kSetupL.lean`'s `Res` without the rooms. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  /-- `mp_count_bits`'s `int` result. -/
  bits : Layout.digitBits * p.a.used < 2 ^ 31
  /-- `s_mp_sub`'s `Pre.sc`. -/
  sd : p.d.Shape
  /-- `s_mp_sub` keeps `d`'s sign for a nonzero result. -/
  dsign : p.d.sign = Layout.mpZpos ∨ p.d.sign = Layout.mpNeg
  apos : 0 < p.a.alloc
  /-- `d`'s digits: `realloc`'s block. -/
  dpos : 0 < p.d.alloc
  doff : OffHeap p.pd 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (_, d') => Setup2kLPost p.a d'

-- Tom/Spec/Reduce.lean
/-- What `mp_reduce_2k_setup_l(a, d)` leaves in `d`: `2^p - |a|` in full. -/
structure Setup2kLPost (a d' : MpInt) : Prop where
  valid : d'.Valid
  mag : d'.mag = 2 ^ nbits a.mag - a.mag
theorem Setup2kLPost.spec {a d' : MpInt} (h : Setup2kLPost a d') : a.mag + d'.mag = 2 ^ nbits a.mag := …  -- proved in Tom/Spec/Reduce.lean

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`)
-/

/-- `mp_reduce_2k_setup_l(a, d)`: the contract (over `Kit/MeetHeap.lean`) -/
theorem Specs.mp_reduce_2k_setup_l_correct_room : Tom.Machine.Api.Reduce2kSetupL.Statement :=
  Tom.Machine.Fn.Reduce2kSetupLG5.correct
/-
Machine plumbing: entry `0x80006174`; the arguments: `a0 = a`, `a1 = d` (`gp` for the allocator); stack reservation `F = 80 + MpInit.Finit`; regions stk aS aD dS dD code; written [.stk, .dS, .dD].

-- Tom/Machine/Api/Reduce2kSetupL.lean
/-- **`mp_reduce_2k_setup_l(a, d)` on the machine.** The site is `d`'s digit array, kept in place. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .dD (out p x) (lay p .dD) (hin p) (hin p) m M)

/-- What `mp_reduce_2k_setup_l(a, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_count_bits` and `s_mp_sub` read `a`. -/
  va : p.a.Valid
  /-- `mp_count_bits`'s `int` result (`Std.cntBits`). -/
  bits : Layout.digitBits * p.a.used < 2 ^ 31
  /-- D5: `mp_2expt(&tmp, p)` stays in `tmp`'s `MP_PREC` digits: `|a| < 2^896`. -/
  room : countBits p.a / Layout.digitBits + 1 ≤ defPrec
  /-- D5: `s_mp_sub(&tmp, a, d)` writes `d` in place (its `mp_grow` does not reallocate). -/
  droom : countBits p.a / Layout.digitBits + 1 ≤ p.d.alloc
  /-- `s_mp_sub`'s `Pre.sc`. -/
  sd : p.d.Shape
  /-- `s_mp_sub` keeps `d`'s sign for a nonzero result: a sign, for `d'` valid. -/
  dsign : p.d.sign = Layout.mpZpos ∨ p.d.sign = Layout.mpNeg
  /-- A nonempty digit array (`HContract.pos`). -/
  apos : 0 < p.a.alloc

def Q (p : P) : Option MpInt → Prop
  | none => True
  | some d' => LPost p d'

/-- What `d` holds after. -/
structure LPost (p : P) (d' : MpInt) : Prop where
  setup : Setup2kLPost p.a d'
  alloc : d'.alloc = p.d.alloc

Also used (printed above): `Tom.Machine.Api.Reduce2kSetupL.P` (`mp_reduce_2k_setup_l`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.countBits` (`mp_count_bits`), `Tom.defPrec` (`mp_init`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.bitLen` (`mp_count_bits`), `Tom.Reduce.Setup2kLPost` (`mp_reduce_2k_setup_l`)
-/

/-! ## `mp_reduce_is_2k`

`mp_bool mp_reduce_is_2k(const mp_int *a);`
-/

/-- `mp_reduce_is_2k`: the standard contract -/
theorem Specs.mp_reduce_is_2k_correct : Tom.Machine.Api.Reduce2k.Statement :=
  Tom.Machine.Fn.Reduce2k.correct
/-
Machine plumbing: entry `0x80001d14`; regions stk aS aD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/Reduce2k.lean
/-- **`mp_reduce_is_2k` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {ra s0 : BitVec 64},
    Pre m sp pa adp a ra →
    Triple (At entry (Fn.Reduce2k.entryL ra s0 sp pa) m v.keepR outp) (Ret m v outp sp pa adp a ra s0)

structure Pre (m : Mem) (sp pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  va : a.Valid
  ga : MpGeom pa adp a.alloc
  bits : Layout.digitBits * a.used < 2 ^ 31
  rs : Ram (sp - 16) 16
  sp_al : sp % 16 = 0
  sp_ge : 16 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp a) isR

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (ra s0 : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 (isReduce2k a))] M v.keepR outp cf ∧
    Frm (lay sp pa adp a) wsR m M

-- Tom/Machine/Api/Un.lean
/-- `a` read only. -/
def isR : R → Bool
  | .stk => true
  | _ => false

def wsR : List R := [.stk]

Also used (printed above): `Tom.isReduce2k` (`mp_exptmod`), `Tom.countBits` (`mp_count_bits`), `Tom.bitLen` (`mp_count_bits`)
-/

/-! ## `mp_reduce_is_2k_l`

`mp_bool mp_reduce_is_2k_l(const mp_int *a);`
-/

/-- `mp_reduce_is_2k_l`: the standard contract -/
theorem Specs.mp_reduce_is_2k_l_correct : Tom.Machine.Api.Reduce2kL.Statement :=
  Tom.Machine.Fn.Reduce2kL.correct
/-
Machine plumbing: entry `0x80001db4`.

-- Tom/Machine/Api/Reduce2kL.lean
/-- **`mp_reduce_is_2k_l` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {pa adp : Nat} {a : MpInt} {ra : BitVec 64},
    Pre m pa adp a ra →
    Triple (At entry (Fn.Reduce2kL.entryL ra pa) m v.keep outp) (Ret m v outp a ra)

structure Pre (m : Mem) (pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  ra_al : ra.toNat % 4 = 0
  img : Img m

def Ret (m : Mem) (v : Abi) (outp : Array String) (a : MpInt) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  At ra [(1, ra), (10, BitVec.ofNat 64 (isReduce2kL a))] m v.keep outp cf

-- Tom/Spec/ModShape.lean
/-- `mp_reduce_is_2k_l(a)` as the C states it (`MP_YES = 1`, `MP_NO = 0`). -/
def isReduce2kL (a : MpInt) : Nat :=
  if a.used = 0 then 0 else if a.used = 1 then 1 else if a.used / 2 ≤ countMax a.digit a.used then 1 else 0

/-- The number of digits below `n` equal to `MP_DIGIT_MAX` (`= MP_MASK`). -/
def countMax (dig : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => countMax dig n + if dig n = Layout.mpMask then 1 else 0
-/

/-! ## `mp_reduce_setup`

`mp_err mp_reduce_setup(mp_int *a, const mp_int *b);`

Coverage: contract.
-/

/-- `mp_reduce_setup(a, b)` growing `a`: the allocating contract -/
theorem Specs.mp_reduce_setup_correct : Tom.Machine.Api.MpReduceSetupG.Statement :=
  Tom.Machine.Fn.MpReduceSetupGG5.correct
/-
Machine plumbing: entry `0x800063a8`; the arguments: `a0 = a`, `a1 = b`; stack reservation `F = MpReduceSetup.F`; regions stk aS aD bS bD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MpReduceSetupG.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

-- Tom/Machine/Api/MpReduceSetup.lean
structure P where  (sp pa adp pb bdp : Nat); (a b : MpInt); (H : List (Nat × Nat))

-- Tom/Machine/Api/MpReduceSetupG.lean
/-- What `mp_reduce_setup(a, b)` needs: `Api/MpReduceSetup.lean`'s `Res` without `room`. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_2expt` zeroes and grows `a`. -/
  sa : p.a.Shape
  /-- The modulus: valid, positive. -/
  vb : p.b.Valid
  b0 : 0 < p.b.used
  bz : p.b.sign = Layout.mpZpos
  /-- `mp_2expt`'s `int b` (`56 b->used`). -/
  k_lt : p.b.used * 2 * Layout.digitBits < 2 ^ 31
  /-- `a`'s digits: `realloc`'s block, `mp_div`'s old block of `c = a`. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  /-- `mp_div`'s `mp_init_copy(&y, b)` copies from a live block. -/
  bblk : digBlk p.bdp p.b ∈ p.H

def Q (p : P) : Out → Prop
  | .mem _ a' => 0 < a'.alloc
  | .ok _ a' => Reduce.ReduceSetupPost p.b a'

/-- `MP_MEM` or `MP_OKAY`, with `a`'s digits at `q` after. -/
inductive Out
  | mem (q : Nat) (a' : MpInt)
  | ok (q : Nat) (a' : MpInt)

-- Tom/Spec/Reduce.lean
/-- What `mp_reduce_setup(a, b)` leaves in `a` (`mp_2expt(a, 2 * b->used * MP_DIGIT_BIT)`,
`mp_div(a, b, a, NULL)`; `b > 0`): `mu = ⌊radix^(2 b->used) / b⌋`. -/
structure ReduceSetupPost (b a' : MpInt) : Prop where
  valid : a'.Valid
  mag : a'.mag = radix ^ (2 * b.used) / b.mag
  sign : a'.sign = Layout.mpZpos

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`)
-/

/-- `mp_reduce_setup(a, b)`: the allocating contract -/
theorem Specs.mp_reduce_setup_correct_room : Tom.Machine.Api.MpReduceSetup.Statement :=
  Tom.Machine.Fn.MpReduceSetupG5.correct
/-
Machine plumbing: entry `0x800063a8`; the arguments: `a0 = a`, `a1 = b`; stack reservation `F = MpDivQ.F`; regions stk aS aD bS bD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MpReduceSetup.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

/-- What `mp_reduce_setup(a, b)` needs (`MpReduceSetupStep.Env` and the machine's facts). -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_2expt` writes `a` in place (D5: `room`). -/
  sa : p.a.Shape
  room : p.b.used * 2 * Layout.digitBits / Layout.digitBits + 1 ≤ p.a.alloc
  /-- The modulus: valid, positive (`ReduceSetupPost` is stated for `b > 0`; `mp_div`'s `b ≠ 0`). -/
  vb : p.b.Valid
  b0 : 0 < p.b.used
  bz : p.b.sign = Layout.mpZpos
  /-- `mp_2expt`'s `int b` (`slliw`/`subw`/`slliw` at `63b8`: `56 b->used`). -/
  k_lt : p.b.used * 2 * Layout.digitBits < 2 ^ 31
  /-- `a`'s digits are `mp_div`'s old block of `c = a`, freed after the exchange: nonempty. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  /-- `mp_div`'s `mp_init_copy(&y, b)` copies from a live block. -/
  bblk : digBlk p.bdp p.b ∈ p.H

/-- What `a` holds. -/
def Q (p : P) : Out → Prop
  | .mem _ => True
  | .ok _ a' => Reduce.ReduceSetupPost p.b a'

/-- `MP_MEM` (`a`'s value then), or `MP_OKAY` with `a'`'s digits at `q`. -/
inductive Out
  | mem (a' : MpInt)
  | ok (q : Nat) (a' : MpInt)

Also used (printed above): `Tom.Machine.Api.MpReduceSetup.P` (`mp_reduce_setup`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Reduce.ReduceSetupPost` (`mp_reduce_setup`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`)
-/

/-! ## `mp_rshd`

`void mp_rshd(mp_int *a, int b);`
-/

/-- `mp_rshd`: the standard contract -/
theorem Specs.mp_rshd_correct : Tom.Machine.Api.MpRshd.Statement :=
  Tom.Machine.Fn.MpRshd.correct
/-
Machine plumbing: entry `0x80001e1c`; regions stk aS aD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MpRshd.lean
/-- **`mp_rshd` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {b : Nat} {ra s0 : BitVec 64},
    Pre m sp pa adp a b ra →
    Triple (At entry (Fn.MpRshd.entryL ra s0 sp pa b) m v.keepR outp) (Ret m v outp sp pa adp a b ra s0)

/-- What `mp_rshd(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  b_lt : b < 2 ^ 31
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp a) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra s0 : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra (Fn.MpRshd.retL ra s0 sp) M v.keepR outp cf ∧ Post m sp pa adp a b a' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  rshd : RshdPost a b a'
  frame : Frm (lay sp pa adp a) ws m M

-- Tom/Spec/DigitShift.lean
/-- What `mp_rshd(a, k)` leaves, by branch. -/
structure RshdPost (a : MpInt) (k : Nat) (a' : MpInt) : Prop where
  noop : k = 0 → a' = a
  zero : 0 < k → a.used ≤ k → ZeroPost a a'
  shift : 0 < k → k < a.used → RshdShift a k a'
theorem RshdPost.spec {a a' : MpInt} {k : Nat} (ha : a.Valid) (h : RshdPost a k a') :
    a'.Valid ∧ a'.mag = a.mag / radix ^ k := …  -- proved in Tom/Spec/DigitShift.lean

-- Tom/Spec/Set.lean
/-- What `mp_zero(a)` leaves. -/
structure ZeroPost (a a' : MpInt) : Prop where
  used : a'.used = 0
  alloc : a'.alloc = a.alloc
  sign : a'.sign = Layout.mpZpos
  len : a'.digits.length = a.alloc
  digit : ∀ i, a'.digit i = 0
theorem ZeroPost.spec {a a' : MpInt} (ha : a.Shape) (h : ZeroPost a a') :
    a'.Valid ∧ a'.mag = 0 ∧ a'.val = 0 := …  -- proved in Tom/Spec/Set.lean

-- Tom/Spec/DigitShift.lean
/-- The shifting branch of `mp_rshd(a, k)` (`0 < k < used`). -/
structure RshdShift (a : MpInt) (k : Nat) (a' : MpInt) : Prop where
  alloc : a'.alloc = a.alloc
  len : a'.digits.length = a.alloc
  used : a'.used = a.used - k
  sign : a'.sign = a.sign
  digit : ∀ i, a'.digit i = if i + k < a.used then a.digit (i + k) else if i < a.used then 0 else a.digit i
theorem RshdShift.spec {a a' : MpInt} {k : Nat} (ha : a.Valid) (hk : k < a.used) (h : RshdShift a k a') :
    a'.Valid ∧ a'.mag = a.mag / radix ^ k := …  -- proved in Tom/Spec/DigitShift.lean
-/

/-! ## `mp_set`

`void mp_set(mp_int *a, mp_digit b);`
-/

/-- `mp_set`: the standard contract -/
theorem Specs.mp_set_correct : Tom.Machine.Api.MpSet.Statement :=
  Tom.Machine.Fn.MpSet.correct
/-
Machine plumbing: entry `0x80001eb0`; regions stk aS aD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MpSet.lean
/-- **`mp_set` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {bn : Nat} {ra : BitVec 64},
    Pre m sp pa adp a ra →
    Triple (At entry (Fn.MpSet.entryL ra pa bn) m v.keep outp) (Ret m v outp sp pa adp a bn ra)

/-- What `mp_set(a, b)` needs. -/
structure Pre (m : Mem) (sp pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  room : 1 ≤ a.alloc
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp a) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (bn : Nat) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra)] M v.keep outp cf ∧ Post m sp pa adp a bn a' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp : Nat) (a : MpInt) (bn : Nat) (a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  set : SetPost a (bn % radix) a'
  frame : Frm (lay sp pa adp a) ws m M

-- Tom/Spec/Set.lean
/-- What `mp_set(a, b)` leaves, `d = b & MP_MASK` (`a->alloc ≥ 1`). -/
structure SetPost (a : MpInt) (d : Nat) (a' : MpInt) : Prop where
  used : a'.used = if d = 0 then 0 else 1
  alloc : a'.alloc = a.alloc
  sign : a'.sign = Layout.mpZpos
  len : a'.digits.length = a.alloc
  digit : ∀ i, a'.digit i = if i = 0 then d else 0
theorem SetPost.spec {a a' : MpInt} {d : Nat} (ha : a.Shape) (hal : 0 < a.alloc) (hd : d < radix)
    (h : SetPost a d a') : a'.Valid ∧ a'.mag = d ∧ a'.val = d := …  -- proved in Tom/Spec/Set.lean
-/

/-! ## `mp_sqr`

`mp_err mp_sqr(const mp_int *a, mp_int *b);`

Coverage: contract (both shapes, no premises).
-/

/-- `mp_sqr(a, b)`, `b` distinct from `a`: the allocating contract -/
theorem Specs.mp_sqr_correct : Tom.Machine.Api.MpSqr.Statement :=
  Tom.Machine.Fn.MulGroupB.sqrCorrect.1
/-
Machine plumbing: entry `0x80006410`; the arguments: `a0 = a`, `a1 = b` (`gp` for the allocator and the cut-offs); stack reservation `F = Fs p.a.used`; regions stk aS aD bS bD ks ts km tm code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/MpSqr.lean
/-- **`mp_sqr(a, b)` on the machine**, as an allocating contract. -/
def Statement : Prop := ∀ p : P, Spec p

structure P where  (sp pa adp pb bdp : Nat); (a b : MpInt); (H : List (Nat × Nat))

def Spec (p : P) : Prop := SpecR Res p

/-- The contract at one `p`, for a residue `Rs` (`Api/SqrRec.lean` adds the induction hypothesis). -/
def SpecR (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .bD (out p x) (site' p x) (hin p) (hout p x) m M)

/-- What `mp_sqr(a, b)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp (F p)
  /-- The algorithms read `a`'s value; karatsuba's halves are valid because `a` is. -/
  va : p.a.Valid
  /-- `b` is written (in place, or exchanged with a temporary and freed): shaped. -/
  sb : p.b.Shape
  /-- `s_mp_sqr_fast` keeps `b`'s sign word for a nonzero result (`SqrFastPost.spec`). -/
  bsign : p.b.sign = Layout.mpZpos ∨ p.b.sign = Layout.mpNeg
  /-- The C's `int` arithmetic on `a->used` (`2 a->used`, `slliw` at `6434`; karatsuba's
  `mp_init_size(&t1, a->used * 2)`). -/
  au : p.a.used < 2 ^ 29
  /-- D5 for the comba path: `s_mp_sqr_fast` would `mp_grow` `b` otherwise. -/
  room : p.a.used < 120 → 2 * p.a.used ≤ p.b.alloc
  /-- Nonempty digit arrays (`HContract.pos`); `b`'s is a live block that may be freed. -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

def Q (p : P) (x : X) : Prop := Out p x

/-- What `b` holds after (`x = (ok, q, b')`). -/
structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  /-- `b->sign := MP_ZPOS` at the end, on every path. -/
  sign : x.2.2.sign = Layout.mpZpos
  pos : 0 < x.2.2.alloc
  /-- `MP_OKAY`: the square (`Tom/Spec/MulAlgo.lean`). -/
  post : x.1 = true → SqrPost p.a x.2.2
  /-- Where `b'`'s digits are (`HPost.place`, restated for a caller that passes the site on). -/
  place : Place (hin p) (lay p .bD) (site' p x)
  /-- `b`'s digits only grow (`mp_grow`; a caller's D5 room for a later call survives). -/
  grow : p.b.alloc ≤ x.2.2.alloc

-- Tom/Spec/MulAlgo.lean
/-- `mp_sqr(a, b)`: `b = a²`, valid. -/
structure SqrPost (a b' : MpInt) : Prop where
  valid : b'.Valid
  val : b'.val = a.val * a.val

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MpSqr.X` (`mp_mul_2`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`)
-/

/-- `mp_sqr(a, a)`: the in-place contract -/
theorem Specs.mp_sqr_correct_inplace : Tom.Machine.Api.MpSqrA.Statement :=
  Tom.Machine.Fn.MulGroupB.sqrCorrect.2
/-
Machine plumbing: entry `0x80006410`; the arguments: `a0 = a1 = a`; stack reservation `F = Fs p.a.used`; regions stk aS aD ks ts km tm code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MpSqrA.lean
/-- **`mp_sqr(a, a)` on the machine.** -/
def Statement : Prop := ∀ p : P, Spec p

structure P where  (sp pa adp : Nat); (a : MpInt); (H : List (Nat × Nat))

def Spec (p : P) : Prop := SpecR Res p

def SpecR (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

/-- `Api.MpSqr.Res` with `b = a` (`a` valid, hence shaped with a sign). -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp (F p)
  va : p.a.Valid
  /-- The C's `int` arithmetic on `a->used`. -/
  au : p.a.used < 2 ^ 29
  /-- D5 for the comba path: `s_mp_sqr_fast` would `mp_grow` `a` otherwise. -/
  room : p.a.used < 120 → 2 * p.a.used ≤ p.a.alloc
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

def Q (p : P) (x : X) : Prop := Out p x

structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  sign : x.2.2.sign = Layout.mpZpos
  pos : 0 < x.2.2.alloc
  post : x.1 = true → SqrPost p.a x.2.2
  place : Place (hin p) (lay p .aD) (site' p x)
  grow : p.a.alloc ≤ x.2.2.alloc

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MpSqr.X` (`mp_mul_2`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.SqrPost` (`mp_sqr`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`)
-/

/-- The squaring group's recursion -/
theorem Specs.mp_sqr_below : ∀ n, Tom.Machine.Api.SqrRec.SqrBelow n :=
  Tom.Machine.Fn.MulGroupB.sqrBelow
/-
-- Tom/Machine/Api/SqrRec.lean
/-- **The induction hypothesis**: both contracts below measure `n`. -/
def SqrBelow (n : Nat) : Prop := ∀ k, k < n → SqrAt k

/-- Both `mp_sqr` contracts at measure `n`. -/
def SqrAt (n : Nat) : Prop :=
  (∀ p : MpSqr.P, p.a.used = n → MpSqr.Spec p) ∧ (∀ p : MpSqrA.P, p.a.used = n → MpSqrA.Spec p)

Also used (printed above): `Tom.Machine.Api.MpSqr.P` (`mp_sqr`), `Tom.Machine.Api.MpSqr.Spec` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.P` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Spec` (`mp_sqr`), `Tom.Machine.Api.MpSqr.SpecR` (`mp_sqr`), `Tom.Machine.Api.MpSqr.Res` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.SpecR` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Res` (`mp_sqr`), `Tom.Machine.Api.MpSqr.Q` (`mp_sqr`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MpSqrA.Q` (`mp_sqr`), `Tom.Machine.Api.MpSqr.X` (`mp_mul_2`), `Tom.Machine.Api.MpSqr.Out` (`mp_sqr`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.MpSqrA.Out` (`mp_sqr`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.SqrPost` (`mp_sqr`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`)
-/

/-! ## `mp_sub`

`mp_err mp_sub(const mp_int *a, const mp_int *b, mp_int *c);`
-/

/-- `mp_sub(a, b, c)` and `mp_sub(a, b, a)` with growth: the allocating contracts -/
theorem Specs.mp_sub_correct : Tom.Machine.Api.MpSubG.Statement :=
  Tom.Machine.Fn.MpSubGG5.correct
/-
Machine plumbing: entry `0x80001ef4`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator); stack reservation `F = 64 + MpGrow.F`; regions stk aS aD bS bD cS cD code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/MpSubG.lean
def Statement : Prop := Standard.Statement Res Q (site .cD)  -- the standard shape (top of file)

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.c.alloc < subSize p.a p.b
  | some (_, x) => SubG p.a p.b (SAddPost p.a p.b (sAddIn p.a p.b (p.c.withSign p.a.sign)) x)
      (SSubPost p.b p.a (sSubIn p.b (p.c.withSign (if p.b.sign = 0 then 1 else 0))) x)
      (SSubPost p.a p.b (sSubIn p.a (p.c.withSign p.b.sign)) x)

-- Tom/Spec/SubGStep.lean
/-- The size the tail callee grows `c` to (when `c->alloc` is less). -/
def subSize (a b : MpInt) : Nat :=
  if a.sign = b.sign then (if a.mag < b.mag then b.used else a.used) else max a.used b.used + 1

/-- What `mp_sub` leaves, by branch. -/
structure SubG (a b : MpInt) (D L G : Prop) : Prop where
  diff : a.sign ≠ b.sign → D
  lt : a.sign = b.sign → a.mag < b.mag → L
  ge : a.sign = b.sign → ¬ a.mag < b.mag → G
theorem SubG.specB {a b x : MpInt} (ha : a.Valid) (hb : b.Valid)
    (h31 : max a.used b.used + 1 < 2 ^ 31)
    (h : SubG a b (SAddPost a (b.withSign a.sign) (sAddIn a (b.withSign a.sign) (b.withSign a.sign)) x)
      (SSubPost (b.withSign (if b.sign = 0 then 1 else 0)) a
        (sSubIn (b.withSign (if b.sign = 0 then 1 else 0)) (b.withSign (if b.sign = 0 then 1 else 0))) x)
      (SSubPost a (b.withSign b.sign) (sSubIn a (b.withSign b.sign)) x)) :
    x.Valid ∧ x.val = a.val - b.val ∧ b.alloc ≤ x.alloc := …  -- proved in Tom/Spec/SubGBStep.lean
theorem SubG.spec {a b c x : MpInt} (ha : a.Valid) (hb : b.Valid) (hc : c.Shape)
    (h31 : max a.used b.used + 1 < 2 ^ 31)
    (h : SubG a b (SAddPost a b (sAddIn a b (c.withSign a.sign)) x)
      (SSubPost b a (sSubIn b (c.withSign (if b.sign = 0 then 1 else 0))) x)
      (SSubPost a b (sSubIn a (c.withSign b.sign)) x)) :
    x.Valid ∧ x.val = a.val - b.val ∧ c.alloc ≤ x.alloc := …  -- proved in Tom/Spec/SubGStep.lean
theorem SubG.specA {a b x : MpInt} (ha : a.Valid) (hb : b.Valid)
    (h31 : max a.used b.used + 1 < 2 ^ 31)
    (h : SubG a b (SAddPost (a.withSign a.sign) b (sAddIn (a.withSign a.sign) b (a.withSign a.sign)) x)
      (SSubPost b (a.withSign (if b.sign = 0 then 1 else 0)) (sSubIn b (a.withSign (if b.sign = 0 then 1 else 0))) x)
      (SSubPost (a.withSign b.sign) b (sSubIn (a.withSign b.sign) (a.withSign b.sign)) x)) :
    x.Valid ∧ x.val = a.val - b.val ∧ a.alloc ≤ x.alloc := …  -- proved in Tom/Spec/SubGStep.lean

Also used (printed above): `Tom.Machine.Api.MpAddG.P` (`mp_add`), `Tom.Machine.Api.MpAddG.Res` (`mp_add`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.SAddPost` (`mp_add`), `Tom.sAddIn` (`mp_add`), `Tom.MpInt.withSign` (`mp_add`), `Tom.SSubPost` (`mp_add`), `Tom.sSubIn` (`mp_add`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.addDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.subDigits` (`mp_add`), `Tom.addCarry` (`mp_add`), `Tom.MpInt.ofDigits` (`mp_abs`), `Tom.subBorrow` (`mp_add`)
-/

/-- `mp_sub(a, b, c)` and `mp_sub(a, b, a)` with growth: the allocating contracts -/
theorem Specs.mp_sub_correct_ca : Tom.Machine.Api.MpSubGA.Statement :=
  Tom.Machine.Fn.MpSubGAG5.correct
/-
Machine plumbing: entry `0x80001ef4`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator); stack reservation `F = 64 + MpGrow.F`; regions stk aS aD bS bD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MpSubG.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.a.alloc < subSize p.a p.b
  | some (_, x) => SubG p.a p.b
      (SAddPost (p.a.withSign p.a.sign) p.b (sAddIn (p.a.withSign p.a.sign) p.b (p.a.withSign p.a.sign)) x)
      (SSubPost p.b (p.a.withSign (if p.b.sign = 0 then 1 else 0))
        (sSubIn p.b (p.a.withSign (if p.b.sign = 0 then 1 else 0))) x)
      (SSubPost (p.a.withSign p.b.sign) p.b (sSubIn (p.a.withSign p.b.sign) (p.a.withSign p.b.sign)) x)

Also used (printed above): `Tom.Machine.Api.MpAddGA.P` (`mp_add`), `Tom.Machine.Api.MpAddGA.Res` (`mp_add`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.subSize` (`mp_sub`), `Tom.SubG` (`mp_sub`), `Tom.SAddPost` (`mp_add`), `Tom.MpInt.withSign` (`mp_add`), `Tom.sAddIn` (`mp_add`), `Tom.SSubPost` (`mp_add`), `Tom.sSubIn` (`mp_add`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.addDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.subDigits` (`mp_add`), `Tom.addCarry` (`mp_add`), `Tom.MpInt.ofDigits` (`mp_abs`), `Tom.subBorrow` (`mp_add`)
-/

/-- `mp_sub(a, b, b)` with growth: the allocating contract and its value form -/
theorem Specs.mp_sub_correct_cb : Tom.Machine.Api.MpSubGB.Statement :=
  Tom.Machine.Fn.MpSubGBG5.correct
/-
Machine plumbing: entry `0x80001ef4`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator); stack reservation `F = 64 + MpGrow.F`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/MpSubGB.lean
def Statement : Prop := Standard.Statement Res Q (site .bD)  -- the standard shape (top of file)

/-- The tail callee's post by branch: `s_mp_add(a, b, b)`, `s_mp_sub(b, a, b)`, `s_mp_sub(a, b, b)`,
each over `b` with the sign `mp_sub` stored. -/
def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.b.alloc < subSize p.a p.b
  | some (_, x) => SubG p.a p.b
      (SAddPost p.a (p.b.withSign p.a.sign) (sAddIn p.a (p.b.withSign p.a.sign) (p.b.withSign p.a.sign)) x)
      (SSubPost (p.b.withSign (if p.b.sign = 0 then 1 else 0)) p.a
        (sSubIn (p.b.withSign (if p.b.sign = 0 then 1 else 0)) (p.b.withSign (if p.b.sign = 0 then 1 else 0))) x)
      (SSubPost p.a (p.b.withSign p.b.sign) (sSubIn p.a (p.b.withSign p.b.sign)) x)

Also used (printed above): `Tom.Machine.Api.MpAddGB.P` (`mp_add`), `Tom.Machine.Api.MpAddGB.Res` (`mp_add`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.subSize` (`mp_sub`), `Tom.SubG` (`mp_sub`), `Tom.SAddPost` (`mp_add`), `Tom.MpInt.withSign` (`mp_add`), `Tom.sAddIn` (`mp_add`), `Tom.SSubPost` (`mp_add`), `Tom.sSubIn` (`mp_add`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.addDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.subDigits` (`mp_add`), `Tom.addCarry` (`mp_add`), `Tom.MpInt.ofDigits` (`mp_abs`), `Tom.subBorrow` (`mp_add`)
-/

/-- `mp_sub`: the standard contract -/
theorem Specs.mp_sub_correct_room : Tom.Machine.Api.MpSub.Statement :=
  Tom.Machine.Fn.MpSub.correct
/-
Machine plumbing: entry `0x80001ef4`; regions stk cS cD aS aD bS bD code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/MpSub.lean
/-- **`mp_sub` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat}
    {a b c : MpInt} {ra s0 : BitVec 64}, Pre m sp pa adp pb bdp pc cdp a b c ra →
    Triple (At entry (Fn.SSub.entryL ra s0 sp pa pb pc) m v.keepR outp)
      (Ret m v outp sp pa adp pb bdp pc cdp a b c ra s0)

/-- What `mp_sub(a, b, c)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  rc : MpAt m pc cdp c
  va : a.Valid
  vb : b.Valid
  sc : c.Shape
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  gc : MpGeom pc cdp c.alloc
  room : max a.used b.used + 1 ≤ c.alloc
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp pc cdp a b c) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp pc cdp a b c c' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp pc cdp : Nat) (a b c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  sub : SubPost a b c c'
  frame : Frm (lay sp pa adp pb bdp pc cdp a b c) ws m M

-- Tom/Spec/Signed.lean
/-- What `mp_sub(a, b, c)` leaves in `c`, by the branch it takes. -/
structure SubPost (a b c c' : MpInt) : Prop where
  diff : a.sign ≠ b.sign → SAddPost a b (c.withSign a.sign) c'
  ge : a.sign = b.sign → cmpMag a b ≠ .lt → SSubPost a b (c.withSign a.sign) c'
  lt : a.sign = b.sign → cmpMag a b = .lt →
    SSubPost b a (c.withSign (if a.sign = Layout.mpZpos then Layout.mpNeg else Layout.mpZpos)) c'
theorem SubPost.spec {a b c c' : MpInt} (ha : a.Valid) (hb : b.Valid)
    (hroom : max a.used b.used + 1 ≤ c.alloc) (hc : c.alloc < 2 ^ 31) (h : SubPost a b c c') :
    c'.Valid ∧ c'.val = a.val - b.val := …  -- proved in Tom/Spec/Signed.lean

Also used (printed above): `Tom.SAddPost` (`mp_add`), `Tom.MpInt.withSign` (`mp_add`), `Tom.cmpMag` (`mp_add`), `Tom.SSubPost` (`mp_add`), `Tom.addDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.cmpTop` (`mp_add`), `Tom.subDigits` (`mp_add`), `Tom.addCarry` (`mp_add`), `Tom.subBorrow` (`mp_add`)
-/

/-- `mp_sub` in place: the standard contracts -/
theorem Specs.mp_sub_correct_room_ca : Tom.Machine.Api.MpSubAlias.StatementCA :=
  Tom.Machine.Fn.MpSub.correctCA
/-
Machine plumbing: entry `0x80001ef4`; regions stk aS aD bS bD code.

-- Tom/Machine/Api/MpSubAlias.lean
/-- **`mp_sub(a, b, a)` on the machine.** -/
def StatementCA : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    PreCA m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.SSub.entryL ra s0 sp pa pb pa) m v.keepR outp)
      (RetCA m v outp sp pa adp pb bdp a b ra s0)

/-- What `mp_sub(a, b, a)` needs. -/
structure PreCA (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop
    extends Base m 64 sp pa adp pb bdp a b ra where
  va : a.Valid
  vb : b.Valid
  room : max a.used b.used + 1 ≤ a.alloc
  lay : Sound (lay sp pa adp pb bdp a b) isWA

def RetCA (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostCA m sp pa adp pb bdp a b a' M

/-- What `mp_sub(a, b, a)` leaves: `a'` at `a`. -/
structure PostCA (m : Mem) (sp pa adp pb bdp : Nat) (a b a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  sub : SubPost a b a a'
  frame : Frm (lay sp pa adp pb bdp a b) wsA m M

Also used (printed above): `Tom.Machine.Api.BinA.Base` (`mp_add`), `Tom.Machine.Api.BinA.isWA` (`mp_add`), `Tom.SubPost` (`mp_sub`), `Tom.Machine.Api.BinA.wsA` (`mp_add`), `Tom.SAddPost` (`mp_add`), `Tom.MpInt.withSign` (`mp_add`), `Tom.cmpMag` (`mp_add`), `Tom.SSubPost` (`mp_add`), `Tom.addDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.cmpTop` (`mp_add`), `Tom.subDigits` (`mp_add`), `Tom.addCarry` (`mp_add`), `Tom.subBorrow` (`mp_add`)
-/

/-- `mp_sub` in place: the standard contracts -/
theorem Specs.mp_sub_correct_room_cb : Tom.Machine.Api.MpSubAlias.StatementCB :=
  Tom.Machine.Fn.MpSub.correctCB
/-
Machine plumbing: entry `0x80001ef4`; regions stk aS aD bS bD code.

-- Tom/Machine/Api/MpSubAlias.lean
/-- **`mp_sub(a, b, b)` on the machine.** -/
def StatementCB : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    PreCB m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.SSub.entryL ra s0 sp pa pb pb) m v.keepR outp)
      (RetCB m v outp sp pa adp pb bdp a b ra s0)

/-- What `mp_sub(a, b, b)` needs. -/
structure PreCB (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop
    extends Base m 64 sp pa adp pb bdp a b ra where
  va : a.Valid
  vb : b.Valid
  room : max a.used b.used + 1 ≤ b.alloc
  lay : Sound (lay sp pa adp pb bdp a b) isWB

def RetCB (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ b' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostCB m sp pa adp pb bdp a b b' M

/-- What `mp_sub(a, b, b)` leaves: `b'` at `b`. -/
structure PostCB (m : Mem) (sp pa adp pb bdp : Nat) (a b b' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pb bdp b'
  sub : SubPost a b b b'
  frame : Frm (lay sp pa adp pb bdp a b) wsB m M

Also used (printed above): `Tom.Machine.Api.BinA.Base` (`mp_add`), `Tom.Machine.Api.BinA.isWB` (`mp_add`), `Tom.SubPost` (`mp_sub`), `Tom.Machine.Api.BinA.wsB` (`mp_add`), `Tom.SAddPost` (`mp_add`), `Tom.MpInt.withSign` (`mp_add`), `Tom.cmpMag` (`mp_add`), `Tom.SSubPost` (`mp_add`), `Tom.addDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.cmpTop` (`mp_add`), `Tom.subDigits` (`mp_add`), `Tom.addCarry` (`mp_add`), `Tom.subBorrow` (`mp_add`)
-/

/-! ## `mp_sub_d`

`mp_err mp_sub_d(const mp_int *a, mp_digit b, mp_int *c);`
-/

/-- `mp_sub_d`: the standard contract -/
theorem Specs.mp_sub_d_correct : Tom.Machine.Api.SubD.Statement :=
  Tom.Machine.Fn.SubD.correct
/-
Machine plumbing: entry `0x800064a4`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/SubD.lean
/-- **`mp_sub_d` on the machine** (stack depth 128: its frame and `mp_add_d`'s). -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat} {c : MpInt}
    {ra s0 : BitVec 64}, Pre 128 m sp pa adp pc cdp a b c ra →
    Triple (At entry (entryL ra s0 sp pa b pc) m v.keepR outp) (Ret 128 m v outp sp pa adp pc cdp a b c ra s0)

/-- What `mp_sub_d(a, b, c)` needs, with a stack of depth `F`. -/
structure Pre (F : Nat) (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c : MpInt) (ra : BitVec 64) :
    Prop where
  ra_ : MpAt m pa adp a
  rc : MpAt m pc cdp c
  va : a.Valid
  sc : c.Shape
  hb : b < radix
  ga : MpGeom pa adp a.alloc
  gc : MpGeom pc cdp c.alloc
  room : a.used + 1 ≤ c.alloc
  rs : Ram (sp - F) F
  sp_al : sp % 16 = 0
  sp_ge : F ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay F sp pa adp pc cdp a c) isW

def Ret (F : Nat) (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat)
    (c : MpInt) (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post F m sp pa adp pc cdp a b c c' M

/-- What it leaves. -/
structure Post (F : Nat) (m : Mem) (sp pa adp pc cdp : Nat) (a : MpInt) (b : Nat) (c c' : MpInt) (M : Mem) :
    Prop where
  repr : MpAt M pc cdp c'
  subd : SubDPost a b c c'
  frame : Frm (lay F sp pa adp pc cdp a c) ws m M

-- Tom/Spec/Digit.lean
/-- What `mp_sub_d(a, b, c)` leaves in `c`, by the branch it takes. -/
structure SubDPost (a : MpInt) (b : Nat) (c c' : MpInt) : Prop where
  neg : a.sign = Layout.mpNeg → DRes c c' (addDDigits a b) (a.used + 1) Layout.mpNeg
  small : a.sign = Layout.mpZpos → SubDSmall a b → DRes c c' (smallDigits a b) 1 Layout.mpNeg
  big : a.sign = Layout.mpZpos → ¬ SubDSmall a b → DRes c c' (subDDigits a b) a.used Layout.mpZpos
theorem SubDPost.spec {a c c' : MpInt} {b : Nat} (ha : a.Valid) (hb : b < radix)
    (hroom : a.used + 1 ≤ c.alloc) (hc : c.alloc < 2 ^ 31) (h : SubDPost a b c c') :
    c'.Valid ∧ c'.val = a.val - b := …  -- proved in Tom/Spec/Digit.lean

/-- `mp_sub_d`'s test for its small branch (`0 ≤ a ≤ b`). -/
def SubDSmall (a : MpInt) (b : Nat) : Prop := (a.used = 1 ∧ a.digit 0 ≤ b) ∨ a.used = 0

Also used (printed above): `Tom.DRes` (`mp_add_d`), `Tom.addDDigits` (`mp_add_d`), `Tom.smallDigits` (`mp_add_d`), `Tom.subDDigits` (`mp_add_d`), `Tom.clampUsed` (`mp_add`), `Tom.addDCarry` (`mp_add_d`), `Tom.subDBorrow` (`mp_add_d`), `Tom.carryChain` (`mp_add_d`), `Tom.borrowChain` (`mp_add_d`)
-/

/-- `mp_sub_d`: the standard contract -/
theorem Specs.mp_sub_d_correct_inplace_pos : Tom.Machine.Api.SubD.StatementInPlacePos :=
  Tom.Machine.Fn.SubD.correct_inplace_pos
/-
Machine plumbing: entry `0x800064a4`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/SubD.lean
/-- **`mp_sub_d(a, b, a)` on the machine for `a ≥ 0`** (any stack depth `F ≥ 64`). -/
def StatementInPlacePos : Prop :=
  ∀ {F : Nat} {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {b : Nat}
    {ra s0 : BitVec 64}, 64 ≤ F → PreI F m sp pa adp a b ra → a.sign = Layout.mpZpos →
    Triple (At entry (entryL ra s0 sp pa b pa) m v.keepR outp) (RetI F m v outp sp pa adp a b ra s0)

/-- What `mp_sub_d(a, b, a)` needs, with a stack of depth `F`. -/
structure PreI (F : Nat) (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  va : a.Valid
  hb : b < radix
  ga : MpGeom pa adp a.alloc
  room : a.used + 1 ≤ a.alloc
  rs : Ram (sp - F) F
  sp_al : sp % 16 = 0
  sp_ge : F ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (layI F sp pa adp a) Un.isW

def RetI (F : Nat) (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (b : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostI F m sp pa adp a b a' M

/-- The regions of the in-place call (`Api/Un.lean`: `a` written). -/
abbrev layI (F sp pa adp : Nat) (a : MpInt) := Un.lay F sp pa adp a

/-- What it leaves. -/
structure PostI (F : Nat) (m : Mem) (sp pa adp : Nat) (a : MpInt) (b : Nat) (a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  subd : SubDPost a b a a'
  frame : Frm (layI F sp pa adp a) Un.ws m M

Also used (printed above): `Tom.SubDPost` (`mp_sub_d`), `Tom.DRes` (`mp_add_d`), `Tom.addDDigits` (`mp_add_d`), `Tom.SubDSmall` (`mp_sub_d`), `Tom.smallDigits` (`mp_add_d`), `Tom.subDDigits` (`mp_add_d`), `Tom.clampUsed` (`mp_add`), `Tom.addDCarry` (`mp_add_d`), `Tom.subDBorrow` (`mp_add_d`), `Tom.carryChain` (`mp_add_d`), `Tom.borrowChain` (`mp_add_d`)
-/

/-! ## `mp_to_radix`

`mp_err mp_to_radix(const mp_int *a, char *str, size_t maxlen, size_t *written, int radix);`

Coverage: contract (written = NULL).
-/

/-- `mp_to_radix(a, str, maxlen, written, radix)`: the allocating contract -/
theorem Specs.mp_to_radix_correct : Tom.Machine.Api.MpToRadix.Statement :=
  Tom.Machine.Fn.MpToRadixG5.correct
/-
Machine plumbing: entry `0x80001f80`; the arguments: `a0 = a`, `a1 = str`, `a2 = maxlen`, `a3 = written = NULL`, `a4 = radix`; stack reservation `F = 816`; regions stk aS aD str code; written [.stk, .str].

-- Tom/Machine/Api/MpToRadix.lean
def Statement : Prop := Standard.Statement Res Q (site .str)  -- the standard shape (top of file)

structure P where  (sp pa adp pstr maxlen radix : Nat); (a : MpInt); (m0 : Mem); (H : List (Nat × Nat))

/-- What `mp_to_radix(a, str, maxlen, NULL, radix)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- `mp_init_copy` copies a valid `a`; the digit loop reads its value. -/
  va : p.a.Valid
  /-- `mp_init_copy` reads `a`'s digit block: live and nonempty (`IcRes`). -/
  ablk : digBlk p.adp p.a ∈ p.H
  apos : 0 < p.a.alloc
  /-- `a`'s struct lies off the arena (`IcRes`). -/
  aoff : OffHeap p.pa 24
  /-- The C's `int radix`, nonnegative: the rows (`mtoradix`) take `a4` as a natural number
  below `2^31` (`addiw`/`bltu` on its low word); a negative radix is not covered. -/
  rx_lt : p.radix < 2 ^ 31

/-- The bytes before and after, as `ToRadixPost` reads them. -/
def Q (p : P) (x : Int × Mem) : Prop :=
  ToRadixPost p.a p.maxlen p.radix false (bytesOf p.m0 p.pstr p.maxlen) (bytesOf x.2 p.pstr p.maxlen) 0 0 x.1 ∨
    x.1 = Layout.mpMem

-- Tom/Spec/Radix.lean
/-- What `mp_to_radix(a, str, maxlen, written, radix)` leaves: `buf`/`buf'` are
the bytes at `str + i` before and after, `w`/`w'` the `size_t` at `written`
before and after (`hasW`: `written ≠ NULL`). Bytes past `toRadixOut` are
unchanged; `written` is stored only on success. -/
structure ToRadixPost (a : MpInt) (maxlen : Nat) (radix : Int) (hasW : Bool)
    (buf buf' : Nat → Nat) (w w' : Nat) (ret : Int) : Prop where
  code : ret = toRadixRet a maxlen radix
  bytes : ∀ i, buf' i = (toRadixOut a maxlen radix).getD i (buf i)
  written : w' = if hasW = true ∧ ret = Layout.mpOkay then (toRadixOut a maxlen radix).length else w
theorem ToRadixPost.spec_ok {a : MpInt} {maxlen : Nat} {radix : Int} {hasW : Bool}
    {buf buf' : Nat → Nat} {w w' : Nat} {ret : Int} (ha : a.Valid) (hr : radixOk radix)
    (hfit : (toRadixStr a radix.toNat).length ≤ maxlen) (hm : 2 ≤ maxlen)
    (h : ToRadixPost a maxlen radix hasW buf buf' w w' ret) :
    ret = Layout.mpOkay ∧
      (∀ i, buf' i = (toRadixStr a radix.toNat).getD i (buf i)) ∧
      w' = (if hasW = true then (toRadixStr a radix.toNat).length else w) := …  -- proved in Tom/Spec/Radix.lean
theorem ToRadixPost.spec_err {a : MpInt} {maxlen : Nat} {radix : Int} {hasW : Bool}
    {buf buf' : Nat → Nat} {w w' : Nat} {ret : Int} (ha : a.Valid)
    (h : ToRadixPost a maxlen radix hasW buf buf' w w' ret) :
    (maxlen < 2 → ret = mpBuf ∧ buf' = buf ∧ w' = w) ∧
      (2 ≤ maxlen → ¬ radixOk radix → ret = Layout.mpVal ∧ buf' = buf ∧ w' = w) ∧
      (2 ≤ maxlen → radixOk radix → maxlen < (toRadixStr a radix.toNat).length → ret = mpBuf ∧ w' = w) := …  -- proved in Tom/Spec/Radix.lean

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`)
-/

/-! ## `mp_zero`

`void mp_zero(mp_int *a);`
-/

/-- `mp_zero`: the standard contract -/
theorem Specs.mp_zero_correct : Tom.Machine.Api.MpZero.Statement :=
  Tom.Machine.Fn.MpZero.correct
/-
Machine plumbing: entry `0x80002178`; regions stk aS aD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MpZero.lean
/-- **`mp_zero` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {ra : BitVec 64},
    Pre m sp pa adp a ra →
    Triple (At entry (Fn.MpZero.entryL ra pa) m v.keep outp) (Ret m v outp sp pa adp a ra)

/-- What `mp_zero(a)` needs. -/
structure Pre (m : Mem) (sp pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp a) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra)] M v.keep outp cf ∧ Post m sp pa adp a a' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp : Nat) (a a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  zero : ZeroPost a a'
  frame : Frm (lay sp pa adp a) ws m M

Also used (printed above): `Tom.ZeroPost` (`mp_rshd`)
-/

/-! ## `s_mp_add`

`mp_err s_mp_add(const mp_int *a, const mp_int *b, mp_int *c);`
-/

/-- `s_mp_add(a, b, c)` with growth: the allocating contract -/
theorem Specs.s_mp_add_correct : Tom.Machine.Api.SAddG.Statement :=
  Tom.Machine.Fn.SAddGG5.correct
/-
Machine plumbing: entry `0x8000219c`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator); stack reservation `F = 64 + MpGrow.F`; regions stk aS aD bS bD cS cD code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/SAddG.lean
def Statement : Prop := Standard.Statement Res Q (site .cD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp pc cdp : Nat); (a b c : MpInt); (H : List (Nat × Nat))

/-- What `s_mp_add(a, b, c)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The loops read the operands' digits below `used`. -/
  sa : p.a.Shape
  sb : p.b.Shape
  /-- `c`'s old digits above the result are zeroed only up to its old `used`. -/
  sc : p.c.Shape
  /-- `mp_grow`'s `int size` (`max(used) + 1`). -/
  size_lt : max p.a.used p.b.used + 1 < 2 ^ 31
  /-- The operands' digit arrays are nonempty (initialised `mp_int`s). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  cpos : 0 < p.c.alloc
  /-- `c`'s struct is off the arena (`mp_grow` reads and writes it). -/
  coff : OffHeap p.pc 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.c.alloc < max p.a.used p.b.used + 1
  | some (_, x) => SAddPost p.a p.b (sAddIn p.a p.b p.c) x

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.SAddPost` (`mp_add`), `Tom.sAddIn` (`mp_add`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.addDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.addCarry` (`mp_add`), `Tom.MpInt.ofDigits` (`mp_abs`)
-/

/-- `s_mp_add(a, b, a)` with growth: the allocating contract -/
theorem Specs.s_mp_add_correct_ca : Tom.Machine.Api.SAddGA.Statement :=
  Tom.Machine.Fn.SAddGAG5.correct
/-
Machine plumbing: entry `0x8000219c`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator); stack reservation `F = 64 + MpGrow.F`; regions stk aS aD bS bD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/SAddGA.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp : Nat); (a b : MpInt); (H : List (Nat × Nat))

/-- What `s_mp_add(a, b, a)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The loops read the operands' digits below `used`. -/
  sa : p.a.Shape
  sb : p.b.Shape
  /-- `mp_grow`'s `int size` (`max(used) + 1`). -/
  size_lt : max p.a.used p.b.used + 1 < 2 ^ 31
  /-- The operands' digit arrays are nonempty (initialised `mp_int`s). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- `a`'s struct is off the arena (`mp_grow` reads and writes it). -/
  coff : OffHeap p.pa 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.a.alloc < max p.a.used p.b.used + 1
  | some (_, x) => SAddPost p.a p.b (sAddIn p.a p.b p.a) x

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.SAddPost` (`mp_add`), `Tom.sAddIn` (`mp_add`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.addDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.addCarry` (`mp_add`), `Tom.MpInt.ofDigits` (`mp_abs`)
-/

/-- `s_mp_add(a, b, b)` with growth: the allocating contract -/
theorem Specs.s_mp_add_correct_cb : Tom.Machine.Api.SAddGB.Statement :=
  Tom.Machine.Fn.SAddGBG5.correct
/-
Machine plumbing: entry `0x8000219c`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator); stack reservation `F = 64 + MpGrow.F`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/SAddGB.lean
def Statement : Prop := Standard.Statement Res Q (site .bD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp : Nat); (a b : MpInt); (H : List (Nat × Nat))

/-- What `s_mp_add(a, b, b)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The loops read the operands' digits below `used`. -/
  sa : p.a.Shape
  sb : p.b.Shape
  /-- `mp_grow`'s `int size` (`max(used) + 1`). -/
  size_lt : max p.a.used p.b.used + 1 < 2 ^ 31
  /-- The operands' digit arrays are nonempty (initialised `mp_int`s). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- `b`'s struct is off the arena (`mp_grow` reads and writes it). -/
  coff : OffHeap p.pb 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.b.alloc < max p.a.used p.b.used + 1
  | some (_, x) => SAddPost p.a p.b (sAddIn p.a p.b p.b) x

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.SAddPost` (`mp_add`), `Tom.sAddIn` (`mp_add`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.addDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.addCarry` (`mp_add`), `Tom.MpInt.ofDigits` (`mp_abs`)
-/

namespace Tom.Machine.Api.SAdd
open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Bin
/-- `s_mp_add`: the standard contract -/
theorem _root_.Specs.s_mp_add_correct_room {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat}
    {a b c : MpInt} {ra s0 : BitVec 64} (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Triple (At entry (Fn.SAdd.entryL ra s0 sp pa pb pc) m v.keepR outp)
      (Ret m v outp sp pa adp pb bdp pc cdp a b c ra s0) :=
  Tom.Machine.Api.SAdd.correct hP
end Tom.Machine.Api.SAdd
/-
-- Tom/Machine/Api/SAdd.lean
/-- What `s_mp_add(a, b, c)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  rc : MpAt m pc cdp c
  sa : a.Shape
  sb : b.Shape
  sc : c.Shape
  csign : c.sign = Layout.mpZpos ∨ c.sign = Layout.mpNeg
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  gc : MpGeom pc cdp c.alloc
  room : max a.used b.used + 1 ≤ c.alloc
  rs : Ram (sp - 64) 64
  sp_al : sp % 16 = 0
  sp_ge : 64 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp pc cdp a b c) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp pc cdp a b c c' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp pc cdp : Nat) (a b c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  sadd : SAddPost a b c c'
  frame : Frm (lay sp pa adp pb bdp pc cdp a b c) ws m M

Also used (printed above): `Tom.SAddPost` (`mp_add`), `Tom.addDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.addCarry` (`mp_add`)
-/

/-- `s_mp_add` in place: the standard contracts -/
theorem Specs.s_mp_add_correct_room_ca : Tom.Machine.Api.SAddAlias.StatementCA :=
  Tom.Machine.Fn.SAdd.correctCA
/-
Machine plumbing: entry `0x8000219c`; regions stk aS aD bS bD code.

-- Tom/Machine/Api/SAddAlias.lean
/-- **`s_mp_add(a, b, a)` on the machine.** -/
def StatementCA : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    PreCA m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.SAdd.entryL ra s0 sp pa pb pa) m v.keepR outp)
      (RetCA m v outp sp pa adp pb bdp a b ra s0)

/-- What `s_mp_add(a, b, a)` needs. -/
structure PreCA (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop
    extends Base m 64 sp pa adp pb bdp a b ra where
  sa : a.Shape
  sb : b.Shape
  asign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg
  room : max a.used b.used + 1 ≤ a.alloc
  lay : Sound (lay sp pa adp pb bdp a b) isWA

def RetCA (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostCA m sp pa adp pb bdp a b a' M

/-- What `s_mp_add(a, b, a)` leaves: `a'` at `a`. -/
structure PostCA (m : Mem) (sp pa adp pb bdp : Nat) (a b a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  sadd : SAddPost a b a a'
  frame : Frm (lay sp pa adp pb bdp a b) wsA m M

Also used (printed above): `Tom.Machine.Api.BinA.Base` (`mp_add`), `Tom.Machine.Api.BinA.isWA` (`mp_add`), `Tom.SAddPost` (`mp_add`), `Tom.Machine.Api.BinA.wsA` (`mp_add`), `Tom.addDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.addCarry` (`mp_add`)
-/

/-- `s_mp_add` in place: the standard contracts -/
theorem Specs.s_mp_add_correct_room_cb : Tom.Machine.Api.SAddAlias.StatementCB :=
  Tom.Machine.Fn.SAdd.correctCB
/-
Machine plumbing: entry `0x8000219c`; regions stk aS aD bS bD code.

-- Tom/Machine/Api/SAddAlias.lean
/-- **`s_mp_add(a, b, b)` on the machine.** -/
def StatementCB : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    PreCB m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.SAdd.entryL ra s0 sp pa pb pb) m v.keepR outp)
      (RetCB m v outp sp pa adp pb bdp a b ra s0)

/-- What `s_mp_add(a, b, b)` needs. -/
structure PreCB (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop
    extends Base m 64 sp pa adp pb bdp a b ra where
  sa : a.Shape
  sb : b.Shape
  bsign : b.sign = Layout.mpZpos ∨ b.sign = Layout.mpNeg
  room : max a.used b.used + 1 ≤ b.alloc
  lay : Sound (lay sp pa adp pb bdp a b) isWB

def RetCB (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ b' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostCB m sp pa adp pb bdp a b b' M

/-- What `s_mp_add(a, b, b)` leaves: `b'` at `b`. -/
structure PostCB (m : Mem) (sp pa adp pb bdp : Nat) (a b b' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pb bdp b'
  sadd : SAddPost a b b b'
  frame : Frm (lay sp pa adp pb bdp a b) wsB m M

Also used (printed above): `Tom.Machine.Api.BinA.Base` (`mp_add`), `Tom.Machine.Api.BinA.isWB` (`mp_add`), `Tom.SAddPost` (`mp_add`), `Tom.Machine.Api.BinA.wsB` (`mp_add`), `Tom.addDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.addCarry` (`mp_add`)
-/

/-! ## `s_mp_balance_mul`

`mp_err s_mp_balance_mul(const mp_int *a, const mp_int *b, mp_int *c);`

Coverage: contract (Res.ih := Fn.MulGroupB.mulBelow _; the left-over slice over ValidU operands); c = a: Tom.Machine.Fn.BalMulAG5.correct.
-/

/-- `s_mp_balance_mul(a, b, c)`, `c` distinct: the contract -/
theorem Specs.s_mp_balance_mul_correct : Tom.Machine.Api.BalMul.Statement :=
  Tom.Machine.Fn.BalMulG5.correct
/-
Machine plumbing: entry `0x8000234c`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator and the cut-offs); stack reservation `F = Fm (μ p.a p.b)`; regions stk aS aD bS bD cS cD kc tc code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/BalMul.lean
/-- **`s_mp_balance_mul(a, b, c)` on the machine** (not proved). -/
def Statement : Prop := ∀ p : P, Spec p

def Spec (p : P) : Prop := MulAlg.SpecR entry Res p

-- Tom/Machine/Api/MulAlg.lean
/-- The contract of an algorithm at `entry` with residue `Rs`, at one `p`. -/
def SpecR (entry : BitVec 64) (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (lay p) MpMul.isW → Bundle (lay p) (MpMul.kind p) m → AHeap m (MpMul.hin p) →
    (∀ r, Off (lay p r) (MpMul.hin p)) →
    Triple (At entry ((1, ra) :: MpMul.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (MpMul.rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) MpMul.ws .cD (MpMul.out p x) (MpMul.site' p x) (MpMul.hin p) (MpMul.hout p x) m M)

-- Tom/Machine/Api/BalMul.lean
structure Res (p : P) : Prop extends MulAlg.Base p where
  /-- `mp_mul`'s dispatch (`18dc`, `18f4`, `197c`). -/
  bmin : 80 ≤ min p.a.used p.b.used
  bhalf : 80 ≤ max p.a.used p.b.used / 2
  bratio : 2 * min p.a.used p.b.used ≤ max p.a.used p.b.used
  ih : MulRec.MulBelow (μ p.a p.b)

-- Tom/Machine/Api/MulAlg.lean
def Q (p : P) : X → Prop
  | (ok, _, c') => Out p ok c'

/-- The residue every algorithm shares (`Api.MpMul.Res` at the depth `F`). -/
structure Base (p : P) : Prop where
  stk : StkRes p.sp (F p)
  va : p.a.ValidU
  vb : p.b.ValidU
  sc : p.c.Shape
  csign : p.c.sign = Layout.mpZpos ∨ p.c.sign = Layout.mpNeg
  uab : μ p.a p.b < 2 ^ 30
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  cpos : 0 < p.c.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24

/-- What `c` holds after an algorithm. -/
structure Out (p : P) (ok : Bool) (c' : MpInt) : Prop where
  shape : c'.Shape
  pos : 0 < c'.alloc
  /-- `MP_OKAY`: `c'` valid with magnitude `|a| |b|`. -/
  valid : ok = true → c'.Valid
  mag : ok = true → c'.mag = p.a.mag * p.b.mag

Also used (printed above): `Tom.Machine.Api.MpMul.P` (`mp_mul`), `Tom.Machine.Api.MulRec.MulBelow` (`mp_mul`), `Tom.Machine.Api.MpMul.μ` (`mp_mul`), `Tom.Machine.Api.MpMul.X` (`mp_mul`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MulRec.MulAt` (`mp_mul`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.MpMul.SpecR` (`mp_mul`), `Tom.Machine.Api.MpMul.ResU` (`mp_mul`), `Tom.Machine.Api.MpMulA.P` (`mp_mul`), `Tom.Machine.Api.MpMulA.Spec` (`mp_mul`), `Tom.Machine.Api.MpMul.Q` (`mp_mul`), `Tom.Machine.Api.MpMulA.SpecR` (`mp_mul`), `Tom.Machine.Api.MpMulA.Res` (`mp_mul`), `Tom.Machine.Api.MpMul.Out` (`mp_mul`), `Tom.Machine.Api.MpMulA.Q` (`mp_mul`), `Tom.MulPost` (`mp_mul`), `Tom.Machine.Api.MpMulA.Out` (`mp_mul`)
-/

/-- The algorithms of `mp_mul(a, b, a)`: their in-place contracts -/
theorem Specs.s_mp_balance_mul_correct_inplace : Tom.Machine.Api.BalMulA.Statement :=
  Tom.Machine.Fn.BalMulAG5.correct
/-
Machine plumbing: entry `0x800018a8`; the arguments: `a0 = a2 = a`, `a1 = b`; stack reservation `F = Fm (μ p.a p.b)`; regions stk aS aD bS bD kc tc code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MulAlgA.lean
/-- **`s_mp_balance_mul(a, b, a)` on the machine** (not proved). -/
def Statement : Prop := ∀ p : P, Spec p

def Spec (p : P) : Prop := MulAlgA.SpecR BalMul.entry Res p

/-- The contract of an in-place algorithm at `entry` with residue `Rs`, at one `p`. -/
def SpecR (entry : BitVec 64) (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (lay p) MpMulA.isW → Bundle (lay p) (MpMulA.kind p) m → AHeap m (MpMulA.hin p) →
    (∀ r, Off (lay p r) (MpMulA.hin p)) →
    Triple (At entry ((1, ra) :: MpMulA.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (MpMulA.rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) MpMulA.ws .aD (MpMulA.out p x) (MpMulA.site' p x) (MpMulA.hin p) (MpMulA.hout p x) m M)

/-- What `s_mp_balance_mul(a, b, a)` needs (`BalMul.Res` in place). -/
structure Res (p : P) : Prop extends MulAlgA.Base p where
  /-- `mp_mul`'s dispatch (`18dc`, `18f4`, `197c`). -/
  bmin : 80 ≤ min p.a.used p.b.used
  bhalf : 80 ≤ max p.a.used p.b.used / 2
  bratio : 2 * min p.a.used p.b.used ≤ max p.a.used p.b.used
  /-- The recursive `mp_mul`s below the measure. -/
  ih : MulRec.MulBelow (μ p.a p.b)

def Q (p : P) : X → Prop
  | (ok, _, a') => Out p ok a'

/-- The residue every in-place algorithm shares (`Api.MpMulA.Res` at the depth `F`). -/
structure Base (p : P) : Prop where
  stk : StkRes p.sp (F p)
  va : p.a.Valid
  vb : p.b.Valid
  uab : μ p.a p.b < 2 ^ 30
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

/-- What `a` holds after an algorithm (`MulAlg.Out` over the operands' old values). -/
structure Out (p : P) (ok : Bool) (a' : MpInt) : Prop where
  shape : a'.Shape
  pos : 0 < a'.alloc
  /-- `MP_OKAY`: `a'` valid with magnitude `|a| |b|` (of the old `a`). -/
  valid : ok = true → a'.Valid
  mag : ok = true → a'.mag = p.a.mag * p.b.mag

Also used (printed above): `Tom.Machine.Api.MpMulA.P` (`mp_mul`), `Tom.Machine.Api.MulRec.MulBelow` (`mp_mul`), `Tom.Machine.Api.MpMul.μ` (`mp_mul`), `Tom.Machine.Api.MpMul.X` (`mp_mul`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MulRec.MulAt` (`mp_mul`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.MpMul.P` (`mp_mul`), `Tom.Machine.Api.MpMul.SpecR` (`mp_mul`), `Tom.Machine.Api.MpMul.ResU` (`mp_mul`), `Tom.Machine.Api.MpMulA.Spec` (`mp_mul`), `Tom.Machine.Api.MpMul.Q` (`mp_mul`), `Tom.Machine.Api.MpMulA.SpecR` (`mp_mul`), `Tom.Machine.Api.MpMulA.Res` (`mp_mul`), `Tom.Machine.Api.MpMul.Out` (`mp_mul`), `Tom.Machine.Api.MpMulA.Q` (`mp_mul`), `Tom.MulPost` (`mp_mul`), `Tom.Machine.Api.MpMulA.Out` (`mp_mul`)
-/

/-! ## `s_mp_div_3`

`mp_err s_mp_div_3(const mp_int *a, mp_int *c, mp_digit *d);`

Coverage: contract (c != NULL).
-/

/-- `s_mp_div_3(a, c, d)`: the allocating contract (over `Kit/MeetHeap.lean`) -/
theorem Specs.s_mp_div_3_correct : Tom.Machine.Api.Div3.Statement :=
  Tom.Machine.Fn.Div3.correct
/-
Machine plumbing: stack reservation `F = 80 + MpInit.Fsize`; regions stk aS aD cS cD dS code; written [.stk, .cS, .cD, .dS].

-- Tom/Machine/Api/Div3.lean
/-- **`s_mp_div_3(a, c, d)` on the machine**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At Fn.Div3.entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

structure P where  (sp pa adp pc cdp : Nat); (hasD : Bool); (pd : Nat); (a c : MpInt); (H : List (Nat × Nat))

structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  apos : 0 < p.a.alloc
  cpos : 0 < p.c.alloc
  aoff : OffHeap p.pa 24
  coff : OffHeap p.pc 24
  dnull : p.hasD = false → p.pd = 0
  dslot : p.hasD = true → p.pd ≠ 0 ∧ p.pd % 4 = 0 ∧ OffHeap p.pd 4

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (_, c') => Div3Quot p.a c'

-- Tom/Spec/DivD.lean
/-- `s_mp_div_3(a, c, d)`: the long division by `3`. -/
def Div3Quot (a c' : MpInt) : Prop := DivLongQuot a 3 c'
theorem Div3Quot.spec {a c' : MpInt} (ha : a.Valid) (h : Div3Quot a c') :
    c'.Valid ∧ c'.mag = a.mag / 3 ∧ c'.val = a.val.tdiv 3 := …  -- proved in Tom/Spec/DivD.lean

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.DivLongQuot` (`mp_div_d`), `Tom.ClampedTo` (`mp_div`), `Tom.divDDigit` (`mp_div_d`), `Tom.clampUsed` (`mp_add`), `Tom.ldQ` (`mp_div_d`), `Tom.ldR` (`mp_div_d`), `Tom.ldV` (`mp_div_d`)
-/

/-- `s_mp_div_3(a, a, d)` in place: the allocating contract -/
theorem Specs.s_mp_div_3_correct_inplace : Tom.Machine.Api.Div3I.Statement :=
  Tom.Machine.Fn.Div3IG5.correct
/-
Machine plumbing: stack reservation `F = 656`; regions stk aS aD dS code; written [.stk, .aS, .aD, .dS].

-- Tom/Machine/Api/Div3I.lean
/-- **`s_mp_div_3(a, a, d)` on the machine**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At Fn.Div3.entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

structure P where  (sp pa adp pd : Nat); (a : MpInt); (H : List (Nat × Nat)); (dd : MpInt)

/-- What `s_mp_div_3(a, a, d)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 656
  va : p.a.Valid
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  /-- `a != 0`: the `a->used == 0` branch (`6788`) is not covered; `mp_div_d` tail-calls
  `s_mp_div_3` only for `a != 0` (its quick out takes `a == 0`). -/
  u_pos : 0 < p.a.used
  /-- `d != NULL`: the `d == NULL` branches are not covered (`mp_div_d` passes its own
  non-`NULL` `d`; `s_mp_toom_mul`'s `s_mp_div_3(&a, &a, NULL)` is not this contract). -/
  d_nn : p.pd ≠ 0
  d_al : p.pd % 4 = 0
  doff : OffHeap p.pd 4
  /-- The slot is one word. -/
  dd1 : p.dd.alloc = 1

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (_, a') => Div3Quot p.a a'

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Div3Quot` (`s_mp_div_3`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.DivLongQuot` (`mp_div_d`), `Tom.ClampedTo` (`mp_div`), `Tom.divDDigit` (`mp_div_d`), `Tom.clampUsed` (`mp_add`), `Tom.ldQ` (`mp_div_d`), `Tom.ldR` (`mp_div_d`), `Tom.ldV` (`mp_div_d`)
-/

/-- `s_mp_div_3(a, a, NULL)` in place: the allocating contract -/
theorem Specs.s_mp_div_3_correct_inplace_null : Tom.Machine.Api.Div3N.Statement :=
  Tom.Machine.Fn.Div3NG5.correct
/-
Machine plumbing: the arguments: `a0 = a1 = a`, `a2 = NULL`; stack reservation `F = 656`; regions stk aS aD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/Div3N.lean
/-- **`s_mp_div_3(a, a, NULL)` on the machine**, as an allocating contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At Fn.Div3.entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

structure P where  (sp pa adp : Nat); (a : MpInt); (H : List (Nat × Nat))

/-- What `s_mp_div_3(a, a, NULL)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 656
  va : p.a.Valid
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  /-- `a != 0`: the `a->used == 0` branch (`6788`) is not covered (as `Api/Div3I.lean`). -/
  u_pos : 0 < p.a.used

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (_, a') => Div3Quot p.a a'

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Div3Quot` (`s_mp_div_3`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.DivLongQuot` (`mp_div_d`), `Tom.ClampedTo` (`mp_div`), `Tom.divDDigit` (`mp_div_d`), `Tom.clampUsed` (`mp_add`), `Tom.ldQ` (`mp_div_d`), `Tom.ldR` (`mp_div_d`), `Tom.ldV` (`mp_div_d`)
-/

/-! ## `s_mp_exptmod`

`mp_err s_mp_exptmod(const mp_int *G, const mp_int *X, const mp_int *P, mp_int *Y, int redmode);`

Coverage: contract (any modulus: P > 0, redmode < 2, MP_DIGIT_BIT (2 P->used + 1) an int; every multiplier at any size; stack Fs = 10576 + 8 (G->used + 3 P->used)).
-/

/-- `s_mp_exptmod_fast(G, X, P, Y, redmode)` and `s_mp_exptmod(G, X, P, Y, redmode)`: the allocating -/
theorem Specs.s_mp_exptmod_correct : Tom.Machine.Api.SMpExptmod.Statement :=
  Tom.Machine.Fn.SExptG5.correct
/-
Machine plumbing: entry `0x8000261c`; the arguments: `a0 = G`, `a1 = X`, `a2 = P`, `a3 = Y`, `a4 = redmode`; stack reservation `F = Fs p.g p.n`; regions stk gS gD xS xD nS nD yS yD ks ts kc tc code; written [.stk, .yS, .yD].

-- Tom/Machine/Api/Exptmod.lean
/-- **`s_mp_exptmod(G, X, P, Y, redmode)` on the machine** (statement only). -/
def Statement : Prop := Spec entry F Res Q

/-- A run from `entry` with stack depth `F p`, residue `Res` and outcome `Q`. -/
def Spec (entry : BitVec 64) (F : P → Nat) (Res : P → Prop) (Q : P → Out → Prop) : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay (F p) p) isW → Bundle (lay (F p) p) (kind p) m → AHeap m (hin p) →
    (∀ r, Off (lay (F p) p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay (F p) p) ws .yD (out p x) (site' (F p) p x) (hin p) (hout p x) m M)

structure Res (p : P) : Prop extends Base (F p) p where
  arith : Arith p.n p.mode

/-- `MP_MEM` (`Y` as it was), `MP_VAL` for `P = 0` in Barrett mode (`SMpExptmodStep.Out.zero`), or
`MP_OKAY` with `SExptmodPost` (`P > 0`). -/
def Q (p : P) : Out → Prop
  | .err r => r = Layout.mpMem ∨ SMpExptmodStep.Out p.g p.x p.n p.y p.y p.mode r
  | .ok _ y' => SMpExptmodStep.Out p.g p.x p.n p.y y' p.mode Layout.mpOkay

/-- The arithmetic residue of the Barrett / `2^p - d` worker. No room on the modulus and no size bound: the setups and the
reductions grow their destinations (`Api/MpReduceSetupG.lean`, `Api/Reduce2kSetupLG.lean`,
`Api/MpReduce2kLG.lean`, `mp_copy(&M[1], &M[2^(w-1)])` by `Api/MpCopyG.lean`; `mp_reduce` grows `x`),
and the multipliers run at any size (`mp_mul` by the closed group, `Std.mpMulG`/`mpMulAG`; `mp_sqr(&x, &x)`
by `Api/MpSqrAG.lean`; `mp_reduce`'s `s_mp_mul_digs`/`s_mp_mul_high_digs` on both paths,
`Api/SMpMulDigsAG.lean`). What is left is what the C needs: the modulus positive (`mp_reduce_setup`'s
`mp_div(mu, P, mu, NULL)` returns `MP_VAL` for `P = 0`, and `mp_reduce_2k_l` would not end), `redmode` one
of the worker's two modes, and the C's `int` arithmetic on a product of two residues (`x->used ≤ 2 P->used`):
`mp_mod_2d`'s and `mp_div_2d`'s `x->used * MP_DIGIT_BIT`, `mp_reduce`'s `MP_DIGIT_BIT * (um + 1)`. -/
structure Arith (n : MpInt) (mode : Nat) : Prop where
  pos : 0 < n.mag
  bits : Layout.digitBits * (2 * n.used + 1) < 2 ^ 31
  mode : mode < 2

-- Tom/Spec/SMpExptmodStep.lean
/-- What `s_mp_exptmod(G, X, P, Y, redmode)` returns (allocations not failing), as `mp_exptmod`
consumes it: for `redmode = 0` and `P = 0`, `MP_VAL` from `mp_reduce_setup`, `Y` untouched; for
`P > 0`, `MP_OKAY` and the Post. -/
structure Out (G X P Y Y' : MpInt) (redmode : Nat) (ret : Int) : Prop where
  zero : redmode = 0 → P.mag = 0 → ret = Layout.mpVal ∧ Y' = Y
  pos : 0 < P.mag → ret = Layout.mpOkay ∧ SExptmodPost G X P Y'

Also used (printed above): `Tom.Machine.Api.Exptmod.P` (`mp_exptmod`), `Tom.Machine.Api.Exptmod.Out` (`mp_exptmod`), `Tom.Machine.Api.Exptmod.Base` (`mp_exptmod`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`)
-/

/-! ## `s_mp_exptmod_fast`

`mp_err s_mp_exptmod_fast(const mp_int *G, const mp_int *X, const mp_int *P, mp_int *Y, int redmode);`

Coverage: contract (all three redmodes on the comba paths: Api.SMpExptmodFast.Res, its D5 rooms; DR moduli with a nonzero low digit).
-/

/-- `s_mp_exptmod_fast(G, X, P, Y, redmode)` and `s_mp_exptmod(G, X, P, Y, redmode)`: the allocating -/
theorem Specs.s_mp_exptmod_fast_correct : Tom.Machine.Api.SMpExptmodFast.Statement :=
  Tom.Machine.Fn.SExptFastG5.correct
/-
Machine plumbing: entry `0x80002c5c`; the arguments: `a0 = G`, `a1 = X`, `a2 = P`, `a3 = Y`, `a4 = redmode`; stack reservation `F = Ff p.g p.n`; regions stk gS gD xS xD nS nD yS yD ks ts kc tc code; written [.stk, .yS, .yD].

-- Tom/Machine/Api/Exptmod.lean
/-- **`s_mp_exptmod_fast(G, X, P, Y, redmode)` on the machine.** -/
def Statement : Prop := Spec entry F Res Q

structure Res (p : P) : Prop extends Base (F p) p where
  arith : Arith p.n p.mode

/-- `MP_MEM` (`Y` as it was), or `MP_OKAY` with `SExptmodFastPost`. -/
def Q (p : P) : Out → Prop
  | .err r => r = Layout.mpMem
  | .ok _ y' => Exptmod.SExptmodFastPost p.g p.x p.n y' p.mode

/-- The arithmetic residue (every callee grows its destination, `Api/ReduxGF.lean`,
`Api/Std_cap.lean`; `mp_montgomery_calc_normalization(&res, P)` grows `res`,
`Api/MontNormG.lean`, so no room on the modulus and no size bound): a modulus `> 1`, the C's `int`
arithmetic on a product of two residues (`mp_reduce_2k`'s `mp_div_2d`, `x->used * MP_DIGIT_BIT`), and
per mode what the setup needs. -/
structure Arith (n : MpInt) (mode : Nat) : Prop where
  gt1 : 1 < n.mag
  bits : Layout.digitBits * (2 * n.used + 1) < 2 ^ 31
  /-- Montgomery: `mp_montgomery_setup` needs an odd modulus (else `MP_VAL`; `mp_exptmod` calls
  this mode only for odd `P`). -/
  mont : mode = 0 → n.mag % 2 = 1
  /-- Diminished radix: a DR modulus (`mp_dr_reduce`'s `|x| mod P`), its setup digit `2^28 - P->dp[0]`
  a digit. -/
  dr : mode = 1 → IsDrModulus n ∧ 0 < n.digit 0
  /-- `2^p - d`: the setup's digit is the true `d`. -/
  r2k : 2 ≤ mode → Exact2k n

Also used (printed above): `Tom.Machine.Api.Exptmod.Spec` (`s_mp_exptmod`), `Tom.Machine.Api.Exptmod.P` (`mp_exptmod`), `Tom.Machine.Api.Exptmod.Out` (`mp_exptmod`), `Tom.Machine.Api.Exptmod.Base` (`mp_exptmod`), `Tom.Exptmod.SExptmodFastPost` (`mp_exptmod`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.IsDrModulus` (`mp_dr_is_modulus`), `Tom.Machine.Api.SMpExptmodFast.Exact2k` (`mp_exptmod`), `Tom.Exptmod.redMont` (`mp_exptmod`), `Tom.Exptmod.winRes` (`mp_exptmod`), `Tom.Exptmod.redDrC` (`mp_exptmod`), `Tom.Exptmod.red2kC` (`mp_exptmod`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Mont.nbits` (`mp_exptmod`), `Tom.Exptmod.wsize` (`mp_exptmod`)
-/

/-! ## `s_mp_invmod_fast`

`mp_err s_mp_invmod_fast(const mp_int *a, const mp_int *b, mp_int *c);`

Coverage: contract (b of any size: Api.InvmodFastG; the D5 statement Api.InvmodFastG.Statement.d5).
-/

/-- `mp_invmod`, `s_mp_invmod_fast`, `s_mp_invmod_slow`: the allocating contracts -/
theorem Specs.s_mp_invmod_fast_correct : Tom.Machine.Api.InvmodFastG.Statement :=
  Tom.Machine.Fn.InvmodFastG5.correct
/-
Machine plumbing: the arguments: `a0 = a`, `a1 = b`, `a2 = c`; stack reservation `F = 1232`; regions stk aS aD bS bD cS cD code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/Invmod.lean
/-- **`s_mp_invmod_fast(a, b, c)` on the machine, `b` of any size.** -/
def Statement : Prop := Spec InvmodFast.entry Res InvmodFast.Q

/-- `s_mp_invmod_fast(a, b, c)` growing its temporaries: `BaseG`, `b` positive. -/
structure Res (p : P) : Prop extends BaseG p where
  bz : p.b.sign = Layout.mpZpos

/-- `MP_MEM`, or what `InvmodFastPost` says. -/
def Q (p : P) : Out → Prop
  | .err r => r = Layout.mpMem ∨ InvmodFastPost p.a p.b p.c p.c r
  | .ok _ c' => InvmodFastPost p.a p.b p.c c' Layout.mpOkay

Also used (printed above): `Tom.Machine.Api.Invmod.Spec` (`mp_invmod`), `Tom.Machine.Api.Invmod.P` (`mp_invmod`), `Tom.Machine.Api.Invmod.Out` (`mp_invmod`), `Tom.Machine.Api.Invmod.BaseG` (`mp_invmod`), `Tom.InvmodFastPost` (`mp_exptmod`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Gcd.fastRes` (`mp_exptmod`), `Tom.invmodRem` (`mp_exptmod`), `Tom.InvmodErr` (`mp_exptmod`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Gcd.fastTop` (`mp_exptmod`), `Tom.Gcd.fastInit` (`mp_exptmod`), `Tom.Gcd.norm` (`mp_exptmod`), `Tom.Gcd.FastSt` (`mp_exptmod`), `Tom.Gcd.fastPass` (`mp_exptmod`), `Tom.Gcd.subDown` (`mp_exptmod`), `Tom.Gcd.addUp` (`mp_exptmod`), `Tom.Gcd.fastSub` (`mp_exptmod`), `Tom.Gcd.fastLoopV` (`mp_exptmod`), `Tom.Gcd.fastLoopU` (`mp_exptmod`), `Tom.Gcd.fastHalfV` (`mp_exptmod`), `Tom.Gcd.fastHalfU` (`mp_exptmod`)
-/

/-! ## `s_mp_invmod_slow`

`mp_err s_mp_invmod_slow(const mp_int *a, const mp_int *b, mp_int *c);`

Coverage: contract (b of any size: Api.InvmodSlowG; b even: mp_invmod's call; odd b with a = 0 mod b loops).
-/

/-- `mp_invmod`, `s_mp_invmod_fast`, `s_mp_invmod_slow`: the allocating contracts -/
theorem Specs.s_mp_invmod_slow_correct : Tom.Machine.Api.InvmodSlowG.Statement :=
  Tom.Machine.Fn.InvmodSlowG5.correct
/-
Machine plumbing: the arguments: `a0 = a`, `a1 = b`, `a2 = c`; stack reservation `F = 1232`; regions stk aS aD bS bD cS cD code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/Invmod.lean
/-- **`s_mp_invmod_slow(a, b, c)` on the machine, `b` of any size.** -/
def Statement : Prop := Spec InvmodSlow.entry Res InvmodSlow.Q

/-- `s_mp_invmod_slow(a, b, c)` growing its temporaries: `BaseG`, `b` positive and even. -/
structure Res (p : P) : Prop extends BaseG p where
  bz : p.b.sign = Layout.mpZpos
  even : p.b.mag % 2 = 0

/-- `MP_MEM`, or what `InvmodSlowPost` says. -/
def Q (p : P) : Out → Prop
  | .err r => r = Layout.mpMem ∨ InvmodSlowPost p.a p.b p.c p.c r
  | .ok _ c' => InvmodSlowPost p.a p.b p.c c' Layout.mpOkay

Also used (printed above): `Tom.Machine.Api.Invmod.Spec` (`mp_invmod`), `Tom.Machine.Api.Invmod.P` (`mp_invmod`), `Tom.Machine.Api.Invmod.Out` (`mp_invmod`), `Tom.Machine.Api.Invmod.BaseG` (`mp_invmod`), `Tom.InvmodSlowPost` (`mp_exptmod`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Gcd.slowRes` (`mp_exptmod`), `Tom.invmodRem` (`mp_exptmod`), `Tom.InvmodErr` (`mp_exptmod`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Gcd.slowTop` (`mp_exptmod`), `Tom.Gcd.slowInit` (`mp_exptmod`), `Tom.Gcd.norm` (`mp_exptmod`), `Tom.Gcd.SlowSt` (`mp_exptmod`), `Tom.Gcd.slowPass` (`mp_exptmod`), `Tom.Gcd.subDown` (`mp_exptmod`), `Tom.Gcd.addUp` (`mp_exptmod`), `Tom.Gcd.slowSub` (`mp_exptmod`), `Tom.Gcd.slowLoopV` (`mp_exptmod`), `Tom.Gcd.slowLoopU` (`mp_exptmod`), `Tom.Gcd.slowHalfV` (`mp_exptmod`), `Tom.Gcd.slowHalfU` (`mp_exptmod`)
-/

/-! ## `s_mp_karatsuba_mul`

`mp_err s_mp_karatsuba_mul(const mp_int *a, const mp_int *b, mp_int *c);`

Coverage: contract (Res.ih := Fn.MulGroupB.mulBelow _); c = a: Tom.Machine.Fn.KMulAG5.correct.
-/

/-- `s_mp_karatsuba_mul(a, b, c)`, `c` distinct: the contract -/
theorem Specs.s_mp_karatsuba_mul_correct : Tom.Machine.Api.KMul.Statement :=
  Tom.Machine.Fn.KMulG5.correct
/-
Machine plumbing: entry `0x80003a98`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator and the cut-offs); stack reservation `F = Fm (μ p.a p.b)`; regions stk aS aD bS bD cS cD kc tc code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/KMul.lean
/-- **`s_mp_karatsuba_mul(a, b, c)` on the machine.** -/
def Statement : Prop := ∀ p : P, Spec p

def Spec (p : P) : Prop := MulAlg.SpecR entry Res p

/-- What `s_mp_karatsuba_mul(a, b, c)` needs. -/
structure Res (p : P) : Prop extends MulAlg.Base p where
  /-- `mp_mul`'s dispatch: `min ≥ KARATSUBA_MUL_CUTOFF = 80`. -/
  kmin : 80 ≤ min p.a.used p.b.used
  /-- `mp_mul`'s dispatch: not the balanced case (`s_mp_balance_mul` is tested first). -/
  kbal : max p.a.used p.b.used < 2 * min p.a.used p.b.used
  /-- The recursive `mp_mul`s below the measure. -/
  ih : MulRec.MulBelow (μ p.a p.b)

Also used (printed above): `Tom.Machine.Api.MpMul.P` (`mp_mul`), `Tom.Machine.Api.MulAlg.SpecR` (`s_mp_balance_mul`), `Tom.Machine.Api.MulAlg.Q` (`s_mp_balance_mul`), `Tom.Machine.Api.MulAlg.Base` (`s_mp_balance_mul`), `Tom.Machine.Api.MulRec.MulBelow` (`mp_mul`), `Tom.Machine.Api.MpMul.μ` (`mp_mul`), `Tom.Machine.Api.MpMul.X` (`mp_mul`), `Tom.Machine.Api.MulAlg.Out` (`s_mp_balance_mul`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MulRec.MulAt` (`mp_mul`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.MpMul.SpecR` (`mp_mul`), `Tom.Machine.Api.MpMul.ResU` (`mp_mul`), `Tom.Machine.Api.MpMulA.P` (`mp_mul`), `Tom.Machine.Api.MpMulA.Spec` (`mp_mul`), `Tom.Machine.Api.MpMul.Q` (`mp_mul`), `Tom.Machine.Api.MpMulA.SpecR` (`mp_mul`), `Tom.Machine.Api.MpMulA.Res` (`mp_mul`), `Tom.Machine.Api.MpMul.Out` (`mp_mul`), `Tom.Machine.Api.MpMulA.Q` (`mp_mul`), `Tom.MulPost` (`mp_mul`), `Tom.Machine.Api.MpMulA.Out` (`mp_mul`)
-/

/-- The algorithms of `mp_mul(a, b, a)`: their in-place contracts -/
theorem Specs.s_mp_karatsuba_mul_correct_inplace : Tom.Machine.Api.KMulA.Statement :=
  Tom.Machine.Fn.KMulAG5.correct
/-
Machine plumbing: entry `0x800018a8`; the arguments: `a0 = a2 = a`, `a1 = b`; stack reservation `F = Fm (μ p.a p.b)`; regions stk aS aD bS bD kc tc code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MulAlgA.lean
/-- **`s_mp_karatsuba_mul(a, b, a)` on the machine** (not proved). -/
def Statement : Prop := ∀ p : P, Spec p

def Spec (p : P) : Prop := MulAlgA.SpecR KMul.entry Res p

/-- What `s_mp_karatsuba_mul(a, b, a)` needs (`KMul.Res` in place). -/
structure Res (p : P) : Prop extends MulAlgA.Base p where
  /-- `mp_mul`'s dispatch: `min ≥ KARATSUBA_MUL_CUTOFF = 80`. -/
  kmin : 80 ≤ min p.a.used p.b.used
  /-- `mp_mul`'s dispatch: not the balanced case. -/
  kbal : max p.a.used p.b.used < 2 * min p.a.used p.b.used
  /-- The recursive `mp_mul`s below the measure. -/
  ih : MulRec.MulBelow (μ p.a p.b)

Also used (printed above): `Tom.Machine.Api.MpMulA.P` (`mp_mul`), `Tom.Machine.Api.MulAlgA.SpecR` (`s_mp_balance_mul`), `Tom.Machine.Api.MulAlgA.Q` (`s_mp_balance_mul`), `Tom.Machine.Api.MulAlgA.Base` (`s_mp_balance_mul`), `Tom.Machine.Api.MulRec.MulBelow` (`mp_mul`), `Tom.Machine.Api.MpMul.μ` (`mp_mul`), `Tom.Machine.Api.MpMul.X` (`mp_mul`), `Tom.Machine.Api.MulAlgA.Out` (`s_mp_balance_mul`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MulRec.MulAt` (`mp_mul`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.MpMul.P` (`mp_mul`), `Tom.Machine.Api.MpMul.SpecR` (`mp_mul`), `Tom.Machine.Api.MpMul.ResU` (`mp_mul`), `Tom.Machine.Api.MpMulA.Spec` (`mp_mul`), `Tom.Machine.Api.MpMul.Q` (`mp_mul`), `Tom.Machine.Api.MpMulA.SpecR` (`mp_mul`), `Tom.Machine.Api.MpMulA.Res` (`mp_mul`), `Tom.Machine.Api.MpMul.Out` (`mp_mul`), `Tom.Machine.Api.MpMulA.Q` (`mp_mul`), `Tom.MulPost` (`mp_mul`), `Tom.Machine.Api.MpMulA.Out` (`mp_mul`)
-/

/-! ## `s_mp_karatsuba_sqr`

`mp_err s_mp_karatsuba_sqr(const mp_int *a, mp_int *b);`

Coverage: contract (Res.ih := Fn.MulGroupB.sqrBelow _).
-/

/-- `s_mp_karatsuba_sqr(a, b)` (`b` distinct, and `b = a`): the contracts -/
theorem Specs.s_mp_karatsuba_sqr_correct : Tom.Machine.Api.KSqr.Statement :=
  Tom.Machine.Fn.KSqrG5.correct Tom.Machine.Fn.GrowH.mpAddH Tom.Machine.Fn.GrowH.mpLshdH
/-
Machine plumbing: entry `0x80006794`.

-- Tom/Machine/Api/KSqr.lean
/-- **`s_mp_karatsuba_sqr(a, b)` on the machine.** -/
def Statement : Prop := ∀ p : MpSqr.P, Spec p

def Spec (p : MpSqr.P) : Prop := SqrAlg.SpecR entry Res p

-- Tom/Machine/Api/SqrAlg.lean
/-- The contract of an algorithm at `entry` with residue `Rs`, at one `p`. -/
def SpecR (entry : BitVec 64) (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (lay p) MpSqr.isW → Bundle (lay p) (MpSqr.kind p) m → AHeap m (MpSqr.hin p) →
    (∀ r, Off (lay p r) (MpSqr.hin p)) →
    Triple (At entry ((1, ra) :: MpSqr.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (MpSqr.rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) MpSqr.ws .bD (MpSqr.out p x) (MpSqr.site' p x) (MpSqr.hin p) (MpSqr.hout p x) m M)

-- Tom/Machine/Api/KSqr.lean
/-- What `s_mp_karatsuba_sqr(a, b)` needs. -/
structure Res (p : MpSqr.P) : Prop extends SqrAlg.Base p where
  /-- `mp_sqr`'s dispatch: `a->used ≥ KARATSUBA_SQR_CUTOFF = 120`. -/
  kmin : 120 ≤ p.a.used
  /-- `mp_sqr`'s dispatch: `a->used < TOOM_SQR_CUTOFF = 400` (toom is tested first). -/
  kmax : p.a.used < 400
  /-- The recursive `mp_sqr`s below the measure. -/
  ih : SqrRec.SqrBelow p.a.used

-- Tom/Machine/Api/SqrAlg.lean
def Q (p : P) (x : X) : Prop := Out p.a p.b.alloc (MpSqr.hin p) (lay p .bD) x

/-- The residue every algorithm shares (`Api.MpSqr.Res` at the depth `F`, without the comba
path's room). -/
structure Base (p : P) : Prop where
  stk : StkRes p.sp (F p)
  va : p.a.Valid
  sb : p.b.Shape
  bsign : p.b.sign = Layout.mpZpos ∨ p.b.sign = Layout.mpNeg
  au : p.a.used < 2 ^ 29
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

/-- What the destination holds after an algorithm (`x = (ok, q, b')`), its digits re-placed
from `I` (the old digit array, `n0` digits) for the blocks `H`: `DOut` (Kit/DOut.lean) at `|a|²` (on
`MP_OKAY` valid with magnitude `|a|²`; where `b'`'s digits are, `HPost.place` restated for `mp_sqr`,
which passes the site on; the digits only grow). -/
abbrev Out (a : MpInt) (n0 : Nat) (H : List (Nat × Nat)) (I : Iv) (x : MpSqr.X) : Prop :=
  DOut (a.mag * a.mag) n0 I H x

Also used (printed above): `Tom.Machine.Api.MpSqr.P` (`mp_sqr`), `Tom.Machine.Api.SqrRec.SqrBelow` (`mp_sqr`), `Tom.Machine.Api.MpSqr.X` (`mp_mul_2`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.SqrRec.SqrAt` (`mp_sqr`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.MpSqr.Spec` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.P` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Spec` (`mp_sqr`), `Tom.Machine.Api.MpSqr.SpecR` (`mp_sqr`), `Tom.Machine.Api.MpSqr.Res` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.SpecR` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Res` (`mp_sqr`), `Tom.Machine.Api.MpSqr.Q` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Q` (`mp_sqr`), `Tom.Machine.Api.MpSqr.Out` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Out` (`mp_sqr`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.SqrPost` (`mp_sqr`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`)
-/

/-- `s_mp_karatsuba_sqr(a, b)` (`b` distinct, and `b = a`): the contracts -/
theorem Specs.s_mp_karatsuba_sqr_correct_inplace : Tom.Machine.Api.KSqr.StatementA :=
  Tom.Machine.Fn.KSqrAG5.correct Tom.Machine.Fn.GrowH.mpAddH Tom.Machine.Fn.GrowH.mpLshdH
/-
Machine plumbing: entry `0x80006794`.

-- Tom/Machine/Api/KSqr.lean
/-- **`s_mp_karatsuba_sqr(a, a)` on the machine.** -/
def StatementA : Prop := ∀ p : MpSqrA.P, SpecA p

def SpecA (p : MpSqrA.P) : Prop := SqrAlg.SpecRA entry ResA p

-- Tom/Machine/Api/SqrAlg.lean
def SpecRA (entry : BitVec 64) (Rs : P → Prop) (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Rs p →
    Sound (layA p) MpSqrA.isW → Bundle (layA p) (MpSqrA.kind p) m → AHeap m (MpSqrA.hin p) →
    (∀ r, Off (layA p r) (MpSqrA.hin p)) →
    Triple (At entry ((1, ra) :: MpSqrA.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (MpSqrA.rets p x ra) M v.keep outp cf ∧ QA p x ∧
        HPost (layA p) MpSqrA.ws .aD (MpSqrA.out p x) (MpSqrA.site' p x) (MpSqrA.hin p) (MpSqrA.hout p x) m M)

-- Tom/Machine/Api/KSqr.lean
/-- What `s_mp_karatsuba_sqr(a, a)` needs. -/
structure ResA (p : MpSqrA.P) : Prop extends SqrAlg.BaseA p where
  kmin : 120 ≤ p.a.used
  kmax : p.a.used < 400
  ih : SqrRec.SqrBelow p.a.used

-- Tom/Machine/Api/SqrAlg.lean
def layA (p : P) : R → Iv
  | .stk => ⟨p.sp - (2208 + 8 * p.a.used), 2208 + 8 * p.a.used⟩
  | r => MpSqrA.lay p r

def QA (p : P) (x : MpSqr.X) : Prop := Out p.a p.a.alloc (MpSqrA.hin p) (layA p .aD) x

structure BaseA (p : P) : Prop where
  stk : StkRes p.sp (FA p)
  va : p.a.Valid
  au : p.a.used < 2 ^ 29
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

def FA (p : P) : Nat := Fa p.a.used

Also used (printed above): `Tom.Machine.Api.MpSqrA.P` (`mp_sqr`), `Tom.Machine.Api.SqrRec.SqrBelow` (`mp_sqr`), `Tom.Machine.Api.MpSqr.X` (`mp_mul_2`), `Tom.Machine.Api.SqrAlg.Out` (`s_mp_karatsuba_sqr`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.SqrRec.SqrAt` (`mp_sqr`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.MpSqr.P` (`mp_sqr`), `Tom.Machine.Api.MpSqr.Spec` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Spec` (`mp_sqr`), `Tom.Machine.Api.MpSqr.SpecR` (`mp_sqr`), `Tom.Machine.Api.MpSqr.Res` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.SpecR` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Res` (`mp_sqr`), `Tom.Machine.Api.MpSqr.Q` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Q` (`mp_sqr`), `Tom.Machine.Api.MpSqr.Out` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Out` (`mp_sqr`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.SqrPost` (`mp_sqr`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`)
-/

/-! ## `s_mp_montgomery_reduce_fast`

`mp_err s_mp_montgomery_reduce_fast(mp_int *x, const mp_int *n, mp_digit rho);`
-/

/-- `s_mp_montgomery_reduce_fast(x, n, rho)` growing `x`: the allocating contract -/
theorem Specs.s_mp_montgomery_reduce_fast_correct : Tom.Machine.Api.MontRedFastG.Statement :=
  Tom.Machine.Fn.MontRedFastGG5.correct
/-
Machine plumbing: entry `0x80003d9c`; the arguments: `a0 = a`, `a1 = n`, `a2 = d` (`gp` for the allocator); stack reservation `F = 4800`; regions stk aS aD nS nD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MontRedFastG.lean
/-- **`s_mp_montgomery_reduce_fast(x, n, rho)` on the machine, growing `x`**, as an allocating
contract. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) MpReduce2k.isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: MpReduce2k.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) MpReduce2k.ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

/-- What `s_mp_montgomery_reduce_fast(x, n, rho)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  vn : p.n.Valid
  /-- `rho` from `mp_montgomery_setup(n, &rho)`: `n rho ≡ -1 (mod radix)`. -/
  rho_ok : (p.n.mag * p.d + 1) % radix = 0
  rho_lt : p.d < radix
  /-- REDC's input range: `|x| < |n| R`. -/
  x_lt : p.a.mag < p.n.mag * radix ^ p.n.used
  /-- `n->used < MP_MAXFAST` (the callers' test). -/
  nu_le : p.n.used ≤ 255
  /-- `x`'s digits are `realloc`'s block: live and nonempty. -/
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24
  noff : OffHeap p.pn 24

def Q (p : P) (x : X) : Prop :=
  ReduxG.Out p (lay p .aD) (MontRedFastGStep.RedcV p.a p.n p.d) x

abbrev X := ReduxG.X

Also used (printed above): `Tom.Machine.Api.MpReduce2k.P` (`mp_dr_reduce`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.ReduxG.Out` (`mp_dr_reduce`), `Tom.MontRedFastGStep.RedcV` (`mp_montgomery_reduce`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.ReduxG.X` (`mp_dr_reduce`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`)
-/

/-- `s_mp_montgomery_reduce_fast`: the standard contract -/
theorem Specs.s_mp_montgomery_reduce_fast_correct_room : Tom.Machine.Api.MontRedFast.Statement :=
  Tom.Machine.Fn.MontRedFast.correct
/-
Machine plumbing: entry `0x80003d9c`.

-- Tom/Machine/Api/MontRedFast.lean
/-- **`s_mp_montgomery_reduce_fast` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp px xdp pn ndp : Nat} {x n : MpInt} {rho : Nat}
    {ra s0 : BitVec 64}, Pre m sp px xdp pn ndp x n rho ra →
    Triple (At entry (entryL ra s0 sp px pn rho) m v.keepR outp) (Ret m v outp sp px xdp pn ndp x n rho ra s0)

/-- What `s_mp_montgomery_reduce_fast(x, n, rho)` needs. -/
structure Pre (m : Mem) (sp px xdp pn ndp : Nat) (x n : MpInt) (rho : Nat) (ra : BitVec 64) : Prop where
  rx : MpAt m px xdp x
  rn : MpAt m pn ndp n
  vx : x.Valid
  vn : n.Valid
  gx : MpGeom px xdp x.alloc
  gn : MpGeom pn ndp n.alloc
  rho_ok : (n.mag * rho + 1) % radix = 0
  rho_lt : rho < radix
  x_lt : x.mag < n.mag * radix ^ n.used
  nu_pos : 1 ≤ n.used
  nu_le : n.used ≤ 255
  room : n.used < x.alloc
  rs : Ram (sp - 4256) 4256
  sp_al : sp % 16 = 0
  sp_ge : 4256 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp px xdp pn ndp x n) Two.isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp px xdp pn ndp : Nat) (x n : MpInt) (rho : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ x' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp px xdp pn ndp x n rho x' M

/-- What it leaves. -/
structure Post (m : Mem) (sp px xdp pn ndp : Nat) (x n : MpInt) (rho : Nat) (x' : MpInt) (M : Mem) : Prop where
  repr : MpAt M px xdp x'
  redc : RedcPost x n rho x'
  frame : Frm (lay sp px xdp pn ndp x n) Two.ws m M

Also used (printed above): `Tom.Mont.redc` (`mp_montgomery_reduce`), `Tom.Mont.RedcPost` (`mp_montgomery_reduce`), `Tom.Mont.montOut` (`mp_montgomery_reduce`), `Tom.Mont.redcT` (`mp_montgomery_reduce`), `Tom.Mont.redcMu` (`mp_montgomery_reduce`)
-/

/-! ## `s_mp_mul_digs`

`mp_err s_mp_mul_digs(const mp_int *a, const mp_int *b, mp_int *c, int digs);`

Coverage: contract.
-/

/-- `s_mp_mul_digs(a, b, c, digs)`: the allocating contract (fresh set; over `Kit/MeetHeap.lean`) -/
theorem Specs.s_mp_mul_digs_correct : Tom.Machine.Api.SMpMulDigs.Statement :=
  Tom.Machine.Fn.SMpMulDigsG5.correct
/-
Machine plumbing: entry `0x800040fc`; the arguments: `a0 = a`, `a1 = b`, `a2 = c`, `a3 = digs` (`gp` for the allocator); stack reservation `F = 2192`; regions stk aS aD bS bD cS cD code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/SMpMulDigs.lean
def Statement : Prop := Standard.Statement Res Q (site .cD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp pc cdp digs : Nat); (a b c : MpInt); (H : List (Nat × Nat))

/-- What `s_mp_mul_digs(a, b, c, digs)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  sa : p.a.ShapeU
  sb : p.b.ShapeU
  /-- `s_mp_mul_digs_fast`'s `Pre.sc`; on the slow path `c`'s value is discarded. -/
  sc : p.c.Shape
  /-- The fast path keeps `c`'s sign for a nonzero result: a sign, for `c'` valid. -/
  csign : p.c.sign = Layout.mpZpos ∨ p.c.sign = Layout.mpNeg
  /-- The C's `int digs`, nonnegative (`bltz a3` at `4104`; the rows take `a3` below `2^31`). -/
  dg_lt : p.digs < 2 ^ 31
  /-- `MulFast.Cond.uab`: the C's `int` sums in `s_mp_mul_digs_fast` stay small. -/
  uab : p.a.used + p.b.used < 2 ^ 30
  /-- D5 on the fast path: `s_mp_mul_digs_fast` does not call `mp_grow` (`MulFast.Pre.room`). -/
  room : Fast p.a p.b p.digs → p.digs ≤ p.c.alloc
  /-- Nonempty digit arrays (`HContract.pos`: an empty region inside the arena is not off it). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- `c`'s old digits are freed by `mp_clear(&t)` on the slow path: a live, nonempty block. -/
  cpos : 0 < p.c.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (q, c') => Digs p q c'

/-- The C's test for the fast multiplier (`digs < MP_WARRAY && MP_MIN(a->used, b->used) < MP_MAXFAST`). -/
def Fast (a b : MpInt) (digs : Nat) : Prop := digs < 512 ∧ min a.used b.used < 256

/-- What `c` holds after, and where. -/
structure Digs (p : P) (q : Nat) (c' : MpInt) : Prop where
  valid : c'.Valid
  mag : c'.mag = (p.a.mag * p.b.mag) % radix ^ p.digs
  /-- The fast path: in place, `s_mp_mul_digs_fast`'s Post. -/
  fast : Fast p.a p.b p.digs → q = p.cdp ∧ MulFastPost p.a p.b p.c c' p.digs
  /-- The slow path: `t`'s allocation and sign. -/
  slow : ¬ Fast p.a p.b p.digs → c'.alloc = initPrec p.digs ∧ c'.sign = Layout.mpZpos

-- Tom/Spec/Mul.lean
/-- What `s_mp_mul_digs_fast(a, b, c, digs)` leaves in `c` when `c->alloc ≥ digs`
(no `mp_grow`, D5): the comba digits, `used` clamped from `pa`, the sign reset if
zero (`mp_clamp`), `alloc` unchanged. -/
structure MulFastPost (a b c c' : MpInt) (digs : Nat) : Prop where
  alloc : c'.alloc = c.alloc
  len : c'.digits.length = c.alloc
  digit : c'.digit = mulFastDigit a b (min digs (a.used + b.used))
  used : c'.used = clampUsed (mulFastDigit a b (min digs (a.used + b.used))) (min digs (a.used + b.used))
  sign : c'.sign = if c'.used = 0 then Layout.mpZpos else c.sign
theorem MulFastPost.spec {a b c c' : MpInt} {digs : Nat} (ha : a.ShapeU) (hb : b.ShapeU)
    (hroom : digs ≤ c.alloc) (hc : c.alloc < 2 ^ 31)
    (hsign : c.sign = Layout.mpZpos ∨ c.sign = Layout.mpNeg) (h : MulFastPost a b c c' digs) :
    c'.Valid ∧ c'.mag = (a.mag * b.mag) % radix ^ (min digs (a.used + b.used)) ∧
      (a.used + b.used ≤ digs → c'.mag = a.mag * b.mag) := …  -- proved in Tom/Spec/Mul.lean

/-- The digits `s_mp_mul_digs_fast(a, b, c, digs)` leaves: the comba digits of the
first `pa = min digs (a.used + b.used)` columns, zero above. -/
def mulFastDigit (a b : MpInt) (pa i : Nat) : Nat :=
  if i < pa then combaD (col a.digit b.digit a.used b.used) i else 0

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.initPrec` (`mp_gcd`), `Tom.clampUsed` (`mp_add`), `Tom.minPrec` (`mp_gcd`), `Tom.combaD` (`mp_mul_d`), `Tom.col` (`mp_reduce`), `Tom.combaW` (`mp_mul_d`), `Tom.sumTo` (`mp_reduce`)
-/

/-- `mp_reduce`'s in-place schoolbook multipliers on both paths -/
theorem Specs.s_mp_mul_digs_correct_inplace : Tom.Machine.Api.SMpMulDigsAG.Statement :=
  Tom.Machine.Fn.SMpMulDigsAGClosed.digsCorrect
/-
Machine plumbing: the arguments: `a0 = a2 = a`, `a1 = b`, `a3 = digs`; stack reservation `F = 2192`; regions stk aS aD bS bD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/SMpMulDigsAG.lean
/-- **`s_mp_mul_digs(a, b, a, digs)` on either path, `a` re-placed as needed.** -/
def Statement : Prop := ∀ {p : P}, Spec p

-- Tom/Machine/Api/SMpMulDigsA.lean
structure P where  (sp pa adp pb bdp digs : Nat); (a b : MpInt); (H : List (Nat × Nat))

-- Tom/Machine/Api/SMpMulDigsAG.lean
/-- The contract at one `p`. -/
def Spec (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At SMpMulDigs.entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

/-- What `s_mp_mul_digs(a, b, a, digs)` needs on either path. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 2736
  sa : p.a.Shape
  sb : p.b.Shape
  /-- The fast routine keeps `a`'s sign word for a nonzero result. -/
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  /-- The C's `int digs`, nonnegative. -/
  dg_lt : p.digs < 2 ^ 31
  /-- The C's `int` sums stay small. -/
  uab : p.a.used + p.b.used < 2 ^ 30
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

def Q (p : P) : Api.MpMul.X → Prop
  | (ok, _, a') => Out p ok a'

/-- What `a` holds after: `MulFastHA.Out` without `grow`. -/
structure Out (p : P) (ok : Bool) (a' : MpInt) : Prop where
  shape : a'.Shape
  sign : a'.sign = Layout.mpZpos ∨ a'.sign = Layout.mpNeg
  pos : 0 < a'.alloc
  mag : ok = true → a'.mag = (p.a.mag * p.b.mag) % radix ^ p.digs
  top : ok = true → 0 < a'.used → a'.digit (a'.used - 1) ≠ 0
  /-- A nonnegative `a` stays nonnegative. -/
  zsign : p.a.sign = Layout.mpZpos → a'.sign = Layout.mpZpos

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MpMul.X` (`mp_mul`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`)
-/

/-! ## `s_mp_mul_digs_fast`

`mp_err s_mp_mul_digs_fast(const mp_int *a, const mp_int *b, mp_int *c, int digs);`
-/

/-- `s_mp_mul_digs_fast(a, b, c, digs)` with growth: the allocating contract (a named premise) -/
theorem Specs.s_mp_mul_digs_fast_correct : Tom.Machine.Api.MulFastH.Statement :=
  Tom.Machine.Fn.MulFastGG5.correct
/-
Machine plumbing: entry `0x800042f0`; the arguments: `a0 = a`, `a1 = b`, `a2 = c`, `a3 = digs` (`gp` for the allocator); stack reservation `F = 2736`; regions stk aS aD bS bD cS cD code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/MulFastH.lean
/-- **`s_mp_mul_digs_fast` with growth** (named premise, not proved). -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: Api.SMpMulDigs.args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

structure Res (p : P) : Prop where
  stk : StkRes p.sp 2736
  sa : p.a.ShapeU
  sb : p.b.ShapeU
  sc : p.c.Shape
  csign : p.c.sign = Layout.mpZpos ∨ p.c.sign = Layout.mpNeg
  /-- `MulFast.Cond`: `digs < MP_WARRAY`, `min ≤ MP_MAXFAST`, the `int` sums. -/
  cond : Api.MulFast.Cond p.a p.b p.digs
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  cpos : 0 < p.c.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  coff : OffHeap p.pc 24

def Q (p : P) : X → Prop
  | (ok, _, c') => Out p ok c'

-- Tom/Machine/Api/MulFast.lean
/-- The C's conditions on the operands. -/
structure Cond (a b : MpInt) (dg : Nat) : Prop where
  dg_w : dg < 512
  maxf : min a.used b.used ≤ 256
  uab : a.used + b.used < 2 ^ 30

-- Tom/Machine/Api/MulFastH.lean
/-- What `c` holds after: shaped and live; on `MP_OKAY` the truncated product, clamped. -/
structure Out (p : P) (ok : Bool) (c' : MpInt) : Prop where
  shape : c'.Shape
  sign : c'.sign = Layout.mpZpos ∨ c'.sign = Layout.mpNeg
  pos : 0 < c'.alloc
  mag : ok = true → c'.mag = (p.a.mag * p.b.mag) % radix ^ p.digs
  top : ok = true → 0 < c'.used → c'.digit (c'.used - 1) ≠ 0
  /-- `c`'s block kept or grown (`mp_grow(c, digs)` only when `c->alloc < digs`). -/
  grow : p.c.alloc ≤ c'.alloc
  /-- A nonnegative destination stays nonnegative (the clamp resets a zero result's sign, else keeps
  `c`'s; `mp_reduce`'s `q3 m`). -/
  zsign : p.c.sign = Layout.mpZpos → c'.sign = Layout.mpZpos

Also used (printed above): `Tom.Machine.Api.SMpMulDigs.P` (`s_mp_mul_digs`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MpMul.X` (`mp_mul`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`)
-/

/-- `s_mp_mul_digs(a, b, a, digs)` and the growing `s_mp_mul_digs_fast(a, b, a, digs)` -/
theorem Specs.s_mp_mul_digs_fast_correct_inplace : Tom.Machine.Api.MulFastHA.Statement :=
  Tom.Machine.Fn.MulFastGAG5.correct
/-
Machine plumbing: entry `0x800018a8`; the arguments: `a0 = a2 = a`, `a1 = b`, `a3 = digs`; stack reservation `F = 2736`; regions stk aS aD bS bD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/SMpMulDigsA.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

/-- What `s_mp_mul_digs_fast(a, b, a, digs)` needs (`MulFastH.Res` in place). -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 2736
  sa : p.a.Shape
  sb : p.b.Shape
  /-- The fast path keeps `a`'s sign word for a nonzero result. -/
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  /-- `MulFast.Cond`: `digs < MP_WARRAY`, `min ≤ MP_MAXFAST`, the `int` sums. -/
  cond : Api.MulFast.Cond p.a p.b p.digs
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

def Q (p : P) : X → Prop
  | (ok, _, a') => Out p ok a'

/-- What `a` holds after (`MulFastH.Out` over the old `a`, `b`). -/
structure Out (p : P) (ok : Bool) (a' : MpInt) : Prop where
  shape : a'.Shape
  sign : a'.sign = Layout.mpZpos ∨ a'.sign = Layout.mpNeg
  pos : 0 < a'.alloc
  mag : ok = true → a'.mag = (p.a.mag * p.b.mag) % radix ^ p.digs
  top : ok = true → 0 < a'.used → a'.digit (a'.used - 1) ≠ 0
  /-- `a`'s block kept or grown. -/
  grow : p.a.alloc ≤ a'.alloc
  /-- A nonnegative `a` stays nonnegative. -/
  zsign : p.a.sign = Layout.mpZpos → a'.sign = Layout.mpZpos

Also used (printed above): `Tom.Machine.Api.SMpMulDigsA.P` (`s_mp_mul_digs`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MulFast.Cond` (`s_mp_mul_digs_fast`), `Tom.Machine.Api.MpMul.X` (`mp_mul`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`)
-/

/-- `s_mp_mul_digs_fast`: the standard contracts -/
theorem Specs.s_mp_mul_digs_fast_correct_room : Tom.Machine.Api.MulFast.Statement :=
  Tom.Machine.Fn.MulFast.correct
/-
Machine plumbing: entry `0x800042f0`.

-- Tom/Machine/Api/MulFast.lean
/-- **`s_mp_mul_digs_fast` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp dg : Nat}
    {a b c : MpInt} {ra s0 : BitVec 64}, Pre m sp pa adp pb bdp pc cdp dg a b c ra →
    Triple (At entry (entryL ra s0 sp pa pb pc dg) m v.keepR outp)
      (Ret m v outp sp pa adp pb bdp pc cdp dg a b c ra s0)

/-- What `s_mp_mul_digs_fast(a, b, c, digs)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp pc cdp dg : Nat) (a b c : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  rc : MpAt m pc cdp c
  sa : a.ShapeU
  sb : b.ShapeU
  sc : c.Shape
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  gc : MpGeom pc cdp c.alloc
  cond : Cond a b dg
  room : dg ≤ c.alloc
  rs : Ram (sp - 2192) 2192
  sp_al : sp % 16 = 0
  sp_ge : 2192 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp pc cdp a b c) Bin.isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp pc cdp dg : Nat) (a b c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp pc cdp dg a b c c' M

structure Post (m : Mem) (sp pa adp pb bdp pc cdp dg : Nat) (a b c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  fast : MulFastPost a b c c' dg
  frame : Frm (lay sp pa adp pb bdp pc cdp a b c) Bin.ws m M

Also used (printed above): `Tom.Machine.Api.MulFast.Cond` (`s_mp_mul_digs_fast`), `Tom.MulFastPost` (`s_mp_mul_digs`), `Tom.mulFastDigit` (`s_mp_mul_digs`), `Tom.clampUsed` (`mp_add`), `Tom.combaD` (`mp_mul_d`), `Tom.col` (`mp_reduce`), `Tom.combaW` (`mp_mul_d`), `Tom.sumTo` (`mp_reduce`)
-/

/-- `s_mp_mul_digs_fast`: the standard contracts -/
theorem Specs.s_mp_mul_digs_fast_correct_room_inplace_a : Tom.Machine.Api.MulFast.StatementInPlaceA :=
  Tom.Machine.Fn.MulFast.correct_inplaceA
/-
Machine plumbing: entry `0x800042f0`.

-- Tom/Machine/Api/MulFast.lean
/-- **`s_mp_mul_digs_fast(a, b, a, digs)`**: `c = a`. -/
def StatementInPlaceA : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp dg : Nat}
    {a b : MpInt} {ra s0 : BitVec 64}, PreI m sp pb bdp pa adp dg b a ra → Cond a b dg →
    Triple (At entry (entryL ra s0 sp pa pb pa dg) m v.keepR outp)
      (fun cf => ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
        PostI m sp pb bdp pa adp b a a' M (MulFastPost a b a a' dg))

/-- Two operands, `x` read, `y` the destination (`Two`'s regions, `y` written). -/
structure PreI (m : Mem) (sp px xdp py ydp dg : Nat) (x y : MpInt) (ra : BitVec 64) : Prop where
  rx : MpAt m px xdp x
  ry : MpAt m py ydp y
  sx : x.Shape
  sy : y.Shape
  gx : MpGeom px xdp x.alloc
  gy : MpGeom py ydp y.alloc
  room : dg ≤ y.alloc
  rs : Ram (sp - 2192) 2192
  sp_al : sp % 16 = 0
  sp_ge : 2192 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (Two.lay 2192 sp px xdp py ydp x y) Two.isW

structure PostI (m : Mem) (sp px xdp py ydp : Nat) (x y y' : MpInt) (M : Mem) (P : Prop) : Prop where
  repr : MpAt M py ydp y'
  fast : P
  frame : Frm (Two.lay 2192 sp px xdp py ydp x y) Two.ws m M

Also used (printed above): `Tom.Machine.Api.MulFast.Cond` (`s_mp_mul_digs_fast`), `Tom.MulFastPost` (`s_mp_mul_digs`), `Tom.mulFastDigit` (`s_mp_mul_digs`), `Tom.clampUsed` (`mp_add`), `Tom.combaD` (`mp_mul_d`), `Tom.col` (`mp_reduce`), `Tom.combaW` (`mp_mul_d`), `Tom.sumTo` (`mp_reduce`)
-/

/-- `s_mp_mul_digs_fast`: the standard contracts -/
theorem Specs.s_mp_mul_digs_fast_correct_room_inplace_b : Tom.Machine.Api.MulFast.StatementInPlaceB :=
  Tom.Machine.Fn.MulFast.correct_inplaceB
/-
Machine plumbing: entry `0x800042f0`.

-- Tom/Machine/Api/MulFast.lean
/-- **`s_mp_mul_digs_fast(a, b, b, digs)`**: `c = b`. -/
def StatementInPlaceB : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp dg : Nat}
    {a b : MpInt} {ra s0 : BitVec 64}, PreI m sp pa adp pb bdp dg a b ra → Cond a b dg →
    Triple (At entry (entryL ra s0 sp pa pb pb dg) m v.keepR outp)
      (fun cf => ∃ b' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
        PostI m sp pa adp pb bdp a b b' M (MulFastPost a b b b' dg))

Also used (printed above): `Tom.Machine.Api.MulFast.PreI` (`s_mp_mul_digs_fast`), `Tom.Machine.Api.MulFast.Cond` (`s_mp_mul_digs_fast`), `Tom.Machine.Api.MulFast.PostI` (`s_mp_mul_digs_fast`), `Tom.MulFastPost` (`s_mp_mul_digs`), `Tom.mulFastDigit` (`s_mp_mul_digs`), `Tom.clampUsed` (`mp_add`), `Tom.combaD` (`mp_mul_d`), `Tom.col` (`mp_reduce`), `Tom.combaW` (`mp_mul_d`), `Tom.sumTo` (`mp_reduce`)
-/

/-! ## `s_mp_mul_high_digs`

`mp_err s_mp_mul_high_digs(const mp_int *a, const mp_int *b, mp_int *c, int digs);`

Coverage: contract (c = a).
-/

/-- `mp_reduce`'s in-place schoolbook multipliers on both paths -/
theorem Specs.s_mp_mul_high_digs_correct : Tom.Machine.Api.SMpMulHighDigsG.Statement :=
  Tom.Machine.Fn.SMpMulDigsAGClosed.highCorrect
/-
Machine plumbing: entry `0x800069e0`; the arguments: `a0 = a`, `a1 = b`, `a2 = c = a`, `a3 = digs` (`gp` for the allocator); stack reservation `F = 2192`; regions stk aS aD bS bD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/SMpMulDigsAG.lean
/-- **`s_mp_mul_high_digs(a, b, a, digs)` on either path, `a` re-placed as needed.** -/
def Statement : Prop := ∀ {p : P}, Spec p

-- Tom/Machine/Api/SMpMulHighDigs.lean
structure P where  (sp pa adp pb bdp digs : Nat); (a b : MpInt); (H : List (Nat × Nat))

-- Tom/Machine/Api/SMpMulDigsAG.lean
/-- The contract at one `p`. -/
def Spec (p : P) : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At SMpMulHighDigs.entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .aD (out p x) (site' p x) (hin p) (hout p x) m M)

/-- What `s_mp_mul_high_digs(a, b, a, digs)` needs on either path. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 2736
  sa : p.a.Shape
  sb : p.b.Shape
  /-- The fast path keeps `a`'s sign for a nonzero result. -/
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  /-- The C's `int digs`, nonnegative. -/
  dg_lt : p.digs < 2 ^ 31
  /-- No column below `digs` past `pa`; on the slow path `t.dp[digs]` inside `t`. -/
  dg_le : p.digs ≤ p.a.used + p.b.used
  /-- The slow path reads `b->dp + (digs - ix)` for `ix < a->used`. -/
  ua_le : p.a.used ≤ p.digs + 1
  ub_pos : 1 ≤ p.b.used
  /-- The C's `int` sums stay small. -/
  uab : p.a.used + p.b.used < 2 ^ 30
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

def Q (p : P) : Api.MpMul.X → Prop
  | (ok, _, a') => Out p ok a'

/-- What `a` holds after: on `MP_OKAY` the high product plus `low`. -/
structure Out (p : P) (ok : Bool) (a' : MpInt) : Prop where
  shape : a'.Shape
  pos : 0 < a'.alloc
  /-- The sign kept, or reset for a zero result. -/
  sign : a'.sign = Layout.mpZpos ∨ a'.sign = p.a.sign
  valid : ok = true → a'.Valid
  mag : ok = true → a'.mag = low p + highProd p.a.digit p.b.digit p.a.used p.b.used p.digs
  /-- The low part is below `radix ^ digs`. -/
  low : low p < radix ^ p.digs

/-- The digits below `digs` beside the high product: `a`'s old ones on the fast path, none on the
slow one. -/
def low (p : P) : Nat := if Fast p.a p.b then natUpTo p.a.digit p.digs else 0

-- Tom/Machine/Api/SMpMulHighDigs.lean
/-- The C's test for the fast routine. -/
def Fast (a b : MpInt) : Prop := a.used + b.used ≤ 510 ∧ min a.used b.used ≤ 255

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MpMul.X` (`mp_mul`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Reduce.highProd` (`mp_reduce`), `Tom.Reduce.highCol` (`mp_reduce`), `Tom.col` (`mp_reduce`), `Tom.sumTo` (`mp_reduce`)
-/

/-- `s_mp_mul_high_digs(a, b, a, digs)`: the allocating contract, in place -/
theorem Specs.s_mp_mul_high_digs_correct_room : Tom.Machine.Api.SMpMulHighDigs.Statement :=
  Tom.Machine.Fn.SMpMulHighDigsG5.correct
/-
Machine plumbing: entry `0x800069e0`; the arguments: `a0 = a`, `a1 = b`, `a2 = c = a`, `a3 = digs` (`gp` for the allocator); stack reservation `F = 2192`; regions stk aS aD bS bD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/SMpMulHighDigs.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

/-- What `s_mp_mul_high_digs(a, b, a, digs)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 2192
  sa : p.a.Shape
  sb : p.b.Shape
  /-- The fast path keeps `a`'s sign for a nonzero result: a sign, for `a'` valid. -/
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  /-- The C's `int digs`, nonnegative (`bltz a3` at `69e8`; the rows take `a3` below `2^31`). -/
  dg_lt : p.digs < 2 ^ 31
  /-- `MulHighFast.Cond.dg_le`; on the slow path the empty rows' carry `t.dp[digs] := 0` stays
  inside `t` (`t->alloc ≥ a->used + b->used + 1`). -/
  dg_le : p.digs ≤ p.a.used + p.b.used
  /-- The slow path reads `b->dp + (digs - ix)` for every `ix < a->used`: in bounds only for
  `ix ≤ digs` (`Reduce.highRow`). `mp_reduce` passes `q` with `used ≤ um + 1`. -/
  ua_le : p.a.used ≤ p.digs + 1
  /-- `MulHighFast.Cond.ub_pos`. -/
  ub_pos : 1 ≤ p.b.used
  /-- The C's `int` sums (`a->used + b->used + 1`) stay small. -/
  uab : p.a.used + p.b.used < 2 ^ 30
  /-- D5 on the fast path: `s_mp_mul_high_digs_fast` does not call `mp_grow`
  (`MulHighFast.Pre.room`). -/
  room : Fast p.a p.b → p.a.used + p.b.used ≤ p.a.alloc
  /-- Nonempty digit arrays (`HContract.pos`); `a`'s is freed by `mp_clear(&t)` on the slow path. -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (q, a') => Digs p q a'

/-- What `a` holds after, and where. -/
structure Digs (p : P) (q : Nat) (a' : MpInt) : Prop where
  valid : a'.Valid
  /-- The fast path: in place, `s_mp_mul_high_digs_fast`'s Post (`a`'s digits below `digs`
  kept, the high product above). -/
  fast : Fast p.a p.b → q = p.adp ∧ MulHighFastPost p.a p.b p.a a' p.digs
  /-- The slow path: the high product alone, in `t`'s allocation. -/
  slow : ¬ Fast p.a p.b → MulHighPost p.a p.b a' p.digs ∧ a'.alloc = initPrec (p.a.used + p.b.used + 1)

-- Tom/Spec/Reduce.lean
/-- What `s_mp_mul_high_digs_fast(a, b, c, digs)` leaves in `c` when `c->alloc ≥ a->used + b->used`
(no `mp_grow`, D5): `highFastDigit`, `used` clamped from `pa`, the sign of `c` (reset if
zero), `alloc` unchanged. -/
structure MulHighFastPost (a b c c' : MpInt) (digs : Nat) : Prop where
  alloc : c'.alloc = c.alloc
  len : c'.digits.length = c.alloc
  digit : c'.digit = highFastDigit a b c digs
  used : c'.used = clampUsed (highFastDigit a b c digs) (a.used + b.used)
  sign : c'.sign = if c'.used = 0 then Layout.mpZpos else c.sign
theorem MulHighFastPost.spec {a b c c' : MpInt} {digs : Nat} (ha : a.Shape) (hb : b.Shape) (hc : c.Shape)
    (hd : digs ≤ a.used + b.used) (hroom : a.used + b.used ≤ c.alloc)
    (hsign : c.sign = Layout.mpZpos ∨ c.sign = Layout.mpNeg) (h : MulHighFastPost a b c c' digs) :
    c'.Valid ∧ c'.mag = natUpTo c.digit digs + highProd a.digit b.digit a.used b.used digs := …  -- proved in Tom/Spec/Reduce.lean

/-- What `s_mp_mul_high_digs(a, b, c, digs)` leaves in `c` on its own path (`a->used + b->used + 1 ≥
MP_WARRAY` or `min(used) ≥ MP_MAXFAST`, `a->used ≤ digs + 1`): the fresh `t` (zero below
`digs`), clamped, exchanged into `c`. -/
structure MulHighPost (a b c' : MpInt) (digs : Nat) : Prop where
  valid : c'.Valid
  mag : c'.mag = highRows a.digit b.digit b.used digs a.used
  sign : c'.sign = Layout.mpZpos
theorem MulHighPost.spec {a b c' : MpInt} {digs : Nat} (h : MulHighPost a b c' digs) :
    c'.Valid ∧ c'.mag = highProd a.digit b.digit a.used b.used digs := …  -- proved in Tom/Spec/Reduce.lean

/-- The digits `s_mp_mul_high_digs_fast(a, b, c, digs)` leaves: `c`'s old digits below `digs`
(they are not written; `c` may be `a`, as in `mp_reduce`), the comba digits of the columns
`digs .. pa - 1` with the carry starting from zero at `digs`, zero from `pa = a->used + b->used`. -/
def highFastDigit (a b c : MpInt) (digs i : Nat) : Nat :=
  if i < digs then c.digit i
  else if i < a.used + b.used then combaD (fun k => col a.digit b.digit a.used b.used (digs + k)) (i - digs)
  else 0

/-- The high product by rows: `Σ_{ix < ua} radix^ix * a_ix * rowHigh b (digs - ix)`. -/
def highRows (da db : Nat → Nat) (ub digs : Nat) : Nat → Nat
  | 0 => 0
  | ua + 1 => highRows da db ub digs ua + radix ^ ua * (da ua * rowHigh db ub (digs - ua))

/-- `Σ_{s ≤ j < ub} db j radix^j`: the part of `b` a row from `digs` on uses. -/
def rowHigh (db : Nat → Nat) (ub s : Nat) : Nat := natUpTo (fun j => if s ≤ j then db j else 0) ub

Also used (printed above): `Tom.Machine.Api.SMpMulHighDigs.P` (`s_mp_mul_high_digs`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.SMpMulHighDigs.Fast` (`s_mp_mul_high_digs`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.initPrec` (`mp_gcd`), `Tom.clampUsed` (`mp_add`), `Tom.minPrec` (`mp_gcd`), `Tom.combaD` (`mp_mul_d`), `Tom.col` (`mp_reduce`), `Tom.combaW` (`mp_mul_d`), `Tom.sumTo` (`mp_reduce`)
-/

/-! ## `s_mp_mul_high_digs_fast`

`mp_err s_mp_mul_high_digs_fast(const mp_int *a, const mp_int *b, mp_int *c, int digs);`
-/

/-- `s_mp_mul_high_digs_fast(a, b, a, digs)` with growth: the allocating contract -/
theorem Specs.s_mp_mul_high_digs_fast_correct : Tom.Machine.Api.MulHighFastHA.Statement :=
  Tom.Machine.Fn.MulHighFastGAG5.correct
/-
Machine plumbing: entry `0x80006be4`; the arguments: `a0 = a`, `a1 = b`, `a2 = c = a`, `a3 = digs` (`gp` for the allocator); stack reservation `F = 2736`; regions stk aS aD bS bD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MulHighFastHA.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

/-- What `s_mp_mul_high_digs_fast(a, b, a, digs)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 2736
  sa : p.a.Shape
  sb : p.b.Shape
  /-- The routine keeps `a`'s sign word for a nonzero result. -/
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  /-- The C's `int digs`, nonnegative. -/
  dg_lt : p.digs < 2 ^ 31
  /-- No column below `digs` is skipped past `pa` (`MulHighFast.Cond.dg_le`). -/
  dg_le : p.digs ≤ p.a.used + p.b.used
  /-- `MulHighFast.Cond.ub_pos`. -/
  ub_pos : 1 ≤ p.b.used
  /-- The C's fast test (`pa` below `MP_WARRAY`, the shorter operand below `MP_MAXFAST`). -/
  fast : Fast p.a p.b
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

def Q (p : P) : X → Prop
  | (ok, _, a') => Out p ok a'

/-- What `a` holds after: on `MP_MEM` (`ok = false`) `a` itself; else the old digits below `digs`
plus the high product (`MulHighFastPost.spec` over the grown `a`). -/
structure Out (p : P) (ok : Bool) (a' : MpInt) : Prop where
  shape : a'.Shape
  pos : 0 < a'.alloc
  /-- `a`'s block kept or grown (`mp_grow` never shrinks). -/
  grow : p.a.alloc ≤ a'.alloc
  /-- The sign kept, or reset for a zero result. -/
  sign : a'.sign = Layout.mpZpos ∨ a'.sign = p.a.sign
  valid : ok = true → a'.Valid
  mag : ok = true → a'.mag = natUpTo p.a.digit p.digs + highProd p.a.digit p.b.digit p.a.used p.b.used p.digs

Also used (printed above): `Tom.Machine.Api.SMpMulHighDigs.P` (`s_mp_mul_high_digs`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.SMpMulHighDigs.Fast` (`s_mp_mul_high_digs`), `Tom.Machine.Api.MpMul.X` (`mp_mul`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Reduce.highProd` (`mp_reduce`), `Tom.Reduce.highCol` (`mp_reduce`), `Tom.col` (`mp_reduce`), `Tom.sumTo` (`mp_reduce`)
-/

/-- `s_mp_mul_high_digs_fast`: the standard contract, in place (`c = a`) -/
theorem Specs.s_mp_mul_high_digs_fast_correct_room : Tom.Machine.Api.MulHighFast.StatementInPlace :=
  Tom.Machine.Fn.MulHighFast.correct
/-
Machine plumbing: entry `0x80006be4`.

-- Tom/Machine/Api/MulHighFast.lean
/-- **`s_mp_mul_high_digs_fast(a, b, a, digs)` on the machine** (`c = a`). -/
def StatementInPlace : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp dg : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    Pre m sp pa adp pb bdp dg a b ra →
    Triple (At entry (entryL ra s0 sp pa pb pa dg) m v.keepR outp) (Ret m v outp sp pa adp pb bdp dg a b ra s0)

/-- What `s_mp_mul_high_digs_fast(a, b, a, digs)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp dg : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  sa : a.Shape
  sb : b.Shape
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  cond : Cond a b dg
  room : a.used + b.used ≤ a.alloc
  rs : Ram (sp - 2192) 2192
  sp_al : sp % 16 = 0
  sp_ge : 2192 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp a b) Two.isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp dg : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp dg a b a' M

/-- The C's conditions on the operands. -/
structure Cond (a b : MpInt) (dg : Nat) : Prop where
  dg_le : dg ≤ a.used + b.used
  pa_w : a.used + b.used ≤ 512
  maxf : min a.used b.used ≤ 256
  ub_pos : 1 ≤ b.used

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp dg : Nat) (a b a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  fast : MulHighFastPost a b a a' dg
  frame : Frm (lay sp pa adp pb bdp a b) Two.ws m M

Also used (printed above): `Tom.Reduce.MulHighFastPost` (`s_mp_mul_high_digs`), `Tom.Reduce.highFastDigit` (`s_mp_mul_high_digs`), `Tom.clampUsed` (`mp_add`), `Tom.combaD` (`mp_mul_d`), `Tom.col` (`mp_reduce`), `Tom.combaW` (`mp_mul_d`), `Tom.sumTo` (`mp_reduce`)
-/

/-! ## `s_mp_reverse`

`void s_mp_reverse(unsigned char *s, size_t len);`
-/

/-- `s_mp_reverse`: the standard contract -/
theorem Specs.s_mp_reverse_correct : Tom.Machine.Api.Reverse.Statement :=
  Tom.Machine.Fn.Reverse.correct
/-
Machine plumbing: entry `0x80004528`; regions arr code.

-- Tom/Machine/Api/Reverse.lean
/-- **`s_mp_reverse` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {s : Nat} {l : List (BitVec 8)} {ra : BitVec 64},
    Pre m s l ra →
    Triple (At entry (Fn.Reverse.entryL ra s l.length) m v.keep outp) (Ret m v outp s l ra)

structure Pre (m : Mem) (s : Nat) (l : List (BitVec 8)) (ra : BitVec 64) : Prop where
  bytes : BytesAt m s l
  n_pos : 1 ≤ l.length
  rs : Ram s l.length
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay s l.length) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (s : Nat) (l : List (BitVec 8)) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ M, At ra [(1, ra)] M v.keep outp cf ∧ Post m s l M

/-- The bytes `l` at `s`, as total reads. -/
def BytesAt (M : Mem) (s : Nat) (l : List (BitVec 8)) : Prop :=
  ∀ i, i < l.length → (M[s + i]?).getD 0 = l.getD i 0

structure Post (m : Mem) (s : Nat) (l : List (BitVec 8)) (M : Mem) : Prop where
  bytes : BytesAt M s l.reverse
  frame : Frm (lay s l.length) [R.arr] m M
-/

/-! ## `s_mp_sqr`

`mp_err s_mp_sqr(const mp_int *a, mp_int *b);`

Coverage: contract.
-/

/-- `s_mp_sqr(a, b)`: the allocating contract -/
theorem Specs.s_mp_sqr_correct : Tom.Machine.Api.SMpSqr.Statement :=
  Tom.Machine.Fn.SMpSqrG5.correct
/-
Machine plumbing: entry `0x80006e54`; the arguments: `a0 = a`, `a1 = b` (`gp` for the allocator); stack reservation `F = 160 + MpInit.Fsize`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/SMpSqr.lean
def Statement : Prop := Standard.Statement Res Q (site .bD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp : Nat); (a b : MpInt); (H : List (Nat × Nat))

/-- What `s_mp_sqr(a, b)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The square reads `a`'s digits below `used` only (`mp_sqr` passes it valid). -/
  sa : p.a.Shape
  /-- `2 a->used + 1` is an `int` (`slli`/`addiw` at `6e68`); the rows (`smsqrg`) bound
  every index of `t.dp` by it. -/
  au : p.a.used < 2 ^ 30
  apos : 0 < p.a.alloc
  /-- `b`'s old digits are freed by `mp_clear(&t)` after the exchange: a live, nonempty block. -/
  bpos : 0 < p.b.alloc
  aoff : OffHeap p.pa 24
  boff : OffHeap p.pb 24

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => True
  | some (_, b') => Sq p.a b'

/-- The square, and `t`'s allocation. -/
structure Sq (a b' : MpInt) : Prop where
  sqr : SqrPost a b'
  alloc : b'.alloc = initPrec (2 * a.used + 1)

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.SqrPost` (`mp_sqr`), `Tom.initPrec` (`mp_gcd`), `Tom.minPrec` (`mp_gcd`)
-/

/-! ## `s_mp_sqr_fast`

`mp_err s_mp_sqr_fast(const mp_int *a, mp_int *b);`
-/

/-- `s_mp_sqr_fast(a, b)` and `s_mp_sqr_fast(a, a)` with growth: the allocating contracts -/
theorem Specs.s_mp_sqr_fast_correct : Tom.Machine.Api.SqrFastH.Statement :=
  Tom.Machine.Fn.SqrFastHG5.correct
/-
Machine plumbing: entry `0x80007010`; stack reservation `F = 2752`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/SqrFastH.lean
def Statement : Prop := Standard.Statement Res Q (site .bD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp : Nat); (a b : MpInt); (H : List (Nat × Nat))

/-- What `s_mp_sqr_fast(a, b)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 2752
  /-- The loops read `a`'s digits below `used`. -/
  sa : p.a.Shape
  /-- `b`'s old digits above the result are zeroed only up to its old `used`. -/
  sb : p.b.Shape
  /-- `mp_clamp` keeps the sign word for a nonzero result (`SqrFastPost.spec`). -/
  bsign : p.b.sign = Layout.mpZpos ∨ p.b.sign = Layout.mpNeg
  /-- `MP_WARRAY` (`2 a->used + 1 < 512`, which `mp_sqr` checks): every column fits 64 bits. -/
  warr : 2 * p.a.used + 1 < 512
  /-- Nonempty digit arrays (`HContract.pos`). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- `b`'s struct is off the arena (`mp_grow` reads and writes it). -/
  boff : OffHeap p.pb 24

def Q (p : P) (x : X) : Prop := SqrAlg.Out p.a p.b.alloc (hin p) (lay p .bD) x

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MpSqr.X` (`mp_mul_2`), `Tom.Machine.Api.SqrAlg.Out` (`s_mp_karatsuba_sqr`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`)
-/

/-- `s_mp_sqr_fast(a, a)` with growth: the allocating contract -/
theorem Specs.s_mp_sqr_fast_correct_inplace : Tom.Machine.Api.SqrFastHA.Statement :=
  Tom.Machine.Fn.SqrFastHAG5.correct
/-
Machine plumbing: entry `0x80007010`; the arguments: `a0 = a1 = a`; stack reservation `F = 2752`; regions stk aS aD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/SqrFastHA.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

structure P where  (sp pa adp : Nat); (a : MpInt); (H : List (Nat × Nat))

/-- What `s_mp_sqr_fast(a, a)` needs (in place: the column loop reads `a` into `W` before the
copy writes it; a grown `a` is read at its new block). -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp 2752
  sa : p.a.Shape
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  warr : 2 * p.a.used + 1 < 512
  apos : 0 < p.a.alloc
  aoff : OffHeap p.pa 24

def Q (p : P) (x : X) : Prop := SqrAlg.Out p.a p.a.alloc (hin p) (lay p .aD) x

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MpSqr.X` (`mp_mul_2`), `Tom.Machine.Api.SqrAlg.Out` (`s_mp_karatsuba_sqr`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`)
-/

/-- `s_mp_sqr_fast`: the standard contracts -/
theorem Specs.s_mp_sqr_fast_correct_room : Tom.Machine.Api.SqrFast.Statement :=
  Tom.Machine.Fn.SqrFast.correct
/-
Machine plumbing: entry `0x80007010`.

-- Tom/Machine/Api/SqrFast.lean
/-- **`s_mp_sqr_fast` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    Pre m sp pa adp pb bdp a b ra →
    Triple (At entry (entryL ra s0 sp pa pb) m v.keepR outp) (Ret m v outp sp pa adp pb bdp a b ra s0)

structure Pre (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  sa : a.Shape
  sb : b.Shape
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  warr : 2 * a.used + 1 < 512
  room : 2 * a.used ≤ b.alloc
  rs : Ram (sp - 2208) 2208
  sp_al : sp % 16 = 0
  sp_ge : 2208 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp a b) Two.isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra s0 : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ b' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp a b b' M

structure Post (m : Mem) (sp pa adp pb bdp : Nat) (a b b' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pb bdp b'
  sqr : SqrFastPost a b b'
  frame : Frm (lay sp pa adp pb bdp a b) Two.ws m M

-- Tom/Spec/Mul.lean
/-- `s_mp_sqr_fast(a, b)` leaves what `s_mp_mul_digs_fast(a, a, b, 2 a.used)` would:
its comba digits over `colS` are those over `col a a` (`colS_eq`, `combaD_congr`). -/
abbrev SqrFastPost (a b b' : MpInt) : Prop := MulFastPost a a b b' (a.used + a.used)
theorem SqrFastPost.spec {a b b' : MpInt} (ha : a.Shape) (hroom : a.used + a.used ≤ b.alloc)
    (hc : b.alloc < 2 ^ 31) (hsign : b.sign = Layout.mpZpos ∨ b.sign = Layout.mpNeg) (h : SqrFastPost a b b') :
    b'.Valid ∧ b'.mag = a.mag * a.mag := …  -- proved in Tom/Spec/Mul.lean

Also used (printed above): `Tom.MulFastPost` (`s_mp_mul_digs`), `Tom.mulFastDigit` (`s_mp_mul_digs`), `Tom.clampUsed` (`mp_add`), `Tom.combaD` (`mp_mul_d`), `Tom.col` (`mp_reduce`), `Tom.combaW` (`mp_mul_d`), `Tom.sumTo` (`mp_reduce`)
-/

/-- `s_mp_sqr_fast`: the standard contracts -/
theorem Specs.s_mp_sqr_fast_correct_room_inplace : Tom.Machine.Api.SqrFast.StatementInPlace :=
  Tom.Machine.Fn.SqrFast.correct_inplace
/-
Machine plumbing: entry `0x80007010`.

-- Tom/Machine/Api/SqrFast.lean
/-- **`s_mp_sqr_fast(a, a)` on the machine.** -/
def StatementInPlace : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt} {ra s0 : BitVec 64},
    PreI m sp pa adp a ra →
    Triple (At entry (entryL ra s0 sp pa pa) m v.keepR outp)
      (fun cf => ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
        PostI m sp pa adp a a' M)

structure PreI (m : Mem) (sp pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  warr : 2 * a.used + 1 < 512
  room : 2 * a.used ≤ a.alloc
  rs : Ram (sp - 2208) 2208
  sp_al : sp % 16 = 0
  sp_ge : 2208 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (layI sp pa adp a) Un.isW

structure PostI (m : Mem) (sp pa adp : Nat) (a a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  sqr : SqrFastPost a a a'
  frame : Frm (layI sp pa adp a) Un.ws m M

abbrev layI (sp pa adp : Nat) (a : MpInt) := Un.lay 2208 sp pa adp a

Also used (printed above): `Tom.SqrFastPost` (`s_mp_sqr_fast`), `Tom.MulFastPost` (`s_mp_mul_digs`), `Tom.mulFastDigit` (`s_mp_mul_digs`), `Tom.clampUsed` (`mp_add`), `Tom.combaD` (`mp_mul_d`), `Tom.col` (`mp_reduce`), `Tom.combaW` (`mp_mul_d`), `Tom.sumTo` (`mp_reduce`)
-/

/-! ## `s_mp_sub`

`mp_err s_mp_sub(const mp_int *a, const mp_int *b, mp_int *c);`
-/

/-- `s_mp_sub(a, b, c)` with growth: the allocating contract -/
theorem Specs.s_mp_sub_correct : Tom.Machine.Api.SSubG.Statement :=
  Tom.Machine.Fn.SSubGG5.correct
/-
Machine plumbing: entry `0x80004564`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator); stack reservation `F = 48 + MpGrow.F`; regions stk aS aD bS bD cS cD code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/SSubG.lean
def Statement : Prop := Standard.Statement Res Q (site .cD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp pc cdp : Nat); (a b c : MpInt); (H : List (Nat × Nat))

/-- What `s_mp_sub(a, b, c)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The loops read the operands' digits below `used`. -/
  sa : p.a.Shape
  sb : p.b.Shape
  /-- `c`'s old digits above the result are zeroed only up to its old `used`. -/
  sc : p.c.Shape
  /-- `mp_grow`'s `int size` (`a->used`). -/
  size_lt : p.a.used < 2 ^ 31
  /-- The operands' digit arrays are nonempty (initialised `mp_int`s). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  cpos : 0 < p.c.alloc
  /-- `c`'s struct is off the arena (`mp_grow` reads and writes it). -/
  coff : OffHeap p.pc 24
  /-- The C's order: the subtrahend no longer than the minuend. -/
  ge : p.b.used ≤ p.a.used

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.c.alloc < p.a.used
  | some (_, x) => SSubPost p.a p.b (sSubIn p.a p.c) x

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.SSubPost` (`mp_add`), `Tom.sSubIn` (`mp_add`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.subDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.subBorrow` (`mp_add`), `Tom.MpInt.ofDigits` (`mp_abs`)
-/

/-- `s_mp_sub(a, b, a)` with growth: the allocating contract -/
theorem Specs.s_mp_sub_correct_ca : Tom.Machine.Api.SSubGA.Statement :=
  Tom.Machine.Fn.SSubGAG5.correct
/-
Machine plumbing: entry `0x80004564`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator); stack reservation `F = 48 + MpGrow.F`; regions stk aS aD bS bD code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/SSubGA.lean
def Statement : Prop := Standard.Statement Res Q (site .aD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp : Nat); (a b : MpInt); (H : List (Nat × Nat))

/-- What `s_mp_sub(a, b, a)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The loops read the operands' digits below `used`. -/
  sa : p.a.Shape
  sb : p.b.Shape
  /-- `mp_grow`'s `int size` (`a->used`). -/
  size_lt : p.a.used < 2 ^ 31
  /-- The operands' digit arrays are nonempty (initialised `mp_int`s). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- `a`'s struct is off the arena (`mp_grow` reads and writes it). -/
  coff : OffHeap p.pa 24
  /-- The C's order: the subtrahend no longer than the minuend. -/
  ge : p.b.used ≤ p.a.used

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.a.alloc < p.a.used
  | some (_, x) => SSubPost p.a p.b (sSubIn p.a p.a) x

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.SSubPost` (`mp_add`), `Tom.sSubIn` (`mp_add`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.subDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.subBorrow` (`mp_add`), `Tom.MpInt.ofDigits` (`mp_abs`)
-/

/-- `s_mp_sub(a, b, b)` with growth: the allocating contract -/
theorem Specs.s_mp_sub_correct_cb : Tom.Machine.Api.SSubGB.Statement :=
  Tom.Machine.Fn.SSubGBG5.correct
/-
Machine plumbing: entry `0x80004564`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator); stack reservation `F = 48 + MpGrow.F`; regions stk aS aD bS bD code; written [.stk, .bS, .bD].

-- Tom/Machine/Api/SSubGB.lean
def Statement : Prop := Standard.Statement Res Q (site .bD)  -- the standard shape (top of file)

structure P where  (sp pa adp pb bdp : Nat); (a b : MpInt); (H : List (Nat × Nat))

/-- What `s_mp_sub(a, b, b)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  /-- The loops read the operands' digits below `used`. -/
  sa : p.a.Shape
  sb : p.b.Shape
  /-- `mp_grow`'s `int size` (`a->used`). -/
  size_lt : p.a.used < 2 ^ 31
  /-- The operands' digit arrays are nonempty (initialised `mp_int`s). -/
  apos : 0 < p.a.alloc
  bpos : 0 < p.b.alloc
  /-- `b`'s struct is off the arena (`mp_grow` reads and writes it). -/
  coff : OffHeap p.pb 24
  /-- The C's order: the subtrahend no longer than the minuend. -/
  ge : p.b.used ≤ p.a.used

def Q (p : P) : Option (Nat × MpInt) → Prop
  | none => p.b.alloc < p.a.used
  | some (_, x) => SSubPost p.a p.b (sSubIn p.a p.b) x

Also used (printed above): `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.SSubPost` (`mp_add`), `Tom.sSubIn` (`mp_add`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.subDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.MpInt.growTo` (`mp_abs`), `Tom.subBorrow` (`mp_add`), `Tom.MpInt.ofDigits` (`mp_abs`)
-/

namespace Tom.Machine.Api.SSub
open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Bin
/-- `s_mp_sub`: the standard contract -/
theorem _root_.Specs.s_mp_sub_correct_room {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat}
    {a b c : MpInt} {ra s0 : BitVec 64} (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Triple (At entry (Fn.SSub.entryL ra s0 sp pa pb pc) m v.keepR outp)
      (Ret m v outp sp pa adp pb bdp pc cdp a b c ra s0) :=
  Tom.Machine.Api.SSub.correct hP
end Tom.Machine.Api.SSub
/-
-- Tom/Machine/Api/SSub.lean
/-- What `s_mp_sub(a, b, c)` needs. -/
structure Pre (m : Mem) (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  rc : MpAt m pc cdp c
  sa : a.Shape
  sb : b.Shape
  sc : c.Shape
  csign : c.sign = Layout.mpZpos ∨ c.sign = Layout.mpNeg
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  gc : MpGeom pc cdp c.alloc
  ge : b.used ≤ a.used
  room : a.used ≤ c.alloc
  rs : Ram (sp - 48) 48
  sp_al : sp % 16 = 0
  sp_ge : 48 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  lay : Sound (lay sp pa adp pb bdp pc cdp a b c) isW

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp pc cdp a b c c' M

/-- What it leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp pc cdp : Nat) (a b c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  ssub : SSubPost a b c c'
  frame : Frm (lay sp pa adp pb bdp pc cdp a b c) ws m M

Also used (printed above): `Tom.SSubPost` (`mp_add`), `Tom.subDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.subBorrow` (`mp_add`)
-/

/-- `s_mp_sub` in place: the standard contracts -/
theorem Specs.s_mp_sub_correct_room_ca : Tom.Machine.Api.SSubAlias.StatementCA :=
  Tom.Machine.Fn.SSub.correctCA
/-
Machine plumbing: entry `0x80004564`; regions stk aS aD bS bD code.

-- Tom/Machine/Api/SSubAlias.lean
/-- **`s_mp_sub(a, b, a)` on the machine.** -/
def StatementCA : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    PreCA m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.SSub.entryL ra s0 sp pa pb pa) m v.keepR outp)
      (RetCA m v outp sp pa adp pb bdp a b ra s0)

/-- What `s_mp_sub(a, b, a)` needs. -/
structure PreCA (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop
    extends Base m 48 sp pa adp pb bdp a b ra where
  sa : a.Shape
  sb : b.Shape
  asign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg
  ge : b.used ≤ a.used
  lay : Sound (lay sp pa adp pb bdp a b) isWA

def RetCA (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostCA m sp pa adp pb bdp a b a' M

/-- What `s_mp_sub(a, b, a)` leaves: `a'` at `a`. -/
structure PostCA (m : Mem) (sp pa adp pb bdp : Nat) (a b a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  ssub : SSubPost a b a a'
  frame : Frm (lay sp pa adp pb bdp a b) wsA m M

Also used (printed above): `Tom.Machine.Api.BinA.Base` (`mp_add`), `Tom.Machine.Api.BinA.isWA` (`mp_add`), `Tom.SSubPost` (`mp_add`), `Tom.Machine.Api.BinA.wsA` (`mp_add`), `Tom.subDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.subBorrow` (`mp_add`)
-/

/-- `s_mp_sub` in place: the standard contracts -/
theorem Specs.s_mp_sub_correct_room_cb : Tom.Machine.Api.SSubAlias.StatementCB :=
  Tom.Machine.Fn.SSub.correctCB
/-
Machine plumbing: entry `0x80004564`; regions stk aS aD bS bD code.

-- Tom/Machine/Api/SSubAlias.lean
/-- **`s_mp_sub(a, b, b)` on the machine.** -/
def StatementCB : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    PreCB m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.SSub.entryL ra s0 sp pa pb pb) m v.keepR outp)
      (RetCB m v outp sp pa adp pb bdp a b ra s0)

/-- What `s_mp_sub(a, b, b)` needs. -/
structure PreCB (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop
    extends Base m 48 sp pa adp pb bdp a b ra where
  sa : a.Shape
  sb : b.Shape
  bsign : b.sign = Layout.mpZpos ∨ b.sign = Layout.mpNeg
  ge : b.used ≤ a.used
  room : a.used ≤ b.alloc
  lay : Sound (lay sp pa adp pb bdp a b) isWB

def RetCB (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ b' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostCB m sp pa adp pb bdp a b b' M

/-- What `s_mp_sub(a, b, b)` leaves: `b'` at `b`. -/
structure PostCB (m : Mem) (sp pa adp pb bdp : Nat) (a b b' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pb bdp b'
  ssub : SSubPost a b b b'
  frame : Frm (lay sp pa adp pb bdp a b) wsB m M

Also used (printed above): `Tom.Machine.Api.BinA.Base` (`mp_add`), `Tom.Machine.Api.BinA.isWB` (`mp_add`), `Tom.SSubPost` (`mp_add`), `Tom.Machine.Api.BinA.wsB` (`mp_add`), `Tom.subDigits` (`mp_add`), `Tom.clampUsed` (`mp_add`), `Tom.subBorrow` (`mp_add`)
-/

/-! ## `s_mp_toom_mul`

`mp_err s_mp_toom_mul(const mp_int *a, const mp_int *b, mp_int *c);`

Coverage: contract (Res.ih := Fn.MulGroupB.mulBelow _); c = a: Tom.Machine.Fn.ToomMulAG5.correct.
-/

/-- `s_mp_toom_mul(a, b, c)`, `c` distinct: the contract -/
theorem Specs.s_mp_toom_mul_correct : Tom.Machine.Api.ToomMul.Statement :=
  Tom.Machine.Fn.ToomMulG5.correct
/-
Machine plumbing: entry `0x800046e0`; the arguments: `a0 = a`, `a1 = b`, `a2 = c` (`gp` for the allocator and the cut-offs); stack reservation `F = Fm (μ p.a p.b)`; regions stk aS aD bS bD cS cD kc tc code; written [.stk, .cS, .cD].

-- Tom/Machine/Api/ToomMul.lean
/-- **`s_mp_toom_mul(a, b, c)` on the machine** (not proved). -/
def Statement : Prop := ∀ p : P, Spec p

def Spec (p : P) : Prop := MulAlg.SpecR entry Res p

structure Res (p : P) : Prop extends MulAlg.Base p where
  /-- `mp_mul`'s dispatch (`18fc`). -/
  tmin : 350 ≤ min p.a.used p.b.used
  tbal : max p.a.used p.b.used < 2 * min p.a.used p.b.used
  ih : MulRec.MulBelow (μ p.a p.b)

Also used (printed above): `Tom.Machine.Api.MpMul.P` (`mp_mul`), `Tom.Machine.Api.MulAlg.SpecR` (`s_mp_balance_mul`), `Tom.Machine.Api.MulAlg.Q` (`s_mp_balance_mul`), `Tom.Machine.Api.MulAlg.Base` (`s_mp_balance_mul`), `Tom.Machine.Api.MulRec.MulBelow` (`mp_mul`), `Tom.Machine.Api.MpMul.μ` (`mp_mul`), `Tom.Machine.Api.MpMul.X` (`mp_mul`), `Tom.Machine.Api.MulAlg.Out` (`s_mp_balance_mul`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MulRec.MulAt` (`mp_mul`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.MpMul.SpecR` (`mp_mul`), `Tom.Machine.Api.MpMul.ResU` (`mp_mul`), `Tom.Machine.Api.MpMulA.P` (`mp_mul`), `Tom.Machine.Api.MpMulA.Spec` (`mp_mul`), `Tom.Machine.Api.MpMul.Q` (`mp_mul`), `Tom.Machine.Api.MpMulA.SpecR` (`mp_mul`), `Tom.Machine.Api.MpMulA.Res` (`mp_mul`), `Tom.Machine.Api.MpMul.Out` (`mp_mul`), `Tom.Machine.Api.MpMulA.Q` (`mp_mul`), `Tom.MulPost` (`mp_mul`), `Tom.Machine.Api.MpMulA.Out` (`mp_mul`)
-/

/-- The algorithms of `mp_mul(a, b, a)`: their in-place contracts -/
theorem Specs.s_mp_toom_mul_correct_inplace : Tom.Machine.Api.ToomMulA.Statement :=
  Tom.Machine.Fn.ToomMulAG5.correct
/-
Machine plumbing: entry `0x800018a8`; the arguments: `a0 = a2 = a`, `a1 = b`; stack reservation `F = Fm (μ p.a p.b)`; regions stk aS aD bS bD kc tc code; written [.stk, .aS, .aD].

-- Tom/Machine/Api/MulAlgA.lean
/-- **`s_mp_toom_mul(a, b, a)` on the machine** (not proved). -/
def Statement : Prop := ∀ p : P, Spec p

def Spec (p : P) : Prop := MulAlgA.SpecR ToomMul.entry Res p

/-- What `s_mp_toom_mul(a, b, a)` needs (`ToomMul.Res` in place). -/
structure Res (p : P) : Prop extends MulAlgA.Base p where
  /-- `mp_mul`'s dispatch (`18fc`). -/
  tmin : 350 ≤ min p.a.used p.b.used
  tbal : max p.a.used p.b.used < 2 * min p.a.used p.b.used
  /-- The recursive `mp_mul`s below the measure. -/
  ih : MulRec.MulBelow (μ p.a p.b)

Also used (printed above): `Tom.Machine.Api.MpMulA.P` (`mp_mul`), `Tom.Machine.Api.MulAlgA.SpecR` (`s_mp_balance_mul`), `Tom.Machine.Api.MulAlgA.Q` (`s_mp_balance_mul`), `Tom.Machine.Api.MulAlgA.Base` (`s_mp_balance_mul`), `Tom.Machine.Api.MulRec.MulBelow` (`mp_mul`), `Tom.Machine.Api.MpMul.μ` (`mp_mul`), `Tom.Machine.Api.MpMul.X` (`mp_mul`), `Tom.Machine.Api.MulAlgA.Out` (`s_mp_balance_mul`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.MulRec.MulAt` (`mp_mul`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.MpMul.P` (`mp_mul`), `Tom.Machine.Api.MpMul.SpecR` (`mp_mul`), `Tom.Machine.Api.MpMul.ResU` (`mp_mul`), `Tom.Machine.Api.MpMulA.Spec` (`mp_mul`), `Tom.Machine.Api.MpMul.Q` (`mp_mul`), `Tom.Machine.Api.MpMulA.SpecR` (`mp_mul`), `Tom.Machine.Api.MpMulA.Res` (`mp_mul`), `Tom.Machine.Api.MpMul.Out` (`mp_mul`), `Tom.Machine.Api.MpMulA.Q` (`mp_mul`), `Tom.MulPost` (`mp_mul`), `Tom.Machine.Api.MpMulA.Out` (`mp_mul`)
-/

/-! ## `s_mp_toom_sqr`

`mp_err s_mp_toom_sqr(const mp_int *a, mp_int *b);`

Coverage: contract (its premise MpMulA.Statement := Fn.MulGroupB.mulCorrect.2).
-/

/-- `s_mp_toom_sqr(a, b)` (`b` distinct, and `b = a`): the contracts -/
theorem Specs.s_mp_toom_sqr_correct : Tom.Machine.Api.ToomSqr.Statement :=
  Tom.Machine.Fn.ToomSqrG5.correctClosed Tom.Machine.Fn.MulGroupB.mulCorrect.2
/-
Machine plumbing: entry `0x800072cc`.

-- Tom/Machine/Api/ToomSqr.lean
/-- **`s_mp_toom_sqr(a, b)` on the machine.** -/
def Statement : Prop := ∀ p : MpSqr.P, Spec p

def Spec (p : MpSqr.P) : Prop := SqrAlg.SpecR entry Res p

/-- What `s_mp_toom_sqr(a, b)` needs. -/
structure Res (p : MpSqr.P) : Prop extends SqrAlg.Base p where
  /-- `mp_sqr`'s dispatch: `a->used ≥ TOOM_SQR_CUTOFF = 400`. -/
  tmin : 400 ≤ p.a.used
  /-- The recursive `mp_sqr`s below the measure. -/
  ih : SqrRec.SqrBelow p.a.used

Also used (printed above): `Tom.Machine.Api.MpSqr.P` (`mp_sqr`), `Tom.Machine.Api.SqrAlg.SpecR` (`s_mp_karatsuba_sqr`), `Tom.Machine.Api.SqrAlg.Q` (`s_mp_karatsuba_sqr`), `Tom.Machine.Api.SqrAlg.Base` (`s_mp_karatsuba_sqr`), `Tom.Machine.Api.SqrRec.SqrBelow` (`mp_sqr`), `Tom.Machine.Api.MpSqr.X` (`mp_mul_2`), `Tom.Machine.Api.SqrAlg.Out` (`s_mp_karatsuba_sqr`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.SqrRec.SqrAt` (`mp_sqr`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.MpSqr.Spec` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.P` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Spec` (`mp_sqr`), `Tom.Machine.Api.MpSqr.SpecR` (`mp_sqr`), `Tom.Machine.Api.MpSqr.Res` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.SpecR` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Res` (`mp_sqr`), `Tom.Machine.Api.MpSqr.Q` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Q` (`mp_sqr`), `Tom.Machine.Api.MpSqr.Out` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Out` (`mp_sqr`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.SqrPost` (`mp_sqr`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`)
-/

/-- `s_mp_toom_sqr(a, b)` (`b` distinct, and `b = a`): the contracts -/
theorem Specs.s_mp_toom_sqr_correct_inplace : Tom.Machine.Api.ToomSqr.StatementA :=
  Tom.Machine.Fn.ToomSqrAG5.correctClosed Tom.Machine.Fn.MulGroupB.mulCorrect.2
/-
Machine plumbing: entry `0x800072cc`.

-- Tom/Machine/Api/ToomSqr.lean
/-- **`s_mp_toom_sqr(a, a)` on the machine.** -/
def StatementA : Prop := ∀ p : MpSqrA.P, SpecA p

def SpecA (p : MpSqrA.P) : Prop := SqrAlg.SpecRA entry ResA p

/-- What `s_mp_toom_sqr(a, a)` needs. -/
structure ResA (p : MpSqrA.P) : Prop extends SqrAlg.BaseA p where
  tmin : 400 ≤ p.a.used
  ih : SqrRec.SqrBelow p.a.used

Also used (printed above): `Tom.Machine.Api.MpSqrA.P` (`mp_sqr`), `Tom.Machine.Api.SqrAlg.SpecRA` (`s_mp_karatsuba_sqr`), `Tom.Machine.Api.SqrAlg.layA` (`s_mp_karatsuba_sqr`), `Tom.Machine.Api.SqrAlg.QA` (`s_mp_karatsuba_sqr`), `Tom.Machine.Api.SqrAlg.BaseA` (`s_mp_karatsuba_sqr`), `Tom.Machine.Api.SqrRec.SqrBelow` (`mp_sqr`), `Tom.Machine.Api.MpSqr.X` (`mp_mul_2`), `Tom.Machine.Api.SqrAlg.Out` (`s_mp_karatsuba_sqr`), `Tom.Machine.Std.StkRes` (`mp_2expt`), `Tom.Machine.Api.SqrAlg.FA` (`s_mp_karatsuba_sqr`), `Tom.Machine.Api.SqrRec.SqrAt` (`mp_sqr`), `Tom.Machine.Api.Alloc.heapEnd` (`mp_2expt`), `Tom.Machine.Api.MpSqr.P` (`mp_sqr`), `Tom.Machine.Api.MpSqr.Spec` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Spec` (`mp_sqr`), `Tom.Machine.Api.MpSqr.SpecR` (`mp_sqr`), `Tom.Machine.Api.MpSqr.Res` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.SpecR` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Res` (`mp_sqr`), `Tom.Machine.Api.MpSqr.Q` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Q` (`mp_sqr`), `Tom.Machine.Api.MpSqr.Out` (`mp_sqr`), `Tom.Machine.Api.MpSqrA.Out` (`mp_sqr`), `Tom.Machine.Api.Alloc.Shape` (`mp_clear`), `Tom.SqrPost` (`mp_sqr`), `Tom.Machine.Api.Alloc.Agree` (`mp_clear`), `Tom.Machine.Api.Alloc.HeapWit` (`mp_clear`), `Tom.Machine.Api.Alloc.Foot` (`mp_clear`), `Tom.Machine.Api.Alloc.Global` (`mp_clear`), `Tom.Machine.Api.Alloc.heapStart` (`mp_clear`), `Tom.Machine.Api.Alloc.InBlk` (`mp_clear`)
-/

/-! ## Appendix: the newlib and libgcc routines

The allocator (newlib's dlmalloc, with its locks and `sbrk`), `memset`/`memcpy`/`memmove` and libgcc's 64-bit multiply and divide, as the libtommath functions call them. Each theorem covers the routines listed with it (callees run inside the proof of their caller).
-/

-- _malloc_r, malloc, _sbrk_r, _sbrk, __malloc_lock, __malloc_unlock, __retarget_lock_acquire_recursive, __retarget_lock_release_recursive
namespace Tom.Machine.Fn.Alloc
open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Vsa.Machine (Config)
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc
open VsaIris VsaIris.VsaHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
/-- **`_malloc_r(reent, N)` on the machine.** -/
theorem _root_.Specs.malloc_r_correct {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)}
    {sp N : Nat} {ra : BitVec 64} (hC : Ctx m v sp depth ra) (hH : Heap m H) (hN : N < 2 ^ 64) :
    Triple (At mallocREntry (mallocRL ra N) m v.keep outp)
      (fun c => ∃ q M, At ra [(1, ra), (10, BitVec.ofNat 64 q)] M v.keep outp c ∧
        MallocRPost m M H sp N q) :=
  Tom.Machine.Fn.Alloc.mallocR_correct hC hH hN
end Tom.Machine.Fn.Alloc

-- free, _free_r, _malloc_trim_r
theorem Specs.free_correct : Tom.Machine.Api.Alloc.Free_Statement :=
  Tom.Machine.Fn.Alloc.free_correct

-- realloc, _realloc_r, memmove
theorem Specs.realloc_correct : Tom.Machine.Api.Alloc.Realloc_Statement :=
  Tom.Machine.Fn.Alloc.realloc_correct

-- calloc, _calloc_r, __errno
theorem Specs.calloc_correct : Tom.Machine.Api.Alloc.Calloc_Statement :=
  Tom.Machine.Fn.Calloc.calloc_correct

-- memset
namespace Tom.Machine.Fn.Memset
open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg
/-- **newlib `memset(d, c, n)` on the machine.** From its entry with `a0 = d`,
`a1 = c`, `a2 = n`, the return address `ra` and the callee-saved registers `w`,
the machine runs `memset` to `ra`, keeping `w`, with `a0 = d`, `[d, d + n)`
filled with the byte `c`, memory unchanged elsewhere, and the code intact. -/
theorem _root_.Specs.memset_correct (ra : BitVec 64) (w : Abi) (outp : Array String) (m : Mem) (d c n : Nat)
    (hra : ra.toNat % 4 = 0) (hP : Pre m d c n) :
    Triple (At entry (entryL ra d (BitVec.ofNat 64 c) n) m w.keep outp)
      (Ret ra w outp m d n (BitVec.ofNat 8 c)) :=
  Tom.Machine.Fn.Memset.correct ra w outp m d c n hra hP
end Tom.Machine.Fn.Memset

-- memcpy
namespace Tom.Machine.Fn.Memcpy
open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg
/-- **newlib `memcpy(d, s, n)` on the machine.** From its entry with `a0 = d`,
`a1 = s`, `a2 = n`, the return address `ra` and the callee-saved registers
`w`, for any `n` and any alignment of `d` and `s`, the machine runs `memcpy`
to `ra`, keeping `w`, with `a0 = d`, the `n` bytes of `s` at `d`, and memory
unchanged elsewhere. -/
theorem _root_.Specs.memcpy_correct (ra : BitVec 64) (w : Abi) (outp : Array String) (m : Mem) (d s n : Nat)
    (hra : ra.toNat % 4 = 0) (hP : Pre m d s n) :
    Triple (At entry (entL ra d s n) m w.keep outp) (Ret ra w outp m d s n) :=
  Tom.Machine.Fn.Memcpy.correct ra w outp m d s n hra hP
end Tom.Machine.Fn.Memcpy

-- __muldi3
theorem Specs.muldi3_correct : Tom.Machine.Api.Libgcc.Muldi3.Statement :=
  Tom.Machine.Fn.Libgcc.Muldi3.correct

-- __hidden___udivdi3
theorem Specs.udivdi3_correct : Tom.Machine.Api.Libgcc.Udivdi3.Statement :=
  Tom.Machine.Fn.Libgcc.Udivdi3.correct

-- __divdi3, __umoddi3
theorem Specs.divdi3_correct : Tom.Machine.Api.Libgcc.Divdi3.Statement :=
  Tom.Machine.Fn.Libgcc.Divdi3.correct

-- __moddi3
theorem Specs.moddi3_correct : Tom.Machine.Api.Libgcc.Moddi3.Statement :=
  Tom.Machine.Fn.Libgcc.Moddi3.correct
