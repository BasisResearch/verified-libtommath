import Tom.Machine.Api.StdHeapFn

/-!
# The conventions of SPECS.lean (read this file once)

Every public specification in SPECS.lean has one shape (Islaris's memcpy specifications differ
"only in the calling convention, system registers, valid ranges of memory"; RefinedC's `ℓ @ &own(τ)`
gives one ownership predicate per argument):

    theorem Specs.mp_f … (cv : Conv m ra sp F hin) (a : MpOwn m H pa adp a) … (y : MpOut m py ydp y)
        (side conditions) :
        ApiTriple m v outp ra entry sp [pa, …, py] ret fun x M => meaning x ∧ HPost … m M

* `MpOwn`: an `mp_int` argument the call reads: its struct and digits in memory, its value valid,
  its digits a live heap block. `MpOut`: an `mp_int` the call writes (initialized, `Shape` only);
  its digit block is the front of the heap's live list `hin`.
* `Conv`: the calling convention: `ra`, the stack of `F` bytes below `sp`, the program image, the
  allocator's heap with the live blocks `hin`. `Cutoffs`: the four cut-off words `mp_mul`/`mp_sqr`
  read (constants of the image's data section).
* `ApiTriple`: total correctness on the Sail RISC-V model: from the entry with the arguments
  in `a0, a1, …`, the run returns to `ra` with `a0 = ret x` for some outcome `x` and memory `M`
  satisfying the post. The post states the result over `Int`/`Nat` first (`OptRes`: `MP_MEM` or the
  written value's meaning), then the frame `HPost` (`Kit/MeetHeap.lean`: only the written regions and
  the allocator's footprint change, the result's digits are the new front block).
* `Sound (lay p) isW` (`Kit/Frame.lean`) stays as stated: the regions written are disjoint from
  every other region (the aliasing a form allows is the one its argument list shows).
* The calls that do not allocate: `MpVal` (a valid `mp_int` in memory), `ConvL`/`ConvS` (the
  convention without the heap), `ApiPure` (a leaf: a value in `a0`, memory unchanged) and
  `ApiTripleS` (the frame-pointer calls writing an `mp_int` in place); `DigOut`/`BufOut` an
  `mp_digit *`/`char *` result.

Each specification is proved from the machine contract (`…Statement`) by one bridging proof (the
second half of this file): the contract's precondition fields are projections of these
structures; its region witnesses and off-allocator facts come from `Reg.call` (one lemma for every
contract), the tactic `mp_regions` choosing per region the `MpOwn`/`MpOut`/`Conv`/`Cutoffs`/`DigOut`
lemma that backs it; `ApiTriple.of`/`ApiTripleS.of` turn the contract's triple into the concise
one given its outcome's `.spec` lemma. The statements fully unfolded (no structure of this file)
are in SPECS_UNFOLDED.lean.
-/

namespace Tom.Machine

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

/-! ## Arguments -/

/-- **A valid `mp_int` in memory**, `a` at `p`: the struct at `p` holds `a`'s
`used`/`alloc`/`sign` and the digit pointer `dp`, the `a.alloc` digits at `dp` are `a`'s, and `a`
is valid (clamped, digits below the radix, zero positive). -/
structure MpVal (m : Mem) (p dp : Nat) (a : MpInt) : Prop where
  valid : a.Valid
  hdr : Hdr m p dp a
  dig : Dig m dp a.alloc a.digit

/-- **An `mp_int` argument of an allocating call** (RefinedC `a @ &own(mp_int)`): `MpVal`, with a
digit, its struct off the allocator's memory and its digits a live block of `H`. -/
structure MpOwn (m : Mem) (H : List (Nat × Nat)) (p dp : Nat) (a : MpInt) : Prop extends MpVal m p dp a where
  pos : 0 < a.alloc
  off : OffHeap p 24
  blk : digBlk dp a ∈ H

/-- **An `mp_int` the call writes** `a` at `p`: as `MpOwn`, initialized (`Shape`: its digits below
the radix, `used ≤ alloc`; not necessarily clamped; its sign `MP_ZPOS` or `MP_NEG`); its digits
are the front block of the heap's list (the call may free and replace them). -/
structure MpOut (m : Mem) (p dp : Nat) (a : MpInt) : Prop where
  shape : a.Shape
  sign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg
  pos : 0 < a.alloc
  off : OffHeap p 24
  hdr : Hdr m p dp a
  dig : Dig m dp a.alloc a.digit

/-- **A result digit `*d`** (an `mp_digit *` argument): a 4-aligned word at `d ≠ 0` off the
allocator's memory, holding `v` before the call. -/
structure DigOut (m : Mem) (d v : Nat) : Prop where
  nn : d ≠ 0
  off : OffHeap d 4
  dig : Dig m d 1 fun _ => v

/-- **An output buffer** of `n` bytes at `b` (a `char *` argument): RAM off the allocator's
memory, holding the bytes of `m0` (the caller's snapshot of it). -/
structure BufOut (m m0 : Mem) (b n : Nat) : Prop where
  off : OffHeap b n
  ram : Ram b n
  snap : ∀ x, (Iv.mk b n).In x → m[x]? = m0[x]?

/-- `mp_count_bits(a)` and `a->used * MP_DIGIT_BIT` are C `int`s. -/
def Fits (a : MpInt) : Prop := Layout.digitBits * a.used < 2 ^ 31

/-- **The calling convention**: `ra` a code address, `F` bytes of stack below `sp` above the
allocator's arena (`sp` 16-aligned), the program image in memory, the allocator's heap with the
live blocks `H`. -/
structure Conv (m : Mem) (ra : BitVec 64) (sp F : Nat) (H : List (Nat × Nat)) : Prop where
  ra_al : ra.toNat % 4 = 0
  stk : StkRes sp F
  img : Img m
  heap : AHeap m H

/-- **The calling convention of a call that does not allocate**: `ra` a code address and the
program image (`ConvS`: and `F` bytes of stack below `sp`, as `Conv`). -/
structure ConvL (m : Mem) (ra : BitVec 64) : Prop where
  ra_al : ra.toNat % 4 = 0
  img : Img m

structure ConvS (m : Mem) (ra : BitVec 64) (sp F : Nat) : Prop extends ConvL m ra where
  stk : StkRes sp F

/-- The cut-off words `mp_mul`/`mp_sqr` read: `KARATSUBA_SQR_CUTOFF`, `TOOM_SQR_CUTOFF`,
`KARATSUBA_MUL_CUTOFF`, `TOOM_MUL_CUTOFF` (`nm c/tommath-arith.elf`). -/
structure Cutoffs (m : Mem) : Prop where
  ks : Dig m 0x800194f8 1 fun _ => 120
  ts : Dig m 0x800194f0 1 fun _ => 400
  kc : Dig m 0x800194fc 1 fun _ => 80
  tc : Dig m 0x800194f4 1 fun _ => 350

/-! ## The call -/

/-- The argument registers `a0, a1, …` (from `x10`) holding the list. -/
def callArgs : Nat → List Nat → GRegs
  | _, [] => []
  | i, a :: rest => (i, BitVec.ofNat 64 a) :: callArgs (i + 1) rest

/-- **The call `f(args)`** from `entry`, `sp` and `gp` set, returning to `ra`: total correctness on the
Sail model; the run ends at `ra` with `a0 = ret x` for an outcome `x` and memory `M` with
`post x M` (registers `keep`: callee-saved, `gp`, `tp`, preserved; console output `outp`
unchanged). -/
def ApiTriple (m : Mem) (v : Abi) (outp : Array String) (ra entry : BitVec 64) (sp : Nat)
    (args : List Nat) {X : Type} (ret : X → BitVec 64) (post : X → Mem → Prop) : Prop :=
  Triple (At entry ((1, ra) :: (2, BitVec.ofNat 64 sp) :: (3, gpV) :: callArgs 10 args) m v.keep outp)
    fun cf => ∃ x M, At ra [(1, ra), (10, ret x)] M v.keep outp cf ∧ post x M

/-- **A pure call `f(args)`** (a leaf: no stack, memory unchanged) returning `ret` in `a0`. -/
def ApiPure (m : Mem) (v : Abi) (outp : Array String) (ra entry : BitVec 64) (args : List Nat)
    (ret : BitVec 64) : Prop :=
  Triple (At entry ((1, ra) :: callArgs 10 args) m v.keep outp)
    fun cf => At ra [(1, ra), (10, ret)] m v.keep outp cf

/-- **A call `f(args)` with a frame pointer** (`s0`; the callee-saved registers `keepR`) writing
an `mp_int` `a'` in place: the run returns to `ra` with `a0 = ret`, `sp` and `s0` as they were,
memory `M` with `post a' M`. -/
def ApiTripleS (m : Mem) (v : Abi) (outp : Array String) (ra s0 entry : BitVec 64) (sp : Nat)
    (args : List Nat) (ret : BitVec 64) (post : MpInt → Mem → Prop) : Prop :=
  Triple (At entry ((1, ra) :: (2, BitVec.ofNat 64 sp) :: (8, s0) :: callArgs 10 args) m v.keepR outp)
    fun cf => ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, ret)] M v.keepR outp cf ∧
      post a' M

/-- `ApiTripleS` from a machine contract and the meaning `ok` of its post `Q`. -/
theorem ApiTripleS.of {m : Mem} {v : Abi} {outp : Array String} {ra s0 entry : BitVec 64} {sp : Nat}
    {args : List Nat} {ret : BitVec 64} {L R : GRegs} {Q : MpInt → Mem → Prop} {ok : MpInt → Prop}
    (h : Triple (At entry L m v.keepR outp) fun cf => ∃ a' M, At ra R M v.keepR outp cf ∧ Q a' M)
    (hq : ∀ a' M, Q a' M → ok a')
    (hL : L = (1, ra) :: (2, BitVec.ofNat 64 sp) :: (8, s0) :: callArgs 10 args := by rfl)
    (hR : R = [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, ret)] := by rfl) :
    ApiTripleS m v outp ra s0 entry sp args ret fun a' M => ok a' ∧ Q a' M := by
  subst hL hR
  exact Triple.rmap (fun _ ⟨a', M, hat, hQ⟩ => ⟨a', M, hat, hq a' M hQ, hQ⟩) h

/-- **From a machine contract**: its triple and its outcome predicate `Q` implying the readable
one `Q'` (its argument and return registers are those of `ApiTriple`, by `rfl` per outcome). -/
theorem ApiTriple.of {m : Mem} {v : Abi} {outp : Array String} {ra entry : BitVec 64} {sp : Nat}
    {args : List Nat} {X : Type} {ret : X → BitVec 64} {L : GRegs} {rets : X → GRegs}
    {Q Q' : X → Prop} {Fr : X → Mem → Prop}
    (h : Triple (At entry L m v.keep outp) fun cf => ∃ x M, At ra (rets x) M v.keep outp cf ∧ Q x ∧ Fr x M)
    (hq : ∀ x, Q x → Q' x)
    (hL : L = (1, ra) :: (2, BitVec.ofNat 64 sp) :: (3, gpV) :: callArgs 10 args := by rfl)
    (hr : ∀ x, rets x = [(1, ra), (10, ret x)] := by intro x; cases x <;> rfl) :
    ApiTriple m v outp ra entry sp args ret fun x M => Q' x ∧ Fr x M := by
  subst hL
  exact Triple.rmap (fun _ ⟨x, M, hat, hQ, hF⟩ => ⟨x, M, hr x ▸ hat, hq x hQ, hF⟩) h

/-- `MP_MEM` or `MP_OKAY` in `a0` (`none`: `MP_MEM`). -/
def optRet {α : Type} : Option α → BitVec 64
  | none => Api.MpGrow.memBV
  | some _ => 0#64

/-- **The outcome of a call that may run out of memory**: `none` (`MP_MEM`, then `mem`) or
`some (q, a')`, the value `a'` written (its digits at `q`), then `ok a'`. -/
def OptRes (x : Option (Nat × MpInt)) (mem : Prop) (ok : MpInt → Prop) : Prop :=
  match x with
  | none => mem
  | some (_, a') => ok a'

/-- `MP_OKAY` or `MP_MEM` in `a0` by the outcome's flag (`(ok, q, a')`). -/
def okRet (x : Bool × Nat × MpInt) : BitVec 64 := if x.1 = true then 0#64 else Api.MpInit.memBV

/-- **The outcome `(ok, q, a')` of a call that may run out of memory**: on `MP_OKAY` (`ok`), `post`
of the value `a'` written (its digits at `q`). -/
def OkRes (x : Bool × Nat × MpInt) (post : MpInt → Prop) : Prop := x.1 = true → post x.2.2

/-! ## The bridge: region witnesses from the arguments -/

theorem MpVal.mpAt {m p dp a} (o : MpVal m p dp a) : MpAt m p dp a := o.hdr.mpAt o.dig
theorem MpVal.geom {m p dp a} (o : MpVal m p dp a) : MpGeom p dp a.alloc := o.hdr.geom
theorem MpOut.mpAt {m p dp a} (o : MpOut m p dp a) : MpAt m p dp a := o.hdr.mpAt o.dig
theorem MpOut.geom {m p dp a} (o : MpOut m p dp a) : MpGeom p dp a.alloc := o.hdr.geom
theorem ConvS.sp_ge {m ra sp F} (c : ConvS m ra sp F) : F ≤ sp := by have := c.stk.lo; omega

/-- A region `I` of kind `k` is backed in `m`: the kind's footprint fits `I`, its witness holds,
and `I` lies off the allocator for the blocks `H`. -/
structure Reg (m : Mem) (H : List (Nat × Nat)) (k : Kind) (I : Iv) : Prop where
  fits : k.Fits I
  wit : k.Wit I m
  off : Off I H

/-- **The one bridging lemma**: a contract whose regions are all backed applies, its witness
bundle and its off-allocator premise built from the backings (`h`, by `mp_regions`). -/
theorem Reg.call {ι : Type} {ρ : ι → Iv} {κ : ι → Kind} {m : Mem} {H : List (Nat × Nat)} {T : Prop}
    (f : Bundle ρ κ m → AHeap m H → (∀ r, Off (ρ r) H) → T) (hh : AHeap m H)
    (h : ∀ r, Reg m H (κ r) (ρ r)) : T :=
  f (fun r => ⟨(h r).fits, (h r).wit⟩) hh fun r => (h r).off

theorem Std.StkRes.ram {sp F : Nat} (h : StkRes sp F) : Ram (sp - F) F := by
  have := h.lo; have := h.hi
  have eE : heapEnd = 0x87800000 := rfl; have eT : tohostAddr = 0x80018880 := rfl
  exact ⟨by omega, by omega, .inr (by omega)⟩

/-- The stack region, matched by its length first (`rfl`): unifying another region's address with
`sp - F` would unfold `Nat.sub` along the literal `F`. -/
theorem Conv.regStk {m ra sp F H} (c : Conv m ra sp F H) {H' : List (Nat × Nat)} {I : Iv}
    (hl : I.len = F) (hb : I.base = sp - F) : Reg m H' .ram I := by
  obtain ⟨b, l⟩ := I; simp only at hl hb; subst hl hb
  exact ⟨trivial, c.stk.ram, Off.of_offHeap c.stk.off (by
    have := c.stk.lo; have e : heapEnd = 0x87800000 := rfl; simp only; omega)⟩

theorem Conv.regCode {m ra sp F H} (c : Conv m ra sp F H) {H' : List (Nat × Nat)} :
    Reg m H' .code textIv :=
  ⟨Iv.sub_self _, c.img, Off.text _⟩

theorem Hdr.off {m : Mem} {p dp : Nat} {a : MpInt} (h : Hdr m p dp a) (ho : OffHeap p 24)
    {H : List (Nat × Nat)} : Off ⟨p, 24⟩ H :=
  Off.of_offHeap ho (by have := h.geom.st.lo_ge; simpa using this)

theorem MpOwn.regS {m H p dp a} (o : MpOwn m H p dp a) {H' : List (Nat × Nat)} :
    Reg m H' (.mpS p dp a) ⟨p, 24⟩ :=
  ⟨Iv.sub_self _, o.hdr, o.hdr.off o.off⟩

theorem Dig.off {m : Mem} {H : List (Nat × Nat)} {dp : Nat} {a : MpInt} (hh : AHeap m H)
    (hb : digBlk dp a ∈ H) (hp : 0 < a.alloc) : Off ⟨dp, 4 * a.alloc⟩ H :=
  Off.of_blk hh.heap hb (by simp only; omega)

/-- An argument's digits, the contract's heap list being `H`. -/
theorem MpOwn.regD {m H p dp a} (o : MpOwn m H p dp a) (hh : AHeap m H) :
    Reg m H (.mpD dp a.alloc a.digit) ⟨dp, 4 * a.alloc⟩ :=
  ⟨Iv.sub_self _, o.dig, Dig.off hh o.blk o.pos⟩

/-- An argument's digits, the contract's heap list being `b :: H` (an output's block in front). -/
theorem MpOwn.regD' {m H p dp a} (o : MpOwn m H p dp a) {b : Nat × Nat} (hh : AHeap m (b :: H)) :
    Reg m (b :: H) (.mpD dp a.alloc a.digit) ⟨dp, 4 * a.alloc⟩ :=
  ⟨Iv.sub_self _, o.dig, Dig.off hh (List.mem_cons_of_mem _ o.blk) o.pos⟩

/-- An argument's digits, the contract's heap list containing `H`. -/
theorem MpOwn.regDin {m H p dp a} (o : MpOwn m H p dp a) {H' : List (Nat × Nat)} (hh : AHeap m H')
    (hs : ∀ e ∈ H, e ∈ H') : Reg m H' (.mpD dp a.alloc a.digit) ⟨dp, 4 * a.alloc⟩ :=
  ⟨Iv.sub_self _, o.dig, Dig.off hh (hs _ o.blk) o.pos⟩

theorem MpOut.regS {m p dp a} (o : MpOut m p dp a) {H' : List (Nat × Nat)} :
    Reg m H' (.mpS p dp a) ⟨p, 24⟩ :=
  ⟨Iv.sub_self _, o.hdr, o.hdr.off o.off⟩

theorem MpOut.regD {m p dp a} (o : MpOut m p dp a) {H : List (Nat × Nat)}
    (hh : AHeap m (digBlk dp a :: H)) :
    Reg m (digBlk dp a :: H) (.mpD dp a.alloc a.digit) ⟨dp, 4 * a.alloc⟩ :=
  ⟨Iv.sub_self _, o.dig, Dig.off hh (List.mem_cons_self ..) o.pos⟩

theorem DigOut.regD {m d v} (o : DigOut m d v) {H : List (Nat × Nat)} :
    Reg m H (.mpD d 1 fun _ => v) ⟨d, 4 * 1⟩ :=
  ⟨Iv.sub_self _, o.dig, Off.of_offHeap o.off (by have := o.dig.ram.lo_ge; simpa using this)⟩

theorem DigOut.regW {m d v} (o : DigOut m d v) {H : List (Nat × Nat)} {I : Iv}
    (hl : I.len = 4) (hb : I.base = d) : Reg m H .ram I := by
  obtain ⟨b, l⟩ := I; simp only at hl hb; subst hl hb
  exact ⟨trivial, o.dig.ram, Off.of_offHeap o.off (by have := o.dig.ram.lo_ge; simpa using this)⟩

/-- A written argument's digits, a live block of the contract's heap list (not its front). -/
theorem MpOut.regDin {m p dp a} (o : MpOut m p dp a) {H : List (Nat × Nat)} (hh : AHeap m H)
    (hb : digBlk dp a ∈ H) : Reg m H (.mpD dp a.alloc a.digit) ⟨dp, 4 * a.alloc⟩ :=
  ⟨Iv.sub_self _, o.dig, Dig.off hh hb o.pos⟩

theorem BufOut.regFrz {m m0 b n} (o : BufOut m m0 b n) {H : List (Nat × Nat)} :
    Reg m H (.frz m0) ⟨b, n⟩ :=
  ⟨trivial, ⟨o.ram, o.snap⟩, Off.of_offHeap o.off (by have := o.ram.lo_ge; simpa using this)⟩

/-- The cut-off words lie between the allocator's globals and its arena. -/
theorem off_word {a : Nat} (h1 : 0x800194f0 ≤ a) (h2 : a + 4 ≤ 0x80019500) {H : List (Nat × Nat)} :
    Off ⟨a, 4⟩ H :=
  ⟨by simp only; omega, fun x hx hf => by
    simp only [Iv.In] at hx
    have eS : heapStart = 0x80019d10 := rfl
    rcases hf with (hg | ⟨hs, _, _⟩) | hi
    · unfold Global at hg; omega
    · omega
    · unfold ImpI impurePtr at hi; omega,
   fun h => by simp at h⟩

theorem Cutoffs.regKs {m} (c : Cutoffs m) {H : List (Nat × Nat)} :
    Reg m H (.mpD 0x800194f8 1 fun _ => 120) ⟨0x800194f8, 4⟩ :=
  ⟨Iv.sub_self _, c.ks, off_word (by decide) (by decide)⟩
theorem Cutoffs.regTs {m} (c : Cutoffs m) {H : List (Nat × Nat)} :
    Reg m H (.mpD 0x800194f0 1 fun _ => 400) ⟨0x800194f0, 4⟩ :=
  ⟨Iv.sub_self _, c.ts, off_word (by decide) (by decide)⟩
theorem Cutoffs.regKc {m} (c : Cutoffs m) {H : List (Nat × Nat)} :
    Reg m H (.mpD 0x800194fc 1 fun _ => 80) ⟨0x800194fc, 4⟩ :=
  ⟨Iv.sub_self _, c.kc, off_word (by decide) (by decide)⟩
theorem Cutoffs.regTc {m} (c : Cutoffs m) {H : List (Nat × Nat)} :
    Reg m H (.mpD 0x800194f4 1 fun _ => 350) ⟨0x800194f4, 4⟩ :=
  ⟨Iv.sub_self _, c.tc, off_word (by decide) (by decide)⟩

/-- `∀ r, Reg m H (kind r) (lay r)`, region by region: the first of the backing lemmas above
whose kind and interval match, with its argument found among the hypotheses. -/
macro "mp_regions" : tactic => `(tactic| (intro r; cases r <;> first
  | exact Conv.regStk ‹_› rfl rfl | exact DigOut.regW ‹_› rfl rfl | exact Conv.regCode ‹_›
  | exact MpOwn.regS ‹_› | exact MpOut.regS ‹_›
  | exact MpOut.regD ‹_› (Conv.heap ‹_›)
  | exact MpOwn.regD ‹_› (Conv.heap ‹_›) | exact MpOwn.regD' ‹_› (Conv.heap ‹_›)
  | exact MpOwn.regDin ‹_› (Conv.heap ‹_›) (fun _ he => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
  | exact MpOut.regDin ‹_› (Conv.heap ‹_›) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  | exact MpOut.regDin ‹_› (Conv.heap ‹_›) ‹_›
  | exact Cutoffs.regKs ‹_› | exact Cutoffs.regTs ‹_› | exact Cutoffs.regKc ‹_›
  | exact Cutoffs.regTc ‹_› | exact DigOut.regD ‹_›
  | exact BufOut.regFrz ‹_›))

end Tom.Machine
