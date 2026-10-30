import Tom.Machine.Api.StdHeapFn
import Tom.Spec.Gcd
import Tom.Spec.InvmodStep
import Tom.Spec.Init

/-!
# `mp_invmod`, `s_mp_invmod_fast`, `s_mp_invmod_slow`: the allocating contracts

`vendor/libtommath/bn_mp_invmod.c` at `0x8000150c` (43 instructions, frame 48): `b` negative or
`mp_cmp_d(b, 1) != MP_GT` → `MP_VAL`; `b` odd → tail call `s_mp_invmod_fast(a, b, c)`
(`0x80003338`, frame 192), else tail call `s_mp_invmod_slow(a, b, c)` (`0x80003670`, frame 256).
The two workers allocate their temporaries by `mp_init_multi` (six and eight), run the binary
extended Euclid (`Tom/Spec/Gcd.lean`) with in-place `mp_add`/`mp_sub` that may grow a temporary
(`Api/MpAddHA.lean`, `Api/MpSubH.lean`), and on success `mp_exch` the result into `c` and
`mp_clear_multi` the temporaries — so `c`'s old digits are freed and `c` ends on a temporary's
block: one site, `c`'s digits (`HPost`, `.regrow` from `c`'s block in front of `hin`).

The three share one shape (`P`, `R`, `lay`, …; the stack depth `F` is the deepest of the three,
`s_mp_invmod_slow`'s 256-byte frame and `mp_mod`'s 976), so the tail calls of `mp_invmod` map the
regions identically. The outcome `Out`:

* `err r`: the return value `r` (`MP_VAL` or `MP_MEM`), `c` and the heap as before;
* `ok q c'`: `MP_OKAY`, `c'` at `q` (the temporary's block `c` was exchanged with).

Residue beyond the C (`Base`): D5 for `mp_copy(b, &x)` (`b->used ≤ MP_DEFAULT_DIGIT_COUNT`, the
Spec steps' `Env.room`), `mp_mod`'s (`Api/MpMod.lean`: `a->used + 3 < 2^30`, the operands' live
blocks), the structs off the arena, `c` live (`mp_clear_multi` frees its old block). The
workers' own: `b` positive (as `mp_invmod` calls them); `s_mp_invmod_slow` also `b` even.

Growing: `BaseG` is `Base` without the D5 room: the workers' `mp_copy` into a temporary
grows it (`Api/MpCopyG.lean`), so `b` of any size. `InvmodFastG`, `InvmodSlowG`, `MpInvmodG` are the
statements over it (each `Statement.d5` gives the `Base` one).
-/

namespace Tom.Machine.Api.Invmod

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

/-- The stack depth: `s_mp_invmod_slow`'s 256-byte frame and `mp_mod`'s 976 (the deepest of the
three functions; `s_mp_invmod_fast` needs 192 + 976, `mp_invmod` 48 + `mp_cmp_d`'s none). -/
abbrev F : Nat := 1232

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  pc : Nat
  cdp : Nat
  a : MpInt
  b : MpInt
  c : MpInt
  H : List (Nat × Nat)

inductive R | stk | aS | aD | bS | bD | cS | cD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .bS, .bD, .cS, .cD, .code] := by cases r <;> simp

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .cS => ⟨p.pc, 24⟩
  | .cD => ⟨p.cdp, 4 * p.c.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .bS => .mpS p.pb p.bdp p.b
  | .bD => .mpD p.bdp p.b.alloc p.b.digit
  | .cS => .mpS p.pc p.cdp p.c
  | .cD => .mpD p.cdp p.c.alloc p.c.digit
  | .code => .code

/-- An error `r` (`c` as it was), or `MP_OKAY` with `c'`'s digits at `q`. -/
inductive Out
  | err (r : Int)
  | ok (q : Nat) (c' : MpInt)

def out (p : P) : Out → R → Kind
  | .ok q c', .cS => .mpS p.pc q c'
  | .ok q c', .cD => .mpD q c'.alloc c'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .cS | .cD => true
  | _ => false

def ws : List R := [.stk, .cS, .cD]

def site' (p : P) : Out → Iv
  | .ok q c' => ⟨q, 4 * c'.alloc⟩
  | .err _ => lay p .cD

/-- `c`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.cdp p.c :: p.H

def hout (p : P) : Out → List (Nat × Nat)
  | .ok q c' => (q, 4 * c'.alloc) :: p.H
  | .err _ => hin p

/-- The arguments: `a0 = a`, `a1 = b`, `a2 = c`. -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
   (12, BitVec.ofNat 64 p.pc)]

def rets (_ : P) (x : Out) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | .err r => BitVec.ofInt 64 r | .ok _ _ => 0#64)]

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

theorem Base.toG {p : P} (h : Base p) : BaseG p := { h with }

/-- A run of one of the three from `entry`, with residue `Res` and outcome `Q`. -/
def Spec (entry : BitVec 64) (Res : P → Prop) (Q : P → Out → Prop) : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .cD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.Invmod

namespace Tom.Machine.Api.InvmodFast

open Tom.Machine.Api.Invmod

def entry : BitVec 64 := 0x80003338#64

/-- What `s_mp_invmod_fast(a, b, c)` needs: `b` positive (as `mp_invmod` calls it). -/
structure Res (p : P) : Prop extends Base p where
  bz : p.b.sign = Layout.mpZpos

/-- `MP_MEM`, or what `InvmodFastPost` says. -/
def Q (p : P) : Out → Prop
  | .err r => r = Layout.mpMem ∨ InvmodFastPost p.a p.b p.c p.c r
  | .ok _ c' => InvmodFastPost p.a p.b p.c c' Layout.mpOkay

/-- An error code as the 64-bit word the code returns (`MP_MEM` or `MP_VAL`). -/
def errI (e : Nat) : Int := if e = 18446744073709551614 then Layout.mpMem else Layout.mpVal

/-- **`s_mp_invmod_fast(a, b, c)` on the machine.** -/
def Statement : Prop := Spec entry Res Q

end Tom.Machine.Api.InvmodFast

namespace Tom.Machine.Api.InvmodSlow

open Tom.Machine.Api.Invmod

def entry : BitVec 64 := 0x80003670#64

/-- What `s_mp_invmod_slow(a, b, c)` needs: `b` positive and **even**. -/
structure Res (p : P) : Prop extends Base p where
  bz : p.b.sign = Layout.mpZpos
  even : p.b.mag % 2 = 0

/-- `MP_MEM`, or what `InvmodSlowPost` says. -/
def Q (p : P) : Out → Prop
  | .err r => r = Layout.mpMem ∨ InvmodSlowPost p.a p.b p.c p.c r
  | .ok _ c' => InvmodSlowPost p.a p.b p.c c' Layout.mpOkay

/-- **`s_mp_invmod_slow(a, b, c)` on the machine.** -/
def Statement : Prop := Spec entry Res Q

end Tom.Machine.Api.InvmodSlow

namespace Tom.Machine.Api.MpInvmod

open Tom.Machine.Api.Invmod

def entry : BitVec 64 := 0x8000150c#64

/-- `MP_MEM`, or what `InvmodPost` says. -/
def Q (p : P) : Out → Prop
  | .err r => r = Layout.mpMem ∨ InvmodPost p.a p.b p.c p.c r
  | .ok _ c' => InvmodPost p.a p.b p.c c' Layout.mpOkay

/-- **`mp_invmod(a, b, c)` on the machine.** -/
def Statement : Prop := Spec entry Base Q

/-- `b` negative: `MP_VAL`. -/
theorem Q_neg {p : P} (h : p.b.sign = 1) : Q p (.err Layout.mpVal) :=
  .inr (InvmodStep.neg_exit (by simpa [Layout.mpNeg] using h))

/-- `mp_cmp_d(b, 1) != MP_GT`: `MP_VAL`. -/
theorem Q_le {p : P} (vb : p.b.Valid) (hn : ¬ p.b.sign = 1) (hc : ¬ cmpD p.b 1 = .gt) :
    Q p (.err Layout.mpVal) :=
  .inr (InvmodStep.le_exit vb (by simpa [Layout.mpNeg] using hn) hc)

/-- The tail call of `s_mp_invmod_fast`. -/
theorem Q_fast {p : P} {x : Out} (vb : p.b.Valid) (hn : ¬ p.b.sign = 1) (hc : cmpD p.b 1 = .gt)
    (ho : 0 < p.b.used ∧ p.b.digit 0 % 2 = 1) (h : InvmodFast.Q p x) : Q p x := by
  have hn' : ¬ p.b.sign = Layout.mpNeg := by simpa [Layout.mpNeg] using hn
  cases x with
  | err r => exact h.imp_right (InvmodStep.fast vb hn' hc ho)
  | ok q c' => exact InvmodStep.fast vb hn' hc ho h

/-- The tail call of `s_mp_invmod_slow`. -/
theorem Q_slow {p : P} {x : Out} (vb : p.b.Valid) (hn : ¬ p.b.sign = 1) (hc : cmpD p.b 1 = .gt)
    (he : ¬ (0 < p.b.used ∧ p.b.digit 0 % 2 = 1)) (h : InvmodSlow.Q p x) : Q p x := by
  have hn' : ¬ p.b.sign = Layout.mpNeg := by simpa [Layout.mpNeg] using hn
  cases x with
  | err r => exact h.imp_right (InvmodStep.slow vb hn' hc he)
  | ok q c' => exact InvmodStep.slow vb hn' hc he h

/-- `b` positive past the sign test. -/
theorem zpos {p : P} (vb : p.b.Valid) (hn : ¬ p.b.sign = 1) : p.b.sign = Layout.mpZpos :=
  InvmodStep.zpos_of vb (by simpa [Layout.mpNeg] using hn)

/-- `b` even (as `s_mp_invmod_slow` needs it) from the parity test. -/
theorem even {p : P} (vb : p.b.Valid) (hn : ¬ p.b.sign = 1)
    (he : ¬ p.b.digit 0 % 2 = 1) : p.b.mag % 2 = 0 := by
  have := InvmodFastStep.even_of
    (⟨vb, Nat.zero_le _, Nat.le_refl _, rfl, trivial⟩ : Ledger.Acct p.b 0 p.b.used p.b.val True)
    (fun ho => he ho.2)
  rw [Ledger.val_zpos (zpos vb hn)] at this; omega

end Tom.Machine.Api.MpInvmod

namespace Tom.Machine.Api.InvmodFastG

open Tom.Machine.Api.Invmod

/-- `s_mp_invmod_fast(a, b, c)` growing its temporaries: `BaseG`, `b` positive. -/
structure Res (p : P) : Prop extends BaseG p where
  bz : p.b.sign = Layout.mpZpos

/-- **`s_mp_invmod_fast(a, b, c)` on the machine, `b` of any size.** -/
def Statement : Prop := Spec InvmodFast.entry Res InvmodFast.Q

/-- The D5 statement follows. -/
theorem Statement.d5 (h : Statement) : InvmodFast.Statement := fun hra hres =>
  h hra { hres.toBase.toG with bz := hres.bz }

end Tom.Machine.Api.InvmodFastG

namespace Tom.Machine.Api.InvmodSlowG

open Tom.Machine.Api.Invmod

/-- `s_mp_invmod_slow(a, b, c)` growing its temporaries: `BaseG`, `b` positive and even. -/
structure Res (p : P) : Prop extends BaseG p where
  bz : p.b.sign = Layout.mpZpos
  even : p.b.mag % 2 = 0

/-- **`s_mp_invmod_slow(a, b, c)` on the machine, `b` of any size.** -/
def Statement : Prop := Spec InvmodSlow.entry Res InvmodSlow.Q

/-- The D5 statement follows. -/
theorem Statement.d5 (h : Statement) : InvmodSlow.Statement := fun hra hres =>
  h hra { hres.toBase.toG with bz := hres.bz, even := hres.even }

end Tom.Machine.Api.InvmodSlowG

namespace Tom.Machine.Api.MpInvmodG

open Tom.Machine.Api.Invmod

/-- **`mp_invmod(a, b, c)` on the machine, `b` of any size** (no D5 room). -/
def Statement : Prop := Spec MpInvmod.entry BaseG MpInvmod.Q

/-- The D5 statement follows. -/
theorem Statement.d5 (h : Statement) : MpInvmod.Statement := fun hra hres => h hra hres.toG

end Tom.Machine.Api.MpInvmodG

namespace Tom.Machine.Api.MpInvmodOf

open Tom.Machine.Api.Invmod

/-- `mp_invmod`'s residue with its (growing) workers' contracts as premises (`Fn/MpInvmodMainG.lean`
proves `Statement`; `Fn/Invmod.lean` closes it with the workers' proofs). -/
structure Res (p : P) : Prop extends BaseG p where
  fast : InvmodFastG.Statement
  slow : InvmodSlowG.Statement

def Statement : Prop := Spec MpInvmod.entry Res MpInvmod.Q

abbrev F : Nat := Invmod.F
abbrev hin : P → List (Nat × Nat) := Invmod.hin

end Tom.Machine.Api.MpInvmodOf
