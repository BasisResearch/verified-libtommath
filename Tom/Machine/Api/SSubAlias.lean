import Tom.Machine.Api.BinA
import Tom.Machine.Fn.SSub
import Tom.Spec.Sub

/-!
# `s_mp_sub` in place: the standard contracts

`s_mp_sub(a, b, a)` (`c = a`: `s_mp_sub(x, n, x)` in `mp_dr_reduce`,
`mp_montgomery_reduce`, `s_mp_sub(&t1, &t2, &t1)`, …) and `s_mp_sub(a, b, b)`
(`c = b`), over `BinA`'s regions (stack depth 48), for `b->used ≤ a->used`.
The contract is `SSubPost a b c c'` with `c` the destination operand as it
was at entry. The room assumption (D5, `c->alloc ≥ a->used`) is `a`'s own
shape when `c = a`, and `a->used ≤ b->alloc` when `c = b`.

The C behaves so: it reads `a->used`, `b->used`, `c->alloc` before it writes
`c->used := a->used`, and `a->dp`, `b->dp` after it (past `used`); loop 1
reads `a->dp[i]`, `b->dp[i]` and loop 2 `a->dp[i]` before writing
`c->dp[i]`; `olduse` is the operand's `used ≤ a->used`, so
`MP_ZERO_DIGITS` clears nothing; `mp_clamp(c)` comes last.
-/

namespace Tom.Machine.Api.SSubAlias

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.BinA

abbrev lay (sp pa adp pb bdp : Nat) (a b : MpInt) := BinA.lay 48 sp pa adp pb bdp a b

/-- What `s_mp_sub(a, b, a)` needs. -/
structure PreCA (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop
    extends Base m 48 sp pa adp pb bdp a b ra where
  sa : a.Shape
  sb : b.Shape
  asign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg
  ge : b.used ≤ a.used
  lay : Sound (lay sp pa adp pb bdp a b) isWA

/-- What `s_mp_sub(a, b, b)` needs. -/
structure PreCB (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop
    extends Base m 48 sp pa adp pb bdp a b ra where
  sa : a.Shape
  sb : b.Shape
  bsign : b.sign = Layout.mpZpos ∨ b.sign = Layout.mpNeg
  ge : b.used ≤ a.used
  room : a.used ≤ b.alloc
  lay : Sound (lay sp pa adp pb bdp a b) isWB

/-- What `s_mp_sub(a, b, a)` leaves: `a'` at `a`. -/
structure PostCA (m : Mem) (sp pa adp pb bdp : Nat) (a b a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  ssub : SSubPost a b a a'
  frame : Frm (lay sp pa adp pb bdp a b) wsA m M

/-- What `s_mp_sub(a, b, b)` leaves: `b'` at `b`. -/
structure PostCB (m : Mem) (sp pa adp pb bdp : Nat) (a b b' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pb bdp b'
  ssub : SSubPost a b b b'
  frame : Frm (lay sp pa adp pb bdp a b) wsB m M

def RetCA (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostCA m sp pa adp pb bdp a b a' M

def RetCB (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ b' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostCB m sp pa adp pb bdp a b b' M

def entry : BitVec 64 := 0x80004564#64

/-- **`s_mp_sub(a, b, a)` on the machine.** -/
def StatementCA : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    PreCA m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.SSub.entryL ra s0 sp pa pb pa) m v.keepR outp)
      (RetCA m v outp sp pa adp pb bdp a b ra s0)

/-- **`s_mp_sub(a, b, b)` on the machine.** -/
def StatementCB : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    PreCB m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.SSub.entryL ra s0 sp pa pb pb) m v.keepR outp)
      (RetCB m v outp sp pa adp pb bdp a b ra s0)

end Tom.Machine.Api.SSubAlias
