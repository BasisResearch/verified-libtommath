import Tom.Machine.Api.BinA
import Tom.Machine.Fn.SSub
import Tom.Spec.Signed

/-!
# `mp_sub` in place: the standard contracts

`mp_sub(a, b, a)` (`c = a`: `mp_sub(&x, &t1, &x)`, …) and `mp_sub(a, b, b)`
(`c = b`), over `BinA`'s regions (stack depth 64: its own frame of 48 bytes
and the tail-called `s_mp_add`'s). The contract is `SubPost a b c c'` with
`c` the destination operand as it was at entry, and the room assumption
(D5) is on it.

The C behaves so: it reads both signs first; in the same-sign branch it
calls `mp_cmp_mag(a, b)` (read-only) before any store; then it stores
`c->sign` and tail-calls `s_mp_add`/`s_mp_sub`, which see the destination
operand with that sign. The branch's `…Post` is the same as for a distinct
`c` started from the destination with that sign, because `SAddPost` and
`SSubPost` do not read the operands' signs (`Tom/Spec/Alias.lean`).
-/

namespace Tom.Machine.Api.MpSubAlias

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.BinA

abbrev lay (sp pa adp pb bdp : Nat) (a b : MpInt) := BinA.lay 64 sp pa adp pb bdp a b

/-- What `mp_sub(a, b, a)` needs. -/
structure PreCA (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop
    extends Base m 64 sp pa adp pb bdp a b ra where
  va : a.Valid
  vb : b.Valid
  room : max a.used b.used + 1 ≤ a.alloc
  lay : Sound (lay sp pa adp pb bdp a b) isWA

/-- What `mp_sub(a, b, b)` needs. -/
structure PreCB (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop
    extends Base m 64 sp pa adp pb bdp a b ra where
  va : a.Valid
  vb : b.Valid
  room : max a.used b.used + 1 ≤ b.alloc
  lay : Sound (lay sp pa adp pb bdp a b) isWB

/-- What `mp_sub(a, b, a)` leaves: `a'` at `a`. -/
structure PostCA (m : Mem) (sp pa adp pb bdp : Nat) (a b a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  sub : SubPost a b a a'
  frame : Frm (lay sp pa adp pb bdp a b) wsA m M

/-- What `mp_sub(a, b, b)` leaves: `b'` at `b`. -/
structure PostCB (m : Mem) (sp pa adp pb bdp : Nat) (a b b' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pb bdp b'
  sub : SubPost a b b b'
  frame : Frm (lay sp pa adp pb bdp a b) wsB m M

def RetCA (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostCA m sp pa adp pb bdp a b a' M

def RetCB (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ b' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostCB m sp pa adp pb bdp a b b' M

def entry : BitVec 64 := 0x80001ef4#64

/-- **`mp_sub(a, b, a)` on the machine.** -/
def StatementCA : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    PreCA m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.SSub.entryL ra s0 sp pa pb pa) m v.keepR outp)
      (RetCA m v outp sp pa adp pb bdp a b ra s0)

/-- **`mp_sub(a, b, b)` on the machine.** -/
def StatementCB : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    PreCB m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.SSub.entryL ra s0 sp pa pb pb) m v.keepR outp)
      (RetCB m v outp sp pa adp pb bdp a b ra s0)

end Tom.Machine.Api.MpSubAlias
