import Tom.Machine.Api.BinA
import Tom.Machine.Fn.SAdd

/-!
# `s_mp_add` in place: the standard contracts

`s_mp_add(a, b, a)` (`c = a`: `mp_reduce_2k`'s `s_mp_add(a, &q, a)`, …) and
`s_mp_add(a, b, b)` (`c = b`), over `BinA`'s regions (stack depth 64). The
destination is the operand, so the contract is `SAddPost a b c c'` with `c`
the operand as it was at entry, and the room assumption (D5) is on it:
`max(a->used, b->used) + 1 ≤ a->alloc` (resp. `b->alloc`).

The C behaves so: it reads `a->used`, `b->used` before it writes
`c->used := max + 1`; the digit pointers are not written; both loops read
`a->dp[i]`, `b->dp[i]` (resp. `x->dp[i]`) before they write `c->dp[i]`; the
carry goes to `c->dp[max]`, above every digit read; `olduse` is the operand's
`used ≤ max`, so `MP_ZERO_DIGITS` clears nothing; `mp_clamp(c)` comes last.
-/

namespace Tom.Machine.Api.SAddAlias

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.BinA

abbrev lay (sp pa adp pb bdp : Nat) (a b : MpInt) := BinA.lay 64 sp pa adp pb bdp a b

/-- What `s_mp_add(a, b, a)` needs. -/
structure PreCA (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop
    extends Base m 64 sp pa adp pb bdp a b ra where
  sa : a.Shape
  sb : b.Shape
  asign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg
  room : max a.used b.used + 1 ≤ a.alloc
  lay : Sound (lay sp pa adp pb bdp a b) isWA

/-- What `s_mp_add(a, b, b)` needs. -/
structure PreCB (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop
    extends Base m 64 sp pa adp pb bdp a b ra where
  sa : a.Shape
  sb : b.Shape
  bsign : b.sign = Layout.mpZpos ∨ b.sign = Layout.mpNeg
  room : max a.used b.used + 1 ≤ b.alloc
  lay : Sound (lay sp pa adp pb bdp a b) isWB

/-- What `s_mp_add(a, b, a)` leaves: `a'` at `a`. -/
structure PostCA (m : Mem) (sp pa adp pb bdp : Nat) (a b a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pa adp a'
  sadd : SAddPost a b a a'
  frame : Frm (lay sp pa adp pb bdp a b) wsA m M

/-- What `s_mp_add(a, b, b)` leaves: `b'` at `b`. -/
structure PostCB (m : Mem) (sp pa adp pb bdp : Nat) (a b b' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pb bdp b'
  sadd : SAddPost a b b b'
  frame : Frm (lay sp pa adp pb bdp a b) wsB m M

def RetCA (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostCA m sp pa adp pb bdp a b a' M

def RetCB (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ b' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    PostCB m sp pa adp pb bdp a b b' M

def entry : BitVec 64 := 0x8000219c#64

/-- **`s_mp_add(a, b, a)` on the machine.** -/
def StatementCA : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    PreCA m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.SAdd.entryL ra s0 sp pa pb pa) m v.keepR outp)
      (RetCA m v outp sp pa adp pb bdp a b ra s0)

/-- **`s_mp_add(a, b, b)` on the machine.** -/
def StatementCB : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64},
    PreCB m sp pa adp pb bdp a b ra →
    Triple (At entry (Fn.SAdd.entryL ra s0 sp pa pb pb) m v.keepR outp)
      (RetCB m v outp sp pa adp pb bdp a b ra s0)

end Tom.Machine.Api.SAddAlias
