import Tom.Machine.Fn.SSub
import Tom.Spec.Sub

/-!
# `s_mp_sub` on the machine: the contract

From the entry,
`s_mp_sub(a, b, c)` with `b->used ≤ a->used` and `c->alloc ≥ a->used` returns
`MP_OKAY` with `c` holding `SSubPost a b c c'`, the callee-saved registers
restored, and memory changed only in its stack frame, `c`'s struct and `c`'s
digits.
-/

namespace Tom.Machine.Fn.SSub

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

/-- The memory layout: the ranges `s_mp_sub` writes (its stack frame, `c`'s
struct and digits) are disjoint from each other and from what it reads
(`a`'s and `b`'s structs and digits) and from the three functions' code. -/
structure Lay (sp pa adp aal pb bdp bal pc cdp cal : Nat) : Prop where
  s_cs : Disj (sp - 48) 48 pc 24
  s_cd : Disj (sp - 48) 48 cdp (4 * cal)
  s_as : Disj (sp - 48) 48 pa 24
  s_ad : Disj (sp - 48) 48 adp (4 * aal)
  s_bs : Disj (sp - 48) 48 pb 24
  s_bd : Disj (sp - 48) 48 bdp (4 * bal)
  s_code : Disj (sp - 48) 48 sMpSubBase 380
  s_ms : Disj (sp - 48) 48 memsetBase 220
  s_cl : Disj (sp - 48) 48 mpClampBase 64
  cs_as : Disj pc 24 pa 24
  cs_ad : Disj pc 24 adp (4 * aal)
  cs_bs : Disj pc 24 pb 24
  cs_bd : Disj pc 24 bdp (4 * bal)
  cs_code : Disj pc 24 sMpSubBase 380
  cs_ms : Disj pc 24 memsetBase 220
  cs_cl : Disj pc 24 mpClampBase 64
  cd_as : Disj cdp (4 * cal) pa 24
  cd_ad : Disj cdp (4 * cal) adp (4 * aal)
  cd_bs : Disj cdp (4 * cal) pb 24
  cd_bd : Disj cdp (4 * cal) bdp (4 * bal)
  cd_code : Disj cdp (4 * cal) sMpSubBase 380
  cd_ms : Disj cdp (4 * cal) memsetBase 220
  cd_cl : Disj cdp (4 * cal) mpClampBase 64

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
  code : CodeAt m sMpSubBase sMpSubCode
  code_ms : CodeAt m memsetBase memsetCode
  code_cl : CodeAt m mpClampBase mpClampCode
  lay : Lay sp pa adp a.alloc pb bdp b.alloc pc cdp c.alloc

/-- The ranges `s_mp_sub` writes. -/
def InW (sp pc cdp cal x : Nat) : Prop :=
  (sp - 48 ≤ x ∧ x < sp) ∨ (pc ≤ x ∧ x < pc + 24) ∨ (cdp ≤ x ∧ x < cdp + 4 * cal)

/-- What `s_mp_sub` leaves. -/
structure Post (m : Mem) (sp pc cdp : Nat) (a b c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  ssub : SSubPost a b c c'
  frame : ∀ x, ¬ InW sp pc cdp c.alloc x → M[x]? = m[x]?

/-- The return state. -/
def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pc cdp : Nat) (a b c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pc cdp a b c c' M

def correct_Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat}
    {a b c : MpInt} {ra s0 : BitVec 64}, Pre m sp pa adp pb bdp pc cdp a b c ra →
    Triple (At 0x80004564#64 (entryL ra s0 sp pa pb pc) m v.keepR outp)
      (Ret m v outp sp pc cdp a b c ra s0)

end Tom.Machine.Fn.SSub
