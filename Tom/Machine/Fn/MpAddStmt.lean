import Tom.Machine.Fn.MpAdd
import Tom.Machine.Fn.SSubStmt
import Tom.Machine.Fn.CmpMag
import Tom.Spec.Signed

/-!
# `mp_add` on the machine: the contract

From the entry, `mp_add(a, b, c)`
with `a`, `b` valid and `c` with room for `max + 1` digits (so neither
`s_mp_add` nor `s_mp_sub` calls `mp_grow`, D5) returns `MP_OKAY` with
`AddPost a b c c'`, the callee-saved registers restored, and memory changed
only in its stack frame (which contains every callee's), `c`'s struct and
`c`'s digits.
-/

namespace Tom.Machine.Fn.MpAdd

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

/-- The memory layout: the written ranges (the stack frame `[sp - 64, sp)`, `c`'s
struct and digits) are disjoint from each other and from what is read (`a`'s and
`b`'s structs and digits) and from the six functions' code. -/
structure Lay (sp pa adp aal pb bdp bal pc cdp cal : Nat) : Prop where
  s_cs : Disj (sp - 64) 64 pc 24
  s_cd : Disj (sp - 64) 64 cdp (4 * cal)
  s_as : Disj (sp - 64) 64 pa 24
  s_ad : Disj (sp - 64) 64 adp (4 * aal)
  s_bs : Disj (sp - 64) 64 pb 24
  s_bd : Disj (sp - 64) 64 bdp (4 * bal)
  s_add : Disj (sp - 64) 64 mpAddBase 144
  s_cm : Disj (sp - 64) 64 mpCmpMagBase 124
  s_sa : Disj (sp - 64) 64 sMpAddBase 432
  s_ss : Disj (sp - 64) 64 sMpSubBase 380
  s_ms : Disj (sp - 64) 64 memsetBase 220
  s_cl : Disj (sp - 64) 64 mpClampBase 64
  cs_as : Disj pc 24 pa 24
  cs_ad : Disj pc 24 adp (4 * aal)
  cs_bs : Disj pc 24 pb 24
  cs_bd : Disj pc 24 bdp (4 * bal)
  cs_add : Disj pc 24 mpAddBase 144
  cs_cm : Disj pc 24 mpCmpMagBase 124
  cs_sa : Disj pc 24 sMpAddBase 432
  cs_ss : Disj pc 24 sMpSubBase 380
  cs_ms : Disj pc 24 memsetBase 220
  cs_cl : Disj pc 24 mpClampBase 64
  cd_as : Disj cdp (4 * cal) pa 24
  cd_ad : Disj cdp (4 * cal) adp (4 * aal)
  cd_bs : Disj cdp (4 * cal) pb 24
  cd_bd : Disj cdp (4 * cal) bdp (4 * bal)
  cd_add : Disj cdp (4 * cal) mpAddBase 144
  cd_cm : Disj cdp (4 * cal) mpCmpMagBase 124
  cd_sa : Disj cdp (4 * cal) sMpAddBase 432
  cd_ss : Disj cdp (4 * cal) sMpSubBase 380
  cd_ms : Disj cdp (4 * cal) memsetBase 220
  cd_cl : Disj cdp (4 * cal) mpClampBase 64

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
  code : CodeAt m mpAddBase mpAddCode
  code_cm : CodeAt m mpCmpMagBase mpCmpMagCode
  code_sa : CodeAt m sMpAddBase sMpAddCode
  code_ss : CodeAt m sMpSubBase sMpSubCode
  code_ms : CodeAt m memsetBase memsetCode
  code_cl : CodeAt m mpClampBase mpClampCode
  lay : Lay sp pa adp a.alloc pb bdp b.alloc pc cdp c.alloc

/-- The ranges `mp_add` (and its callees) write. -/
def InW (sp pc cdp cal x : Nat) : Prop :=
  (sp - 64 ≤ x ∧ x < sp) ∨ (pc ≤ x ∧ x < pc + 24) ∨ (cdp ≤ x ∧ x < cdp + 4 * cal)

/-- What `mp_add` leaves. -/
structure Post (m : Mem) (sp pc cdp : Nat) (a b c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  add : AddPost a b c c'
  frame : ∀ x, ¬ InW sp pc cdp c.alloc x → M[x]? = m[x]?

/-- The return state. -/
def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pc cdp : Nat) (a b c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pc cdp a b c c' M

/--
The callee contracts are `SAdd.correct` (statement in `Fn/SAddMain.lean`),
`SSub.correct_Statement` and `CmpMag.correct`. -/
def correct_Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat}
    {a b c : MpInt} {ra s0 : BitVec 64}, Pre m sp pa adp pb bdp pc cdp a b c ra →
    Triple (At 0x80000608#64 (SSub.entryL ra s0 sp pa pb pc) m v.keepR outp)
      (Ret m v outp sp pc cdp a b c ra s0)

end Tom.Machine.Fn.MpAdd
