import Tom.Machine.Fn.SAddDst

/-!
# `s_mp_add` on the machine: the whole function

From the entry, `s_mp_add(a, b, c)` with `c` distinct from `a` and `b`
returns `MP_OKAY` with `c` holding `SAddPost a b c c'` (so `|c'| = |a| + |b|`
and `c'` valid, `SAddPost.spec`), the callee-saved registers restored, and
memory changed only in its stack frame, `c`'s struct and `c`'s digits.

The assembly is `Fn.SAdd.AnyDst.correct` (`SAddDst.lean`), which covers
every destination; here both operands are `Dst.Src.own`, kept by `Frm.keep`
in the regions `R` (placed by `lay`, disjoint where it matters by `sound`,
once, from `Pre.lay`) through the kernel's frame pushed by `kR`.
-/

namespace Tom.Machine.Fn.SAdd

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

/-- The memory layout: the ranges `s_mp_add` writes (its stack frame `S`, `c`'s
struct `CS` and digits `CD`) are disjoint from each other and from what it
reads (`a`'s and `b`'s structs and digits) and from the three functions'
code. -/
structure Lay (sp pa adp aal pb bdp bal pc cdp cal : Nat) : Prop where
  s_cs : Disj (sp - 64) 64 pc 24
  s_cd : Disj (sp - 64) 64 cdp (4 * cal)
  s_as : Disj (sp - 64) 64 pa 24
  s_ad : Disj (sp - 64) 64 adp (4 * aal)
  s_bs : Disj (sp - 64) 64 pb 24
  s_bd : Disj (sp - 64) 64 bdp (4 * bal)
  s_code : Disj (sp - 64) 64 sMpAddBase 432
  s_ms : Disj (sp - 64) 64 memsetBase 220
  s_cl : Disj (sp - 64) 64 mpClampBase 64
  cs_as : Disj pc 24 pa 24
  cs_ad : Disj pc 24 adp (4 * aal)
  cs_bs : Disj pc 24 pb 24
  cs_bd : Disj pc 24 bdp (4 * bal)
  cs_code : Disj pc 24 sMpAddBase 432
  cs_ms : Disj pc 24 memsetBase 220
  cs_cl : Disj pc 24 mpClampBase 64
  cd_as : Disj cdp (4 * cal) pa 24
  cd_ad : Disj cdp (4 * cal) adp (4 * aal)
  cd_bs : Disj cdp (4 * cal) pb 24
  cd_bd : Disj cdp (4 * cal) bdp (4 * bal)
  cd_code : Disj cdp (4 * cal) sMpAddBase 432
  cd_ms : Disj cdp (4 * cal) memsetBase 220
  cd_cl : Disj cdp (4 * cal) mpClampBase 64

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
  code : CodeAt m sMpAddBase sMpAddCode
  code_ms : CodeAt m memsetBase memsetCode
  code_cl : CodeAt m mpClampBase mpClampCode
  lay : Lay sp pa adp a.alloc pb bdp b.alloc pc cdp c.alloc

/-- The ranges `s_mp_add` writes. -/
def InW (sp pc cdp cal x : Nat) : Prop :=
  (sp - 64 ≤ x ∧ x < sp) ∨ (pc ≤ x ∧ x < pc + 24) ∨ (cdp ≤ x ∧ x < cdp + 4 * cal)

/-! ## Regions -/

/-- `s_mp_add`'s regions: its stack frame, the three structs and digit
arrays, the three functions' code. -/
inductive R | fr | cS | cD | aS | aD | bS | bD | code | ms | cl
  deriving DecidableEq

/-- The regions it writes. -/
def isW : R → Bool
  | .fr | .cS | .cD => true
  | _ => false

/-- Their placement. -/
def lay (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt) : R → Iv
  | .fr => ⟨sp - 64, 64⟩
  | .cS => ⟨pc, 24⟩
  | .cD => ⟨cdp, 4 * c.alloc⟩
  | .aS => ⟨pa, 24⟩
  | .aD => ⟨adp, 4 * a.alloc⟩
  | .bS => ⟨pb, 24⟩
  | .bD => ⟨bdp, 4 * b.alloc⟩
  | .code => ⟨sMpAddBase, 432⟩
  | .ms => ⟨memsetBase, 220⟩
  | .cl => ⟨mpClampBase, 64⟩

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat} {a b c : MpInt}
  {ra s0 : BitVec 64}

/-- **Disjointness, once**: from `Pre.lay` and `c`'s geometry. -/
theorem sound (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Sound (lay sp pa adp pb bdp pc cdp a b c) isW := by
  have hg : Disj pc 24 cdp (4 * c.alloc) := hP.gc.disj
  have L := hP.lay
  cases L
  sound_cases

end

/-- What `s_mp_add` leaves. -/
structure Post (m : Mem) (sp pa adp pb bdp pc cdp : Nat) (a b c c' : MpInt) (M : Mem) : Prop where
  repr : MpAt M pc cdp c'
  sadd : SAddPost a b c c'
  frame : ∀ x, ¬ InW sp pc cdp c.alloc x → M[x]? = m[x]?

/-- The return state. -/
def Ret (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Post m sp pa adp pb bdp pc cdp a b c c' M

/-- The kernel's regions are ours. -/
def kR : Tom.Machine.Dst.K → R
  | .fr => .fr | .cS => .cS | .cD => .cD | .code => .code | .ms => .ms | .cl => .cl

/-- **`s_mp_add` on the machine.** From its entry (`a0 = a`, `a1 = b`,
`a2 = c`, return address `ra`, stack `sp`, `s0` and the other callee-saved
registers of the caller), with `Pre` (the three `mp_int`s in memory, shaped,
`c` with room for `max + 1` digits, the stack frame and the code in memory,
the written ranges off everything else), the machine returns to `ra` with
`a0 = MP_OKAY`, `sp`, `s0` and the callee-saved registers restored, `c'` at
`c` with `SAddPost a b c c'`, and memory changed only in the stack frame and
`c`'s struct and digits. -/
theorem correct {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat}
    {a b c : MpInt} {ra s0 : BitVec 64} (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Triple (At 0x8000219c#64 (entryL ra s0 sp pa pb pc) m v.keepR outp)
      (Ret m v outp sp pa adp pb bdp pc cdp a b c ra s0) := by
  have hS := sound hP
  have hsub : ∀ k, (AnyDst.lay sp pc cdp c k).Sub (lay sp pa adp pb bdp pc cdp a b c (kR k)) := by
    intro k; cases k <;> exact Iv.sub_self _
  have hP' : AnyDst.Pre m sp pa adp pb bdp pc cdp a b c ra :=
    { hP with
      srcA := .own (fun M hF => (Frm.push kR hsub hF).keep hS
          (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_)
        (hS.disj (r := R.aS) (s := R.fr)) (hS.disj (r := R.aS) (s := R.cS))
      srcB := .own (fun M hF => (Frm.push kR hsub hF).keep hS
          (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _)) hP.rb)
        (hS.disj (r := R.bS) (s := R.fr)) (hS.disj (r := R.bS) (s := R.cS))
      lay := hS.pull kR _ Tom.Machine.Dst.all hsub }
  exact Triple.rmap (fun _ ⟨c', M, hat, hpost⟩ => ⟨c', M, hat,
      { repr := hpost.repr, sadd := hpost.sadd
        frame := (Frm.push kR hsub hpost.frame).clause fun x hx => by
          have := hP.sp_ge
          simp only [InAny, Iv.In, lay, InW, Tom.Machine.Dst.ws, List.map, kR, or_false] at hx ⊢; omega }⟩)
    (AnyDst.correct hP')

/-- `s_mp_add` on the machine, against the specification: `|c'| = |a| + |b|`
and `c'` is valid (`SAddPost.spec`). -/
theorem correct_spec {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat}
    {a b c : MpInt} {ra s0 : BitVec 64} (hP : Pre m sp pa adp pb bdp pc cdp a b c ra) :
    Triple (At 0x8000219c#64 (entryL ra s0 sp pa pb pc) m v.keepR outp)
      (fun cf => ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
        MpAt M pc cdp c' ∧ c'.Valid ∧ c'.mag = a.mag + b.mag) :=
  Triple.rmap (fun _ ⟨c', M, hat, hpost⟩ =>
    have hs := hpost.sadd.spec hP.sa hP.sb hP.room hP.sc.alloc_lt hP.csign
    ⟨c', M, hat, hpost.repr, hs.1, hs.2⟩) (correct hP)

end Tom.Machine.Fn.SAdd
