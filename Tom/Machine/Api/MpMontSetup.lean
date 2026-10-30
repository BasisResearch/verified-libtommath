import Tom.Machine.Img
import Tom.Machine.Repr
import Tom.Machine.Kit.Frame
import Tom.Machine.Fn.MpMontSetup
import Tom.Spec.Mont

/-!
# `mp_montgomery_setup`: the standard contract

`mp_montgomery_setup(n, rho)` with `n` shaped, `alloc > 0`, and a word `rho`:
returns `MP_VAL` for even `n->dp[0]` and `MP_OKAY` with
`*rho = setupRho (n->dp[0])` for odd (`SetupPost`, `Tom/Spec/Mont.lean`;
`SetupPost.spec`: `rho = -1/n mod radix` for odd `n`). Memory changes only in
the stack `[sp - 48, sp)` and `*rho`; the callee-saved registers are kept.
`__muldi3` (six calls) is `Fn.Libgcc.Muldi3.correctK`.
-/

namespace Tom.Machine.Api.MpMontSetup

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Mont

/-- The regions: the stack, `n`'s struct and digits, `*rho`, the code. -/
inductive R | stk | nS | nD | rho | code
  deriving DecidableEq

def isW : R → Bool
  | .stk | .rho => true
  | _ => false

def lay (sp p dp rp : Nat) (n : MpInt) : R → Iv
  | .stk => ⟨sp - 48, 48⟩
  | .nS => ⟨p, 24⟩
  | .nD => ⟨dp, 4 * n.alloc⟩
  | .rho => ⟨rp, 4⟩
  | .code => textIv

def ws : List R := [.stk, .rho]

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

/-- What it leaves with result `ret`: `*rho` holds `rho`. -/
structure Post (m : Mem) (sp p dp rp : Nat) (n : MpInt) (ret : Int) (rho : Nat) (M : Mem) : Prop where
  rho_v : bytesT4 M rp = BitVec.ofNat 32 rho
  setup : SetupPost n ret rho
  frame : Frm (lay sp p dp rp n) ws m M

def Ret (m : Mem) (v : Abi) (outp : Array String) (sp p dp rp : Nat) (n : MpInt) (ra : BitVec 64)
    (c : Vsa.Machine.Config) : Prop :=
  ∃ ret rho M, At ra [(1, ra), (10, BitVec.ofInt 64 ret)] M v.keep outp c ∧ Post m sp p dp rp n ret rho M

/-- The entry: `ra`, `a0 = n`, `a1 = rho`. -/
def entryL (ra : BitVec 64) (p rp : Nat) : GRegs := [(1, ra), (10, BitVec.ofNat 64 p), (11, BitVec.ofNat 64 rp)]

/-- **`mp_montgomery_setup` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {sp p dp rp : Nat} {n : MpInt} {ra : BitVec 64},
    Pre m v sp p dp rp n ra →
    Triple (At Fn.MpMontSetup.entry (entryL ra p rp) m v.keep outp) (Ret m v outp sp p dp rp n ra)

end Tom.Machine.Api.MpMontSetup
