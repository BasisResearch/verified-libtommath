import Tom.Machine.Api.StdHeapFn
import Tom.Machine.Fn.Reduce2kSetupLG
import Tom.Spec.Reduce
import Tom.Spec.Bits
import Tom.Spec.Init

/-!
# `mp_reduce_2k_setup_l(a, d)`: the contract (over `Kit/MeetHeap.lean`)

`mp_init(&tmp)` (struct in the frame at `sp - 56`, `MP_PREC = 32` digits), `mp_2expt(&tmp,
mp_count_bits(a))`, `s_mp_sub(&tmp, a, d)`, `mp_clear(&tmp)`: `d` receives `2^p - |a|` in full
(`Setup2kLPost`, `Spec/Reduce.lean`: valid, that magnitude; its sign is `d`'s unless the result
is zero, as `s_mp_sub` leaves it), in place (`d->alloc` kept). On `MP_MEM` from `mp_init` nothing
is changed; `mp_2expt` and `s_mp_sub` cannot fail under the residue. The heap has the same
blocks after (`tmp`'s freed). Memory changes only in the stack `[sp - 640, sp)` (the 80-byte
frame and `mp_init`'s 560), `d` and the allocator's footprint.
-/

namespace Tom.Machine.Api.Reduce2kSetupL

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Reduce Tom.Mont

def entry : BitVec 64 := 0x80006174#64

inductive R | stk | aS | aD | dS | dD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .aS, .aD, .dS, .dD, .code] := by cases r <;> simp

/-- The stack depth: the 80-byte frame and `mp_init`'s. -/
abbrev F : Nat := 80 + MpInit.Finit

structure P where
  sp : Nat
  pa : Nat
  adp : Nat
  pd : Nat
  ddp : Nat
  a : MpInt
  d : MpInt
  H : List (Nat × Nat)

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .dS => ⟨p.pd, 24⟩
  | .dD => ⟨p.ddp, 4 * p.d.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .dS => .mpS p.pd p.ddp p.d
  | .dD => .mpD p.ddp p.d.alloc p.d.digit
  | .code => .code

/-- After: `none` on `MP_MEM`, `some d'` with `d'` at `d`'s place. -/
def out (p : P) : Option MpInt → R → Kind
  | some d', .dS => .mpS p.pd p.ddp d'
  | some d', .dD => .mpD p.ddp d'.alloc d'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .dS | .dD => true
  | _ => false

def ws : List R := [.stk, .dS, .dD]

def hin (p : P) : List (Nat × Nat) := p.H

/-- The arguments: `a0 = a`, `a1 = d` (`gp` for the allocator). -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pd)]

def rets (_ : P) (x : Option MpInt) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | none => MpInit.memBV | some _ => 0#64)]

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

/-- What `d` holds after. -/
structure LPost (p : P) (d' : MpInt) : Prop where
  setup : Setup2kLPost p.a d'
  alloc : d'.alloc = p.d.alloc

def Q (p : P) : Option MpInt → Prop
  | none => True
  | some d' => LPost p d'

/-- **`mp_reduce_2k_setup_l(a, d)` on the machine.** The site is `d`'s digit array, kept in place. -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .dD (out p x) (lay p .dD) (hin p) (hin p) m M)

end Tom.Machine.Api.Reduce2kSetupL
