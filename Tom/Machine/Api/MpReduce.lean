import Tom.Machine.Api.MpSqr
import Tom.Spec.Reduce

/-!
# `mp_reduce(x, m, mu)`: the allocating contract

Barrett reduction (`bn_mp_reduce.c` at `0x8000620c`, 103 instructions): `x` (written) becomes
`barrett x m mu` (`Spec/Reduce.lean`'s `ReducePost`; `ReducePost.spec`: `|x| mod |m|` for
`mu = ⌊radix^(2 um) / m⌋` and `x < radix^(2 um)`), `m`, `mu` read. The temporary `q` (struct in the
frame, digits allocated by `mp_init_copy` and re-placed by its in-place callees) is freed; `x`'s
digits may be re-placed by `mp_sub(x, &q, x)` and `mp_add(x, &q, x)` (growing), so the site is
`x`'s digit array and the result is `(ok, q, x')` as `Api/MpAddHA.lean`'s: on `MP_MEM` (an
allocation failed) `x'` is shaped and live at its block; on `MP_OKAY` `ReducePost`.

The residue: `0 < um` with `MP_DIGIT_BIT (um + 1)` and `MP_DIGIT_BIT x->used` `int`s, `x->used ≤ 2 um` (Barrett's range `x < radix^(2 um)` in digits) and
`um ≤ mu->used ≤ um + 2` (Barrett's `mu` has `um + 1` digits, `um + 2` for `m = radix^(um-1)`); `x`, `m`, `mu` valid and nonnegative.
Regions `stk xS xD nS nD uS uD code` (`n` is the modulus `m`, `u` is `mu`), written `stk xS xD`. Stack: the 80-byte
frame and the multipliers' 2736.
-/

namespace Tom.Machine.Api.MpReduce

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std Tom.Reduce
open Tom.Machine.Api.MpSqr (X)

def entry : BitVec 64 := 0x8000620c#64

/-- The stack depth: the 80-byte frame and the in-place multipliers' 2736 below it. -/
def F : Nat := 2816

structure P where
  sp : Nat
  px : Nat
  xdp : Nat
  pn : Nat
  ndp : Nat
  pu : Nat
  udp : Nat
  x : MpInt
  n : MpInt
  mu : MpInt
  H : List (Nat × Nat)

inductive R | stk | xS | xD | nS | nD | uS | uD | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .xS, .xD, .nS, .nD, .uS, .uD, .code] := by cases r <;> simp

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .xS => ⟨p.px, 24⟩
  | .xD => ⟨p.xdp, 4 * p.x.alloc⟩
  | .nS => ⟨p.pn, 24⟩
  | .nD => ⟨p.ndp, 4 * p.n.alloc⟩
  | .uS => ⟨p.pu, 24⟩
  | .uD => ⟨p.udp, 4 * p.mu.alloc⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .xS => .mpS p.px p.xdp p.x
  | .xD => .mpD p.xdp p.x.alloc p.x.digit
  | .nS => .mpS p.pn p.ndp p.n
  | .nD => .mpD p.ndp p.n.alloc p.n.digit
  | .uS => .mpS p.pu p.udp p.mu
  | .uD => .mpD p.udp p.mu.alloc p.mu.digit
  | .code => .code

def out (p : P) : X → R → Kind
  | (_, q, x'), .xS => .mpS p.px q x'
  | (_, q, x'), .xD => .mpD q x'.alloc x'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .xS | .xD => true
  | _ => false

def ws : List R := [.stk, .xS, .xD]

def site' (_ : P) : X → Iv
  | (_, q, x') => ⟨q, 4 * x'.alloc⟩

/-- `x`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.xdp p.x :: p.H

def hout (p : P) : X → List (Nat × Nat)
  | (_, q, x') => (q, 4 * x'.alloc) :: p.H

/-- The arguments: `a0 = x`, `a1 = m`, `a2 = mu`. -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.px), (11, BitVec.ofNat 64 p.pn),
   (12, BitVec.ofNat 64 p.pu)]

def rets (_ : P) (x : X) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, if x.1 then 0#64 else MpInit.memBV)]

/-- What `mp_reduce(x, m, mu)` needs. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  vx : p.x.Valid
  xz : p.x.sign = Layout.mpZpos
  vn : p.n.Valid
  nz : p.n.sign = Layout.mpZpos
  vmu : p.mu.Valid
  muz : p.mu.sign = Layout.mpZpos
  k1 : 0 < p.n.used
  /-- The C's `int` arithmetic: `MP_DIGIT_BIT * (um + 1)` (`mp_mod_2d`'s bit count; it also puts `um`
  below `2^27`, so `s_mp_mul_high_digs` is called, not `mp_mul`). Both multipliers on either path
  (`Api/SMpMulDigsAG.lean`). -/
  bits : Layout.digitBits * (p.n.used + 1) < 2 ^ 31
  /-- `mp_mod_2d(x, ·, x)`'s `x->used * MP_DIGIT_BIT`, an `int`. -/
  xbits : Layout.digitBits * p.x.used < 2 ^ 31
  /-- Barrett's range `x < radix^(2 um)`, in digits. -/
  xu : p.x.used ≤ 2 * p.n.used
  /-- Barrett's `mu = ⌊radix^(2 um) / m⌋` lies in `[radix^um, radix^(um+1)]`: `um + 1` digits, or
  `um + 2` for `m = radix^(um-1)` (`mp_reduce_setup`'s, `ReduceSetupPost`). -/
  mul : p.n.used ≤ p.mu.used
  muh : p.mu.used ≤ p.n.used + 2
  xpos : 0 < p.x.alloc
  npos : 0 < p.n.alloc
  upos : 0 < p.mu.alloc
  xoff : OffHeap p.px 24
  noff : OffHeap p.pn 24
  uoff : OffHeap p.pu 24

/-- What `x` holds after: shaped, live, placed, grown only; on `MP_OKAY` Barrett's result. -/
structure Out (p : P) (x : X) : Prop where
  shape : x.2.2.Shape
  pos : 0 < x.2.2.alloc
  place : Place (hin p) (lay p .xD) (site' p x)
  grow : p.x.alloc ≤ x.2.2.alloc
  valid : x.1 = true → x.2.2.Valid
  post : x.1 = true → ReducePost p.x p.n p.mu x.2.2

def Q (p : P) (x : X) : Prop := Out p x

/-- **`mp_reduce(x, m, mu)` on the machine.** -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .xD (out p x) (site' p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.MpReduce
