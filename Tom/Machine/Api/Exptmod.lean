import Tom.Machine.Api.MpMul
import Tom.Machine.Api.MpSqr
import Tom.Spec.SMpExptmodFastStep
import Tom.Spec.SMpExptmodStep

/-!
# `s_mp_exptmod_fast(G, X, P, Y, redmode)` and `s_mp_exptmod(G, X, P, Y, redmode)`: the allocating
contracts

The two window-loop workers of `mp_exptmod` share their signature and their effect: `Y` (written,
distinct from `G`, `X`, `P`, D6) receives `res` by `mp_exch(&res, Y)` and `mp_clear(&res)` frees
`Y`'s old digit block, so the site is `Y`'s digit array, at `res`'s block `q` after; the table
`M[]` and `res` are temporaries (allocated and freed). On an error every temporary is freed and `Y`
is as it was. `mp_sqr`/`mp_mul` read the cut-off words (`ks`, `ts`, `kc = KARATSUBA_MUL_CUTOFF`,
`tc = TOOM_MUL_CUTOFF`, `Api/MpSqr.lean`, `Api/MpMul.lean`): read-only one-word regions.

Regions `stk gS gD xS xD nS nD yS yD ks ts kc tc code` (`n` is the modulus `P`), written
`stk yS yD`. The stack depth `F` is the function's (`Ff`, `Fs`).

* `Api.SMpExptmodFast` (`0x80002c5c`): `Out.ok` holds `Exptmod.SExptmodFastPost`; errors are
  `MP_MEM` (the setups cannot fail under `Res`: `P` odd for Montgomery). Every multiplier and
  reduction grows its destination (`redux` by `Std.reduxG`, `mp_mul`/`mp_sqr` at any size by
  `Std.mpMulG`/`mpMulAG`/`mpSqrAG`), so `Res` has no `P->used` bound and no room on the products;
  what is left is the frozen `mp_montgomery_calc_normalization`'s room, the DR digit, the lossy
  `2^p - d` setup and the C's `int`s.
* `Api.SMpExptmod` (`0x8000261c`): **statement only**: `Out.ok` holds `SMpExptmodStep.Out`'s `MP_OKAY` case, errors
  are `MP_MEM` or its `P = 0` `MP_VAL`. Its arithmetic residue `Arith` is opaque to its callers
  (`mp_exptmod` passes it on), so its prover may restate it (no room on the modulus).
-/

namespace Tom.Machine.Api.Exptmod

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

structure P where
  sp : Nat
  pg : Nat
  gdp : Nat
  px : Nat
  xdp : Nat
  pn : Nat
  ndp : Nat
  py : Nat
  ydp : Nat
  g : MpInt
  x : MpInt
  n : MpInt
  y : MpInt
  /-- `redmode` (an `int`, nonnegative). -/
  mode : Nat
  H : List (Nat × Nat)

inductive R | stk | gS | gD | xS | xD | nS | nD | yS | yD | ks | ts | kc | tc | code
  deriving DecidableEq

theorem all (r : R) : r ∈ [R.stk, .gS, .gD, .xS, .xD, .nS, .nD, .yS, .yD, .ks, .ts, .kc, .tc, .code] := by
  cases r <;> simp

/-- The layout for a stack depth `F`. -/
def lay (F : Nat) (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .gS => ⟨p.pg, 24⟩
  | .gD => ⟨p.gdp, 4 * p.g.alloc⟩
  | .xS => ⟨p.px, 24⟩
  | .xD => ⟨p.xdp, 4 * p.x.alloc⟩
  | .nS => ⟨p.pn, 24⟩
  | .nD => ⟨p.ndp, 4 * p.n.alloc⟩
  | .yS => ⟨p.py, 24⟩
  | .yD => ⟨p.ydp, 4 * p.y.alloc⟩
  | .ks => ⟨MpSqr.ksAddr, 4⟩
  | .ts => ⟨MpSqr.tsAddr, 4⟩
  | .kc => ⟨MpMul.kcAddr, 4⟩
  | .tc => ⟨MpMul.tcAddr, 4⟩
  | .code => textIv

def kind (p : P) : R → Kind
  | .stk => .ram
  | .gS => .mpS p.pg p.gdp p.g
  | .gD => .mpD p.gdp p.g.alloc p.g.digit
  | .xS => .mpS p.px p.xdp p.x
  | .xD => .mpD p.xdp p.x.alloc p.x.digit
  | .nS => .mpS p.pn p.ndp p.n
  | .nD => .mpD p.ndp p.n.alloc p.n.digit
  | .yS => .mpS p.py p.ydp p.y
  | .yD => .mpD p.ydp p.y.alloc p.y.digit
  | .ks => .mpD MpSqr.ksAddr 1 MpSqr.ksV
  | .ts => .mpD MpSqr.tsAddr 1 MpSqr.tsV
  | .kc => .mpD MpMul.kcAddr 1 MpMul.kcV
  | .tc => .mpD MpMul.tcAddr 1 MpMul.tcV
  | .code => .code

/-- An error `r` (`Y` as it was), or `MP_OKAY` with `Y'`'s digits at `q` (`res`'s block). -/
inductive Out
  | err (r : Int)
  | ok (q : Nat) (y' : MpInt)

def out (p : P) : Out → R → Kind
  | .ok q y', .yS => .mpS p.py q y'
  | .ok q y', .yD => .mpD q y'.alloc y'.digit
  | _, r => kind p r

def isW : R → Bool
  | .stk | .yS | .yD => true
  | _ => false

def ws : List R := [.stk, .yS, .yD]

def site' (F : Nat) (p : P) : Out → Iv
  | .ok q y' => ⟨q, 4 * y'.alloc⟩
  | .err _ => lay F p .yD

/-- `Y`'s digits are the front live block. -/
def hin (p : P) : List (Nat × Nat) := digBlk p.ydp p.y :: p.H

def hout (p : P) : Out → List (Nat × Nat)
  | .ok q y' => (q, 4 * y'.alloc) :: p.H
  | .err _ => hin p

/-- The arguments: `a0 = G`, `a1 = X`, `a2 = P`, `a3 = Y`, `a4 = redmode`. -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pg), (11, BitVec.ofNat 64 p.px),
   (12, BitVec.ofNat 64 p.pn), (13, BitVec.ofNat 64 p.py), (14, BitVec.ofNat 64 p.mode)]

def rets (_ : P) (x : Out) (ra : BitVec 64) : GRegs :=
  [(1, ra), (10, match x with | .err r => BitVec.ofInt 64 r | .ok _ _ => 0#64)]

/-- What both workers need beyond their arithmetic: the stack, the operands valid and their
structs off the arena, `Y` live (its block is freed), the blocks `mp_mod`'s `mp_div` copies
(`G`'s and `P`'s) live, `redmode` an `int`, the C's `int` arithmetic on the sizes. -/
structure Base (F : Nat) (p : P) : Prop where
  stk : StkRes p.sp F
  vg : p.g.Valid
  vx : p.x.Valid
  vn : p.n.Valid
  sy : p.y.Shape
  /-- `P` positive (`mp_exptmod` returns `MP_VAL` before for a negative modulus). -/
  nz : p.n.sign = Layout.mpZpos
  /-- `mp_count_bits(X)`, `mp_count_bits(P)` are `int`s; `digidx = X->used - 1`. -/
  xbits : Layout.digitBits * p.x.used < 2 ^ 31
  nbits : Layout.digitBits * p.n.used < 2 ^ 31
  /-- `mp_mod(G, P, ·)`'s `mp_div` sizes (`Api/MpMod.lean` `au`). -/
  gu : p.g.used + p.n.used + 3 < 2 ^ 30
  mode : p.mode < 2 ^ 31
  gpos : 0 < p.g.alloc
  xpos : 0 < p.x.alloc
  npos : 0 < p.n.alloc
  ypos : 0 < p.y.alloc
  goff : OffHeap p.pg 24
  xoff : OffHeap p.px 24
  noff : OffHeap p.pn 24
  yoff : OffHeap p.py 24
  gblk : digBlk p.gdp p.g ∈ p.H
  nblk : digBlk p.ndp p.n ∈ p.H

/-- A run from `entry` with stack depth `F p`, residue `Res` and outcome `Q`. -/
def Spec (entry : BitVec 64) (F : P → Nat) (Res : P → Prop) (Q : P → Out → Prop) : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay (F p) p) isW → Bundle (lay (F p) p) (kind p) m → AHeap m (hin p) →
    (∀ r, Off (lay (F p) p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay (F p) p) ws .yD (out p x) (site' (F p) p x) (hin p) (hout p x) m M)

end Tom.Machine.Api.Exptmod

namespace Tom.Machine.Api.SMpExptmodFast

open Tom.Machine.Api.Exptmod

def entry : BitVec 64 := 0x80002c5c#64

/-- The stack depth: the 6320-byte frame (`M[256]`, `res`, the spills, twelve saved registers) and
the deepest callee (every callee growing): `redux`'s 4800 (`Std.reduxG`, the Montgomery
routines'), `mp_mul`'s `2768 + 8 (a->used + b->used)` on two residues (at most `2 P->used` digits) and
`mp_mulmod(G, &res, P, &M[1])`'s `2864 + 8 (G->used + res->used)` (`res = R mod P`) below
`4800 + 8 (G->used + 2 P->used)`. -/
def Ff (g n : MpInt) : Nat := 11120 + 8 * (g.used + 2 * n.used)

abbrev F (p : P) : Nat := Ff p.g p.n

/-- The non-lossy `mp_reduce_2k_setup` (`Exptmod.Lossy2k`'s negation for an `is2k` modulus):
its digit is the true `d` of `P = 2^p - d` (`Api.MpReduce2k.Res.hd`). -/
def Exact2k (n : MpInt) : Prop :=
  n.mag + (2 ^ Mont.nbits n.mag - n.mag) % radix = 2 ^ Mont.nbits n.mag

/-- The arithmetic residue (every callee grows its destination, `Api/ReduxGF.lean`,
`Api/Std_cap.lean`; `mp_montgomery_calc_normalization(&res, P)` grows `res`,
`Api/MontNormG.lean`, so no room on the modulus and no size bound): a modulus `> 1`, the C's `int`
arithmetic on a product of two residues (`mp_reduce_2k`'s `mp_div_2d`, `x->used * MP_DIGIT_BIT`), and
per mode what the setup needs. -/
structure Arith (n : MpInt) (mode : Nat) : Prop where
  gt1 : 1 < n.mag
  bits : Layout.digitBits * (2 * n.used + 1) < 2 ^ 31
  /-- Montgomery: `mp_montgomery_setup` needs an odd modulus (else `MP_VAL`; `mp_exptmod` calls
  this mode only for odd `P`). -/
  mont : mode = 0 → n.mag % 2 = 1
  /-- Diminished radix: a DR modulus (`mp_dr_reduce`'s `|x| mod P`), its setup digit `2^28 - P->dp[0]`
  a digit. -/
  dr : mode = 1 → IsDrModulus n ∧ 0 < n.digit 0
  /-- `2^p - d`: the setup's digit is the true `d`. -/
  r2k : 2 ≤ mode → Exact2k n

structure Res (p : P) : Prop extends Base (F p) p where
  arith : Arith p.n p.mode

/-- `MP_MEM` (`Y` as it was), or `MP_OKAY` with `SExptmodFastPost`. -/
def Q (p : P) : Out → Prop
  | .err r => r = Layout.mpMem
  | .ok _ y' => Exptmod.SExptmodFastPost p.g p.x p.n y' p.mode

/-- **`s_mp_exptmod_fast(G, X, P, Y, redmode)` on the machine.** -/
def Statement : Prop := Spec entry F Res Q

end Tom.Machine.Api.SMpExptmodFast

namespace Tom.Machine.Api.SMpExptmod

open Tom.Machine.Api.Exptmod

def entry : BitVec 64 := 0x8000261c#64

/-- The stack depth: the frame and spills (6336 bytes: `M[256]`, `mu`, `res`) and the deepest callee at
any modulus: `redux`'s `2872 + 8 (x->used + P->used)` on a product of two residues
(`x->used ≤ 2 P->used`, `Api/MpReduce2kLG.lean`'s `F`, `mp_reduce`'s 2816 below it), above `mp_mul`'s
`2768 + 8 (res->used + M[i]->used)` and `mp_sqr`'s `2768 + 8 res->used`; `mp_mod(G, P, &M[1])` and the
setups within the old `10576 + 8 (G->used + P->used)`. `mp_exptmod` reserves it by name. -/
def Fs (g n : MpInt) : Nat := 10576 + 8 * (g.used + 3 * n.used)

abbrev F (p : P) : Nat := Fs p.g p.n

/-- The arithmetic residue of the Barrett / `2^p - d` worker. No room on the modulus and no size bound: the setups and the
reductions grow their destinations (`Api/MpReduceSetupG.lean`, `Api/Reduce2kSetupLG.lean`,
`Api/MpReduce2kLG.lean`, `mp_copy(&M[1], &M[2^(w-1)])` by `Api/MpCopyG.lean`; `mp_reduce` grows `x`),
and the multipliers run at any size (`mp_mul` by the closed group, `Std.mpMulG`/`mpMulAG`; `mp_sqr(&x, &x)`
by `Api/MpSqrAG.lean`; `mp_reduce`'s `s_mp_mul_digs`/`s_mp_mul_high_digs` on both paths,
`Api/SMpMulDigsAG.lean`). What is left is what the C needs: the modulus positive (`mp_reduce_setup`'s
`mp_div(mu, P, mu, NULL)` returns `MP_VAL` for `P = 0`, and `mp_reduce_2k_l` would not end), `redmode` one
of the worker's two modes, and the C's `int` arithmetic on a product of two residues (`x->used ≤ 2 P->used`):
`mp_mod_2d`'s and `mp_div_2d`'s `x->used * MP_DIGIT_BIT`, `mp_reduce`'s `MP_DIGIT_BIT * (um + 1)`. -/
structure Arith (n : MpInt) (mode : Nat) : Prop where
  pos : 0 < n.mag
  bits : Layout.digitBits * (2 * n.used + 1) < 2 ^ 31
  mode : mode < 2

structure Res (p : P) : Prop extends Base (F p) p where
  arith : Arith p.n p.mode

/-- `MP_MEM` (`Y` as it was), `MP_VAL` for `P = 0` in Barrett mode (`SMpExptmodStep.Out.zero`), or
`MP_OKAY` with `SExptmodPost` (`P > 0`). -/
def Q (p : P) : Out → Prop
  | .err r => r = Layout.mpMem ∨ SMpExptmodStep.Out p.g p.x p.n p.y p.y p.mode r
  | .ok _ y' => SMpExptmodStep.Out p.g p.x p.n p.y y' p.mode Layout.mpOkay

/-- **`s_mp_exptmod(G, X, P, Y, redmode)` on the machine** (statement only). -/
def Statement : Prop := Spec entry F Res Q

end Tom.Machine.Api.SMpExptmod
