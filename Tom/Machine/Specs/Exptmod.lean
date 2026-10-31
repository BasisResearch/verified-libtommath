import Tom.Machine.Conventions
import Tom.Machine.Fn.MpExptmod

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_exptmod`: the concise specification (SPECS.lean), from `Fn.MpExptmod.correct` -/

namespace Tom.Machine.Api.MpExptmod
open Tom.Machine.Api.Exptmod (P R lay kind out isW ws site' hin hout rets Base Out)
open Tom Tom.Exptmod Tom.MpExptmodStep

/-- The machine's `2^k` premise excludes the lossy setups (README, bug 1). -/
theorem not_lossy {n : MpInt} (hv : n.Valid) (h : isReduce2k n = 1 → SMpExptmodFast.Exact2k n) :
    ¬ Lossy2k n := by
  rintro ⟨-, -, h2k, hr⟩
  have he := h ((is2k_iff hv).1 h2k)
  unfold SMpExptmodFast.Exact2k at he
  have := Nat.mod_lt (2 ^ Mont.nbits n.mag - n.mag) (show 0 < radix by decide)
  omega

def eff (p : P) := Eff.heap (lay (F p) p) isW ws .yD (out p) (site' (F p) p) (hin p) (hout p)
  fun | .err r => errView r p.y | .ok _ y' => some y'

/-- **`mp_exptmod(G, X, P, Y)`**: `Y ← G^X mod P`, for `X ≥ 0` and `P > 1` (`MP_MEM` leaves `Y`
as it was). `r2k`: for a `2^k`-reduction modulus the setup is exact (README, bug 1). -/
theorem _root_.Specs.mp_exptmod {p : P} (cv : Conv m ra p.sp (F p) (eff p)) (cut : Cutoffs m)
    (g : MpOwn m p.H p.pg p.gdp p.g) (x : MpOwn m p.H p.px p.xdp p.x)
    (n : MpOwn m p.H p.pn p.ndp p.n) (y : MpOut m p.py p.ydp p.y) (hx : 0 ≤ p.x.val)
    (hn : 1 < p.n.val) (r2k : isReduce2k p.n = 1 → SMpExptmodFast.Exact2k p.n) (fx : Fits p.x)
    (fn : FitsBits (2 * p.n.used + 1)) (gu : CIdx (p.g.used + p.n.used + 3)) :
    ApiTriple m v outp ra entry p.sp [p.pg, p.px, p.pn, p.py] (eff p)
      fun y' => y'.Valid ∧ y'.val = p.g.val ^ p.x.mag % p.n.val := by
  have nz : p.n.sign = Layout.mpZpos := DivStep.sign_of_val_nonneg n.valid (by omega)
  have n1 : 1 < p.n.mag := by have := MpInt.val_pos_of_sign (P := p.n) (by rw [nz]; decide); omega
  have xs : p.x.sign ≠ Layout.mpNeg := by rw [DivStep.sign_of_val_nonneg x.valid hx]; decide
  have nb : Layout.digitBits * p.n.used < 2 ^ 31 := by
    have e : Layout.digitBits = 28 := rfl; unfold FitsBits at fn; rw [e] at fn ⊢; omega
  have nl := not_lossy n.valid r2k
  have spec := fun {Y Y' : MpInt} {r : Int} (h : ExptmodPost p.g p.x p.n Y Y' r) =>
    ExptmodPost.spec_nonneg x.valid.toShape n.valid (by rw [nz]; decide) n1 xs nl h
  exact ApiTriple.of (Reg.call (Fn.MpExptmod.correct (p := { p with mode := 0 }) cv.ra_al
    ⟨⟨cv.stk, g.valid, x.valid, n.valid, y.shape, nz, fx, nb, gu, show 0 < 2 ^ 31 by decide,
      g.pos, x.pos, n.pos, y.pos, g.off, x.off, n.off, y.off, g.blk, n.blk⟩, ⟨n1, fn, r2k⟩⟩ cv.sound)
    cv.heap (by mp_regions)) (fun | .err _, hq => .errView (hq.imp_right spec) | .ok .., hq => (spec hq).2)
    (hr := fun
      | .err _, hq => congrArg (fun b => [(1, ra), (10, b)]) (errView_ret (hq.imp_right spec))
      | .ok .., _ => rfl)

end Tom.Machine.Api.MpExptmod
