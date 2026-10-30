import Tom.Spec.WindowStep
import Tom.Spec.ModShape
import Tom.Spec.MontRedFastGStep

/-!
# `s_mp_exptmod_fast`: the model steps over the Ledger

`bn_s_mp_exptmod_fast.c` at `0x80002c5c` (frame `2032 + 4288` bytes: `M[256]` at `sp + 64`,
`res` at `sp + 40`, `mp` at `sp + 36`). `winsize` from `mp_count_bits(X)` (`winsize_eq`; the
compiled chain is `7 → 2, 36 → 3, 140 → 4, 450 → 5, 1303 → 6`, then `slt` on `3529` for `7`/`8`,
`MAX_WINSIZE = 0`), `mp_init_size(&M[1], P->alloc)` and the upper half; then by `redmode`:

* `0` (Montgomery): `mp_montgomery_setup(P, &mp)` (`setup_mont`), `redux` the comba
  `s_mp_montgomery_reduce_fast` for `2 P->used ≤ 510` (`MP_WARRAY`, `MP_MAXFAST`), else
  `mp_montgomery_reduce` (both leave `RedcPost`, `Api/MontRedFast.lean`, `Api/MontRed.lean`:
  `rx_mont`); `mp_init_size(&res, P->alloc)`, `mp_montgomery_calc_normalization(&res, P)`
  (`res_mont`: `R mod P`), `mp_mulmod(G, &res, P, &M[1])` (`m1_mont`);
* `1` (DR): `mp_dr_setup(P, &mp)` (`mp = drSetupDigit P`), `redux = mp_dr_reduce` (`rx_dr`);
* else (`2`): `mp_reduce_2k_setup(P, &mp)` (`Setup2kPost`), `redux = mp_reduce_2k`;
  for `1` and `2`: `mp_init_size(&res, P->alloc)`, `mp_set(&res, 1)` (`res_one`), `mp_mod(G, P, &M[1])`
  (`m1_mod`).

Then the table, the loop and the tail of `Tom/Spec/WindowStep.lean` over `run red X m1 res0`; for
`redmode == 0` one more `redux(&res, P, mp)`; `mp_exch(&res, Y)` (`Y` now holds `res`); the fin
lemmas `fin_mont`, `fin_dr`, `fin_2k` → `Exptmod.SExptmodFastPost`.

Callee Posts as the frozen contracts give them: `CountBits` (`countBits X`), `MpMontSetup`
(`SetupPost`), `MontRed`/`MontRedFast` (`RedcPost`), `DrSetup` (`drSetupDigit`), `DrReduce`
(`DrReducePost`), `Reduce2kSetup` (`Setup2kPost`), `MpReduce2k` (`Red.red : Reduce2kPost`),
`MontNorm` (`NormPost`), `MpSet` (`SetPost _ (1 % radix)`), `MpCopy` (`CopyPost`), `MpSqrA`
(`SqrPost`), `MpMulA`/`MpMul` (`MulPost`). No contract yet, stated over the Spec Post:
`mp_mulmod` (`MulmodPost`), `mp_mod` (`ModPost`).

Not derivable here (named, the machine proof's premises): the callees' D5 rooms (`MulPost`
has no `alloc`, so `res->alloc` is lost after `mp_mul`), and the frozen `MpReduce2k` contract's
`hd : n + d = 2^p` in the lossy case (its `Res` asks for it; `Reduce2kPost` itself does not).
-/

namespace Tom.SMpExptmodFastStep

open MpInt Ledger Window WindowStep Exptmod Mont Reduce

variable {G X P res res' M1 : MpInt}

/-! ## The reductions as transfers -/

theorem fit {P : MpInt} (hP : P.Shape) : P.mag ≤ radix ^ P.used := Nat.le_of_lt (MpInt.mag_lt hP)

/-- `mp_montgomery_setup(P, &mp)` on an odd `P`: `MP_OKAY`, `mp = setupRho P->dp[0]`. -/
theorem setup_mont {ret : Int} {rho : Nat} (hP : P.Shape) (hodd : P.mag % 2 = 1) (h : SetupPost P ret rho) :
    ret = Layout.mpOkay ∧ rho = setupRho (P.digit 0) :=
  h.odd (by rw [← MpInt.mag_mod_radix hP, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ radix)]; exact hodd)

/-- REDC with `x` grown (`MontRedFastGStep.RedcV`: the value and the sign, any block). -/
theorem xfer_redcV {x x' n : MpInt} {al M rho : Nat} (h : Ledger.Settled x al M Layout.mpZpos)
    (hr : MontRedFastGStep.RedcV x n rho x') :
    Ledger.Settled x' x'.alloc (redc M n.mag rho n.used) Layout.mpZpos :=
  ⟨hr.valid, rfl, by rw [hr.mag, h.mag], by rw [hr.sign, h.zpos]⟩

/-- Montgomery (`s_mp_montgomery_reduce_fast` or `mp_montgomery_reduce`, both growing `x`:
`MontRedFastGStep.RedcV`). -/
theorem rx_mont (hP : P.Valid) (hodd : P.mag % 2 = 1) :
    Rx (fun x x' => MontRedFastGStep.RedcV x P (setupRho (P.digit 0)) x') (redMont P) P.mag P.used where
  fit := fit hP.toShape
  lt := (red_mont hP.toShape hodd).lt
  xfer := fun h _ hp => xfer_redcV h hp

theorem dr_pos (hdr : IsDrModulus P) (hP : P.Valid) : 0 < P.mag :=
  Nat.lt_of_lt_of_le (Nat.pow_pos radix_pos) (MpInt.mag_ge hP (by have := hdr.1; omega))

/-- Diminished radix (`mp_dr_reduce` with `mp = mp_dr_setup(P)`), for a DR modulus. -/
theorem rx_dr (hP : P.Valid) (hdr : IsDrModulus P) :
    Rx (fun x x' => DrReducePost x P (drSetupDigit P) x') (redDrC P) P.mag P.used where
  fit := fit hP.toShape
  lt := (red_dr hP.toShape (dr_pos hdr hP) (drSetupDigit_spec hP.toShape hdr)).lt
  xfer := fun h _ hp => xfer_drReduce h hp

/-- A fold that never grows the value: the loop ends below `n` (enough fuel). -/
theorem redLoop_lt (fold : Nat → Nat) (n : Nat) (hn : 0 < n) (hle : ∀ a, fold a ≤ a) :
    ∀ fuel a, a < fuel → redLoop fold n fuel a < n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, a, h => by
    simp only [redLoop]
    split <;> rename_i hge
    · exact redLoop_lt fold n hn hle fuel _ (by have := hle a; omega)
    · omega

theorem fold2k_le {p d : Nat} (hd : d ≤ 2 ^ p) (a : Nat) : fold2k p d a ≤ a := by
  unfold fold2k
  have := Nat.mod_add_div a (2 ^ p)
  have : d * (a / 2 ^ p) ≤ 2 ^ p * (a / 2 ^ p) := Nat.mul_le_mul_right _ hd
  omega

/-- `mp_reduce_2k` with `mp` from `mp_reduce_2k_setup(P, &mp)`: also for the lossy setup. -/
theorem rx_2k {d : Nat} (hP : P.Valid) (hP0 : 0 < P.mag) (hs : Setup2kPost P d) :
    Rx (fun x x' => Reduce2kPost x P d x') (red2kC P) P.mag P.used where
  fit := fit hP.toShape
  lt := fun v _ => redLoop_lt _ _ hP0 (fold2k_le (Nat.le_trans (Nat.mod_le _ _) (Nat.sub_le _ _))) _ _
    (Nat.lt_succ_self _)
  xfer := fun h _ hp => by have := xfer_reduce2k h hp; rw [hs.val] at this; exact this

/-! ## `res` and `M[1]` -/

/-- `mp_montgomery_calc_normalization(&res, P)`: `res = R mod P`. -/
theorem res_mont (hP : P.Valid) (hodd : P.mag % 2 = 1) (h1 : 1 < P.mag) (h : NormPost P res') :
    Rs P.mag P.used res' (radix ^ P.used % P.mag) :=
  Rs.of (xfer_norm hP hodd h1 h) (Nat.mod_lt _ (by omega)) (fit hP.toShape)

theorem int_mul_emod_left (a b m : Int) : a * b % m = a % m * b % m := by
  rw [Int.mul_emod, Int.mul_emod (a % m) b m, Int.emod_emod]

/-- `mp_mulmod(G, &res, P, &M[1])`: `M[1] = G R mod P`. -/
theorem m1_mont (hP : P.Valid) (hPs : P.sign = Layout.mpZpos) (hP0 : 0 < P.mag)
    (hres : Rs P.mag P.used res (radix ^ P.used % P.mag)) (h : MulmodPost G res P M1) :
    Rs P.mag P.used M1 ((base G P * (radix ^ P.used % P.mag)) % P.mag) := by
  have hv : P.val = P.mag := val_zpos hPs
  have s := xfer_mulmod (by omega) h
  have e : ((G.val * res.val) % P.val).toNat = (base G P * (radix ^ P.used % P.mag)) % P.mag := by
    rw [hres.val, hv, int_mul_emod_left, ← hv, ← base_cast G P (by omega), hv, ← Int.natCast_mul,
      ← Int.natCast_emod, Int.toNat_natCast]
  rw [e] at s
  exact Rs.of s (Nat.mod_lt _ hP0) (fit hP.toShape)

/-! ## The result (`redux` fixup for Montgomery, `mp_exch(&res, Y)`) -/

/-- `redmode == 0`: `redux(&res, P, mp)` once more; `Y` gets `res`. -/
theorem fin_mont (hP : P.Valid) (hodd : P.mag % 2 = 1)
    (h : Done (run (redMont P) X ((base G P * (radix ^ P.used % P.mag)) % P.mag) (radix ^ P.used % P.mag))
      P.mag P.used res)
    (hp : MontRedFastGStep.RedcV res P (setupRho (P.digit 0)) res') : SExptmodFastPost G X P res' 0 :=
  have a := (rx_mont hP hodd).once h.winRes hp
  { valid := a.valid
    sign := a.zpos (by omega)
    mont := fun _ => a.magN
    dr := fun e => absurd e (by decide)
    r2k := fun e => absurd e (by decide) }

/-- `redmode == 1`. -/
theorem fin_dr (h : Done (run (redDrC P) X (base G P) 1) P.mag P.used res) : SExptmodFastPost G X P res 1 :=
  have a := h.winRes
  { valid := a.valid
    sign := a.zpos (by omega)
    mont := fun e => absurd e (by decide)
    dr := fun _ => a.magN
    r2k := fun e => absurd e (by decide) }

/-- `redmode ∉ {0, 1}` (the `else` of the C; the Spec's `redmode = 2`). -/
theorem fin_2k {redmode : Nat} (hm : 2 ≤ redmode) (h : Done (run (red2kC P) X (base G P) 1) P.mag P.used res) :
    SExptmodFastPost G X P res redmode :=
  have a := h.winRes
  { valid := a.valid
    sign := a.zpos (by omega)
    mont := fun e => absurd e (by omega)
    dr := fun e => absurd e (by omega)
    r2k := fun _ => a.magN }

/-! ## Side facts -/

/-- The DR and `2^k` runs start from `res = 1 < P` (`res_one`'s `1 < B`): their moduli have two
digits or more as `mp_exptmod` calls them (`IsDrModulus`; `mp_reduce_is_2k_l` is yes for one
digit). -/
theorem one_lt_of_used {P : MpInt} (hP : P.Valid) (h2 : 2 ≤ P.used) : 1 < P.mag := by
  have := MpInt.mag_ge hP (by omega)
  have := Nat.pow_le_pow_right radix_pos (show 1 ≤ P.used - 1 by omega)
  rw [Nat.pow_one] at this
  have : 1 < radix := by decide
  omega

end Tom.SMpExptmodFastStep
