import Tom.Machine.Fn.MontRedFast
import Tom.Machine.Api.MontRedFast
import Tom.Machine.Api.Std
import Tom.Machine.Kit.Buf
import Tom.Machine.Kit.W64

/-!
# `s_mp_montgomery_reduce_fast` on the machine: the whole function

The segments of `Tom.Machine.Fn.MontRedFast` and the contracts of `__muldi3`,
`memset` (`memsetD`), `mp_clamp`, `mp_cmp_mag` by `call_std` and of `s_mp_sub(x, n,
x)` (`sSubCA`) by `tail_std` (`Kit/Meet.lean`, `Api/StdLib.lean`, `Api/Std.lean`).
Regions: `Two`'s (`n` read, `x` written) with the stack cut by `Kit/Buf.lean` into
the spills `lo`, the columns `buf` (`W`, 512 `mp_word`s as 1024 digit halves,
`Kit/W64.lean`) and the saves `hi`. `W`'s digits are `gW W old`: the halves of the
model's first `2 n->used + 1` columns, the stack's old contents above. The model is
`Tom.Mont`'s: `W0` → `fastRows` (each row `wRow`, `wFix`) → `fastTail`; the copy-out
reads `T / R` (`fastOut_val`).
-/

-- Six loops and three joins



namespace Tom.Machine.Fn.MontRedFast

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api Tom.Machine.Std
open Tom.Machine.Api.Two (R isW)
open Tom.Mont

/-! ## The column model over the digit halves -/

/-- `W` before the rows: `x`'s digits, zero above. -/
def W0 (x : MpInt) (i : Nat) : Nat := if i < x.used then x.digit i else 0

/-- `W`'s digits: the halves of the model's first `D = 2 (2 n->used + 1)` halves, `old` above. -/
abbrev gW (W old : Nat → Nat) (nu : Nat) : Nat → Nat := ovl (h32 W) old (2 * (2 * nu + 1))

theorem gW_upd {W old : Nat → Nat} {nu i v : Nat} (hi : i < 2 * nu + 1) :
    upd (upd (gW W old nu) (2 * i) (v % 4294967296)) (2 * i + 1) (v / 4294967296 % 4294967296) =
      gW (upd W i v) old nu := by
  funext t
  have h := congrFun (h32_upd W i v) t
  by_cases ht : t < 2 * (2 * nu + 1)
  · have e1 : gW (upd W i v) old nu t = h32 (upd W i v) t := by simp only [gW, ovl, if_pos ht]
    rw [e1, ← h]; unfold upd
    by_cases h1 : t = 2 * i + 1
    · simp only [h1, if_true]
    · by_cases h0 : t = 2 * i
      · simp only [h1, h0, if_false, if_true]
      · simp only [h1, h0, if_false, gW, ovl, if_pos ht]
  · unfold upd gW ovl; rw [if_neg (by omega), if_neg (by omega), if_neg ht, if_neg ht]

theorem gW_w64 {W old : Nat → Nat} {nu i : Nat} (hi : i < 2 * nu + 1) (hW : W i < 2 ^ 64) :
    w64 (gW W old nu) i = W i := by
  rw [← w64_h32 W i hW]; unfold w64 gW ovl; rw [if_pos (by omega), if_pos (by omega)]

theorem gW_lt {W old : Nat → Nat} {nu t : Nat} (ht : t < 2 * (2 * nu + 1)) : gW W old nu t < 2 ^ 32 := by
  unfold gW ovl; rw [if_pos ht]; exact h32_lt W t

/-- An `ld` of column `i`. -/
theorem gW_ld {M : Mem} {dp : Nat} {W old : Nat → Nat} {nu i : Nat} (d : Dig M dp 1024 (gW W old nu))
    (hnu : 2 * (2 * nu + 1) ≤ 1024) (hi : i < 2 * nu + 1) (hW : W i < 2 ^ 64) :
    bytesT8 M (dp + 8 * i) = BitVec.ofNat 64 (W i) := by
  rw [d.ld (i := i) (by omega) (gW_lt (by omega)) (gW_lt (by omega)), gW_w64 hi hW]

/-- The copy-in after `i` columns. -/
theorem gC_step {W old : Nat → Nat} {i : Nat} :
    upd (upd (ovl (h32 W) old (2 * i)) (2 * i) (W i % 4294967296)) (2 * i + 1) (W i / 4294967296 % 4294967296) =
      ovl (h32 W) old (2 * (i + 1)) := by
  funext t
  by_cases h1 : t = 2 * i + 1
  · subst h1
    simp only [upd, ovl, h32, if_true, show (2 * i + 1) % 2 = 1 by omega, show (2 * i + 1) / 2 = i by omega,
      show 2 * i + 1 < 2 * (i + 1) by omega]
    simp
  · by_cases h0 : t = 2 * i
    · subst h0
      simp only [upd, ovl, h32, h1, if_false, if_true, show 2 * i % 2 = 0 by omega, show 2 * i / 2 = i by omega,
        show 2 * i < 2 * (i + 1) by omega]
    · simp only [upd, h1, h0, if_false]; unfold ovl
      by_cases ht : t < 2 * i
      · rw [if_pos ht, if_pos (by omega)]
      · rw [if_neg ht, if_neg (by omega)]

/-- The `memset` of the high columns. -/
theorem gC_fill {x : MpInt} {old : Nat → Nat} {nu : Nat} (hou : x.used ≤ 2 * nu + 1) :
    zfill (ovl (h32 (W0 x)) old (2 * x.used)) (2 * x.used) (2 * (2 * nu + 1)) = gW (W0 x) old nu := by
  funext t; unfold zfill gW ovl
  by_cases h1 : t < 2 * x.used
  · rw [if_neg (by omega), if_pos h1, if_pos (by omega)]
  · by_cases h2 : t < 2 * (2 * nu + 1)
    · rw [if_pos ⟨by omega, h2⟩, if_pos h2]
      unfold h32 W0; rw [if_neg (show ¬ t / 2 < x.used by omega)]; split <;> rfl
    · rw [if_neg (by omega), if_neg h1, if_neg h2]

/-! ## Bounds -/

section bounds
variable {nd W : Nat → Nat} {rho nu : Nat}

theorem W0_lt {x : MpInt} (hx : x.Shape) (i : Nat) : W0 x i < radix := by
  unfold W0; split
  · exact hx.digit_lt i
  · exact radix_pos

theorem rows_lt (hnd : ∀ i, nd i < radix) {x : MpInt} (hx : x.Shape) (hnu : nu ≤ 255) {j : Nat} (hj : j ≤ nu)
    (i : Nat) : fastRows nd rho nu (W0 x) j i < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (fastRows_bound nd (W0 x) rho nu hnd (W0_lt hx) hnu j hj i) (wBound_lt _ _ _ (by omega))

theorem row_lt (hnd : ∀ i, nd i < radix) {x : MpInt} (hx : x.Shape) (hnu : nu ≤ 255) {j : Nat} (hj : j < nu)
    {mu : Nat} (hmu : mu < radix) (iy i : Nat) :
    wRow nd mu j (fastRows nd rho nu (W0 x) j) iy i ≤ wBound j (j + 1) i := by
  have h1 := wRow_le nd hnd mu j hmu (fastRows nd rho nu (W0 x) j) iy i
  have h2 := fastRows_bound nd (W0 x) rho nu hnd (W0_lt hx) hnu j (by omega) i
  have h3 : (if j ≤ i ∧ i < j + iy then (radix - 1) * (radix - 1) else 0) ≤ (radix - 1) * (radix - 1) := by
    split <;> omega
  unfold wBound at *; rw [Nat.succ_mul]; omega

end bounds

theorem gC_zero {x : MpInt} {old : Nat → Nat} {nu : Nat} (hou : x.used = 0) :
    zfill old 0 (2 * (2 * nu + 1)) = gW (W0 x) old nu := by
  funext t; unfold zfill gW ovl
  by_cases h2 : t < 2 * (2 * nu + 1)
  · rw [if_pos ⟨by omega, h2⟩, if_pos h2]
    unfold h32 W0; rw [if_neg (show ¬ t / 2 < x.used by omega)]; split <;> rfl
  · rw [if_neg (by omega), if_neg h2]

/-- `blez` on a negative doubleword. -/
theorem bge_zero_neg {e : Nat} (h1 : 0 < e) (h2 : e < 2 ^ 63) :
    zopz0zKzJ_s (0#64) (BitVec.ofNat 64 (18446744073709551616 - e)) = true := by
  unfold zopz0zKzJ_s
  have : (BitVec.ofNat 64 (18446744073709551616 - e)).toInt = -(e : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofNat]; split <;> omega
  rw [this]; simp only [BitVec.toInt_zero, decide_eq_true_eq]; omega

/-! ## The machine -/

abbrev ρm (q px xdp pn ndp : Nat) (x n : MpInt) := Bf.lay (Two.lay 4256 (q + 4256) pn ndp px xdp n x) R.stk 4256 48 4096

abbrev Wm : List (Bf R) := [.lo, .buf, .hi, .o .stk, .o .bS, .o .bD]

/-- The state over our regions. -/
abbrev SM (m : Mem) (q px xdp pn ndp : Nat) (x n : MpInt) (κ : Bf R → Kind) (M : Mem) : Prop :=
  St (ρm q px xdp pn ndp x n) (Bf.wr isW) Wm κ m M

/-- The saves. -/
abbrev mH (m : Mem) (ra s0 : BitVec 64) (v : Abi) (q : Nat) : Mem :=
  writeLog (writeLog m (log2a ra s0 v q)) (log2b v q)

/-- The spills after the prologue, with `2 n->used`, with `8 n->used`. -/
abbrev mLa (m : Mem) (q px rho ou : Nat) : Mem :=
  writeLog (writeLog m [(q + 16, 8, BitVec.ofNat 64 ou)]) (log5 q px rho)

abbrev mLb (m : Mem) (q px rho ou nu : Nat) : Mem :=
  writeLog (mLa m q px rho ou) [(q + 40, 8, BitVec.ofNat 64 (2 * nu))]

abbrev mLc (m : Mem) (q px rho ou nu : Nat) : Mem :=
  writeLog (mLb m q px rho ou nu) [(q + 32, 8, BitVec.ofNat 64 (8 * nu))]

abbrev mLd (m : Mem) (q px rho ou nu : Nat) : Mem :=
  writeLog (mLc m q px rho ou nu) [(q + 32, 8, BitVec.ofNat 64 (8 * nu))]

/-- The kinds: `x`'s struct `xc`, the spills `ml`, `W`'s digits `g`. -/
abbrev κM (m : Mem) (ra s0 : BitVec 64) (v : Abi) (q px xdp pn ndp : Nat) (n xc : MpInt) (ml : Mem)
    (g : Nat → Nat) : Bf R → Kind :=
  Bf.kind (Two.kind pn ndp px xdp n xc) ml (mH m ra s0 v q) (.mpD (q + 48) 1024 g)

def σm : Cd → Bf R := fun _ => .o .code

def σw : Dz → Bf R
  | .D => .buf
  | .code => .o .code

def σd : Dz → Bf R
  | .D => .o .bD
  | .code => .o .code

def σz : Ob → Bf R
  | .S => .o .bS
  | .D => .o .bD
  | .code => .o .code

def σc : Cm → Bf R
  | .aS => .o .bS
  | .aD => .o .bD
  | .bS => .o .aS
  | .bD => .o .aD
  | .code => .o .code

def σs : BinA.R → Bf R
  | .stk => .hi
  | .aS => .o .bS
  | .aD => .o .bD
  | .bS => .o .aS
  | .bD => .o .aD
  | .code => .o .code

theorem cd {m M : Mem} {q px xdp pn ndp : Nat} {x n : MpInt} {κ : Bf R → Kind}
    (h : SM m q px xdp pn ndp x n κ M) (hk : κ (.o .code) = .code := by rfl) :
    CodeAt M sMpMontgomeryReduceFastBase sMpMontgomeryReduceFastCode :=
  (h.img (.o .code) hk).sMpMontgomeryReduceFast

/-- The scalars every step needs. -/
structure Sc (x n : MpInt) : Prop where
  nu_pos : 1 ≤ n.used
  nu_le : n.used ≤ 255
  ou_le : x.used ≤ 2 * n.used
  room : n.used < x.alloc
  al_le : x.alloc ≤ 2 ^ 29

theorem sc_of {m : Mem} {q px xdp pn ndp : Nat} {x n : MpInt} {rho : Nat} {ra : BitVec 64}
    (hP : MontRedFast.Pre m (q + 4256) px xdp pn ndp x n rho ra) : Sc x n := by
  have h1 := hP.gx.ds.lo_ge; have h2 := hP.gx.ds.hi_le; simp only [Layout.sizeofDigit] at h1 h2
  have hn := MpInt.mag_lt hP.vn.toShape
  have hx : x.mag < radix ^ (2 * n.used) := by
    calc x.mag < n.mag * radix ^ n.used := hP.x_lt
      _ ≤ radix ^ n.used * radix ^ n.used := Nat.mul_le_mul_right _ (Nat.le_of_lt hn)
      _ = radix ^ (2 * n.used) := by rw [← Nat.pow_add, Nat.two_mul]
  have hu : x.used ≤ 2 * n.used := by
    rcases Nat.eq_zero_or_pos x.used with h0 | h0
    · omega
    · have := MpInt.mag_ge hP.vx h0
      have : radix ^ (x.used - 1) < radix ^ (2 * n.used) := Nat.lt_of_le_of_lt this hx
      have := (Nat.pow_lt_pow_iff_right (by simp only [radix, Layout.digitBits]; decide)).1 this
      omega
  exact ⟨hP.nu_pos, hP.nu_le, hu, hP.room, by omega⟩

theorem kf_of {m : Mem} {q px xdp pn ndp : Nat} {x n : MpInt} {rho : Nat} {ra : BitVec 64}
    (hP : MontRedFast.Pre m (q + 4256) px xdp pn ndp x n rho ra) : KF q := by
  have hd := hP.lay (Api.Two.R.stk) (Api.Two.R.code) (by decide)
  have := hP.sp_al
  simp only [Iv.Disj, Disj, Two.lay, textIv, textBase, textLen, Nat.add_sub_cancel] at hd
  exact ⟨by simpa using hP.rs, by omega, by simp only [sMpMontgomeryReduceFastBase]; omega⟩

/-- A spill read back (the frozen `lo`). -/
theorem spill {m M ml : Mem} {q px xdp pn ndp : Nat} {x n : MpInt} {κ : Bf R → Kind}
    (h : SM m q px xdp pn ndp x n κ M) (hk : κ .lo = .frz ml) {o : Nat} (ho : o + 8 ≤ 48) :
    bytesT8 M (q + o) = bytesT8 ml (q + o) :=
  h.frz .lo hk (by simp only [Iv.Sub, ρm, Bf.lay, Two.lay]; omega)

/-- A save read back (the frozen `hi`). -/
theorem save {m M mh : Mem} {q px xdp pn ndp : Nat} {x n : MpInt} {κ : Bf R → Kind}
    (h : SM m q px xdp pn ndp x n κ M) (hk : κ .hi = .frz mh) {o : Nat} (ho : 4144 ≤ o) (ho' : o + 8 ≤ 4256) :
    bytesT8 M (q + o) = bytesT8 mh (q + o) :=
  h.frz .hi hk (by simp only [Iv.Sub, ρm, Bf.lay, Two.lay]; omega)

theorem tex {A : Mem → Prop} {B : Mem → Vsa.Machine.Config → Prop} {Q : Vsa.Machine.Config → Prop}
    (h : ∀ M, A M → Triple (B M) Q) : Triple (fun cf => ∃ M, A M ∧ B M cf) Q := fun cf ⟨M, hA, hB⟩ => h M hA cf hB

theorem fin_of {B : Vsa.Machine.Config → Prop} {Q : Vsa.Machine.Config → Prop} (h : ∀ cf, B cf → Q cf) :
    Triple B Q := fun cf hc => ⟨cf, Vsa.Machine.Steps.refl _, h cf hc⟩

section rows
variable {m : Mem} {v : Abi} {outp : Array String} {q px xdp pn ndp : Nat} {x n : MpInt} {rho : Nat}
  {ra s0 : BitVec 64}

/-- The rows' model. -/
abbrev Ws (x n : MpInt) (rho j : Nat) : Nat → Nat := fastRows n.digit rho n.used (W0 x) j

/-- `mu` of row `j`. -/
abbrev muR (x n : MpInt) (rho j : Nat) : Nat := Ws x n rho j j % radix * rho % radix

theorem wread {M : Mem} {κ : Bf R → Kind} (h : SM m q px xdp pn ndp x n κ M) {W old : Nat → Nat} {nu i : Nat}
    (hk : κ .buf = .mpD (q + 48) 1024 (gW W old nu)) (hnu : nu ≤ 255) (hi : i < 2 * nu + 1)
    (hW : W i < 2 ^ 64) : WRead M ((q + 48) + 8 * i) (W i) := by
  have d := h.dig .buf hk
  exact ⟨Ram.sub d.ram (by omega) (by omega), gW_ld d (by omega) hi hW, hW⟩

/-- `W`'s kind replaced. -/
theorem setW {M ml : Mem} {xc : MpInt} {g g' : Nat → Nat}
    (h : SM m q px xdp pn ndp x n (Kind.set (κM m ra s0 v q px xdp pn ndp n xc ml g) .buf
      (.mpD (q + 48) 1024 g')) M) : SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n xc ml g') M :=
  h.congrK (by intro r; rcases r with _ | _ | _ | r <;> rfl)

/-- The inner loop of row `j`: term `iy` to the carry fix at `3ebc`. -/
theorem inner (hP : MontRedFast.Pre m (q + 4256) px xdp pn ndp x n rho ra) (hS : Sc x n) (hk : KF q) {ml : Mem}
    {old : Nat → Nat} {j : Nat} (hj : j < n.used) :
    ∀ iy, iy < n.used → Triple (fun cf => ∃ M, SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x ml
        (gW (wRow n.digit (muR x n rho j) j (Ws x n rho j) iy) old n.used)) M ∧
        At 0x80003e98#64 (iH q pn n.used xdp ndp j iy (muR x n rho j)) M (kF v) outp cf)
      (fun cf => ∃ M, SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x ml
        (gW (wRow n.digit (muR x n rho j) j (Ws x n rho j) n.used) old n.used)) M ∧
        At 0x80003ebc#64 (fxL q pn n.used xdp ndp j (muR x n rho j)) M (kF v) outp cf) := by
  have := hS.nu_pos; have := hS.nu_le; have := hk.q_al
  have hns := hP.vn.toShape; have hxs := hP.vx.toShape
  have hmu : muR x n rho j < radix := Nat.mod_lt _ radix_pos
  have hng := hP.gn.ds.hi_le; simp only [Layout.sizeofDigit] at hng; have := hns.used_le
  have hbd : ∀ iy i, wRow n.digit (muR x n rho j) j (Ws x n rho j) iy i < 2 ^ 64 := fun iy i =>
    Nat.lt_of_le_of_lt (row_lt hns.digit_lt hxs (by omega) hj hmu iy i) (wBound_lt _ _ _ (by omega))
  have hsucc : ∀ iy, wRow n.digit (muR x n rho j) j (Ws x n rho j) (iy + 1) =
      upd (wRow n.digit (muR x n rho j) j (Ws x n rho j) iy) (j + iy)
        (wRow n.digit (muR x n rho j) j (Ws x n rho j) iy (j + iy) + n.digit iy * muR x n rho j) := fun iy => by
    simp only [wRow]; rw [Nat.mul_comm (muR x n rho j)]
  have hsum : ∀ iy, wRow n.digit (muR x n rho j) j (Ws x n rho j) iy (j + iy) + n.digit iy * muR x n rho j <
      2 ^ 64 := fun iy => by
    have := hbd (iy + 1) (j + iy); rw [hsucc, upd_same] at this; exact this
  have hmu32 : muR x n rho j < 2 ^ 32 := Nat.lt_of_lt_of_le hmu (by decide)
  intro iy hiy
  refine Triple.countup_from (lo := 0) (n := n.used) (P := fun iy cf => ∃ M,
    SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x ml
      (gW (wRow n.digit (muR x n rho j) j (Ws x n rho j) iy) old n.used)) M ∧
      At 0x80003e98#64 (iH q pn n.used xdp ndp j iy (muR x n rho j)) M (kF v) outp cf)
    (fun iy _ hi => ?_) ?_ iy (Nat.zero_le _) hiy
  · refine tex fun M h => ?_
    refine St.seq0 (m18_step v outp q pn n.used xdp ndp j iy (muR x n rho j) (n.digit iy) M (cd h) (by facts h))
      (call_std muldi3 ⟨n.digit iy, muR x n rho j⟩ σm h (cd h) 0x69c130ef#32 0x1369c#21 0x80003ea8#64 trivial
        fun _ M' _ h' => ?_)
    refine h'.seqD8 .buf rfl (m19t_step v outp q pn n.used xdp ndp j iy (muR x n rho j) _ _ M' (cd h')
      ⟨hk, by omega⟩ (wread h' rfl (by omega) (by omega) (hbd iy (j + iy))) (hsum iy) hi (by omega))
      (by omega) fun M'' h'' => fin_of fun cf hc => ⟨M'', setW (by rw [gW_upd (by omega), ← hsucc] at h''; exact h''), hc⟩
  · refine tex fun M h => ?_
    have hi1 : n.used - 1 + 1 = n.used := by omega
    refine St.seq0 (m18_step v outp q pn n.used xdp ndp j (n.used - 1) (muR x n rho j) (n.digit (n.used - 1)) M
        (cd h) (by facts h))
      (call_std muldi3 ⟨n.digit (n.used - 1), muR x n rho j⟩ σm h (cd h) 0x69c130ef#32 0x1369c#21 0x80003ea8#64 trivial
        fun _ M' _ h' => ?_)
    refine h'.seqD8 .buf rfl (m19f_step v outp q pn n.used xdp ndp j (n.used - 1) (muR x n rho j) _ _ M' (cd h')
      ⟨hk, by omega⟩ (wread h' rfl (by omega) (by omega) (hbd _ _)) (hsum _) hi1)
      (by omega) fun M'' h'' => fin_of fun cf hc => ⟨M'', setW (by rw [gW_upd (by omega), ← hsucc, hi1] at h''; exact h''), hc⟩

end rows

/-- At a row head: row `j`. -/
def RH (m : Mem) (v : Abi) (outp : Array String) (ra s0 : BitVec 64) (q px xdp pn ndp : Nat) (x n : MpInt)
    (rho ou : Nat) (old : Nat → Nat) (j : Nat) (cf : Vsa.Machine.Config) : Prop :=
  ∃ M j0 j7 j11, SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x (mLc m q px rho ou n.used)
    (gW (Ws x n rho j) old n.used)) M ∧ At 0x80003e74#64 (rowL q pn n.used xdp ndp j j0 j7 j11) M (kF v) outp cf

/-- After the rows (`3ed8`). -/
def AR (m : Mem) (v : Abi) (outp : Array String) (ra s0 : BitVec 64) (q px xdp pn ndp : Nat) (x n : MpInt)
    (rho ou : Nat) (old : Nat → Nat) (cf : Vsa.Machine.Config) : Prop :=
  ∃ M j0 j7 j11, SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x (mLc m q px rho ou n.used)
    (gW (Ws x n rho n.used) old n.used)) M ∧ At 0x80003ed8#64 (aL q pn n.used xdp ndp j0 j7 j11) M (kF v) outp cf

section rows2
variable {m : Mem} {v : Abi} {outp : Array String} {q px xdp pn ndp : Nat} {x n : MpInt} {rho ou : Nat}
  {ra s0 : BitVec 64}

/-- A row up to its carry fix. -/
theorem rowpre (hP : MontRedFast.Pre m (q + 4256) px xdp pn ndp x n rho ra) (hS : Sc x n) (hk : KF q)
    {old : Nat → Nat} {j : Nat} (hj : j < n.used) :
    Triple (RH m v outp ra s0 q px xdp pn ndp x n rho ou old j)
      (fun cf => ∃ M, SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x (mLc m q px rho ou n.used)
        (gW (wRow n.digit (muR x n rho j) j (Ws x n rho j) n.used) old n.used)) M ∧
        At 0x80003ebc#64 (fxL q pn n.used xdp ndp j (muR x n rho j)) M (kF v) outp cf) := by
  intro cf ⟨M, j0, j7, j11, h, hat⟩
  have := hS.nu_pos; have := hS.nu_le; have := hk.q_al
  have hns := hP.vn.toShape; have hxs := hP.vx.toShape; have hrl := hP.rho_lt
  have hWj := rows_lt (rho := rho) hns.digit_lt hxs (by omega) (Nat.le_of_lt hj) j
  have hp : Ws x n rho j j % 268435456 * rho < 2 ^ 64 := by
    have : Ws x n rho j j % 268435456 < 268435456 := Nat.mod_lt _ (by decide)
    have : Ws x n rho j j % 268435456 * rho ≤ 268435455 * 268435455 :=
      Nat.mul_le_mul (by omega) (by simp only [radix, Layout.digitBits] at hrl; omega)
    omega
  refine (St.seq0 (m16_step v outp q pn n.used xdp ndp j rho (Ws x n rho j j) j0 j7 j11 M (cd h) hk
      (wread h rfl (by omega) (by omega) hWj) (by rw [spill h rfl (by decide)]; rd_log))
    (call_std muldi3 ⟨Ws x n rho j j % 268435456, rho⟩ σm h (cd h) 0x6bc130ef#32 0x136bc#21 0x80003e88#64 trivial
      fun _ M' _ h' => ?_)) cf hat
  refine St.seq0 (m17_step v outp q pn n.used xdp ndp j _ j0 j7 M' (cd h') hp) ?_
  exact Triple.lmap (fun cf hc => ⟨M', h', hc⟩) (inner hP hS hk hj 0 (by omega))

/-- The carry fix of row `j` (`j + 1 < n->used`): the next row. -/
theorem rowstep (hP : MontRedFast.Pre m (q + 4256) px xdp pn ndp x n rho ra) (hS : Sc x n) (hk : KF q)
    {old : Nat → Nat} {j : Nat} (hj : j + 1 < n.used) :
    Triple (fun cf => ∃ M, SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x (mLc m q px rho ou n.used)
        (gW (wRow n.digit (muR x n rho j) j (Ws x n rho j) n.used) old n.used)) M ∧
        At 0x80003ebc#64 (fxL q pn n.used xdp ndp j (muR x n rho j)) M (kF v) outp cf)
      (RH m v outp ra s0 q px xdp pn ndp x n rho ou old (j + 1)) := by
  refine tex fun M h => ?_
  have := hS.nu_pos; have := hS.nu_le; have := hk.q_al
  have hns := hP.vn.toShape; have hxs := hP.vx.toShape
  have hmu : muR x n rho j < radix := Nat.mod_lt _ radix_pos
  have hb := fun i => Nat.lt_of_le_of_lt (row_lt (rho := rho) hns.digit_lt hxs (by omega) (show j < n.used by omega) hmu
    n.used i) (wBound_lt _ _ _ (by omega))
  have hs0 := rows_lt (rho := rho) hns.digit_lt hxs (by omega) (show j + 1 ≤ n.used by omega) (j + 1)
  have hs : wRow n.digit (muR x n rho j) j (Ws x n rho j) n.used (j + 1) +
      wRow n.digit (muR x n rho j) j (Ws x n rho j) n.used j / 268435456 < 2 ^ 64 := by
    simp only [Ws, fastRows, wFix, upd_same] at hs0; exact hs0
  have h1 := wread h rfl (by omega) (show j + 1 < 2 * n.used + 1 by omega) (hb (j + 1))
  rw [show (q + 48) + 8 * (j + 1) = (q + 48) + 8 * j + 8 by omega] at h1
  exact h.seqD8 .buf rfl (m20t_step v outp q pn n.used xdp ndp j (muR x n rho j) _ _ M (cd h) ⟨hk, by omega⟩
    (wread h rfl (by omega) (by omega) (hb j)) h1 hs hj (by omega)) (by omega)
    fun M' h' => fin_of fun cf hc => ⟨M', _, _, _, setW (by rw [gW_upd (by omega)] at h'; exact h'), hc⟩

/-- The carry fix of the last row. -/
theorem rowlast (hP : MontRedFast.Pre m (q + 4256) px xdp pn ndp x n rho ra) (hS : Sc x n) (hk : KF q)
    {old : Nat → Nat} {j : Nat} (hj : j + 1 = n.used) :
    Triple (fun cf => ∃ M, SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x (mLc m q px rho ou n.used)
        (gW (wRow n.digit (muR x n rho j) j (Ws x n rho j) n.used) old n.used)) M ∧
        At 0x80003ebc#64 (fxL q pn n.used xdp ndp j (muR x n rho j)) M (kF v) outp cf)
      (AR m v outp ra s0 q px xdp pn ndp x n rho ou old) := by
  refine tex fun M h => ?_
  have := hS.nu_pos; have := hS.nu_le; have := hk.q_al
  have hns := hP.vn.toShape; have hxs := hP.vx.toShape
  have hmu : muR x n rho j < radix := Nat.mod_lt _ radix_pos
  have hb := fun i => Nat.lt_of_le_of_lt (row_lt (rho := rho) hns.digit_lt hxs (by omega) (show j < n.used by omega) hmu
    n.used i) (wBound_lt _ _ _ (by omega))
  have hs0 := rows_lt (rho := rho) hns.digit_lt hxs (by omega) (show j + 1 ≤ n.used by omega) (j + 1)
  have hs : wRow n.digit (muR x n rho j) j (Ws x n rho j) n.used (j + 1) +
      wRow n.digit (muR x n rho j) j (Ws x n rho j) n.used j / 268435456 < 2 ^ 64 := by
    simp only [Ws, fastRows, wFix, upd_same] at hs0; exact hs0
  have h1 := wread h rfl (by omega) (show j + 1 < 2 * n.used + 1 by omega) (hb (j + 1))
  rw [show (q + 48) + 8 * (j + 1) = (q + 48) + 8 * j + 8 by omega] at h1
  exact h.seqD8 .buf rfl (m20f_step v outp q pn n.used xdp ndp j (muR x n rho j) _ _ M (cd h) ⟨hk, by omega⟩
    (wread h rfl (by omega) (by omega) (hb j)) h1 hs hj (by omega)) (by omega)
    fun M' h' => fin_of fun cf hc => ⟨M', _, _, _, by
      have h2 : SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x (mLc m q px rho ou n.used)
          (gW (Ws x n rho (j + 1)) old n.used)) M' := setW (by rw [gW_upd (by omega)] at h'; exact h')
      rw [hj] at h2; exact h2, hc⟩

/-- **The rows.** -/
theorem rows (hP : MontRedFast.Pre m (q + 4256) px xdp pn ndp x n rho ra) (hS : Sc x n) (hk : KF q) {old : Nat → Nat} :
    Triple (RH m v outp ra s0 q px xdp pn ndp x n rho ou old 0) (AR m v outp ra s0 q px xdp pn ndp x n rho ou old) :=
  Triple.countup_from (lo := 0) (n := n.used) (P := RH m v outp ra s0 q px xdp pn ndp x n rho ou old)
    (fun j _ hj => Triple.seq (rowpre hP hS hk (by omega)) (rowstep hP hS hk hj))
    (Triple.seq (rowpre hP hS hk (by have := hS.nu_pos; omega)) (rowlast hP hS hk (by have := hS.nu_pos; omega)))
    0 (Nat.le_refl _) (by have := hS.nu_pos; omega)

/-- The model after the tail carries. -/
abbrev Wt (x n : MpInt) (rho : Nat) : Nat → Nat := fastTail n.used (Ws x n rho n.used) n.used

/-- The copy-out digits. -/
abbrev Fo (x n : MpInt) (rho : Nat) (i : Nat) : Nat := Wt x n rho (n.used + i) % radix

theorem tail_lt (hP : MontRedFast.Pre m (q + 4256) px xdp pn ndp x n rho ra) (hS : Sc x n) (k i : Nat) :
    fastTail n.used (Ws x n rho n.used) k i < 2 ^ 64 := by
  have := hS.nu_le
  exact Nat.lt_of_le_of_lt (fastTail_bound n.used _ (by omega)
    (fun i => fastRows_bound _ _ rho _ hP.vn.toShape.digit_lt (W0_lt hP.vx.toShape) (by omega) _ (Nat.le_refl _) i) k i)
    (wBound_lt _ _ _ (by omega))

/-- **The tail carries**, from `3ed8` to `3f34`. -/
theorem tail (hP : MontRedFast.Pre m (q + 4256) px xdp pn ndp x n rho ra) (hS : Sc x n) (hk : KF q) {old : Nat → Nat} :
    Triple (AR m v outp ra s0 q px xdp pn ndp x n rho ou old)
      (fun cf => ∃ M j0 j7 j11, SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x
        (mLc m q px rho ou n.used) (gW (Wt x n rho) old n.used)) M ∧
        At 0x80003f34#64 (t1L q pn n.used xdp ndp j0 j7 j11) M (kF v) outp cf) := by
  intro cf ⟨M, j0, j7, j11, h, hat⟩
  have := hS.nu_pos; have := hS.nu_le; have := hk.q_al
  have r32 : bytesT8 M (q + 32) = BitVec.ofNat 64 (8 * n.used) := by
    rw [spill h rfl (by decide)]; rd_log
  have r40 : bytesT8 M (q + 40) = BitVec.ofNat 64 (2 * n.used) := by
    rw [spill h rfl (by decide)]; rd_log
  refine (St.seq0 (m21_step v outp q pn n.used xdp ndp j0 j7 j11 M (cd h) hk r40 hS.nu_pos (by omega))
    (St.seq0 (m22_step v outp q pn n.used xdp ndp j0 j7 j11 M (cd h) hk r32 r40 hS.nu_pos
      (by omega)) ?_)) cf hat
  refine Triple.lmap (fun cf hc => ⟨M, h, hc⟩) (Triple.countup_from (lo := 0) (n := n.used)
    (P := fun k cf => ∃ M, SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x
      (mLc m q px rho ou n.used) (gW (fastTail n.used (Ws x n rho n.used) k) old n.used)) M ∧
      At 0x80003f14#64 (tL q pn n.used xdp ndp k j0 j7 j11) M (kF v) outp cf)
    (fun k _ hi => ?_) ?_ 0 (Nat.le_refl _) (by omega))
  · refine tex fun M h => ?_
    have hb := tail_lt hP hS (rho := rho) k
    have hs : fastTail n.used (Ws x n rho n.used) k (n.used + k + 1) +
        fastTail n.used (Ws x n rho n.used) k (n.used + k) / 268435456 < 2 ^ 64 := by
      have := tail_lt hP hS (rho := rho) (k + 1) (n.used + k + 1)
      simp only [fastTail, wFix, upd_same] at this; exact this
    exact h.seqD8 .buf rfl (m23t_step v outp q pn n.used xdp ndp k _ _ j0 j7 j11 M (cd h) ⟨hk, by omega⟩
      (wread h rfl (by omega) (by omega) (hb _)) (wread h rfl (by omega) (by omega) (hb _))
      hs hi) (by omega) fun M' h' => fin_of fun cf hc => ⟨M', setW (by rw [gW_upd (by omega)] at h'; exact h'), hc⟩
  · refine tex fun M h => ?_
    have hi1 : n.used - 1 + 1 = n.used := by omega
    have hb := tail_lt hP hS (rho := rho) (n.used - 1)
    have hs : fastTail n.used (Ws x n rho n.used) (n.used - 1) (n.used + (n.used - 1) + 1) +
        fastTail n.used (Ws x n rho n.used) (n.used - 1) (n.used + (n.used - 1)) / 268435456 < 2 ^ 64 := by
      have := tail_lt hP hS (rho := rho) (n.used - 1 + 1) (n.used + (n.used - 1) + 1)
      simp only [fastTail, wFix, upd_same] at this; exact this
    exact h.seqD8 .buf rfl (m23f_step v outp q pn n.used xdp ndp (n.used - 1) _ _ j0 j7 j11 M (cd h) ⟨hk, by omega⟩
      (wread h rfl (by omega) (by omega) (hb _)) (wread h rfl (by omega) (by omega) (hb _))
      hs hi1) (by omega) fun M' h' => fin_of fun cf hc => ⟨M', _, _, _, by
        have h2 : SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x (mLc m q px rho ou n.used)
            (gW (fastTail n.used (Ws x n rho n.used) (n.used - 1 + 1)) old n.used)) M' :=
          setW (by rw [gW_upd (by omega)] at h'; exact h')
        rw [hi1] at h2; exact h2, hc⟩

end rows2

section out
variable {m : Mem} {v : Abi} {outp : Array String} {q px xdp pn ndp : Nat} {x n : MpInt} {rho ou : Nat}
  {ra s0 : BitVec 64}

/-- The kinds of the copy-out: `x`'s digits `ovl Fo x.digit i`. -/
abbrev κO (m : Mem) (ra s0 : BitVec 64) (v : Abi) (q px xdp pn ndp : Nat) (x n : MpInt) (rho ou : Nat)
    (old : Nat → Nat) (i : Nat) : Bf R → Kind :=
  Kind.set (κM m ra s0 v q px xdp pn ndp n x (mLd m q px rho ou n.used) (gW (Wt x n rho) old n.used)) (.o .bD)
    (.mpD xdp x.alloc (ovl (Fo x n rho) x.digit i))

/-- **The copy-out** `x[i] = W[n->used + i] & MASK`, `i ≤ n->used`. -/
theorem copyout (hP : MontRedFast.Pre m (q + 4256) px xdp pn ndp x n rho ra) (hS : Sc x n) (hk : KF q)
    {old : Nat → Nat} {j0 j7 j11 : BitVec 64} {M : Mem}
    (h : SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x (mLd m q px rho ou n.used)
      (gW (Wt x n rho) old n.used)) M) :
    Triple (At 0x80003f58#64 (oL q pn n.used xdp ndp 0 j0 j7 j11) M (kF v) outp)
      (fun cf => ∃ M', SM m q px xdp pn ndp x n (κO m ra s0 v q px xdp pn ndp x n rho ou old (n.used + 1)) M' ∧
        At 0x80003f78#64 (o2L q pn n.used xdp ndp j0 j7 j11) M' (kF v) outp cf) := by
  have := hS.nu_pos; have := hS.nu_le; have := hS.room; have := hS.al_le
  have h0 : SM m q px xdp pn ndp x n (κO m ra s0 v q px xdp pn ndp x n rho ou old 0) M := by
    rw [κO, ovl_zero]
    exact h.congrK (by intro r; rcases r with _ | _ | _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl)
  refine Triple.lmap (fun cf hc => ⟨M, h0, hc⟩) (Triple.countup_from (lo := 0) (n := n.used + 1)
    (P := fun i cf => ∃ M, SM m q px xdp pn ndp x n (κO m ra s0 v q px xdp pn ndp x n rho ou old i) M ∧
      At 0x80003f58#64 (oL q pn n.used xdp ndp i j0 j7 j11) M (kF v) outp cf)
    (fun i _ hi => ?_) ?_ 0 (Nat.le_refl _) (by omega))
  · refine tex fun M h => ?_
    have hw := tail_lt hP hS (rho := rho) n.used (n.used + i)
    refine h.seqOvl (.o .bD) rfl (m26a_step v outp q pn n.used xdp ndp i _ x.alloc j0 j7 j11 M (cd h) (by facts h)
      (by omega) (wread h rfl (by omega) (by omega) hw) (by omega)) (by omega)
      (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)) rfl fun M' h' => ?_
    rw [Kind.set_set] at h'
    exact St.seq0 (m26t_step v outp q pn n.used xdp ndp i j0 j7 j11 M' (cd h') (by facts h') (by omega))
      (fin_of fun cf hc => ⟨M', h', hc⟩)
  · refine tex fun M h => ?_
    have hw := tail_lt hP hS (rho := rho) n.used (n.used + n.used)
    refine h.seqOvl (.o .bD) rfl (m26a_step v outp q pn n.used xdp ndp (n.used + 1 - 1) _ x.alloc j0 j7 j11 M (cd h)
      (by facts h) (by omega) (wread h rfl (by omega) (by omega) hw) (by omega)) (by omega)
      (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)) rfl fun M' h' => ?_
    rw [Kind.set_set, show n.used + 1 - 1 + 1 = n.used + 1 by omega] at h'
    exact St.seq0 (m26f_step v outp q pn n.used xdp ndp (n.used + 1 - 1) j0 j7 j11 M' (cd h') (by facts h')
      (by omega)) (fin_of fun cf hc => ⟨M', h', hc⟩)

end out

/-! ## The end: `x->used`, `mp_clamp`, `mp_cmp_mag`, return or `s_mp_sub` -/

/-- What `mp_clamp` is handed: `used = n->used + 1`, the copy-out's digits. -/
def xm (x n : MpInt) (rho : Nat) : MpInt :=
  MpInt.ofDigits (n.used + 1) x.alloc x.sign (fun i => if i < n.used + 1 then Fo x n rho i else 0)

theorem mag_zero {a : MpInt} (h : a.used = 0) : a.mag = 0 := by unfold MpInt.mag; rw [h]; rfl

theorem ordCode_ne {c : Ordering} (h : c ≠ .lt) : BitVec.ofInt 64 (ordCode c) ≠ m1 := by
  cases c
  · exact absurd rfl h
  · decide
  · decide

section fin
variable {m : Mem} {v : Abi} {outp : Array String} {q px xdp pn ndp : Nat} {x n : MpInt} {rho ou : Nat}
  {ra s0 : BitVec 64}

/-- The saved registers, from the frozen `hi`. -/
theorem hfacts {M : Mem} {κ : Bf R → Kind} (h : SM m q px xdp pn ndp x n κ M)
    (hk' : κ .hi = .frz (mH m ra s0 v q)) (hra : ra.toNat % 4 = 0) (hk : KF q) : HFacts M ra s0 v q :=
  { k := hk, ra_al := hra
    ra_v := by rw [save h hk' (by decide) (by decide)]; rd_log
    s0_v := by rw [save h hk' (by decide) (by decide)]; rd_log
    s1_v := by rw [save h hk' (by decide) (by decide)]; rd_log
    s2_v := by rw [save h hk' (by decide) (by decide)]; rd_log
    s3_v := by rw [save h hk' (by decide) (by decide)]; rd_log
    s4_v := by rw [save h hk' (by decide) (by decide)]; rd_log
    s5_v := by rw [save h hk' (by decide) (by decide)]; rd_log
    s6_v := by rw [save h hk' (by decide) (by decide)]; rd_log
    s7_v := by rw [save h hk' (by decide) (by decide)]; rd_log
    s8_v := by rw [save h hk' (by decide) (by decide)]; rd_log
    s9_v := by rw [save h hk' (by decide) (by decide)]; rd_log
    s10_v := by rw [save h hk' (by decide) (by decide)]; rd_log
    s11_v := by rw [save h hk' (by decide) (by decide)]; rd_log }

/-- The value: `T / R`. -/
theorem xm_mag (hP : MontRedFast.Pre m (q + 4256) px xdp pn ndp x n rho ra) (hS : Sc x n) :
    (xm x n rho).mag = redcT x.mag n.mag rho n.used / radix ^ n.used := by
  have := hS.nu_pos; have := hS.ou_le; have := hS.room
  have hrho : (n.mag % radix * rho + 1) % radix = 0 := by rw [← mul_add_one_mod]; exact hP.rho_ok
  have hv : wVal (W0 x) 0 0 (2 * n.used + 1) = x.mag := by
    unfold wVal MpInt.mag
    rw [natUpTo_congr (2 * n.used + 1) (e := x.digit) (fun i _ => by
      simp only [Nat.not_lt_zero, if_false, W0]; split
      · rfl
      · exact (hP.vx.high_zero i (by omega)).symm)]
    exact natUpTo_zeros _ _ _ (by omega) fun i h1 _ => hP.vx.high_zero i h1
  have hr := fastRows_spec x.mag n.mag rho n.used n.digit (W0 x) rfl hrho hv n.used (Nat.le_refl _)
  have ht := fastTail_val n.used (Ws x n rho n.used) (2 * n.used + 1) n.used (by omega)
  rw [show n.used + n.used = 2 * n.used by omega, hr] at ht
  have ho := fastOut_val x.mag n.mag rho n.used (Wt x n rho) (MpInt.mag_lt hP.vn.toShape) hP.x_lt ht
  rw [← ho]
  show natUpTo (xm x n rho).digit (n.used + 1) = _
  exact natUpTo_congr _ fun i hi => by
    rw [xm, MpInt.ofDigits_digit, if_pos (by omega), if_pos hi]

theorem xm_shape (hP : MontRedFast.Pre m (q + 4256) px xdp pn ndp x n rho ra) (hS : Sc x n) : (xm x n rho).Shape :=
  { len := MpInt.ofDigits_len _ _ _ _
    used_le := by have := hS.room; simp only [xm, MpInt.ofDigits]; omega
    alloc_lt := by simp only [xm, MpInt.ofDigits]; exact hP.vx.alloc_lt
    digit_lt := fun i => by
      rw [xm, MpInt.ofDigits_digit]; split
      · split
        · exact Nat.mod_lt _ radix_pos
        · exact radix_pos
      · exact radix_pos
    high_zero := fun i hi => by
      simp only [xm, MpInt.ofDigits] at hi
      rw [xm, MpInt.ofDigits_digit, if_neg (show ¬ i < n.used + 1 by omega)]; split <;> rfl }

/-- From `3fa0`: `x->used := n->used + 1`, `mp_clamp`, `mp_cmp_mag`, the return or the tail call. -/
theorem fin2 (hP : MontRedFast.Pre m (q + 4256) px xdp pn ndp x n rho ra) (hS : Sc x n) (hk : KF q)
    {old : Nat → Nat} {ml : Mem} {G : Nat → Nat} {M : Mem} {j0 j7 j11 : BitVec 64}
    (h : SM m q px xdp pn ndp x n (Kind.set (κM m ra s0 v q px xdp pn ndp n x ml (gW (Wt x n rho) old n.used))
      (.o .bD) (.mpD xdp x.alloc G)) M)
    (hG : ∀ i, i < x.alloc → (xm x n rho).digit i = G i) (hl24 : bytesT8 ml (q + 24) = BitVec.ofNat 64 px) :
    Triple (At 0x80003fa0#64 (o3L q pn n.used xdp ndp j0 j7 j11) M (kF v) outp)
      (MontRedFast.Ret m v outp (q + 4256) px xdp pn ndp x n rho ra s0) := by
  have := hS.nu_pos; have := hS.nu_le; have := hS.room; have := hS.al_le; have hra := hP.ra_al
  have hxs := xm_shape hP hS; have hmag := xm_mag hP hS
  have hnp : 0 < n.mag := by have := hP.x_lt; rcases Nat.eq_zero_or_pos n.mag with h0 | h0
                             · rw [h0, Nat.zero_mul] at this; omega
                             · exact h0
  have r24 : bytesT8 M (q + 24) = BitVec.ofNat 64 px := by rw [spill h rfl (by decide)]; exact hl24
  refine h.seqU (.o .bS) rfl (m29_step v outp q px pn n.used xdp ndp j0 j7 j11 M (cd h)
    { k := hk, rx := by facts h, rn := by facts h, px_al := by facts h, nu_v := by facts h, px_v := r24
      nu_lt := by omega, code_x := by facts h }) (by omega) fun M1 h1 => ?_
  have h2 := h1.setMp (.o .bS) (.o .bD) rfl rfl (xm x n rho) rfl rfl rfl rfl hG
  refine call_std clamp ⟨px, xdp, xm x n rho⟩ σz h2 (cd h2) 0x024010ef#32 0x1024#21 0x80003fb8#64 hxs
    (fun xcl M2 hcl h3 => ?_) (hsub := fun r => by cases r <;> exact Iv.sub_self _)
  have hcs := ClampPost.spec hxs (by simp only [xm, MpInt.ofDigits]; exact hP.vx.sign_ok) hcl
  have hxal : xcl.alloc = x.alloc := hcl.alloc
  have h4 := (h3.setMp (.o .bS) (.o .bD) rfl rfl xcl rfl rfl rfl hcl.alloc (fun j _ => congrFun hcl.digit j)).congrK
    (κ' := κM m ra s0 v q px xdp pn ndp n xcl ml (gW (Wt x n rho) old n.used))
    (by intro r; rcases r with _ | _ | _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl)
  have r24' : bytesT8 M2 (q + 24) = BitVec.ofNat 64 px := by rw [spill h4 rfl (by decide)]; exact hl24
  refine St.seq0 (m30_step v outp q px pn n.used xdp ndp j0 j7 j11 M2 (cd h4) hk r24') ?_
  refine call_std Std.cmpMag ⟨px, xdp, pn, ndp, xcl, n⟩ σc h4 (cd h4) 0xfa4fc0ef#32 0x1fc7a4#21 0x80003fc4#64
    ⟨hcs.1, hP.vn⟩ (fun _ M3 _ h5 => ?_) (hsub := fun r => by
      cases r <;> first
        | exact Iv.sub_self _
        | (show Iv.Sub ⟨xdp, 4 * xcl.alloc⟩ _; rw [hxal]; exact Iv.sub_self _))
  have hxm : xcl.mag = redcT x.mag n.mag rho n.used / radix ^ n.used := by rw [hcs.2, hmag]
  by_cases hlt : xcl.mag < n.mag
  · have hc : compare xcl.mag n.mag = .lt := Nat.compare_eq_lt.2 hlt
    refine St.seq0 (m31lt_step v outp q pn n.used xdp ndp (BitVec.ofInt 64 (ordCode (compare xcl.mag n.mag))) j0 j7
      j11 M3 (cd h5) (by rw [hc]; decide)) ?_
    refine St.seq0 (m32a_step v outp q M3 (cd h5) hk) ?_
    exact (Triple.rmap (fun cf hc' => ⟨xcl, _, hc'.sub rfl rfl,
      { repr := h5.mpAt (.o .bS) (.o .bD) rfl rfl
        redc := { valid := hcs.1, alloc := hxal
                  mag := by rw [hxm, redc, montOut, if_neg (by omega)]
                  sign := by rw [hcl.sign]; rfl }
        frame := h5.unbuf (by decide) (by simp [Two.lay]) }⟩)
      (m32_step ra s0 v outp q M3 (cd h5) (hfacts h5 rfl hra hk))).pre
  · refine St.seq0 (m31ge_step v outp q pn n.used xdp ndp (BitVec.ofInt 64 (ordCode (compare xcl.mag n.mag))) j0 j7
      j11 M3 (cd h5) (ordCode_ne fun h' => hlt (Nat.compare_eq_lt.1 h'))) ?_
    have r24'' : bytesT8 M3 (q + 24) = BitVec.ofNat 64 px := by rw [spill h5 rfl (by decide)]; exact hl24
    refine St.seq0 (m33a_step v outp q px pn n.used xdp ndp j0 j7 j11 M3 (cd h5) hk r24'') ?_
    refine St.seq0 (m33_step ra s0 v outp q px pn M3 (cd h5) (hfacts h5 rfl hra hk)) ?_
    exact tail_std sSubCA ⟨q + 4256, px, xdp, pn, ndp, xcl, n⟩ σs (h5.forget .hi rfl)
      ⟨hcs.1.toShape, hP.vn.toShape, hcs.1.sign_ok, MpInt.used_le_of_mag_le hcs.1.toShape hP.vn (Nat.le_of_not_lt hlt),
        show (q + 4256) % 16 = 0 by have := hk.q_al; omega, show 48 ≤ q + 4256 by omega⟩ hra
      (fun x2 M4 cf hss h7 hat => by
        have hs2 := SSubPost.spec hcs.1.toShape hP.vn.toShape (Nat.le_of_not_lt hlt) hcs.1.used_le
          hcs.1.alloc_lt hcs.1.sign_ok hss
        exact ⟨x2, M4, hat,
          { repr := h7.mpAt (.o .bS) (.o .bD) rfl rfl
            redc := { valid := hs2.1, alloc := by rw [hss.alloc, hxal]
                      mag := by rw [hs2.2, hxm, redc, montOut, if_pos (by omega)]
                      sign := by
                        rw [hss.sign]; split
                        · rfl
                        · rw [hcl.sign, if_neg]
                          · rfl
                          · intro h0; have := mag_zero h0; omega }
            frame := h7.unbuf (by decide) (by simp [Two.lay]) }⟩)
      (hsub := fun r => by
        cases r <;> first
          | iv_omega
          | exact Iv.sub_self _
          | (show Iv.Sub ⟨xdp, 4 * xcl.alloc⟩ _; rw [hxal]; exact Iv.sub_self _))

end fin

/-- A region's kind, both sides computed to a constructor first. -/
macro "kindr" : tactic => `(tactic|
  first
  | (show Kind.frz _ = _; rfl)
  | (show Kind.mpS _ _ _ = _; rfl)
  | (show Kind.mpD _ _ _ = _; rfl)
  | (show Kind.ram = _; rfl)
  | (show Kind.code = _; rfl))

section stE
variable {m : Mem} {v : Abi} {outp : Array String} {q px xdp pn ndp : Nat} {x n : MpInt} {rho : Nat}
  {ra s0 : BitVec 64}

theorem hG1 (hS : Sc x n) (hx : x.Shape) (i : Nat) (hi : i < x.alloc) (hle : x.used ≤ n.used + 1) :
    (xm x n rho).digit i = ovl (Fo x n rho) x.digit (n.used + 1) i := by
  rw [xm, MpInt.ofDigits_digit, if_pos hi]; unfold ovl; split
  · rfl
  · exact (hx.high_zero i (by omega)).symm

theorem hG2 (hS : Sc x n) (hx : x.Shape) (i : Nat) (hi : i < x.alloc) :
    (xm x n rho).digit i = zfill (ovl (Fo x n rho) x.digit (n.used + 1)) (n.used + 1) x.used i := by
  rw [xm, MpInt.ofDigits_digit, if_pos hi]; unfold zfill ovl
  by_cases h1 : i < n.used + 1
  · rw [if_pos h1, if_neg (by omega), if_pos h1]
  · rw [if_neg h1]; split
    · rfl
    · exact (hx.high_zero i (by omega)).symm

/-- From `3f78`: `MP_ZERO_DIGITS`, then `fin2`. -/
theorem stageE (hP : MontRedFast.Pre m (q + 4256) px xdp pn ndp x n rho ra) (hS : Sc x n) (hk : KF q)
    {old : Nat → Nat} {M : Mem} {j0 j7 j11 : BitVec 64}
    (h : SM m q px xdp pn ndp x n (κO m ra s0 v q px xdp pn ndp x n rho x.used old (n.used + 1)) M) :
    Triple (At 0x80003f78#64 (o2L q pn n.used xdp ndp j0 j7 j11) M (kF v) outp)
      (MontRedFast.Ret m v outp (q + 4256) px xdp pn ndp x n rho ra s0) := by
  have := hS.nu_pos; have := hS.nu_le; have := hS.room; have := hS.al_le; have := hS.ou_le
  have hxs := hP.vx.toShape
  have r16 : bytesT8 M (q + 16) = BitVec.ofNat 64 x.used := by rw [spill h rfl (by decide)]; rd_log
  by_cases h1 : n.used + 1 ≤ x.used
  · refine h.seqW .lo rfl (m27p_step v outp q pn n.used xdp ndp x.used j0 j7 j11 M (cd h) hk r16 h1 (by omega))
      fun M1 h1' => ?_
    have s16 : bytesT8 M1 (q + 16) = BitVec.ofNat 64 (x.used - (n.used + 1)) := by
      rw [spill h1' rfl (by decide)]; rd_log
    by_cases h2 : n.used + 1 < x.used
    · refine St.seq0 (m28n_step v outp q pn n.used xdp ndp x.used j0 j7 j11 M1 (cd h1') hk s16 h2 (by omega)) ?_
      refine call_std memsetD ⟨xdp, x.alloc, ovl (Fo x n rho) x.digit (n.used + 1), n.used + 1, x.used,
        x.used - (n.used + 1)⟩ σd h1' (cd h1') 0x408050ef#32 0x5408#21 0x80003fa0#64
        ⟨show n.used + 1 ≤ x.used by omega, show x.used ≤ x.alloc from hxs.used_le, rfl⟩ (fun _ M2 _ h2' => ?_)
        (hsub := fun r => by cases r <;> exact Iv.sub_self _)
      exact (fin2 hP hS hk (h2'.congrK (by intro r; rcases r with _ | _ | _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> kindr))
        (fun i hi => hG2 hS hxs i hi) (by rd_log)).pre
    · refine St.seq0 (m28z_step v outp q pn n.used xdp ndp (x.used - (n.used + 1)) j0 j7 j11 M1 (cd h1') hk s16
        (by rw [show x.used - (n.used + 1) = 0 by omega]; decide)) ?_
      exact fin2 hP hS hk (h1'.congrK (by intro r; rcases r with _ | _ | _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> kindr))
        (fun i hi => hG1 hS hxs i hi (by omega)) (by rd_log)
  · refine h.seqW .lo rfl (m27n_step v outp q pn n.used xdp ndp x.used j0 j7 j11 M (cd h) hk r16 (by omega)
      (by omega)) fun M1 h1' => ?_
    have s16 : bytesT8 M1 (q + 16) = BitVec.ofNat 64 (18446744073709551616 - (n.used + 1 - x.used)) := by
      rw [spill h1' rfl (by decide)]; rd_log
    refine St.seq0 (m28z_step v outp q pn n.used xdp ndp _ j0 j7 j11 M1 (cd h1') hk s16
      (bge_zero_neg (by omega) (by omega))) ?_
    exact fin2 hP hS hk (h1'.congrK (by intro r; rcases r with _ | _ | _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> kindr))
      (fun i hi => hG1 hS hxs i hi (by omega)) (by rd_log)

end stE

section top
variable {m : Mem} {v : Abi} {outp : Array String} {q px xdp pn ndp : Nat} {x n : MpInt} {rho : Nat}
  {ra s0 : BitVec 64}

/-- From the rows' set-up (`3e50`) to the end. -/
theorem fromRows (hP : MontRedFast.Pre m (q + 4256) px xdp pn ndp x n rho ra) (hS : Sc x n) (hk : KF q)
    {old : Nat → Nat} {M : Mem}
    (h : SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x (mLb m q px rho x.used n.used)
      (gW (W0 x) old n.used)) M) :
    Triple (At 0x80003e50#64 (hL0 s0 v q pn n.used xdp) M (kF v) outp)
      (MontRedFast.Ret m v outp (q + 4256) px xdp pn ndp x n rho ra s0) := by
  have := hS.nu_pos; have := hS.nu_le
  refine h.seqW .lo rfl (m15_step s0 v outp q pn n.used xdp ndp M (cd h) hk (by facts h) (by omega)) fun M1 h1 => ?_
  have h2 : SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x (mLc m q px rho x.used n.used)
      (gW (Ws x n rho 0) old n.used)) M1 :=
    h1.congrK (by intro r; rcases r with _ | _ | _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> kindr)
  refine Triple.seq (fin_of fun cf hc => ⟨M1, s0, v.s.s7, v.s.s11, h2, hc⟩)
    (Triple.seq (rows (ou := x.used) hP hS hk) (Triple.seq (tail hP hS hk) ?_))
  intro cf ⟨M2, j0, j7, j11, h3, hat⟩
  refine (h3.seqW .lo rfl (m24_step v outp q pn n.used xdp ndp j0 j7 j11 M2 (cd h3) hk (by omega))
    fun M3 h4 => ?_) cf hat
  have h5 : SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x (mLd m q px rho x.used n.used)
      (gW (Wt x n rho) old n.used)) M3 :=
    h4.congrK (by intro r; rcases r with _ | _ | _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> kindr)
  have r32 : bytesT8 M3 (q + 32) = BitVec.ofNat 64 (8 * n.used) := by rw [spill h5 rfl (by decide)]; rd_log
  refine St.seq0 (m25_step v outp q pn n.used xdp ndp j0 j7 j11 M3 (cd h5) hk r32 (by omega)) ?_
  exact Triple.seq (copyout hP hS hk h5) (tex fun M4 h6 => stageE hP hS hk h6)

/-- The copy-in loop and the `memset` of the high columns, to the rows. -/
theorem copyin (hP : MontRedFast.Pre m (q + 4256) px xdp pn ndp x n rho ra) (hS : Sc x n) (hk : KF q)
    (hou : 0 < x.used) {old : Nat → Nat} {M : Mem}
    (h : SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x (mLa m q px rho x.used)
      (ovl (h32 (W0 x)) old (2 * 0))) M) :
    Triple (At 0x80003e2c#64 (cL s0 v q pn n.used x.used xdp 0) M (kF v) outp)
      (MontRedFast.Ret m v outp (q + 4256) px xdp pn ndp x n rho ra s0) := by
  have := hS.nu_pos; have := hS.nu_le; have := hS.ou_le; have := hS.room; have := hS.al_le
  have hxs := hP.vx.toShape; have := hxs.used_le
  have hga := hP.gx.ds.hi_le; simp only [Layout.sizeofDigit] at hga
  refine Triple.lmap (fun cf hc => ⟨M, h, hc⟩) (Triple.countup_from (lo := 0) (n := x.used) (P := fun i cf => ∃ M,
    SM m q px xdp pn ndp x n (κM m ra s0 v q px xdp pn ndp n x (mLa m q px rho x.used)
      (ovl (h32 (W0 x)) old (2 * i))) M ∧ At 0x80003e2c#64 (cL s0 v q pn n.used x.used xdp i) M (kF v) outp cf)
    (fun i _ hi => ?_) ?_ 0 (Nat.le_refl _) hou)
  · refine tex fun M h => ?_
    have e : W0 x i = x.digit i := if_pos (by omega)
    exact h.seqD8 .buf rfl (m8t_step s0 v outp q pn n.used x.used xdp i (x.digit i) M (cd h) ⟨hk, by omega⟩
      (by facts h) hi (by omega)) (by omega) fun M' h' => fin_of fun cf hc => ⟨M', setW (by
        rw [← e, gC_step] at h'; exact h'), hc⟩
  · refine tex fun M h => ?_
    have e : W0 x (x.used - 1) = x.digit (x.used - 1) := if_pos (by omega)
    refine h.seqD8 .buf rfl (m8f_step s0 v outp q pn n.used x.used xdp (x.used - 1) (x.digit (x.used - 1)) M (cd h)
      ⟨hk, by omega⟩ (by facts h) (by omega) (by omega)) (by omega) fun M1 h1 => ?_
    rw [← e, gC_step, show x.used - 1 + 1 = x.used by omega] at h1
    have h2 := setW h1
    refine h2.seqW .lo rfl (m9_step s0 v outp q pn n.used x.used xdp M1 (cd h2) hk (by omega)) fun M2 h3 => ?_
    refine St.seq0 (m9t_step s0 v outp q pn n.used x.used xdp M2 (cd h3) (by omega) (by omega) (by omega)) ?_
    refine St.seq0 (m10_step s0 v outp q pn n.used x.used xdp M2 (cd h3) hk (by omega) hou (by omega) (by omega)) ?_
    refine call_std memsetD ⟨q + 48, 1024, ovl (h32 (W0 x)) old (2 * x.used), 2 * x.used, 2 * (2 * n.used + 1),
      2 * (2 * n.used + 1) - 2 * x.used⟩ σw h3 (cd h3) 0x36c050ef#32 0x536c#21 0x8000403c#64
      ⟨show 2 * x.used ≤ 2 * (2 * n.used + 1) by omega, show 2 * (2 * n.used + 1) ≤ 1024 by omega, rfl⟩
      (fun _ M3 _ h4 => ?_)
    have hle : x.used ≤ 2 * n.used + 1 := by omega
    refine St.seq0 (m11_step s0 v outp q pn n.used xdp M3 (cd h4)) ?_
    exact fromRows hP hS hk (h4.congrK (by
      intro r; rcases r with _ | _ | _ | ⟨_ | _ | _ | _ | _ | _⟩ <;>
        first | (show Kind.mpD _ _ (zfill _ _ _) = _; rw [gC_fill hle]; try rfl) | kindr))

end top

/-- **`s_mp_montgomery_reduce_fast` on the machine.** -/
theorem correct : Api.MontRedFast.Statement := by
  intro m v outp sp px xdp pn ndp x n rho ra s0 hP
  obtain ⟨q, rfl⟩ : ∃ q, sp = q + 4256 := ⟨sp - 4256, by have := hP.sp_ge; omega⟩
  have hS := sc_of hP; have hk := kf_of hP
  have := hS.nu_pos; have := hS.nu_le; have := hS.ou_le; have := hS.room; have := hS.al_le
  have hxs := hP.vx.toShape; have := hxs.used_le; have := hP.vx.alloc_lt
  have h0 := St.twoB (f := 4256) (a := 48) (B := 4096) hP.rn hP.gn hP.rx hP.gx hP.rs hP.img hP.lay (by decide)
    (by decide)
  refine Triple.lmap (fun cf h => h.sub (L' := entL ra s0 v q px pn rho) (K' := kF v) rfl rfl) ?_
  refine St.seq0 (m1_step ra s0 v outp q px pn rho x.used m (cd h0) hk (by facts h0)) ?_
  refine h0.seqW .hi rfl (m2a_step ra s0 v outp q px pn rho x.used m (cd h0) hk) fun M1 h1 => ?_
  refine h1.seqW .hi rfl (m2b_step ra s0 v outp q px pn rho x.used M1 (cd h1) hk) fun M2 h2 => ?_
  refine h2.seqW .lo rfl (m3_step ra s0 v outp q px pn rho x.used M2 (cd h2) hk) fun M3 h3 => ?_
  refine St.seq0 (m4_step ra s0 v outp q px pn rho x.used M3 (cd h3) hk
    (by rw [spill h3 rfl (by decide)]; rd_log) (by omega)) ?_
  refine h3.seqW .lo rfl (m5_step ra s0 v outp q px pn rho x.used n.used x.alloc M3 (cd h3) hk (by facts h3)
    (by omega)) fun M4 h4 => ?_
  have h5 : SM m q px xdp pn ndp x n (Bf.kind (Two.kind pn ndp px xdp n x) (mLa m q px rho x.used)
      (mH m ra s0 v q) .ram) M4 :=
    h4.congrK (by intro r; rcases r with _ | _ | _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> kindr)
  have hxf : XFacts M4 q px xdp :=
    { k := hk, rx := by facts h5, px_v := by rw [spill h5 rfl (by decide)]; rd_log, xdp_v := by facts h5 }
  have h6 := h5.ramDig .buf rfl (dp := q + 48) (n := 1024) (by simp only [ρm, Bf.lay, Two.lay]; omega) rfl
    (by have := hk.q_al; omega)
  rcases Nat.eq_zero_or_pos x.used with hou0 | hou
  · have e : m5L s0 v q pn n.used x.used = m5L s0 v q pn n.used 0 := by rw [hou0]
    rw [e]
    refine St.seq0 (m6z_step s0 v outp q px pn n.used xdp M4 (cd h6) hxf) ?_
    refine h6.seqW .lo rfl (m13a_step s0 v outp q pn n.used xdp M4 (cd h6) hk (by omega)) fun M5 h7 => ?_
    refine St.seq0 (m13b_step s0 v outp q pn n.used xdp M5 (cd h7) hk (by omega)) ?_
    refine call_std memsetD ⟨q + 48, 1024, rdD M4 (q + 48), 0, 2 * (2 * n.used + 1), 2 * (2 * n.used + 1) - 0⟩ σw h7
      (cd h7) 0x2d8050ef#32 0x52d8#21 0x800040d0#64
      ⟨show 0 ≤ 2 * (2 * n.used + 1) by omega, show 2 * (2 * n.used + 1) ≤ 1024 by omega, rfl⟩
      (fun _ M6 _ h8 => ?_)
    refine St.seq0 (m14_step s0 v outp q pn n.used xdp M6 (cd h8) (by omega) (by omega)) ?_
    exact fromRows (old := rdD M4 (q + 48)) hP hS hk (h8.congrK (by
      intro r; rcases r with _ | _ | _ | ⟨_ | _ | _ | _ | _ | _⟩ <;>
        first | (show Kind.mpD _ _ (zfill _ _ _) = _; rw [gC_zero hou0]; try rfl) | kindr))
  · refine St.seq0 (m6n_step s0 v outp q px pn n.used x.used xdp M4 (cd h6) hxf hou (by omega)) ?_
    refine St.seq0 (m7_step s0 v outp q pn n.used x.used xdp M4 (cd h6) hk (by omega)) ?_
    refine copyin (old := rdD M4 (q + 48)) hP hS hk hou (h6.congrK (by
      intro r; rcases r with _ | _ | _ | ⟨_ | _ | _ | _ | _ | _⟩ <;>
        first | (show Kind.mpD _ _ _ = _; rw [show 2 * 0 = 0 from rfl, ovl_zero]; try rfl) | kindr))

end Tom.Machine.Fn.MontRedFast
