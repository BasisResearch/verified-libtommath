import Tom.Machine.Fn.DrReduce
import Tom.Machine.Api.DrReduce
import Tom.Machine.Api.Std

/-!
# `mp_dr_reduce` on the machine: the whole function

The segments of `Tom.Machine.Fn.DrReduce` and the contracts of `__muldi3`,
`memset` (`memsetD`), `mp_clamp`, `mp_cmp_mag` and `s_mp_sub(x, n, x)`
(`sSubCA`) by `call_std` (`Kit/Meet.lean`, `Api/StdLib.lean`, `Api/Std.lean`).
Regions: `Two`'s (`n` read, `x` written) with the stack cut into our 128-byte
frame and the 48 bytes of `s_mp_sub` below (`Split`). The digit loop is
`Triple.countup_from` over `drRow` (`St.seqD` into `x`'s digits); a pass
leaves `drPass` (`pass_digit`), whose value is `drFold` (`pass_mag`). The
`goto top` loop is an induction on the fuel of `redLoop` (`top`): the value
after a pass that subtracts is below the value before (`drFold_le`).
`x`'s `alloc` is kept literally `x->alloc` in the kinds (`xa`), re-abstracted
by `St.setMp` after each call that changes `x`.
-/


namespace Tom.Machine.Fn.DrReduce

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api Tom.Machine.Std
open Tom.Machine.Api.Two (R isW)
open Tom.Reduce Tom.Mont

/-! ## The value of a pass -/

section value
variable {f : Nat → Nat} {m k u : Nat}

theorem upd_self (f : Nat → Nat) (i : Nat) : upd f i (f i) = f := by
  funext j; unfold upd; split <;> simp_all

/-- Above `x->used ≤ m` a pass changes nothing. -/
theorem drRow_zero (hf : ∀ i, f i < radix) (hz : ∀ j, u ≤ j → f j = 0) (hu : u ≤ m) :
    ∀ i, drRow f m k i = ⟨f, 0⟩
  | 0 => rfl
  | i + 1 => by
    simp only [drRow, drRow_zero hf hz hu i, hz (m + i) (by omega), Nat.mul_zero, cstep, Nat.zero_add,
      Nat.add_zero, Nat.mod_eq_of_lt (hf i), Nat.div_eq_of_lt (hf i), upd_self]

/-- `drPass` is zero from `x->used` on. -/
theorem drPass_high (hf : ∀ i, f i < radix) (hz : ∀ j, u ≤ j → f j = 0) : ∀ i, u ≤ i → drPass f m k i = 0 := by
  intro i hi
  unfold drPass
  by_cases h1 : i < m
  · rw [if_pos h1, drRow_zero hf hz (by omega) m]; exact hz i hi
  · rw [if_neg h1]
    by_cases h2 : i = m
    · rw [if_pos h2, drRow_zero hf hz (by omega) m]
    · rw [if_neg h2]

/-- **A pass's value**: `drFold` of the value before. -/
theorem pass_mag (hf : ∀ i, f i < radix) (hz : ∀ j, u ≤ j → f j = 0) (hu : u ≤ 2 * m) :
    natUpTo (drPass f m k) u = drFold m k (natUpTo f u) := by
  have hN1 : natUpTo (drPass f m k) (max u (m + 1)) = natUpTo (drPass f m k) u :=
    natUpTo_zeros _ _ _ (Nat.le_max_left _ _) fun i h1 _ => drPass_high hf hz i h1
  have hN2 : natUpTo (drPass f m k) (max u (m + 1)) = natUpTo (drPass f m k) (m + 1) :=
    natUpTo_zeros _ _ _ (Nat.le_max_right _ _) fun i h1 _ => by
      unfold drPass; rw [if_neg (by omega), if_neg (by omega)]
  have h2m : natUpTo f (2 * m) = natUpTo f u := natUpTo_zeros _ _ _ hu fun i h1 _ => hz i h1
  rw [← hN1, hN2, drPass_val f m k hf, h2m]

/-- **A pass's digits**: the loop's, `x[m] = mu`, zero up to `x->used` (`MP_ZERO_DIGITS`). -/
theorem pass_digit (hz : ∀ j, u ≤ j → f j = 0) (j : Nat) :
    zfill (upd (drRow f m k m).dig m (drRow f m k m).u) (m + 1) u j = drPass f m k j := by
  unfold zfill drPass upd
  by_cases h1 : j < m
  · simp only [show ¬ (m + 1 ≤ j ∧ j < u) by omega, show ¬ j = m by omega, h1, if_false, if_true]
  · by_cases h2 : j = m
    · subst h2; simp only [show ¬ (j + 1 ≤ j ∧ j < u) by omega, h1, if_false, if_true]
    · by_cases h3 : m + 1 ≤ j ∧ j < u
      · rw [if_pos h3, if_neg h1, if_neg h2]
      · simp only [h3, h1, h2, if_false]
        rw [drRow_out f m k m j (by omega)]; exact hz j (by omega)

theorem zfill_nil (g : Nat → Nat) {i k : Nat} (h : k ≤ i) : zfill g i k = g := by
  funext j; unfold zfill; rw [if_neg (by omega)]

/-- The fold does not grow the value (`k < radix ≤ radix^m`). -/
theorem drFold_le (hm : 1 ≤ m) (hk : k < radix) {a0 a : Nat} (ha0 : a0 < radix ^ (2 * m)) (ha : a ≤ a0) :
    drFold m k a ≤ a := by
  have hR : radix ≤ radix ^ m := by
    calc radix = radix ^ 1 := (Nat.pow_one _).symm
      _ ≤ radix ^ m := Nat.pow_le_pow_right radix_pos hm
  exact (drFold_ok m k (radix ^ m - k) a0 (by omega) ha0).le a ha

theorem drFold_zero : drFold m k 0 = 0 := by simp [drFold]

end value

theorem used_le_of_lt {a : MpInt} (ha : a.Valid) {j : Nat} (h : a.mag < radix ^ j) : a.used ≤ j := by
  rcases Nat.eq_zero_or_pos a.used with h0 | h0
  · omega
  · have := MpInt.mag_ge ha h0
    have : radix ^ (a.used - 1) < radix ^ j := Nat.lt_of_le_of_lt this h
    have := (Nat.pow_lt_pow_iff_right (by simp only [radix, Layout.digitBits]; decide)).1 this
    omega

theorem used_zero_of_mag {a : MpInt} (ha : a.Valid) (h : a.mag = 0) : a.used = 0 := by
  rcases Nat.eq_zero_or_pos a.used with h0 | h0
  · exact h0
  · have := MpInt.mag_ge ha h0; have := Nat.pow_pos (n := a.used - 1) radix_pos; omega

theorem mag_zero_of_used {a : MpInt} (h : a.used = 0) : a.mag = 0 := by
  unfold MpInt.mag; rw [h]; rfl

/-- `x` with `alloc` literally `x->alloc`. -/
abbrev xa (x : MpInt) (u sg : Nat) (ds : List Nat) : MpInt := ⟨u, x.alloc, sg, ds⟩

theorem xa_eq {x a : MpInt} (h : a.alloc = x.alloc) : xa x a.used a.sign a.digits = a := by
  cases a; simp only at h; subst h; rfl

/-! ## The machine -/

/-- A region's kind, both sides computed to a constructor first (comparing two
`Split.kind`s argument-wise would unfold the frame's write logs). -/
macro "kind_rfl" : tactic => `(tactic|
  first
  | (show Kind.frz _ = _; rfl)
  | (show Kind.mpS _ _ _ = _; rfl)
  | (show Kind.mpD _ _ _ = _; rfl)
  | (show Kind.ram = _; rfl)
  | (show Kind.code = _; rfl))

abbrev ρd (sp px xdp pn ndp : Nat) (x n : MpInt) := Split.lay (Two.lay 176 sp pn ndp px xdp n x) R.stk 128

abbrev Wd : List (Option R) := [none, some .stk, some .bS, some .bD]

/-- The state over our regions. -/
abbrev SD (m : Mem) (sp px xdp pn ndp : Nat) (x n : MpInt) (κ : Option R → Kind) (M : Mem) : Prop :=
  St (ρd sp px xdp pn ndp x n) (Split.wr isW) Wd κ m M

/-- Our frame after the prologue. -/
abbrev mF (m : Mem) (ra s0 : BitVec 64) (v : Abi) (sp nm : Nat) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog m [(sp - 56, 8, v.s.s5)]) (log3 ra v sp)) (log4a v sp))
    (log4b s0 v sp)) (log4c sp nm)

/-- The kinds at `top` with `x` holding `xc`. -/
abbrev κT (m : Mem) (ra s0 : BitVec 64) (v : Abi) (sp px xdp pn ndp : Nat) (n xc : MpInt) : Option R → Kind :=
  Split.kind (Two.kind pn ndp px xdp n xc) (mF m ra s0 v sp n.used)

/-- The kinds in the digit loop: `x`'s digits after `i` steps. -/
abbrev κI (m : Mem) (ra s0 : BitVec 64) (v : Abi) (sp px xdp pn ndp : Nat) (n xc : MpInt) (k i : Nat) :
    Option R → Kind :=
  Kind.set (κT m ra s0 v sp px xdp pn ndp n xc) (some .bD) (.mpD xdp xc.alloc (drRow xc.digit n.used k i).dig)

def σm : Cd → Option R := fun _ => some .code

def σms : Dz → Option R
  | .D => some .bD
  | .code => some .code

def σz : Ob → Option R
  | .S => some .bS
  | .D => some .bD
  | .code => some .code

def σc : Cm → Option R
  | .aS => some .bS
  | .aD => some .bD
  | .bS => some .aS
  | .bD => some .aD
  | .code => some .code

def σs : BinA.R → Option R
  | .stk => some .stk
  | .aS => some .bS
  | .aD => some .bD
  | .bS => some .aS
  | .bD => some .aD
  | .code => some .code

theorem cd {m M : Mem} {sp px xdp pn ndp : Nat} {x n : MpInt} {κ : Option R → Kind}
    (h : SD m sp px xdp pn ndp x n κ M) (hk : κ (some .code) = .code := by rfl) :
    CodeAt M mpDrReduceBase mpDrReduceCode :=
  (h.img (some .code) hk).mpDrReduce

/-- What holds at `top`, fuel `F` left. -/
structure TopC (x n : MpInt) (k F : Nat) (xc : MpInt) : Prop where
  valid : xc.Valid
  le : xc.mag ≤ x.mag
  lt : xc.mag < F
  tgt : redLoop (drFold n.used k) n.mag F xc.mag = redLoop (drFold n.used k) n.mag (x.mag + 1) x.mag
  sign : xc.sign = if xc.used = 0 then Layout.mpZpos else x.sign

/-- The scalars every step needs. -/
structure Sc (x n : MpInt) (k : Nat) : Prop where
  m_pos : 1 ≤ n.used
  m_lt : n.used < 2 ^ 29
  room : 2 * n.used ≤ x.alloc
  al_le : x.alloc ≤ 2 ^ 29
  k_lt : k < radix

theorem sc_of {m : Mem} {sp px xdp pn ndp : Nat} {x n : MpInt} {k : Nat} {ra : BitVec 64}
    (hP : DrReduce.Pre m sp px xdp pn ndp x n k ra) : Sc x n k := by
  have h1 := hP.gx.ds.lo_ge; have h2 := hP.gx.ds.hi_le; simp only [Layout.sizeofDigit] at h1 h2
  have hroom := hP.room
  have hm : 1 ≤ n.used := by
    rcases Nat.eq_zero_or_pos n.used with h | h
    · have := mag_zero_of_used h; have := hP.n_pos; omega
    · exact h
  exact ⟨hm, by omega, hroom, by omega, hP.k_lt⟩

section run
variable {m : Mem} {v : Abi} {outp : Array String} {sp px xdp pn ndp : Nat} {x n : MpInt} {k : Nat}
  {ra s0 : BitVec 64}

/-- One step of the digit loop: `x[m + i]`, `__muldi3`, `x[i]`, to `56a4`. -/
theorem body (hP : DrReduce.Pre m sp px xdp pn ndp x n k ra) (hS : Sc x n k) {xc : MpInt} (hs : xc.Shape)
    (hal : xc.alloc = x.alloc) {i : Nat} (hi : i < n.used) {M : Mem}
    (h : SD m sp px xdp pn ndp x n (κI m ra s0 v sp px xdp pn ndp n xc k i) M) {Q : Vsa.Machine.Config → Prop}
    (kont : ∀ M', SD m sp px xdp pn ndp x n (κI m ra s0 v sp px xdp pn ndp n xc k i) M' →
      Triple (At 0x800056a4#64 (sI sp px pn k n.used xdp i (drRow xc.digit n.used k i).u
        (xc.digit (n.used + i) * k + xc.digit i + (drRow xc.digit n.used k i).u)) M' (kF v) outp) Q) :
    Triple (At 0x80005680#64 (iL sp px pn k n.used xdp i (drRow xc.digit n.used k i).u) M (kF v) outp) Q := by
  have := hS.room; have := hS.m_lt
  have hb := drRow_bound xc.digit n.used k hs.digit_lt hS.k_lt i
  have e1 : (drRow xc.digit n.used k i).dig (n.used + i) = xc.digit (n.used + i) :=
    drRow_out _ _ _ i _ (by omega)
  have e2 : (drRow xc.digit n.used k i).dig i = xc.digit i := drRow_out _ _ _ i _ (Nat.le_refl _)
  have hd := h.dig (some .bD) rfl
  have hy : DRead M (xdp + 4 * (n.used + i)) (xc.digit (n.used + i)) :=
    ⟨Ram.sub hd.ram (by omega) (by omega), by rw [← e1]; exact hd.arr _ (by omega),
     Nat.lt_of_lt_of_le (hs.digit_lt _) (by decide)⟩
  refine St.seq0 (iA_step v outp sp px pn k n.used xdp i _ _ M (cd h) hy)
    (call_std muldi3 ⟨xc.digit (n.used + i), k⟩ σm h (cd h) 0x6b5110ef#32 0x11eb4#21 0x80005690#64 trivial
      fun _ M' _ h' => ?_)
  have hd' := h'.dig (some .bD) rfl
  have hu : (drRow xc.digit n.used k i).u < radix := hb.2
  have hk := hS.k_lt; have hx := hs.digit_lt (n.used + i); have hxi := hs.digit_lt i
  have hp : xc.digit (n.used + i) * k ≤ (radix - 1) * (radix - 1) := Nat.mul_le_mul (by omega) (by omega)
  refine St.seq0 (iB1_step v outp sp px pn k n.used xdp i _ _ _ M' (cd h')
    ⟨Ram.sub hd'.ram (by omega) (by omega), by rw [← e2]; exact hd'.arr _ (by omega),
     Nat.lt_of_lt_of_le hxi (by decide)⟩ (Nat.lt_of_lt_of_le hu (by decide))
    (by simp only [radix, Layout.digitBits] at *; omega)) (kont M' h')

theorem drRow_succ_eq {f : Nat → Nat} {nm k i : Nat} :
    f (nm + i) * k + f i + (drRow f nm k i).u = k * f (nm + i) + (drRow f nm k i).u + (drRow f nm k i).dig i := by
  rw [drRow_out f nm k i i (Nat.le_refl _), Nat.mul_comm]; omega

/-- **The digit loop**: from `i = 0` to the carry `mu` at `56bc`. -/
theorem inner (hP : DrReduce.Pre m sp px xdp pn ndp x n k ra) (hS : Sc x n k) {xc : MpInt} (hs : xc.Shape)
    (hal : xc.alloc = x.alloc) {Q : Vsa.Machine.Config → Prop}
    (kont : ∀ M, SD m sp px xdp pn ndp x n (κI m ra s0 v sp px xdp pn ndp n xc k n.used) M →
      Triple (At 0x800056bc#64 (fL sp px pn k n.used xdp (drRow xc.digit n.used k n.used).u) M (kF v) outp) Q)
    {M : Mem} (h : SD m sp px xdp pn ndp x n (κI m ra s0 v sp px xdp pn ndp n xc k 0) M) :
    Triple (At 0x80005680#64 (iL sp px pn k n.used xdp 0 0) M (kF v) outp) Q := by
  have := hS.room; have := hS.m_lt; have := hS.m_pos; have := hS.al_le
  have hxa := hP.gx.ds_al
  have hga := hP.gx.ds.hi_le; simp only [Layout.sizeofDigit] at hga
  have hrb : ∀ i, (drRow xc.digit n.used k i).u < radix ∧ xc.digit (n.used + i) * k + xc.digit i +
      (drRow xc.digit n.used k i).u < radix * radix := fun i => by
    have hb := drRow_bound xc.digit n.used k hs.digit_lt hS.k_lt i
    have hk := hS.k_lt; have hx := hs.digit_lt (n.used + i); have hxi := hs.digit_lt i
    have hp : xc.digit (n.used + i) * k ≤ (radix - 1) * (radix - 1) := Nat.mul_le_mul (by omega) (by omega)
    refine ⟨hb.2, ?_⟩
    have := hb.2; simp only [radix, Layout.digitBits] at *; omega
  have key : ∀ i, i < n.used → ∀ M', SD m sp px xdp pn ndp x n (Kind.set (κI m ra s0 v sp px xdp pn ndp n xc k i)
      (some .bD) (.mpD xdp xc.alloc (fun j => if j = i then (xc.digit (n.used + i) * k + xc.digit i +
        (drRow xc.digit n.used k i).u) % 268435456 else (drRow xc.digit n.used k i).dig j))) M' →
      SD m sp px xdp pn ndp x n (κI m ra s0 v sp px xdp pn ndp n xc k (i + 1)) M' := fun i _ M' h' => by
    rw [Kind.set_set] at h'
    have e : (fun j => if j = i then (xc.digit (n.used + i) * k + xc.digit i + (drRow xc.digit n.used k i).u) %
        268435456 else (drRow xc.digit n.used k i).dig j) = (drRow xc.digit n.used k (i + 1)).dig := by
      funext j; simp only [drRow, cstep, upd]; rw [drRow_succ_eq]; rfl
    rw [e] at h'; exact h'
  have keyu : ∀ i, (xc.digit (n.used + i) * k + xc.digit i + (drRow xc.digit n.used k i).u) / 268435456 =
      (drRow xc.digit n.used k (i + 1)).u := fun i => by
    simp only [drRow, cstep]; rw [drRow_succ_eq]; rfl
  refine Triple.lmap (fun cf hc => ⟨M, h, hc⟩) (Triple.countup_from (lo := 0) (n := n.used)
    (P := fun i cf => ∃ M, SD m sp px xdp pn ndp x n (κI m ra s0 v sp px xdp pn ndp n xc k i) M ∧
      At 0x80005680#64 (iL sp px pn k n.used xdp i (drRow xc.digit n.used k i).u) M (kF v) outp cf)
    (fun i _ hi => ?_) ?_ 0 (Nat.le_refl _) (by omega))
  · intro cf ⟨M, h, hat⟩
    have hr := hrb i
    refine (body hP hS hs hal (by omega) h fun M' h' => ?_) cf hat
    refine h'.seqD (some .bD) rfl (iBt_step v outp sp px pn k n.used xdp i _
      (xc.digit (n.used + i) * k + xc.digit i + (drRow xc.digit n.used k i).u) xc.alloc M' (cd h') (by facts h')
      (by simp only [radix, Layout.digitBits] at hr; omega) (by simp only [radix, Layout.digitBits] at hr; omega)
      hi (by omega)) (by omega) (by omega) fun M3 h3 cf' hc' => ⟨cf', Vsa.Machine.Steps.refl _, M3, key i (by omega) M3 h3,
        by rw [← keyu]; exact hc'⟩
  · intro cf ⟨M, h, hat⟩
    have hr := hrb (n.used - 1)
    refine (body hP hS hs hal (by omega) h fun M' h' => ?_) cf hat
    have hi1 : n.used - 1 + 1 = n.used := by omega
    refine h'.seqD (some .bD) rfl (iBf_step v outp sp px pn k n.used xdp (n.used - 1) _
      (xc.digit (n.used + (n.used - 1)) * k + xc.digit (n.used - 1) + (drRow xc.digit n.used k (n.used - 1)).u)
      xc.alloc M' (cd h')
      (by facts h') (by simp only [radix, Layout.digitBits] at hr; omega)
      (by simp only [radix, Layout.digitBits] at hr; omega) hi1) (by omega) (by omega) fun M3 h3 => ?_
    have h4 := key (n.used - 1) (by omega) M3 h3
    rw [hi1] at h4
    have e := keyu (n.used - 1); rw [hi1] at e
    rw [e]; exact kont M3 h4

end run

theorem ordCode_ne {c : Ordering} (h : c ≠ .lt) : BitVec.ofInt 64 (ordCode c) ≠ m1 := by
  cases c
  · exact absurd rfl h
  · decide
  · decide

theorem ordCode_lt : BitVec.ofInt 64 (ordCode .lt) = m1 := by decide

theorem drPass_lt {f : Nat → Nat} {m k : Nat} (hf : ∀ i, f i < radix) (hk : k < radix) (i : Nat) :
    drPass f m k i < radix := by
  have hb := drRow_bound f m k hf hk m
  unfold drPass; split
  · exact hb.1 i
  · split
    · exact hb.2
    · exact radix_pos

theorem kf_of {m : Mem} {sp px xdp pn ndp : Nat} {x n : MpInt} {k : Nat} {ra : BitVec 64}
    (hP : DrReduce.Pre m sp px xdp pn ndp x n k ra) : KF sp := by
  have hd := hP.lay (Api.Two.R.stk) (Api.Two.R.code) (by decide)
  have := hP.sp_ge
  simp only [Iv.Disj, Disj, Two.lay, textIv, textBase, textLen] at hd
  exact ⟨hP.rs, hP.sp_al, this, by simp only [mpDrReduceBase]; omega⟩

section run2
variable {m : Mem} {v : Abi} {outp : Array String} {sp px xdp pn ndp : Nat} {x n : MpInt} {k : Nat}
  {ra s0 : BitVec 64}

/-- The rest of the loop, from `top`, by the fuel. -/
abbrev IHT (m : Mem) (v : Abi) (outp : Array String) (sp px xdp pn ndp : Nat) (x n : MpInt) (k : Nat)
    (ra s0 : BitVec 64) (F : Nat) : Prop :=
  ∀ xc, xc.alloc = x.alloc → TopC x n k F xc → ∀ M j0 j3 j7 j10 j11,
    SD m sp px xdp pn ndp x n (κT m ra s0 v sp px xdp pn ndp n xc) M →
    Triple (At 0x80005664#64 (uL sp px pn k n.used j0 j3 j7 j10 j11) M (kF v) outp)
      (DrReduce.Ret m v outp sp px xdp pn ndp x n k ra s0)

/-- From `56ec`: re-abstract `x`, `mp_clamp`, `mp_cmp_mag`, return or `s_mp_sub` and `goto top`. -/
theorem after (hP : DrReduce.Pre m sp px xdp pn ndp x n k ra) (hS : Sc x n k) (hk : KF sp) {F u sg : Nat}
    {ds : List Nat} (hC : TopC x n k (F + 1) (xa x u sg ds)) (IH : IHT m v outp sp px xdp pn ndp x n k ra s0 F)
    {M : Mem} {j0 j3 j7 j10 j11 : BitVec 64}
    (h : SD m sp px xdp pn ndp x n (Kind.set (κT m ra s0 v sp px xdp pn ndp n (xa x u sg ds)) (some .bD)
      (.mpD xdp x.alloc (zfill (upd (drRow (xa x u sg ds).digit n.used k n.used).dig n.used
        (drRow (xa x u sg ds).digit n.used k n.used).u) (n.used + 1) u))) M) :
    Triple (At 0x800056ec#64 (uL sp px pn k n.used j0 j3 j7 j10 j11) M (kF v) outp)
      (DrReduce.Ret m v outp sp px xdp pn ndp x n k ra s0) := by
  have hv := hC.valid; have := hS.m_pos; have := hS.m_lt; have := hS.al_le; have := hS.room
  have := hP.sp_ge; have := hP.sp_al; have hra := hP.ra_al; have hnp := hP.n_pos
  have hz : ∀ j, u ≤ j → (xa x u sg ds).digit j = 0 := hv.high_zero
  have hu2 : u ≤ 2 * n.used := used_le_of_lt hv (Nat.lt_of_le_of_lt hC.le hP.x_lt)
  have hul : u ≤ x.alloc := hv.used_le
  have hxm : ∀ j, j < x.alloc → (MpInt.ofDigits u x.alloc sg (drPass (xa x u sg ds).digit n.used k)).digit j =
      zfill (upd (drRow (xa x u sg ds).digit n.used k n.used).dig n.used
        (drRow (xa x u sg ds).digit n.used k n.used).u) (n.used + 1) u j := fun j hj => by
    rw [MpInt.ofDigits_digit, if_pos hj, pass_digit hz]
  have hxs : (MpInt.ofDigits u x.alloc sg (drPass (xa x u sg ds).digit n.used k)).Shape :=
    { len := MpInt.ofDigits_len _ _ _ _, used_le := hul, alloc_lt := hP.vx.alloc_lt
      digit_lt := fun i => by
        rw [MpInt.ofDigits_digit]; split
        · exact drPass_lt hv.digit_lt hS.k_lt i
        · exact radix_pos
      high_zero := fun i hi => by
        rw [MpInt.ofDigits_digit]; split
        · exact drPass_high hv.digit_lt hz i hi
        · rfl }
  have hmag : (MpInt.ofDigits u x.alloc sg (drPass (xa x u sg ds).digit n.used k)).mag =
      drFold n.used k (xa x u sg ds).mag := by
    show natUpTo (MpInt.ofDigits u x.alloc sg (drPass (xa x u sg ds).digit n.used k)).digit u =
      drFold n.used k (natUpTo (xa x u sg ds).digit u)
    rw [← pass_mag hv.digit_lt hz hu2]
    exact natUpTo_congr u (fun j hj => by rw [MpInt.ofDigits_digit, if_pos (by omega)])
  have h2 := h.setMp (some .bS) (some .bD) rfl rfl (MpInt.ofDigits u x.alloc sg
    (drPass (xa x u sg ds).digit n.used k)) rfl rfl rfl rfl hxm
  refine St.seq0 (f3_step v outp sp px pn k n.used j0 j3 j7 j10 j11 M (cd h2)) ?_
  refine call_std clamp ⟨px, xdp, _⟩ σz h2 (cd h2) 0x8e9ff0ef#32 0x1ff8e8#21 0x800056f4#64 hxs
    (fun xcl M1 hcl h3 => ?_) (hsub := fun r => by cases r <;> exact Iv.sub_self _)
  have hcs := ClampPost.spec hxs hv.sign_ok hcl
  have hxal : xcl.alloc = x.alloc := hcl.alloc
  have h4 := (h3.setMp (some .bS) (some .bD) rfl rfl xcl rfl rfl rfl hcl.alloc
    (fun j _ => congrFun hcl.digit j)).congrK (κ' := κT m ra s0 v sp px xdp pn ndp n xcl)
    (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl)
  refine St.seq0 (f4_step v outp sp px pn k n.used j0 j3 j7 j10 j11 M1 (cd h4)) ?_
  refine call_std Std.cmpMag ⟨px, xdp, pn, ndp, xcl, n⟩ σc h4 (cd h4) 0x868fb0ef#32 0x1fb068#21 0x80005700#64
    ⟨hcs.1, hP.vn⟩ (fun _ M2 _ h5 => ?_) (hsub := fun r => by
      cases r <;> first
        | exact Iv.sub_self _
        | (show Iv.Sub ⟨xdp, 4 * xcl.alloc⟩ _; rw [hxal]; exact Iv.sub_self _))
  have hfold := drFold_le (m := n.used) (k := k) hS.m_pos hS.k_lt hP.x_lt hC.le
  have hxm' : xcl.mag = drFold n.used k (xa x u sg ds).mag := by rw [hcs.2, hmag]
  have hsg : xcl.sign = if xcl.used = 0 then Layout.mpZpos else x.sign := by
    rw [hcl.sign]; split
    · rfl
    · rename_i hne
      have hpos : 0 < xcl.mag := by
        have := MpInt.mag_ge hcs.1 (by omega); have := Nat.pow_pos (n := xcl.used - 1) radix_pos; omega
      have hu0 : u ≠ 0 := fun h0 => by
        have : (xa x u sg ds).mag = 0 := mag_zero_of_used h0
        rw [this, drFold_zero] at hxm'; omega
      show sg = _; have := hC.sign; simp only [xa] at this; rw [this, if_neg hu0]
  by_cases hlt : xcl.mag < n.mag
  · have hc : compare xcl.mag n.mag = .lt := Nat.compare_eq_lt.2 hlt
    refine St.seq0 (f5t_step v outp sp px pn k n.used (BitVec.ofInt 64 (ordCode (compare xcl.mag n.mag))) j0 j3 j7 j10 j11
      M2 (cd h5) (by rw [hc]; exact ordCode_lt)) ?_
    refine (Triple.rmap (fun cf hc' => ⟨xcl, _, hc'.sub rfl rfl,
      { repr := h5.mpAt (some .bS) (some .bD) rfl rfl
        dr := { valid := hcs.1, mag := ?_, sign := hsg }
        alloc := hxal
        frame := h5.unsplit (by simp [Two.lay]) }⟩) (e_step ra s0 v outp sp M2 (cd h5) (by facts h5))).pre
    rw [← hC.tgt, redLoop, if_neg (by omega), ← hxm']
  · refine St.seq0 (f5f_step v outp sp px pn k n.used (BitVec.ofInt 64 (ordCode (compare xcl.mag n.mag))) j0 j3 j7
      j10 j11 M2 (cd h5)
      (ordCode_ne fun h' => hlt (Nat.compare_eq_lt.1 h'))) ?_
    refine call_std sSubCA ⟨sp - 128, px, xdp, pn, ndp, xcl, n⟩ σs h5 (cd h5) 0xe55fe0ef#32 0x1fee54#21
      0x80005714#64 ⟨hcs.1.toShape, hP.vn.toShape, hcs.1.sign_ok,
        MpInt.used_le_of_mag_le hcs.1.toShape hP.vn (Nat.le_of_not_lt hlt), show (sp - 128) % 16 = 0 by omega,
        show 48 ≤ sp - 128 by omega⟩
      (fun x2 M3 hss h6 => ?_) (hsub := fun r => by
        cases r <;> first
          | iv_omega
          | exact Iv.sub_self _
          | (show Iv.Sub ⟨xdp, 4 * xcl.alloc⟩ _; rw [hxal]; exact Iv.sub_self _))
    have hs2 := SSubPost.spec hcs.1.toShape hP.vn.toShape (Nat.le_of_not_lt hlt) hcs.1.used_le hcs.1.alloc_lt
      hcs.1.sign_ok hss
    have := hC.le; have := hC.lt
    refine St.seq0 (f6_step v outp sp px pn k n.used j0 j3 j7 j10 j11 M3 (cd h6)) ?_
    refine IH x2 (by rw [hss.alloc, hxal]) ⟨hs2.1, by rw [hs2.2]; omega, by rw [hs2.2]; have := hC.lt; omega, ?_, ?_⟩
      M3 j0 j3 j7 j10 j11 (h6.congrK (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl))
    · rw [← hC.tgt, redLoop, if_pos (by omega), hs2.2, hxm']
    · rw [hss.sign]; split
      · rfl
      · rename_i hne
        have hpos : 0 < xcl.used := by
          rcases Nat.eq_zero_or_pos xcl.used with h0 | h0
          · have := mag_zero_of_used h0; omega
          · exact h0
        rw [hsg, if_neg (by omega)]

/-- From `56bc`: `x[m] := mu`, `MP_ZERO_DIGITS`, then `after`. -/
theorem tail (hP : DrReduce.Pre m sp px xdp pn ndp x n k ra) (hS : Sc x n k) (hk : KF sp) {F u sg : Nat}
    {ds : List Nat} (hC : TopC x n k (F + 1) (xa x u sg ds)) (IH : IHT m v outp sp px xdp pn ndp x n k ra s0 F)
    {M : Mem} (h : SD m sp px xdp pn ndp x n (κI m ra s0 v sp px xdp pn ndp n (xa x u sg ds) k n.used) M) :
    Triple (At 0x800056bc#64 (fL sp px pn k n.used xdp (drRow (xa x u sg ds).digit n.used k n.used).u) M (kF v) outp)
      (DrReduce.Ret m v outp sp px xdp pn ndp x n k ra s0) := by
  have hv := hC.valid; have := hS.m_pos; have := hS.m_lt; have := hS.al_le; have := hS.room
  have := hP.sp_ge; have hul : u ≤ x.alloc := hv.used_le
  have hga := hP.gx.ds.hi_le; simp only [Layout.sizeofDigit] at hga
  have hb := (drRow_bound (xa x u sg ds).digit n.used k hv.digit_lt hS.k_lt n.used).2
  refine h.seqD (some .bD) rfl (f1_step v outp sp px pn k n.used xdp _ x.alloc M (cd h) (by facts h))
    (show n.used < x.alloc by omega) (Nat.lt_of_lt_of_le hb (by decide)) fun M1 h1 => ?_
  rw [Kind.set_set] at h1
  by_cases hu1 : u ≤ n.used + 1
  · refine St.seq0 (f2a_step v outp sp px pn k n.used u _ _ _ _ _ M1 (cd h1) (by facts h1) hS.m_lt) ?_
    refine St.seq0 (f2t_step v outp sp px pn k n.used u _ _ _ _ _ M1 (cd h1) (dW_le hS.m_lt (by omega) hu1)) ?_
    exact after hP hS hk hC IH (h1.congrK (by
      intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> try rfl
      show Kind.mpD _ _ _ = Kind.mpD _ _ _; rw [zfill_nil _ hu1]; rfl))
  · refine St.seq0 (f2m_step v outp sp px pn k n.used xdp _ u M1 (cd h1) (by facts h1) hS.m_lt (by omega)) ?_
    refine St.seq0 (f2n_step v outp sp px pn k n.used xdp _ u M1 (cd h1) hS.m_lt (by omega) (by omega)
      (by omega)) ?_
    refine call_std memsetD ⟨xdp, x.alloc, _, n.used + 1, u, u - (n.used + 1)⟩ σms h1 (cd h1) 0x4bd030ef#32
      0x3cbc#21 0x800056ec#64 ⟨show n.used + 1 ≤ u by omega, show u ≤ x.alloc by omega, rfl⟩ (fun _ M2 _ h2 => ?_)
      (hsub := fun r => by cases r <;> exact Iv.sub_self _)
    exact (after hP hS hk hC IH (h2.congrK (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl))).pre

/-- **The `goto top` loop**, by the fuel. -/
theorem top (hP : DrReduce.Pre m sp px xdp pn ndp x n k ra) (hS : Sc x n k) (hk : KF sp) :
    ∀ F, IHT m v outp sp px xdp pn ndp x n k ra s0 F
  | 0 => fun _ _ hC => absurd hC.lt (Nat.not_lt_zero _)
  | F + 1 => fun xc hal hC M j0 j3 j7 j10 j11 h => by
    obtain ⟨u, al, sg, ds⟩ := xc
    simp only at hal; subst hal
    have := hP.sp_ge; have := hS.m_pos; have := hS.m_lt
    refine St.seq0 (t0_step v outp sp px pn k n.used xdp j0 j3 j7 j10 j11 M (cd h) (by facts h)) ?_
    exact inner hP hS hC.valid.toShape rfl (fun M1 h1 => tail hP hS hk hC (top hP hS hk F) h1)
      (h.congrK (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl))

end run2

/-- **`mp_dr_reduce` on the machine.** -/
theorem correct : Api.DrReduce.Statement := by
  intro m v outp sp px xdp pn ndp x n k ra s0 hP
  have hS := sc_of hP; have hk := kf_of hP
  have h0 := St.two (f := 128) hP.rn hP.gn hP.rx hP.gx hP.rs hP.img hP.lay (by decide)
  have := hP.sp_ge; have := hP.sp_al; have := hS.m_pos; have := hS.m_lt; have := hS.room; have := hS.al_le
  have := hP.vx.alloc_lt; have hkr : k < 2 ^ 32 := Nat.lt_of_lt_of_le hS.k_lt (by decide)
  refine Triple.lmap (fun cf h => h.sub (L' := entL ra s0 v sp px pn k) (K' := kF v) rfl rfl) ?_
  refine h0.seqW none rfl (d1_step ra s0 v outp sp px pn k m (cd h0) hk) fun M1 h1 => ?_
  refine St.seq0 (d2_step ra s0 v outp sp px pn k n.used x.alloc M1 (cd h1) (by facts h1)) ?_
  refine h1.seqW none rfl (d3_step ra s0 v outp sp px pn k n.used x.alloc M1 (cd h1) hk hS.m_lt) fun M2 h2 => ?_
  refine St.seq0 (d3b_step s0 v outp sp px pn k n.used x.alloc M2 (cd h2) hS.m_lt (by omega) hS.room) ?_
  refine h2.seqW none rfl (d4a_step s0 v outp sp px pn k n.used M2 (cd h2) hk hS.m_pos hS.m_lt hkr)
    fun M3 h3 => ?_
  refine h3.seqW none rfl (d4b_step s0 v outp sp px pn k n.used M3 (cd h3) hk hkr) fun M4 h4 => ?_
  refine h4.seqW none rfl (d4c_step s0 v outp sp px pn k n.used M4 (cd h4) hk) fun M5 h5 => ?_
  exact top hP hS hk (x.mag + 1) x rfl
    ⟨hP.vx, Nat.le_refl _, Nat.lt_succ_self _, rfl, by
      split
      · exact hP.vx.zero_pos ‹_›
      · rfl⟩ M5 _ _ _ _ _
    (h5.congrK (by intro r; rcases r with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> kind_rfl))

end Tom.Machine.Fn.DrReduce
