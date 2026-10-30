import Tom.Machine.Fn.MulFast
import Tom.Machine.Kit.Frame
import Tom.Machine.Fn.Memset
import Tom.Machine.Fn.MemcpyMain
import Tom.Machine.Fn.Clamp
import Tom.Spec.Mul

/-!
# `s_mp_mul_digs_fast` on the machine: the comba loop, for any placement

The column loop runs over an in-place array state on `W` (`ASt` over the one
region `⟨sp - 2160, 2048⟩`, `ρW`): column `ix` reaches the store point with
the sum `_W = combaW (col …) ix + col … ix` by one of its paths (`reach`), the
store makes `W[ix]` the comba digit (`column`), and `Triple.countup` runs the
columns (`loop`). The inner loop (`inner`) is a `__muldi3` call between two
segments per term (`Kit/MulCall.lean`). What the loop reads is supplied as
plain facts (`ColH`, `LoopH`): the loop writes only `W`, so `a` and `b` read
as at the snapshot even when `c` is one of them.
-/

namespace Tom.Machine.Fn.MulFast

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api.Libgcc

theorem col_zero_ub (da db : Nat → Nat) (ua k : Nat) : col da db ua 0 k = 0 := by
  unfold col
  rw [sumTo_congr ua (g := fun _ => 0) (fun i _ => by simp), sumTo_zero_fun]

/-- The inner loop's partial sum. -/
abbrev pS (da db : Nat → Nat) (tx ty n : Nat) : Nat := sumTo (fun k => da (tx + k) * db (ty - k)) n

theorem DRead.cast {M : Mem} {a a' x : Nat} (h : DRead M a x) (e : a = a') : DRead M a' x := e ▸ h

/-! ## The inner loop -/

section inner
variable {M : Mem} {v : Abi} {outp : Array String} {sp ua ub pa adp bdp ix tx ty iy S0 : Nat}
  {da db : Nat → Nat}

/-- What the inner loop of one column reads. -/
structure InH (M : Mem) (adp bdp tx ty iy : Nat) (da db : Nat → Nat) (S0 : Nat) : Prop where
  rdA : ∀ iz, iz < iy → DRead M (adp + 4 * tx + 4 * iz) (da (tx + iz))
  rdB : ∀ iz, iz < iy → DRead M (bdp + 4 * ty - 4 * iz) (db (ty - iz))
  hty : iy ≤ ty + 1
  bnd : S0 + pS da db tx ty iy < 2 ^ 64
  ha : adp + 4 * tx + 4 * iy ≤ 2 ^ 32
  hb : 4 ≤ bdp
  img : Img M

theorem prod_lt' {x y : Nat} (hx : x < 268435456) (hy : y < 268435456) : x * y < 2 ^ 56 := by
  have := Nat.mul_lt_mul'' hx hy; omega

/-- **The inner loop** of a column, from term `iz` to the exit at `43e4`. -/
theorem inner (h : InH M adp bdp tx ty iy da db S0) (hiy : 1 ≤ iy) :
    ∀ iz, iz < iy → Triple (At 0x800043c8#64 (iH sp ua ub pa adp ix tx ty iy bdp iz (S0 + pS da db tx ty iz)) M
        (kF v) outp)
      (At 0x800043e4#64 (xL sp ua ub pa adp ix (S0 + pS da db tx ty iy)
          (BitVec.ofNat 64 (adp + 4 * tx + 4 * iy)) (BitVec.ofNat 64 (adp + 4 * tx + 4 * iy))
          (BitVec.ofNat 64 (bdp + 4 * ty - 4 * iy))) M (kF v) outp) := by
  have hc := h.img.sMpMulDigsFast
  have hty := h.hty; have hb := h.hb
  have hmono : ∀ n, n ≤ iy → S0 + pS da db tx ty n < 2 ^ 64 := fun n hn =>
    Nat.lt_of_le_of_lt (Nat.add_le_add_left (sumTo_mono _ hn) _) h.bnd
  have body : ∀ iz, iz < iy → ∀ (pc' : BitVec 64) (L' : GRegs),
      (Triple (At 0x800043dc#64 (rI sp ua ub pa adp ix tx ty iy bdp iz (S0 + pS da db tx ty iz)
          (da (tx + iz) * db (ty - iz))) M (kF v) outp) (At pc' L' (writeLog M []) (kF v) outp)) →
      Triple (At 0x800043c8#64 (iH sp ua ub pa adp ix tx ty iy bdp iz (S0 + pS da db tx ty iz)) M (kF v) outp)
        (At pc' L' M (kF v) outp) := by
    intro iz hiz pc' L' hlast
    have hx := h.rdA iz hiz; have hy := h.rdB iz hiz
    refine Triple.seq (l1_step v outp sp ua ub pa adp ix tx ty iy bdp iz _ _ _ M hc hx hy (by omega)) ?_
    refine Triple.seq (muldi3_call (pc := 0x800043d8#64) (w := 0x168130ef#32) (imm := 0x013168#21)
      (Lk := kI sp ua ub pa adp ix tx ty iy bdp iz (S0 + pS da db tx ty iz))
      (L2 := rI sp ua ub pa adp ix tx ty iy bdp iz (S0 + pS da db tx ty iz) (da (tx + iz) * db (ty - iz)))
      h.img hc (by decide +kernel) (by decide) (by decide) (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide) (by decide)
      (fun p hp => hp) (by simp [kI, keysG]) (by simp [kF, keysG])
      (by unfold KeepOK
          rw [show keysG (kI sp ua ub pa adp ix tx ty iy bdp iz (S0 + pS da db tx ty iz) ++ kF v) =
            [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 3, 4] from rfl]; decide)
      (fun p hp => List.mem_cons_of_mem _ (by rw [ofNat_mul_ofNat]; exact hp))) ?_
    exact Triple.rmap (fun _ h => h) hlast
  refine Triple.countup (n := iy)
    (P := fun iz => At 0x800043c8#64 (iH sp ua ub pa adp ix tx ty iy bdp iz (S0 + pS da db tx ty iz)) M (kF v) outp)
    (fun iz hi => body iz (by omega) _ _ ?_) ?_
  · have := l2_step v outp sp ua ub pa adp ix tx ty iy bdp iz (S0 + pS da db tx ty iz)
      (da (tx + iz) * db (ty - iz)) M hc (by have := hmono (iz + 1) (by omega); simp only [pS, sumTo] at this ⊢; omega)
      hi (h.ha)
    simp only [pS, sumTo, Nat.add_assoc] at this ⊢
    exact this
  · refine body (iy - 1) (by omega) _ _ ?_
    have := l2e_step v outp sp ua ub pa adp ix tx ty iy bdp (iy - 1) (S0 + pS da db tx ty (iy - 1))
      (da (tx + (iy - 1)) * db (ty - (iy - 1))) M hc
      (by have := hmono iy (Nat.le_refl _); rw [show iy = iy - 1 + 1 by omega] at this
          simp only [pS, sumTo] at this ⊢; omega) (by omega)
    have e : S0 + pS da db tx ty (iy - 1) + da (tx + (iy - 1)) * db (ty - (iy - 1)) = S0 + pS da db tx ty iy := by
      conv => rhs; rw [show iy = iy - 1 + 1 by omega]
      simp only [pS, sumTo, Nat.add_assoc]
    rwa [e] at this

end inner

/-! ## One column, up to its store -/

section column
variable {M : Mem} {v : Abi} {outp : Array String} {sp ua ub pa adp bdp ix : Nat} {da db : Nat → Nat}

/-- What a column reads (memory `M`, which the column does not change). -/
structure ColH (M : Mem) (sp ua ub pa adp bdp : Nat) (da db : Nat → Nat) : Prop where
  k : KF sp
  sf : SpFacts M sp ua ub bdp
  img : Img M
  rdA : ∀ i, i < ua → DRead M (adp + 4 * i) (da i)
  rdB : ∀ i, i < ub → DRead M (bdp + 4 * i) (db i)
  ua_lt : ua < 2 ^ 30
  ub_lt : ub < 2 ^ 30
  pa_le : pa ≤ ua + ub
  pa_w : pa ≤ 512
  ha : adp + 4 * ua ≤ 2 ^ 32
  hb4 : 4 ≤ bdp

/-- The store point of column `ix` with sum `s`: after the inner loop, or for an empty column. -/
def SP (sp ua ub pa adp ix s : Nat) (M : Mem) (v : Abi) (outp : Array String) (cf : Vsa.Machine.Config) : Prop :=
  ∃ j0 j9 j10 : BitVec 64, At 0x800043e4#64 (xL sp ua ub pa adp ix s j0 j9 j10) M (kF v) outp cf ∨
    At 0x800044c4#64 (xL sp ua ub pa adp ix s j0 j9 j10) M (kF v) outp cf

theorem s6Of_pos {ub : Nat} (h : 1 ≤ ub) : s6Of ub = BitVec.ofNat 64 (ub - 1) := by
  apply BitVec.eq_of_toNat_eq; simp only [toNat_ofNat']; omega

theorem bge_m1 (x : Nat) (hx : x < 2 ^ 63) : zopz0zKzJ_s (s6Of 0) (BitVec.ofNat 64 x) = false := by
  unfold zopz0zKzJ_s
  rw [toInt_ofNat_small x hx, show (s6Of 0).toInt = -1 by decide]
  simp; omega

theorem col_eq_pS (da db : Nat → Nat) (ua ub k : Nat) (hub : 1 ≤ ub) :
    col da db ua ub k = pS da db (combaTx ub k) (combaTy ub k) (combaIy ua ub k) :=
  (colC_eq da db ua ub k hub).symm

/-- The set-up and the inner loop, from `43b4`. -/
theorem run_inner (h : ColH M sp ua ub pa adp bdp da db) (tx ty iy w : Nat) (j10 : BitVec 64)
    (htx : tx + iy ≤ ua) (hty : iy ≤ ty + 1) (hub : ty < ub) (hiy : 1 ≤ iy) (hix : ix < pa)
    (hw : w + pS da db tx ty iy < 2 ^ 64) :
    Triple (At 0x800043b4#64 (sL sp ua ub pa adp ix w tx ty iy j10) M (kF v) outp)
      (SP sp ua ub pa adp ix (w + pS da db tx ty iy) M v outp) := by
  have hua := h.ua_lt; have hubl := h.ub_lt; have hb4 := h.hb4; have hha := h.ha
  have hin : InH M adp bdp tx ty iy da db w :=
    { rdA := fun iz hiz => (h.rdA (tx + iz) (by omega)).cast (by omega)
      rdB := fun iz hiz => (h.rdB (ty - iz) (by omega)).cast (by omega)
      hty := hty, bnd := hw, ha := by omega, hb := hb4, img := h.img }
  refine Triple.seq (i0_step v outp sp ua ub pa adp bdp ix w tx ty iy j10 M h.img.sMpMulDigsFast h.k h.sf.bdp_v
    (by omega) (by omega)) ?_
  exact Triple.rmap (fun cf h => ⟨_, _, _, Or.inl h⟩) (inner (sp := sp) (ua := ua) (ub := ub) (pa := pa)
    (ix := ix) (v := v) (outp := outp) hin hiy 0 (by omega))

theorem sp_empty {w : Nat} {j0 j9 j10 : BitVec 64} {cf : Vsa.Machine.Config}
    (h : At 0x800044c4#64 (xL sp ua ub pa adp ix w j0 j9 j10) (writeLog M []) (kF v) outp cf) :
    SP sp ua ub pa adp ix w M v outp cf := ⟨_, _, _, Or.inr h⟩

/-- **A column up to its store**: the sum is the carry plus the column. -/
theorem reach (h : ColH M sp ua ub pa adp bdp da db) (ix w : Nat) (hix : ix < pa)
    (hw : w + col da db ua ub ix < 2 ^ 64) (j0 j2 j9 j10 : BitVec 64) :
    Triple (At 0x8000439c#64 (oH sp ua ub pa adp ix w j0 j2 j9 j10) M (kF v) outp)
      (SP sp ua ub pa adp ix (w + col da db ua ub ix) M v outp) := by
  have hua := h.ua_lt; have hub := h.ub_lt; have hpa := h.pa_le; have hpw := h.pa_w
  have hc := h.img.sMpMulDigsFast
  by_cases hb0 : ub = 0
  · subst hb0
    rw [col_zero_ub, Nat.add_zero]
    refine Triple.seq (cc0_step v outp sp ua 0 pa adp bdp ix w j0 j2 j9 j10 M hc h.k h.sf (by omega)
      (by omega) hua hub) ?_
    refine Triple.seq (ccf_step v outp sp ua 0 pa adp ix w _ _ j2 j10 M hc (bge_m1 _ (by omega))) ?_
    exact Triple.rmap (fun cf h => sp_empty h) (g0_step v outp sp ua 0 pa adp ix w _ _ j2 j10 M hc (by omega))
  rw [col_eq_pS da db ua ub ix (by omega)] at hw ⊢
  by_cases hlt : ix < ub
  · have htx : combaTx ub ix = 0 := by unfold combaTx combaTy; omega
    have hty : combaTy ub ix = ix := by unfold combaTy; omega
    by_cases hla : ix < ua
    · have hiy : combaIy ua ub ix = ix + 1 := by unfold combaIy; rw [htx, hty]; omega
      rw [htx, hty, hiy] at hw ⊢
      exact Triple.seq (ca_step v outp sp ua ub pa adp ix w j0 j2 j9 j10 M hc hlt hla hua hub)
        (run_inner h 0 ix (ix + 1) w j10 (by omega) (by omega) hlt (by omega) hix hw)
    · have hiy : combaIy ua ub ix = ua := by unfold combaIy; rw [htx, hty]; omega
      rw [htx, hty, hiy] at hw ⊢
      refine Triple.seq (cb_step v outp sp ua ub pa adp ix w j0 j2 j9 j10 M hc hlt (by omega) hub) ?_
      by_cases hz : ua = 0
      · subst hz
        exact Triple.rmap (fun cf h => sp_empty h) (g0_step v outp sp 0 ub pa adp ix w 0 _ j2 j10 M hc (by omega))
      · exact Triple.seq (g1_step v outp sp ua ub pa adp ix w ua ix 0 j2 j10 M hc (by omega) (by omega) (by omega))
          (run_inner h 0 ix ua w j10 (by omega) (by omega) hlt (by omega) hix hw)
  · have htx : combaTx ub ix = ix + 1 - ub := by unfold combaTx combaTy; omega
    have hty : combaTy ub ix = ub - 1 := by unfold combaTy; omega
    rw [htx, hty] at hw ⊢
    have h0 := cc0_step v outp sp ua ub pa adp bdp ix w j0 j2 j9 j10 M hc h.k h.sf (by omega) (by omega) hua hub
    have h6 := s6Of_pos (ub := ub) (by omega)
    by_cases hge : ua + ub - 1 - ix ≤ ub - 1
    · have hiy : combaIy ua ub ix = ua + ub - 1 - ix := by unfold combaIy; rw [htx, hty]; omega
      rw [hiy] at hw ⊢
      refine Triple.seq h0 (Triple.seq (cct_step v outp sp ua ub pa adp ix w _ _ j2 j10 M hc
        (by rw [h6, bge_ofNat _ _ (by omega) (by omega)]; simp; omega)) ?_)
      by_cases hz : ua + ub - 1 - ix = 0
      · rw [hz]
        rw [hz] at hw
        have := g0_step v outp sp ua ub pa adp ix w (ix + 1 - ub) (s6Of ub) j2 j10 M hc (by omega)
        simp only [pS, sumTo, Nat.add_zero] at this ⊢
        exact Triple.rmap (fun cf h => sp_empty h) this
      · rw [h6]
        exact Triple.seq (g1_step v outp sp ua ub pa adp ix w _ (ub - 1) (ix + 1 - ub) j2 j10 M hc
            (by omega) (by omega) (by omega))
          (run_inner h (ix + 1 - ub) (ub - 1) (ua + ub - 1 - ix) w j10 (by omega) (by omega) (by omega)
            (by omega) hix hw)
    · have hiy : combaIy ua ub ix = ub := by unfold combaIy; rw [htx, hty]; omega
      rw [hiy] at hw ⊢
      refine Triple.seq h0 (Triple.seq (ccf_step v outp sp ua ub pa adp ix w _ _ j2 j10 M hc
        (by rw [h6, bge_ofNat _ _ (by omega) (by omega)]; simp; omega)) ?_)
      rw [h6]
      exact Triple.seq (g1_step v outp sp ua ub pa adp ix w ub (ub - 1) (ix + 1 - ub) j2 j10 M hc
          (by omega) (by omega) (by omega))
        (run_inner h (ix + 1 - ub) (ub - 1) ub w j10 (by omega) (by omega) (by omega) (by omega) hix hw)

end column

/-! ## The column loop, over the array `W` -/

/-- The region of `W[MP_WARRAY]`. -/
def ρW (sp : Nat) : Unit → Iv := fun _ => ⟨sp - 2160, 2048⟩

section loop
variable {m0 : Mem} {v : Abi} {outp : Array String} {sp ua ub pa adp bdp : Nat} {da db old : Nat → Nat}

/-- The loop's join points: `W` holds `f`, nothing else changed since `m0`. -/
abbrev WSt (m0 : Mem) (v : Abi) (outp : Array String) (sp : Nat) :=
  ASt (ρW sp) () m0 (sp - 2160) 512 (kF v) outp

/-- What the column loop needs, for every array state. -/
structure LoopH (m0 : Mem) (sp ua ub pa adp bdp : Nat) (da db : Nat → Nat) : Prop where
  ch : ∀ M f, ArrFrm (ρW sp) () m0 M (sp - 2160) 512 f → ColH M sp ua ub pa adp bdp da db
  bnd : ∀ k, combaW (col da db ua ub) k + col da db ua ub k < 2 ^ 64
  pa_lt : pa < 2 ^ 30
  pa_w : pa ≤ 512

theorem combaD_eq (cl : Nat → Nat) (k : Nat) : (combaW cl k + cl k) % 268435456 = combaD cl k := by
  simp [combaD, radix_eq]

theorem combaW_eq (cl : Nat → Nat) (k : Nat) : (combaW cl k + cl k) / 268435456 = combaW cl (k + 1) := by
  simp [combaW, radix_eq]

/-- One column: up to the store, the store, and the last segment `hfin` (back edge or exit). -/
theorem column (h : LoopH m0 sp ua ub pa adp bdp da db) (ix : Nat) (hix : ix < pa) (pc' : BitVec 64)
    (hfin : ∀ M, CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode → ∀ (s : Nat) (j0 j9 j10 : BitVec 64), s < 2 ^ 64 →
      Triple (At 0x800043ec#64 (xL sp ua ub pa adp ix s j0 j9 j10) M (kF v) outp)
        (At pc' (oH sp ua ub pa adp (ix + 1) (s / 268435456) j0 (BitVec.ofNat 64 (ix + 1)) j9 j10)
          (writeLog M []) (kF v) outp) ∧
      Triple (At 0x800044cc#64 (xL sp ua ub pa adp ix s j0 j9 j10) M (kF v) outp)
        (At pc' (oH sp ua ub pa adp (ix + 1) (s / 268435456) j0 (BitVec.ofNat 64 (ix + 1)) j9 j10)
          (writeLog M []) (kF v) outp))
    (j0 j2 j9 j10 : BitVec 64) :
    Triple (WSt m0 v outp sp 0x8000439c#64
        (oH sp ua ub pa adp ix (combaW (col da db ua ub) ix) j0 j2 j9 j10) (ovl (combaD (col da db ua ub)) old ix))
      (fun cf => ∃ j0' j9' j10' : BitVec 64, WSt m0 v outp sp pc'
        (oH sp ua ub pa adp (ix + 1) (combaW (col da db ua ub) (ix + 1)) j0' (BitVec.ofNat 64 (ix + 1)) j9' j10')
        (ovl (combaD (col da db ua ub)) old (ix + 1)) cf) := by
  intro cf ⟨M, hA, hat⟩
  have hC := h.ch M _ hA
  have hw := h.bnd ix
  have hpw := h.pa_w
  have hk := hC.k
  have hA1 := hA.step (i := ix) (v := (combaW (col da db ua ub) ix + col da db ua ub ix) % 268435456)
    (by omega) (by omega) (combaD_eq _ _)
  have hc1 := (h.ch _ _ hA1).img.sMpMulDigsFast
  refine Triple.seq (reach hC ix _ hix hw j0 j2 j9 j10) ?_ cf hat
  rintro cf ⟨j0', j9', j10', hat' | hat'⟩
  · refine Triple.rmap (fun cf h => ⟨j0', j9', j10', _, hA1, h⟩) ?_ cf hat'
    have := (hfin _ hc1 _ j0' j9' j10' hw).1
    rw [combaW_eq] at this
    exact Triple.seq (e1a_step v outp sp ua ub pa adp ix _ j0' j9' j10' M hC.img.sMpMulDigsFast ⟨hk, by omega⟩ hw)
      this
  · refine Triple.rmap (fun cf h => ⟨j0', j9', j10', _, hA1, h⟩) ?_ cf hat'
    have := (hfin _ hc1 _ j0' j9' j10' hw).2
    rw [combaW_eq] at this
    exact Triple.seq (e2a_step v outp sp ua ub pa adp ix _ j0' j9' j10' M hC.img.sMpMulDigsFast ⟨hk, by omega⟩ hw)
      this

/-- **The column loop**: from column `ix` to the exit at `43fc`, `W[0..pa)` the comba digits. -/
theorem loop (h : LoopH m0 sp ua ub pa adp bdp da db) (hpa : 1 ≤ pa) :
    ∀ ix, ix < pa → Triple (fun cf => ∃ j0 j2 j9 j10 : BitVec 64, WSt m0 v outp sp 0x8000439c#64
        (oH sp ua ub pa adp ix (combaW (col da db ua ub) ix) j0 j2 j9 j10) (ovl (combaD (col da db ua ub)) old ix) cf)
      (fun cf => ∃ j0 j9 j10 : BitVec 64, WSt m0 v outp sp 0x800043fc#64
        (oH sp ua ub pa adp pa (combaW (col da db ua ub) pa) j0 (BitVec.ofNat 64 pa) j9 j10)
        (ovl (combaD (col da db ua ub)) old pa) cf) := by
  have hpl := h.pa_lt
  refine Triple.countup (fun ix hi => ?_) ?_
  · intro cf ⟨j0, j2, j9, j10, hs⟩
    refine Triple.rmap (fun cf ⟨a, b, c, h⟩ => ⟨a, _, b, c, h⟩)
      (column h ix (by omega) _ (fun M hc s j0 j9 j10 hs =>
        ⟨e1b_step v outp sp ua ub pa adp ix s j0 j9 j10 M hc hs hi hpl,
         e2b_step v outp sp ua ub pa adp ix s j0 j9 j10 M hc hs hi hpl⟩) j0 j2 j9 j10) cf hs
  · intro cf ⟨j0, j2, j9, j10, hs⟩
    have := column (v := v) (outp := outp) (old := old) h (pa - 1) (by omega) 0x800043fc#64
      (fun M hc s j0 j9 j10 hs => by
        rw [show pa - 1 + 1 = pa by omega]
        exact ⟨e1x_step v outp sp ua ub pa adp (pa - 1) s j0 j9 j10 M hc hs (by omega) hpl,
          e2x_step v outp sp ua ub pa adp (pa - 1) s j0 j9 j10 M hc hs (by omega) hpl⟩) j0 j2 j9 j10
    rw [show pa - 1 + 1 = pa by omega] at this
    exact this cf hs

end loop

end Tom.Machine.Fn.MulFast
