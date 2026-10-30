import Tom.Machine.Api.StdLib
import Tom.Machine.Api.Expt2

/-!
# `mp_2expt` on the machine: the whole function

The segments of `Tom.Machine.Fn.Expt2` and the contracts of `mp_zero`,
`__divdi3`, `mp_grow` (with room) and `__moddi3` by `call_std` (`Kit/Meet.lean`,
`Api/StdLib.lean`). Regions are `Un`'s, the stack (48 bytes) all our own frame
(`Split`); `a->used` by `St.seqU`, the digit by `St.seqD`, the result
re-abstracted by `St.setMp`.
-/


namespace Tom.Machine.Fn.Expt2

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api Tom.Machine.Std
open Tom.Machine.Api.Un (R isW)

/-- The result: one digit `2^(b mod 28)` at `b / 28`. -/
def res (a : MpInt) (b : Nat) : MpInt :=
  MpInt.ofDigits (b / 28 + 1) a.alloc a.sign fun j => if j = b / 28 then 2 ^ (b % 28) else 0

theorem res_post {a a' : MpInt} {b : Nat} (hz : ZeroPost a a') (hroom : b / 28 + 1 ≤ a.alloc) :
    Expt2Post a b (res a' b) :=
  { alloc := hz.alloc, len := by rw [res, MpInt.ofDigits_len, hz.alloc], used := rfl, sign := hz.sign
    digit := fun j => by
      rw [res, MpInt.ofDigits_digit]; split
      · rfl
      · rw [if_neg (by simp only [Layout.digitBits]; rw [hz.alloc] at *; omega)] }

def σz : Ob → Option R
  | .S => some .aS
  | .D => some .aD
  | .code => some .code

def σc : Cd → Option R := fun _ => some .code

theorem cd {sp pa adp : Nat} {a : MpInt} {W : List (Option R)} {κ : Option R → Kind} {m M : Mem}
    (h : St (Split.lay (Un.lay 48 sp pa adp a) .stk 48) (Split.wr isW) W κ m M)
    (hk : κ (some .code) = .code := by rfl) : CodeAt M mp2exptBase mp2exptCode := (h.img (some .code) hk).mp2expt

/-- **`mp_2expt` on the machine.** -/
theorem correct : Api.Expt2.Statement := by
  intro m v outp sp pa adp a b ra s0 hP
  have h0 := St.un (f := 48) hP.ra_ hP.ga hP.rs hP.img hP.lay (by decide)
  have := hP.sp_ge; have := hP.sp_al; have hra := hP.ra_al; have hb := hP.b_lt
  have hroom : b / 28 + 1 ≤ a.alloc := hP.room
  have := hP.sa.alloc_lt
  have hd : b % 28 < 28 := Nat.mod_lt _ (by decide)
  refine Triple.lmap (fun cf h => h.sub (L' := entry1 ra s0 v.s.s1 v.s.s2 sp pa b) (K' := keepE v) rfl rfl) ?_
  refine h0.seqW none rfl (p_step ra s0 v.s.s1 v.s.s2 v outp sp pa b m (cd h0) (by facts h0) hb) fun M1 h1 => ?_
  refine call_std mpZero ⟨pa, adp, a⟩ σz h1 (cd h1) 0xa85fa0ef#32 0x1faa84#21 0x800076f8#64 hP.sa
    fun a1 M2 hq h2 => ?_
  have hz : ZeroPost a a1 := hq.1; have hal := hz.alloc
  refine St.seq0 (g_step v.s.s2 v outp sp pa b M2 (cd h2)) ?_
  refine call_std divdi3 ⟨b, 28⟩ σc h2 (cd h2) 0x6a50f0ef#32 0x0fea4#21 0x80007704#64
    (DivRes.of (by omega) (by decide) (by decide)) fun _ M3 _ h3 => ?_
  refine h3.seqW none rfl (w_step v.s.s2 v outp sp pa b (b / 28) M3 (cd h3) (by facts h3) (by omega))
    fun M4 h4 => ?_
  refine call_std mpGrow ⟨pa, adp, a1, b / 28 + 1⟩ σz h4 (cd h4) 0xb5df90ef#32 0x1f9b5c#21 0x80007718#64
    ⟨hq.2, by (try dsimp only); omega⟩ fun _ M5 _ h5 => ?_
  refine h5.seqW none rfl (u1_step v outp sp pa b adp (b / 28) M5 (cd h5) (by facts h5)) fun M6 h6 => ?_
  refine h6.seqU (some .aS) rfl (u2_step v outp sp pa b adp (b / 28) M6 (cd h6) (by facts h6)) (by omega)
    fun M7 h7 => ?_
  refine call_std moddi3 ⟨b, 28⟩ σc h7 (cd h7) 0x6e90f0ef#32 0x0fee8#21 0x80007744#64
    (DivRes.of (by omega) (by decide) (by decide)) fun _ M8 _ h8 => ?_
  refine h8.seqD (some .aD) rfl (e1_step v outp sp pa (adp + 4 * (b / 28)) (b % 28) (b / 28) M8 (cd h8)
    (by facts h8) hd) (by omega) (Nat.lt_trans (Nat.pow_lt_pow_right (by decide) hd) (by decide))
    fun M9 h9 => ?_
  have h10 := h9.setMp (some .aS) (some .aD) rfl rfl (res a1 b) rfl rfl rfl rfl fun j hj => by
    simp only [res, MpInt.ofDigits_digit, if_pos hj]; split
    · rfl
    · exact (hz.digit j).symm
  exact (Triple.rmap (fun cf hc => ⟨res a1 b, M9, hc.sub rfl rfl, ⟨h10.mpAt (some .aS) (some .aD) rfl rfl,
      res_post hz hroom, h10.unsplit (by simp [Un.lay])⟩⟩)
    (e2_step ra s0 v.s.s1 v.s.s2 v outp sp pa (b / 28) M9 (cd h9) (by facts h9))).pre

end Tom.Machine.Fn.Expt2
