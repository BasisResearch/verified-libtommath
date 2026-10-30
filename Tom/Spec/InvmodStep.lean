import Tom.Spec.InvmodSlowStep

/-!
# `mp_invmod`: the dispatch

`bn_mp_invmod.c` at `0x8000150c` (checked against `experiments/disasm.txt`): `b->sign == MP_NEG`
(`lw a5, 8(a1)`, `beq a5, 1`) → `MP_VAL`; `mp_cmp_d(b, 1) != MP_GT` → `MP_VAL`; `MP_IS_ODD(b)`
(`used > 0`, `dp[0] & 1`) → tail call `s_mp_invmod_fast(a, b, c)`, else tail call
`s_mp_invmod_slow(a, b, c)` (both `MP_HAS` are set: both tail calls are in the code). No temporaries.

Callee Posts: `cmpD b 1` (`Api/CmpD.lean`), and the two paths' Spec Posts `InvmodFastPost`,
`InvmodSlowPost` (`Tom/Spec/Gcd.lean`; no machine contract yet: `InvmodFastStep.fin_post`,
`InvmodSlowStep.fin_post` and the exits there are their model steps). `env` gives the tail
calls' `Env` from `mp_invmod`'s own facts (`b` not negative is `b` positive).
-/

namespace Tom.InvmodStep

open MpInt Ledger InvmodFastStep

variable {a b c c' : MpInt} {ret : Int}

/-- `b->sign == MP_NEG`: `MP_VAL`. -/
theorem neg_exit (hn : b.sign = Layout.mpNeg) : InvmodPost a b c c Layout.mpVal :=
  ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd hn h, fun h => absurd hn h⟩

theorem zpos_of (vb : b.Valid) (hn : ¬ b.sign = Layout.mpNeg) : b.sign = Layout.mpZpos := by
  rcases vb.sign_ok with h | h
  · exact h
  · exact absurd h hn

/-- `mp_cmp_d(b, 1) == MP_GT` for a nonnegative `b`: `b > 1`. -/
theorem gt_iff (vb : b.Valid) (hn : ¬ b.sign = Layout.mpNeg) : cmpD b 1 = .gt ↔ 1 < b.mag := by
  rw [cmpD_spec vb (by decide), val_zpos (zpos_of vb hn), Int.compare_eq_gt]; omega

/-- `mp_cmp_d(b, 1) != MP_GT`: `MP_VAL`. -/
theorem le_exit (vb : b.Valid) (hn : ¬ b.sign = Layout.mpNeg) (hc : ¬ cmpD b 1 = .gt) :
    InvmodPost a b c c Layout.mpVal := by
  have := mt (gt_iff vb hn).2 hc
  exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ h => absurd h (by omega), fun _ h => absurd h (by omega)⟩

/-- The tail calls' run facts (`Env`). -/
theorem env (va : a.Valid) (vb : b.Valid) (hn : ¬ b.sign = Layout.mpNeg) : Env a b where
  va := va
  vb := vb
  bz := zpos_of vb hn

/-- `MP_IS_ODD(b)`: `return s_mp_invmod_fast(a, b, c)`. -/
theorem fast (vb : b.Valid) (hn : ¬ b.sign = Layout.mpNeg) (hc : cmpD b 1 = .gt) (ho : isOdd b)
    (hf : InvmodFastPost a b c c' ret) : InvmodPost a b c c' ret := by
  have h1 := (gt_iff vb hn).1 hc
  have h2 := odd_of (⟨vb, Nat.zero_le _, Nat.le_refl _, rfl, trivial⟩ : Acct b 0 b.used b.val True) ho
  rw [val_zpos (zpos_of vb hn)] at h2
  exact ⟨fun h => absurd h (by omega), fun _ _ _ => hf, fun _ _ h => absurd h (by omega)⟩

/-- `MP_IS_EVEN(b)`: `return s_mp_invmod_slow(a, b, c)`. -/
theorem slow (vb : b.Valid) (hn : ¬ b.sign = Layout.mpNeg) (hc : cmpD b 1 = .gt) (he : ¬ isOdd b)
    (hs : InvmodSlowPost a b c c' ret) : InvmodPost a b c c' ret := by
  have h1 := (gt_iff vb hn).1 hc
  have h2 := even_of (⟨vb, Nat.zero_le _, Nat.le_refl _, rfl, trivial⟩ : Acct b 0 b.used b.val True) he
  rw [val_zpos (zpos_of vb hn)] at h2
  exact ⟨fun h => absurd h (by omega), fun _ _ h => absurd h (by omega), fun _ _ _ => hs⟩

end Tom.InvmodStep
