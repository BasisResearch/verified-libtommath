import Tom.Spec.MpReduce2kLStep
import Tom.Spec.CopyGStep
import Tom.Spec.SAddGStep

/-!
# `mp_reduce_2k_l` with `a` and `q` growing: the model steps

`Tom/Spec/MpReduce2kLStep.lean`'s pass with the callees that grow: `mp_div_2d(a, p, &q, a)` copies `a`
into the grown `copyIn a q` (`RIG.div`), `s_mp_add(a, &q, a)` adds into the grown `sAddIn a q a`
(`S2.addG`), so `a`'s allocation is not fixed (`RIG`: `MagAcct` at `a1`'s own allocation) and there is
no room premise (`EnvG`: `Env` without `aroom`, with the C's `int` bound on `max(used) + 1`).
`quo_used`: the quotient `a1 / 2^p` has at most `a->used + 1 - n->used` digits (`p = nbits |n|` is at
least `28 (n->used - 1) + 1`), which keeps `mp_mul(&q, d, &q)` on the comba path for a modulus of fewer
than 79 digits and products of residues.
-/

namespace Tom.MpReduce2kLStep

open MpInt Ledger Reduce
open Mont (nbits)

variable {a n d q a1 a2 q2 q3 a3 a4 : MpInt}

/-- The run's fixed facts (no room for `a`). -/
structure EnvG (a n d : MpInt) : Prop where
  va : a.Valid
  vn : n.Valid
  vd : d.Valid
  npos : 0 < n.mag
  hd : n.mag + d.mag = 2 ^ nbits n.mag
  /-- `s_mp_add`'s `mp_grow(a, max + 1)`: an `int`. -/
  usz : a.used + 1 < 2 ^ 31

theorem EnvG.p (e : EnvG a n d) : countBits n = nbits n.mag := countBits_spec e.vn

/-- `|d| < 2^p ≤ radix^(n->used)`: `d` has at most `n->used` digits. -/
theorem EnvG.dused (e : EnvG a n d) : d.used ≤ n.used := by
  have h1 := Mont.nbits_le n.mag e.npos
  have h2 := MpInt.mag_lt e.vn.toShape
  rw [show radix = 2 ^ 28 from rfl, ← Nat.pow_mul] at h2
  have h3 : nbits n.mag - 1 < 28 * n.used := (Nat.pow_lt_pow_iff_right (by decide)).1 (Nat.lt_of_le_of_lt h1 h2)
  apply used_le_of_lt e.vd
  rw [show radix = 2 ^ 28 from rfl, ← Nat.pow_mul]
  have := e.hd; have := e.npos
  exact Nat.lt_of_lt_of_le (show d.mag < 2 ^ nbits n.mag by omega) (Nat.pow_le_pow_right (by decide) (by omega))

/-- The loop head `top` with `a`'s digits possibly re-placed. -/
structure RIG (a n a1 q : MpInt) : Prop where
  acct : MagAcct a1 a1.alloc a1.mag a.sign
  le : a1.mag ≤ a.mag
  res : a1.mag % n.mag = a.mag % n.mag
  q : q.Shape

theorem RIG.start (e : EnvG a n d) : RIG a n a (MpInt.zeroN defPrec) :=
  ⟨MagAcct.start e.va, Nat.le_refl _, rfl, (MpInt.zeroN_valid (by decide)).toShape⟩

theorem RIG.used (e : EnvG a n d) (h : RIG a n a1 q) : a1.used ≤ a.used :=
  MpInt.used_le_of_mag_le e.va.toShape h.acct.valid h.le

/-- After the growing `mp_div_2d(a, p, &q, a)`. -/
structure S1G (a n a1 a2 q2 : MpInt) : Prop where
  rem : MagAcct a2 a1.alloc (a1.mag % 2 ^ nbits n.mag) a.sign
  quo : MagAcct q2 q2.alloc (a1.mag / 2 ^ nbits n.mag) a.sign

theorem RIG.div (e : EnvG a n d) (h : RIG a n a1 q) (hd : Div2dPost a1 (countBits n) (copyIn a1 q) q2)
    (hm : Mod2dPost a1 (countBits n) a1 a2) : S1G a n a1 a2 q2 := by
  rw [e.p] at hd hm
  have h31 : a1.used < 2 ^ 31 := Nat.lt_of_le_of_lt h.acct.valid.used_le h.acct.valid.alloc_lt
  obtain ⟨r, qq⟩ := xfer_div2dR h.acct (copyIn_grown h.q h31).shape (copyIn_room a1 q) hd hm
  exact ⟨r, ⟨qq.valid, rfl, qq.mag, qq.sign⟩⟩

/-- `mp_mul(&q, d, &q)`. -/
theorem S1G.mul (s : S1G a n a1 a2 q2) (hm : MulPost q2 d q3) : S2 n d a1 q3 :=
  have m := xfer_mulM hm
  ⟨m.1, by rw [m.2, s.quo.mag]⟩

/-- The quotient `m / 2^p` of a value below `radix^u` has at most `u + 1 - n->used` digits. -/
theorem quo_used {x : MpInt} {m u : Nat} (hn : n.Valid) (hn0 : 0 < n.mag) (hx : x.Valid)
    (hxm : x.mag = m / 2 ^ nbits n.mag) (hm : m < radix ^ u) : x.used ≤ u + 1 - n.used := by
  have hu0 : 0 < n.used := by
    rcases Nat.eq_zero_or_pos n.used with h | h
    · have := MpInt.mag_used_zero (x := n) h; omega
    · exact h
  have h1 := MpInt.mag_ge hn hu0
  have h2 := Mont.nbits_lt n.mag
  have hk : 2 ^ (28 * (n.used - 1)) ≤ 2 ^ nbits n.mag := by
    rw [Nat.pow_mul]; exact Nat.le_of_lt (Nat.lt_of_le_of_lt h1 h2)
  have hk' : 28 * (n.used - 1) ≤ nbits n.mag := (Nat.pow_le_pow_iff_right (by decide)).1 hk
  by_cases hu : n.used - 1 ≤ u
  · apply used_le_of_lt hx
    rw [hxm, show u + 1 - n.used = u - (n.used - 1) by omega]
    have hp : 0 < 2 ^ (28 * (n.used - 1)) := Nat.two_pow_pos _
    refine Nat.lt_of_le_of_lt (Nat.div_le_div_left (Nat.pow_le_pow_right (by decide) hk') hp) ?_
    rw [Nat.div_lt_iff_lt_mul hp, Nat.pow_mul, show (2 : Nat) ^ 28 = radix from rfl, ← Nat.pow_add, Nat.sub_add_cancel hu]
    exact hm
  · apply used_le_of_lt hx
    rw [hxm, Nat.div_eq_of_lt]
    · exact Nat.pow_pos (by decide)
    · refine Nat.lt_of_lt_of_le hm (Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt (Nat.lt_of_not_le hu))) ?_)
      rw [show radix = 2 ^ 28 from rfl, ← Nat.pow_mul]; exact hk

theorem fold_q_leG (e : EnvG a n d) (m : Nat) : m / 2 ^ nbits n.mag * d.mag ≤ m :=
  Nat.le_trans (Nat.mul_le_mul_left _ (show d.mag ≤ 2 ^ nbits n.mag by have := e.hd; omega)) (Nat.div_mul_le_self _ _)

/-- After the growing `s_mp_add(a, &q, a)`: the fold. -/
abbrev S3G (a n d a1 a3 : MpInt) : Prop := MagAcct a3 a3.alloc (fold2k (nbits n.mag) d.mag a1.mag) a.sign

theorem S2.addG (e : EnvG a n d) (h : RIG a n a1 q) (s : S1G a n a1 a2 q2) (s2 : S2 n d a1 q3)
    (hadd : SAddPost a2 q3 (sAddIn a2 q3 a2) a3) : S3G a n d a1 a3 := by
  have hu1 := RIG.used e h
  have hu2 : a2.used ≤ a.used := MpInt.used_le_of_mag_le e.va.toShape s.rem.valid
    (by rw [s.rem.mag]; exact Nat.le_trans (Nat.mod_le _ _) h.le)
  have hu3 : q3.used ≤ a.used := MpInt.used_le_of_mag_le e.va.toShape s2.valid
    (by rw [s2.mag]; exact Nat.le_trans (Nat.le_trans (Nat.mul_le_mul_left _
      (show d.mag ≤ 2 ^ nbits n.mag by have := e.hd; omega)) (Nat.div_mul_le_self _ _)) h.le)
  have hg := sAddIn_grown (a := a2) (b := q3) s.rem.valid.toShape (by have := e.usz; omega)
  obtain ⟨hv, hm⟩ := hadd.spec s.rem.valid.toShape s2.valid.toShape (sAddIn_room a2 q3 a2) hg.shape.alloc_lt
    (by rw [hg.sign]; exact s.rem.valid.sign_ok)
  exact ⟨hv, rfl, by rw [hm, s.rem.mag, s2.mag, fold2k, Nat.mul_comm], sign_clamp hadd.sign (by rw [hg.sign]; exact s.rem.sign)⟩

theorem S3G.le (e : EnvG a n d) (h : RIG a n a1 q) (s : S3G a n d a1 a3) : a3.mag ≤ a1.mag := by
  rw [s.mag]; exact (fold2k_ok _ d.mag n.mag a.mag e.hd).le _ h.le

theorem S3G.res (e : EnvG a n d) (h : RIG a n a1 q) (s : S3G a n d a1 a3) : a3.mag % n.mag = a.mag % n.mag := by
  rw [s.mag, (fold2k_ok _ d.mag n.mag a.mag e.hd).mod _ h.le, h.res]

/-- `mp_cmp_mag(a, n) == MP_LT`: done. -/
theorem S3G.fin (e : EnvG a n d) (h : RIG a n a1 q) (s : S3G a n d a1 a3) (hlt : a3.mag < n.mag) :
    Reduce2kPost a n d.mag a3 where
  valid := s.valid
  mag := by
    rw [redLoop_spec _ _ e.npos _ a.mag a.mag (fold2k_ok _ _ _ _ e.hd) (Nat.le_refl _) (Nat.lt_succ_self _),
      ← S3G.res e h s, Nat.mod_eq_of_lt hlt]
  sign := s.sign

theorem S3G.ge (e : EnvG a n d) (s : S3G a n d a1 a3) (hge : ¬ a3.mag < n.mag) : n.used ≤ a3.used :=
  MpInt.used_le_of_mag_le s.valid.toShape e.vn (by omega)

/-- `s_mp_sub(a, n, a)`, `goto top`. -/
theorem S3G.sub (e : EnvG a n d) (h : RIG a n a1 q) (s : S3G a n d a1 a3) (s2 : S2 n d a1 q3)
    (hge : ¬ a3.mag < n.mag) (hsub : SSubPost a3 n a3 a4) : RIG a n a4 q3 ∧ a4.mag < a1.mag := by
  have r := xfer_ssubM s e.vn.toShape (by have := s.mag; omega) hsub
  have hle := S3G.le e h s
  have hres := S3G.res e h s
  have hm := s.mag
  have := e.npos
  refine ⟨⟨⟨r.valid, rfl, rfl, r.sign⟩, ?_, ?_, s2.valid.toShape⟩, ?_⟩
  · rw [r.mag]; have := h.le; omega
  · rw [r.mag, ← hm, ← Nat.mod_eq_sub_mod (by omega), hres]
  · rw [r.mag]; omega

end Tom.MpReduce2kLStep
