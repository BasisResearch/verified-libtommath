import Tom.Spec.Reduce
import Tom.Spec.Div2d
import Tom.Spec.Init
import Tom.Spec.Sub
import Tom.Spec.Bits

/-!
# `mp_reduce_2k`'s loop: the model steps

`bn_mp_reduce_2k.c`: `top: mp_div_2d(a, p, &q, a); if (d != 1) mp_mul_d(&q, d, &q);
s_mp_add(a, &q, a); if (mp_cmp_mag(a, n) != MP_LT) { s_mp_sub(a, n, a); goto top; }`.
`RI a n a1` is the loop head's value premise (`a1` valid, in place, congruent to `a` modulo `n`
and not larger); one pass is `S1` (after `mp_div_2d`: `|a| mod 2^p`, `|q| = |a| / 2^p`), `S2`
(`q`, after `mp_mul_d` or not) and `S3` (after `s_mp_add`: `fold2k p d |a1|`, the fold of
`Tom/Spec/Reduce.lean`); then `S3.fin` (`|a| < |n|`: `Reduce2kPost`) or `S3.sub` (one
subtraction: `RI` again, the magnitude smaller, the measure of the back edge). `Env` holds the
run's fixed facts (`Api/MpReduce2k.lean`'s `Res` with `p = mp_count_bits(n)`).
-/

namespace Tom.Reduce2kStep

open MpInt Tom.Reduce Tom.Mont

variable {a n a1 a2 q2 q3 a3 a4 : MpInt} {d k : Nat}

/-- The fixed facts of a run (`k = mp_count_bits(n)`). -/
structure Env (a n : MpInt) (d k : Nat) : Prop where
  va : a.Valid
  vn : n.Valid
  npos : 0 < n.mag
  hd : n.mag + d = 2 ^ k
  hk : k = nbits n.mag
  aroom : a.used + 1 ≤ a.alloc
  qroom : a.used + 1 ≤ defPrec

/-- The loop head (`top`): `a1` valid, in place, congruent to `a`, not larger. -/
structure RI (a n a1 : MpInt) : Prop where
  va : a1.Valid
  alloc : a1.alloc = a.alloc
  le : a1.mag ≤ a.mag
  res : a1.mag % n.mag = a.mag % n.mag
  sign : a1.sign = Layout.mpZpos ∨ a1.sign = a.sign

theorem RI.start (ha : a.Valid) : RI a n a := ⟨ha, rfl, Nat.le_refl _, rfl, Or.inr rfl⟩

theorem RI.used (h : RI a n a1) (ha : a.Valid) : a1.used ≤ a.used :=
  MpInt.used_le_of_mag_le ha.toShape h.va h.le

/-- After `mp_div_2d(a, k, &q, a)`: the remainder in `a`, the quotient in `q`. -/
structure S1 (a : MpInt) (k : Nat) (a1 a2 q2 : MpInt) : Prop where
  va2 : a2.Valid
  m2 : a2.mag = a1.mag % 2 ^ k
  al2 : a2.alloc = a.alloc
  sg2 : a2.sign = Layout.mpZpos ∨ a2.sign = a1.sign
  u2 : a2.used ≤ a.used
  vq2 : q2.Valid
  mq2 : q2.mag = a1.mag / 2 ^ k
  alq2 : q2.alloc = defPrec
  uq2 : q2.used + 1 ≤ defPrec

theorem S1.of (e : Env a n d k) (h : RI a n a1) {qv : MpInt} (hqa : qv.alloc = defPrec)
    (hmod : Mod2dPost a1 k a1 a2) (hdiv : Div2dPost a1 k qv q2) : S1 a k a1 a2 q2 := by
  have hu := h.used e.va
  have hq32 := e.qroom
  have hm := Mod2dPost.spec h.va h.va.used_le h.va.alloc_lt hmod
  have hq := Div2dPost.spec h.va (by rw [hqa]; omega) (by rw [hqa]; decide) hdiv
  have hle2 : a2.mag ≤ a.mag := by rw [hm.2.1]; exact Nat.le_trans (Nat.mod_le _ _) h.le
  have hleq : q2.mag ≤ a.mag := by rw [hq.2.1]; exact Nat.le_trans (Nat.div_le_self _ _) h.le
  have hsg : a2.sign = if a2.used = 0 then Layout.mpZpos else a1.sign := ClampedTo.sign hmod
  exact { va2 := hm.1, m2 := hm.2.1, al2 := (ClampedTo.alloc hmod).trans h.alloc
          sg2 := by rw [hsg]; split; exact Or.inl rfl; exact Or.inr rfl
          u2 := MpInt.used_le_of_mag_le e.va.toShape hm.1 hle2
          vq2 := hq.1, mq2 := hq.2.1, alq2 := (ClampedTo.alloc hdiv).trans hqa
          uq2 := by have := MpInt.used_le_of_mag_le e.va.toShape hq.1 hleq; omega }

/-- `q` after `mp_mul_d(&q, d, &q)` (or `d = 1`): `|a1| / 2^k · d`, not above `|a1|`. -/
structure S2 (a : MpInt) (d k : Nat) (a1 q3 : MpInt) : Prop where
  vq3 : q3.Valid
  mq3 : q3.mag = a1.mag / 2 ^ k * d
  alq3 : q3.alloc = defPrec
  uq3 : q3.used ≤ a.used

theorem fold_q_le (e : Env a n d k) (m : Nat) : m / 2 ^ k * d ≤ m :=
  Nat.le_trans (Nat.mul_le_mul_left _ (show d ≤ 2 ^ k by have := e.hd; omega)) (Nat.div_mul_le_self _ _)

theorem S1.mul (s : S1 a k a1 a2 q2) (e : Env a n d k) (h : RI a n a1) (hdr : d < radix)
    (hmul : MulDPost q2 d q2 q3) : S2 a d k a1 q3 := by
  have hq := MulDPost.spec s.vq2 hdr (by rw [s.alq2]; exact s.uq2) (by rw [s.alq2]; decide) hmul
  have hmq : q3.mag = a1.mag / 2 ^ k * d := by rw [hq.2.1, s.mq2]
  refine { vq3 := hq.1, mq3 := hmq, alq3 := hmul.alloc.trans s.alq2, uq3 := ?_ }
  exact MpInt.used_le_of_mag_le e.va.toShape hq.1 (by rw [hmq]; exact Nat.le_trans (fold_q_le e _) h.le)

theorem S1.one (s : S1 a k a1 a2 q2) (e : Env a n d k) (h : RI a n a1) (hd1 : d = 1) : S2 a d k a1 q2 :=
  { vq3 := s.vq2, mq3 := by rw [s.mq2, hd1, Nat.mul_one], alq3 := s.alq2
    uq3 := MpInt.used_le_of_mag_le e.va.toShape s.vq2 (by rw [s.mq2]; exact Nat.le_trans (Nat.div_le_self _ _) h.le) }

/-- After `s_mp_add(a, &q, a)`: the fold. -/
structure S3 (a : MpInt) (d k : Nat) (a1 a3 : MpInt) : Prop where
  va3 : a3.Valid
  m3 : a3.mag = fold2k k d a1.mag
  al3 : a3.alloc = a.alloc
  sg3 : a3.sign = Layout.mpZpos ∨ a3.sign = a1.sign

theorem S1.add (s : S1 a k a1 a2 q2) (s2 : S2 a d k a1 q3) (e : Env a n d k)
    (hadd : SAddPost a2 q3 a2 a3) : S3 a d k a1 a3 := by
  have hr : max a2.used q3.used + 1 ≤ a2.alloc := by
    rw [s.al2]; have := s.u2; have := s2.uq3; have := e.aroom; omega
  have hq := SAddPost.spec s.va2.toShape s2.vq3.toShape hr (by rw [s.al2]; exact e.va.alloc_lt) s.va2.sign_ok hadd
  have hsg : a3.sign = if a3.used = 0 then Layout.mpZpos else a2.sign := hadd.sign
  refine { va3 := hq.1, m3 := ?_, al3 := hadd.alloc.trans s.al2, sg3 := ?_ }
  · rw [hq.2, s.m2, s2.mq3, fold2k, Nat.mul_comm]
  · rw [hsg]; split
    · exact Or.inl rfl
    · rcases s.sg2 with h | h
      · exact Or.inl h
      · exact Or.inr h

theorem S3.res (s : S3 a d k a1 a3) (e : Env a n d k) (h : RI a n a1) : a3.mag % n.mag = a.mag % n.mag := by
  rw [s.m3, (fold2k_ok k d n.mag a.mag e.hd).mod _ h.le, h.res]

theorem S3.le (s : S3 a d k a1 a3) (e : Env a n d k) (h : RI a n a1) : a3.mag ≤ a1.mag := by
  rw [s.m3]; exact (fold2k_ok k d n.mag a.mag e.hd).le _ h.le

/-- `|a| < |n|`: done. -/
theorem S3.fin (s : S3 a d k a1 a3) (e : Env a n d k) (h : RI a n a1) (hlt : a3.mag < n.mag) :
    Reduce2kPost a n d a3 := by
  have hd' : n.mag + d = 2 ^ nbits n.mag := by rw [← e.hk]; exact e.hd
  refine { valid := s.va3, mag := ?_, sign := ?_ }
  · rw [redLoop_spec _ _ e.npos _ a.mag a.mag (fold2k_ok _ _ _ _ hd') (Nat.le_refl _) (Nat.lt_succ_self _),
      ← s.res e h, Nat.mod_eq_of_lt hlt]
  · rcases s.sg3 with h3 | h3
    · exact Or.inl h3
    · rw [h3]; exact h.sign

/-- `|a| ≥ |n|`: `s_mp_sub(a, n, a)`'s operand order. -/
theorem S3.ge (s : S3 a d k a1 a3) (e : Env a n d k) (hge : ¬ a3.mag < n.mag) : n.used ≤ a3.used :=
  MpInt.used_le_of_mag_le s.va3.toShape e.vn (by omega)

/-- `|a| ≥ |n|`: one subtraction, back to `top` with a smaller value. -/
theorem S3.sub (s : S3 a d k a1 a3) (e : Env a n d k) (h : RI a n a1) (hge : ¬ a3.mag < n.mag)
    (hsub : SSubPost a3 n a3 a4) : RI a n a4 ∧ a4.mag < a1.mag := by
  have hq := SSubPost.spec s.va3.toShape e.vn.toShape (by omega) s.va3.used_le s.va3.alloc_lt
    s.va3.sign_ok hsub
  have hle := s.le e h
  have hsg : a4.sign = if a4.used = 0 then Layout.mpZpos else a3.sign := hsub.sign
  have hnp := e.npos
  refine ⟨{ va := hq.1, alloc := hsub.alloc.trans s.al3, le := ?_, res := ?_, sign := ?_ }, ?_⟩
  · rw [hq.2]; have := h.le; omega
  · rw [hq.2, ← Nat.mod_eq_sub_mod (by omega), s.res e h]
  · rw [hsg]; split
    · exact Or.inl rfl
    · rcases s.sg3 with h3 | h3
      · exact Or.inl h3
      · rw [h3]; exact h.sign
  · rw [hq.2]; omega

end Tom.Reduce2kStep
