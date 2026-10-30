import Tom.Spec.Ledger
import Tom.Spec.Reduce
import Tom.Spec.Bits

/-!
# `mp_reduce_2k_l`: the model steps over the Ledger

`bn_mp_reduce_2k_l.c` at `0x80005f70` (frame 96, `q` at `sp + 8`): `mp_init(&q)` (`q = zeroN MP_PREC`,
`Api/StdHeapFn.lean` `mpInit`), `p = mp_count_bits(n)` (`Std.cntBits`: `countBits n`), then
`top: mp_div_2d(a, p, &q, a)` (`80006040`, `a3 = a`), `mp_mul(&q, d, &q)` (`80005fe0`, `a0 = a2 = &q`),
`s_mp_add(a, &q, a)`, and `mp_cmp_mag(a, n) != MP_LT` (`beq a5, s5 = -1`) → `s_mp_sub(a, n, a)`,
`goto top`; finally `mp_clear(&q)`. One pass is a chain of magnitude-only transfers on the Ledger's
`MagAcct` (the sign stays `a`'s or becomes `MP_ZPOS` at a clamp in between: `Reduce2kPost`'s `sign`).
`RI` is the loop head; `S1` (after `mp_div_2d`), `S2` (after `mp_mul`), `S3` (after `s_mp_add`: the
fold `fold2k p |d| |a1|`); then `S3.fin` (`Reduce2kPost a n |d| a3`) or `S3.sub` (`RI` again, the
magnitude smaller: the back edge's measure). Post checked against the C and the disassembly
(`Reduce2kPost`, `Tom/Spec/Reduce.lean`, with `d := |d|`: `mp_mul`'s sign is never read,
`s_mp_add` adds magnitudes).

Callee Posts: `mp_div_2d(a, p, &q, a)` as `Api/MpDiv2dR.lean` (`Div2dPost`, `Mod2dPost`); `mp_mul(&q, d,
&q)` as `Api/MpMulA.lean` (`Out.post`: `MulPost`); `s_mp_add(a, &q, a)` as `Api/SAddAlias.lean`
(room, `SAddPost a2 q3 a2 a3`); `mp_cmp_mag` as `Std.cmpMag` (`compare |a| |n|`); `s_mp_sub(a, n, a)`
as `Api/SSubAlias.lean` (`SSubPost a3 n a3 a4`, `n->used ≤ a->used`: `S3.ge`).

D5 for `mp_div_2d`'s `mp_copy(a, &q)` (`a->used ≤ q->alloc`, `Api/MpDiv2dR.lean`'s Pre) is a premise
of `RI.div`: on the first pass it is `a->used ≤ MP_PREC`; after `mp_mul(&q, d, &q)` it is not
derivable from `MulPost` / `MpMulA.Out`.
-/

namespace Tom.MpReduce2kLStep

open MpInt Ledger Reduce
open Mont (nbits)

variable {a n d q a1 a2 q2 q3 a3 a4 : MpInt}

/-- The run's fixed facts. -/
structure Env (a n d : MpInt) : Prop where
  va : a.Valid
  vn : n.Valid
  vd : d.Valid
  /-- `n ≠ 0`: `p > 0` and a loop that ends. -/
  npos : 0 < n.mag
  /-- `n = 2^p - |d|`, `p = mp_count_bits(n)` (`mp_reduce_2k_setup_l`: `Setup2kLPost.spec`). -/
  hd : n.mag + d.mag = 2 ^ nbits n.mag
  /-- D5 for `s_mp_add(a, &q, a)` on every pass (every value of `a` is at most `|a|`). -/
  aroom : a.used + 1 ≤ a.alloc

/-- `p = mp_count_bits(n)` is `nbits |n|`. -/
theorem Env.p (e : Env a n d) : countBits n = nbits n.mag := countBits_spec e.vn

/-- The loop head `top`: `a1` congruent to `a`, not larger, sign `a`'s or `MP_ZPOS`; `q` shaped. -/
structure RI (a n a1 q : MpInt) : Prop where
  acct : MagAcct a1 a.alloc a1.mag a.sign
  le : a1.mag ≤ a.mag
  res : a1.mag % n.mag = a.mag % n.mag
  q : q.Shape

/-- After `mp_init(&q)`, `p = mp_count_bits(n)`. -/
theorem RI.start (e : Env a n d) : RI a n a (MpInt.zeroN defPrec) :=
  ⟨MagAcct.start e.va, Nat.le_refl _, rfl, (MpInt.zeroN_valid (by decide)).toShape⟩

theorem RI.used (e : Env a n d) (h : RI a n a1 q) : a1.used ≤ a.used :=
  MpInt.used_le_of_mag_le e.va.toShape h.acct.valid h.le

/-- After `mp_div_2d(a, p, &q, a)`: `a1 mod 2^p` in place, `a1 / 2^p` in `q`. -/
structure S1 (a n a1 a2 q2 : MpInt) : Prop where
  rem : MagAcct a2 a.alloc (a1.mag % 2 ^ nbits n.mag) a.sign
  quo : MagAcct q2 q2.alloc (a1.mag / 2 ^ nbits n.mag) a.sign

/-- `mp_div_2d(a, p, &q, a)`. -/
theorem RI.div (e : Env a n d) (h : RI a n a1 q) (hroom : a1.used ≤ q.alloc)
    (hd : Div2dPost a1 (countBits n) q q2) (hm : Mod2dPost a1 (countBits n) a1 a2) : S1 a n a1 a2 q2 := by
  rw [e.p] at hd hm
  obtain ⟨r, qq⟩ := xfer_div2dR h.acct h.q hroom hd hm
  exact ⟨r, ⟨qq.valid, rfl, qq.mag, qq.sign⟩⟩

/-- After `mp_mul(&q, d, &q)`: `|q3| = |a1| / 2^p · |d|`. -/
structure S2 (n d a1 q3 : MpInt) : Prop where
  valid : q3.Valid
  mag : q3.mag = a1.mag / 2 ^ nbits n.mag * d.mag

/-- `mp_mul(&q, d, &q)`. -/
theorem S1.mul (s : S1 a n a1 a2 q2) (hm : MulPost q2 d q3) : S2 n d a1 q3 :=
  have m := xfer_mulM hm
  ⟨m.1, by rw [m.2, s.quo.mag]⟩

theorem fold_q_le (e : Env a n d) (m : Nat) : m / 2 ^ nbits n.mag * d.mag ≤ m :=
  Nat.le_trans (Nat.mul_le_mul_left _ (show d.mag ≤ 2 ^ nbits n.mag by have := e.hd; omega)) (Nat.div_mul_le_self _ _)

/-- After `s_mp_add(a, &q, a)`: the fold `fold2k p |d| |a1|`. -/
abbrev S3 (a n d a1 a3 : MpInt) : Prop := MagAcct a3 a.alloc (fold2k (nbits n.mag) d.mag a1.mag) a.sign

/-- `s_mp_add(a, &q, a)` (room: both operands have at most `a->used` digits). -/
theorem S2.add (e : Env a n d) (h : RI a n a1 q) (s : S1 a n a1 a2 q2) (s2 : S2 n d a1 q3)
    (hadd : SAddPost a2 q3 a2 a3) : S3 a n d a1 a3 := by
  have hu2 : a2.used ≤ a.used := MpInt.used_le_of_mag_le e.va.toShape s.rem.valid
    (by rw [s.rem.mag]; exact Nat.le_trans (Nat.mod_le _ _) h.le)
  have hu3 : q3.used ≤ a.used := MpInt.used_le_of_mag_le e.va.toShape s2.valid
    (by rw [s2.mag]; exact Nat.le_trans (fold_q_le e _) h.le)
  have r := xfer_saddI s.rem s2.valid.toShape (by rw [s.rem.alloc]; have := e.aroom; omega) hadd
  exact ⟨r.valid, r.alloc, by rw [r.mag, s2.mag, fold2k, Nat.mul_comm], r.sign⟩

theorem S3.le (e : Env a n d) (h : RI a n a1 q) (s : S3 a n d a1 a3) : a3.mag ≤ a1.mag := by
  rw [s.mag]; exact (fold2k_ok _ d.mag n.mag a.mag e.hd).le _ h.le

theorem S3.res (e : Env a n d) (h : RI a n a1 q) (s : S3 a n d a1 a3) : a3.mag % n.mag = a.mag % n.mag := by
  rw [s.mag, (fold2k_ok _ d.mag n.mag a.mag e.hd).mod _ h.le, h.res]

/-- `mp_cmp_mag(a, n) == MP_LT`: done. -/
theorem S3.fin (e : Env a n d) (h : RI a n a1 q) (s : S3 a n d a1 a3) (hlt : a3.mag < n.mag) :
    Reduce2kPost a n d.mag a3 where
  valid := s.valid
  mag := by
    rw [redLoop_spec _ _ e.npos _ a.mag a.mag (fold2k_ok _ _ _ _ e.hd) (Nat.le_refl _) (Nat.lt_succ_self _),
      ← S3.res e h s, Nat.mod_eq_of_lt hlt]
  sign := s.sign

/-- `mp_cmp_mag(a, n) != MP_LT`: `s_mp_sub(a, n, a)`'s operand order. -/
theorem S3.ge (e : Env a n d) (s : S3 a n d a1 a3) (hge : ¬ a3.mag < n.mag) : n.used ≤ a3.used :=
  MpInt.used_le_of_mag_le s.valid.toShape e.vn (by omega)

/-- `s_mp_sub(a, n, a)`, `goto top`: the head again (with `q` now `q3`), the magnitude smaller. -/
theorem S3.sub (e : Env a n d) (h : RI a n a1 q) (s : S3 a n d a1 a3) (s2 : S2 n d a1 q3)
    (hge : ¬ a3.mag < n.mag) (hsub : SSubPost a3 n a3 a4) : RI a n a4 q3 ∧ a4.mag < a1.mag := by
  have r := xfer_ssubM s e.vn.toShape (by have := s.mag; omega) hsub
  have hle := S3.le e h s
  have hres := S3.res e h s
  have hm := s.mag
  have := e.npos
  refine ⟨⟨⟨r.valid, r.alloc, rfl, r.sign⟩, ?_, ?_, s2.valid.toShape⟩, ?_⟩
  · rw [r.mag]; have := h.le; omega
  · rw [r.mag, ← hm, ← Nat.mod_eq_sub_mod (by omega), hres]
  · rw [r.mag]; omega

end Tom.MpReduce2kLStep
