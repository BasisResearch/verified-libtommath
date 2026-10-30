import Tom.Spec.Ledger

/-!
# `mp_mod`: the model steps over the Ledger

`bn_mp_mod.c` at `0x80001680` (frame 80, `t` at `sp + 24`): `mp_init_size(&t, b->used)`
(`t = zeroN (initPrec b->used)`, `Api/StdHeapFn.lean` `mpInitSize`); `mp_div(a, b, NULL, &t)`
(`DivRem`); then `MP_IS_ZERO(&t) || t.sign == b->sign` (`800016ec`–`800016fc`: `t.used`, then
`t.sign` against `b->sign`): `mp_exch(&t, c)` (`c`'s struct holds `t'`), else `mp_add(b, &t, c)`;
`mp_clear(&t)`. Post: `ModPost a b c'` (`Tom/Spec/Div.lean`; `.spec`: `c' = a.fmod b`), checked
against the C and the disassembly: the test is `ModPost`'s case split (`T.cond`).

Callee Posts:
* `mp_div`: the frozen `Api/MpDiv.lean` covers `c`, `d` non-NULL only; this call passes
  `c = NULL` (`li a2, 0` at `800016d8`), `d = &t`: **not covered**. The step is over the Spec Post
  `DivRem a b t t'` (the `d` half of that contract's `Q`). That contract's `droom : a->used ≤
  d->alloc` also fails here in general (`t.alloc = initPrec b->used`, `a` longer); `DivRem` needs it
  only when `|a| < |b|` (`mp_copy(a, d)`), where it holds (`xfer_divRem`).
* `mp_add(b, &t, c)`: `Api/MpAddG.lean`'s `Q` (growing `c`; `b`, `t`, `c` distinct).
* `mp_init_size`, `mp_exch`, `mp_clear`: `Api/StdHeapFn.lean`, `Api/StdHeap.lean` (no value content).
-/

namespace Tom.MpModStep

open MpInt Ledger

variable {a b c t c' : MpInt}

/-- The run's fixed facts. -/
structure Env (a b c : MpInt) : Prop where
  va : a.Valid
  vb : b.Valid
  /-- `b ≠ 0` (`mp_div`'s `MP_VAL` is not covered). -/
  b0 : 0 < b.used
  sc : c.Shape
  /-- `mp_add`'s `mp_grow` size (`Api/MpAddG.lean` `size_lt`; `t->used ≤ b->used`). -/
  bsize : b.used + 1 < 2 ^ 31

/-- `t` after `mp_div(a, b, NULL, &t)`: `|a| mod |b|`, `a`'s sign unless zero. -/
abbrev T (a b t : MpInt) : Prop := Settled t t.alloc (a.mag % b.mag) a.sign

/-- `mp_init_size(&t, b->used)`, `mp_div(a, b, NULL, &t)`. -/
theorem t_of (e : Env a b c) (h : DivRem a b (MpInt.zeroN (initPrec b.used)) t) : T a b t :=
  xfer_divRem e.va
    (fun hs => Nat.le_trans (MpInt.used_le_of_mag_le e.vb.toShape e.va (Nat.le_of_lt hs)) (Nat.le_max_right _ _))
    (by have := e.vb.used_le; have := e.vb.alloc_lt; show initPrec b.used < 2 ^ 31; unfold initPrec
        rw [minPrec_eq]; omega) h

theorem T.val (h : T a b t) : t.val = a.val.tmod b.val := by
  rw [MpInt.val_sval a, MpInt.val_sval b, sval_tmod_sval, MpInt.val_of_sign h.sign, h.mag]; rfl

/-- The C's test `MP_IS_ZERO(&t) || t.sign == b->sign` is `ModPost`'s case split. -/
theorem T.cond (h : T a b t) : (t.used = 0 ∨ t.sign = b.sign) ↔ (a.mag % b.mag = 0 ∨ a.sign = b.sign) := by
  have hz : t.used = 0 ↔ a.mag % b.mag = 0 :=
    ⟨fun hu => by rw [← h.mag]; exact MpInt.mag_used_zero hu, fun hm => h.valid.used_zero (by rw [h.mag]; exact hm)⟩
  by_cases hu : t.used = 0
  · exact ⟨fun _ => Or.inl (hz.1 hu), fun _ => Or.inl hu⟩
  · have hs : t.sign = a.sign := by rw [h.sign, if_neg hu]
    rw [hs]
    exact ⟨fun h' => h'.imp (fun h0 => absurd h0 hu) id, fun h' => h'.imp (fun h0 => absurd (hz.2 h0) hu) id⟩

/-- `t` zero or of `b`'s sign: `mp_exch(&t, c)`; `c` holds `t`. -/
theorem fin_keep (h : T a b t) (hk : t.used = 0 ∨ t.sign = b.sign) : ModPost a b t :=
  ⟨fun _ => ⟨h.valid, T.val h⟩, fun hn => absurd ((T.cond h).1 hk) hn⟩

/-- Otherwise `mp_add(b, &t, c)` (`Api/MpAddG.lean`): `c = b + t`. -/
theorem fin_add (e : Env a b c) (h : T a b t) (hn : ¬ (t.used = 0 ∨ t.sign = b.sign))
    (hadd : AddG b t (SAddPost b t (sAddIn b t (c.withSign b.sign)) c') (SSubPost t b (sSubIn t (c.withSign t.sign)) c')
      (SSubPost b t (sSubIn b (c.withSign b.sign)) c')) : ModPost a b c' := by
  have hu : t.used ≤ b.used := MpInt.used_le_of_mag_le e.vb.toShape h.valid
    (by rw [h.mag]; exact Nat.le_of_lt (Nat.mod_lt _ (e.vb.mag_pos e.b0)))
  refine ⟨fun hk => absurd ((T.cond h).2 hk) hn, fun _ => ?_⟩
  have := xfer_addG e.vb h.valid e.sc (by have := e.bsize; omega) hadd
  rwa [T.val h] at this

end Tom.MpModStep
