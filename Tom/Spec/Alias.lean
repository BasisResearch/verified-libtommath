import Tom.Spec.Signed

/-!
# In-place calls: the operands' signs do not matter

`mp_add(a, b, a)` stores `c->sign` before it calls `s_mp_add(a, b, a)` or
`s_mp_sub(…, a, …)`, so the low-level routine sees the operand `a` with the
new sign. `SAddPost` and `SSubPost` read only the operands' `used` and digits,
so the operand's sign can be dropped (`unsign_a`, `unsign_b`). The branch on
`mp_cmp_mag` gives the digit-count order the tail call needs
(`cmpMag_lt_used`, `cmpMag_ge_used`).
-/

namespace Tom

theorem SAddPost.unsign_a {x y c c' : MpInt} {s : Nat} (h : SAddPost (x.withSign s) y c c') :
    SAddPost x y c c' := ⟨h.alloc, h.len, h.digit, h.used, h.sign⟩

theorem SAddPost.unsign_b {x y c c' : MpInt} {s : Nat} (h : SAddPost x (y.withSign s) c c') :
    SAddPost x y c c' := ⟨h.alloc, h.len, h.digit, h.used, h.sign⟩

theorem SSubPost.unsign_a {x y c c' : MpInt} {s : Nat} (h : SSubPost (x.withSign s) y c c') :
    SSubPost x y c c' := ⟨h.alloc, h.len, h.digit, h.used, h.sign⟩

theorem SSubPost.unsign_b {x y c c' : MpInt} {s : Nat} (h : SSubPost x (y.withSign s) c c') :
    SSubPost x y c c' := ⟨h.alloc, h.len, h.digit, h.used, h.sign⟩

/-- `mp_cmp_mag(a, b) = MP_LT` bounds the digit counts: the tail call
`s_mp_sub(b, a, ·)` meets its `a->used ≤ b->used`. -/
theorem cmpMag_lt_used {a b : MpInt} (va : a.Valid) (vb : b.Valid) (h : cmpMag a b = .lt) :
    a.used ≤ b.used := by
  rw [cmpMag_eq va vb] at h
  exact MpInt.used_le_of_mag_le vb.toShape va (Nat.le_of_lt (Nat.compare_eq_lt.1 h))

/-- Otherwise `s_mp_sub(a, b, ·)` meets its `b->used ≤ a->used`. -/
theorem cmpMag_ge_used {a b : MpInt} (va : a.Valid) (vb : b.Valid) (h : cmpMag a b ≠ .lt) :
    b.used ≤ a.used := by
  rw [cmpMag_eq va vb] at h
  exact MpInt.used_le_of_mag_le va.toShape vb (Nat.le_of_not_lt fun h' => h (Nat.compare_eq_lt.2 h'))

end Tom
