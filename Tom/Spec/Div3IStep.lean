import Tom.Spec.DivDStep

/-!
# `s_mp_div_3`'s model steps on the generated route

The loop of `s_mp_div_3` (`Fn/Div3.lean`'s pieces: `W = w 2^28 + a[ix]`, the digit `t` and
the remainder `r`, `t = W / 3`, `r = W % 3` on every branch) over `Tom/Spec/DivDStep.lean`'s
long division head `LH` with divisor `3`. The pieces store the digit at `q + 4 (k + 1)` with
`ix = k + 1` (or at `q + 4 · 0`), so the stored digit function is spelled with `ix - 1 + 1`
(resp. `0`); `d3` and `d3fin` restate `LH.next`/`LH.fin` in that spelling.
-/

namespace Tom.Div3IStep

open Tom.DivDStep

/-- An iteration at `ix > 0`: `t = W / 3` stored at `ix`, `r = W % 3` carried to `ix - 1`. -/
theorem d3 {da : Nat → Nat} {n ix w t r W : Nat} {f : Nat → Nat} (h : LH da 3 n f ix w) (hix : ix < n)
    (h0 : 0 < ix) (hW : W = w * 268435456 + da ix) (ht : t = W / 3) (hr : r = W % 3) :
    LH da 3 n (fun j => if j = ix - 1 + 1 then t else f j) (ix - 1) r := by
  subst hW ht hr
  rw [show ix - 1 + 1 = ix by omega,
    show (w * 268435456 + da ix) % 3 = w * 268435456 + da ix - (w * 268435456 + da ix) / 3 * 3 by omega]
  exact h.next hix h0

/-- The last iteration (`ix = 0`): the quotient's digits and `|a| mod 3`. -/
theorem d3fin {a : MpInt} {ix w t r W : Nat} {f : Nat → Nat} (h : LH a.digit 3 a.used f ix w) (h0 : ¬ 0 < ix)
    (hu : 0 < a.used) (hW : W = w * 268435456 + a.digit ix) (ht : t = W / 3) (hr : r = W % 3) :
    ZH a 3 (fun j => if j = 0 then t else f j) r := by
  have e : ix = 0 := by omega
  subst e hW ht hr
  rw [show (w * 268435456 + a.digit 0) % 3 = w * 268435456 + a.digit 0 - (w * 268435456 + a.digit 0) / 3 * 3 by
    omega]
  exact h.fin hu

end Tom.Div3IStep
