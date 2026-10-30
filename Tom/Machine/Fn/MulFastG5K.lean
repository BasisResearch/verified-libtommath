import Tom.Machine.Api.StdLib
import Tom.Spec.MulFastGStep

/-!
# `s_mp_mul_digs_fast` with growth: the tails' digits

`mp_clamp`'s argument `mfRes a b A n` (`Spec/MulFastGStep.lean`) against the digit function the
callees leave in `c->dp` (`Std.memcpyD`'s `cpy`, `Std.memsetD`'s `zfill`) on the four tails of
`experiments/asm/mfastg.asm.json`: `pa > 0` with and without `MP_ZERO_DIGITS`, `pa = 0` likewise.
-/

namespace Tom.Machine.Fn.MulFastG5K

open Tom.Machine Tom.Machine.Std Tom.MulFastGStep

variable {a b A : MpInt} {n w : Nat} {g : Nat → Nat}

theorem fill_cm (hA : A.Shape) (hroom : n ≤ A.alloc) (h : OF a b n w g) (j : Nat) :
    (mfRes a b A n).digit j = zfill (cpy A.digit g 0 0 n) n A.used j :=
  fill hA hroom h (fun j hj => by simp only [zfill, cpy]; rw [if_neg (by omega), if_pos (by omega), Nat.zero_add, Nat.sub_zero])
    (fun j h1 h2 => by simp [zfill, h1, h2])
    (fun j h1 h2 => by simp only [zfill, cpy]; rw [if_neg (by omega), if_neg (by omega)]) j

theorem fill_cn (hA : A.Shape) (hroom : n ≤ A.alloc) (h : OF a b n w g) (hle : A.used ≤ n) (j : Nat) :
    (mfRes a b A n).digit j = cpy A.digit g 0 0 n j :=
  fill hA hroom h (fun j hj => by simp only [cpy]; rw [if_pos (by omega), Nat.zero_add, Nat.sub_zero]) (fun j h1 h2 => absurd h2 (by omega))
    (fun j h1 h2 => by simp only [cpy]; rw [if_neg (by omega)]) j

theorem fill_zm (hA : A.Shape) (j : Nat) : (mfRes a b A 0).digit j = zfill A.digit 0 A.used j :=
  fill hA (Nat.zero_le _) (OF.zero (fun _ => 0)) (fun j hj => absurd hj (Nat.not_lt_zero _))
    (fun j _ h2 => by simp [zfill, h2]) (fun j _ h2 => by simp only [zfill]; rw [if_neg (by omega)]) j

theorem fill_zn (hA : A.Shape) (h0 : A.used = 0) (j : Nat) : (mfRes a b A 0).digit j = A.digit j :=
  fill hA (Nat.zero_le _) (OF.zero (fun _ => 0)) (fun j hj => absurd hj (Nat.not_lt_zero _))
    (fun j _ h2 => absurd h2 (by omega)) (fun _ _ _ => rfl) j

/-- Continue with a restated hypothesis (`"tac"` steps rebinding the state `@H`: the kinds after
`memset` and `mp_clamp` re-stated in closed form before the epilogue's frame reads). -/
theorem pass {P C : Prop} (h : P) (k : P → C) : C := k h

end Tom.Machine.Fn.MulFastG5K
