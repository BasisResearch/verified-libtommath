import Tom.Machine.Kit.Mem

/-!
# Word arrays and frames

`ArrAt m base n f`: the `n` 32-bit words at `base` hold `f 0, …, f (n-1)`
(total reads). A digit loop's invariant is an `ArrAt` whose function is the
model up to the loop index and the old contents above it; `ArrAt.set` is one
`sw` into it.

`MpAt.of_agree`: an `mp_int`'s representation only depends on the bytes of
its struct and digit array (its footprint), so stores elsewhere keep it.
-/

namespace Tom.Machine

open Vsa.Sim

/-- `n` words at `base` hold `f`. -/
def ArrAt (m : Mem) (base n : Nat) (f : Nat → Nat) : Prop :=
  ∀ j, j < n → bytesT4 m (base + 4 * j) = BitVec.ofNat 32 (f j)

theorem bytesT4_congr {m m' : Mem} {a : Nat} (h : ∀ x, a ≤ x → x < a + 4 → m'[x]? = m[x]?) :
    bytesT4 m' a = bytesT4 m a := by
  simp only [bytesT4]
  rw [h a (by omega) (by omega), h (a + 1) (by omega) (by omega), h (a + 2) (by omega) (by omega),
    h (a + 3) (by omega) (by omega)]

theorem bytesT8_congr {m m' : Mem} {a : Nat} (h : ∀ x, a ≤ x → x < a + 8 → m'[x]? = m[x]?) :
    bytesT8 m' a = bytesT8 m a := by
  simp only [bytesT8]
  rw [h a (by omega) (by omega), h (a + 1) (by omega) (by omega), h (a + 2) (by omega) (by omega),
    h (a + 3) (by omega) (by omega), h (a + 4) (by omega) (by omega), h (a + 5) (by omega) (by omega),
    h (a + 6) (by omega) (by omega), h (a + 7) (by omega) (by omega)]

/-- Memory agreeing with `m` on an `mp_int`'s footprint keeps its representation. -/
theorem MpAt.of_agree {m m' : Mem} {p dp : Nat} {a : MpInt} (h : MpAt m p dp a)
    (hs : ∀ x, p ≤ x → x < p + 24 → m'[x]? = m[x]?)
    (hd : ∀ x, dp ≤ x → x < dp + 4 * a.alloc → m'[x]? = m[x]?) : MpAt m' p dp a :=
  { used := by
      rw [bytesT4_congr (fun x h1 h2 => hs x (by simp [Layout.offUsed] at *; omega)
        (by simp [Layout.offUsed] at *; omega))]; exact h.used
    alloc := by
      rw [bytesT4_congr (fun x h1 h2 => hs x (by simp [Layout.offAlloc] at *; omega)
        (by simp [Layout.offAlloc] at *; omega))]; exact h.alloc
    sign := by
      rw [bytesT4_congr (fun x h1 h2 => hs x (by simp [Layout.offSign] at *; omega)
        (by simp [Layout.offSign] at *; omega))]; exact h.sign
    dpv := by
      rw [bytesT8_congr (fun x h1 h2 => hs x (by simp [Layout.offDp] at *; omega)
        (by simp [Layout.offDp] at *; omega))]; exact h.dpv
    digits := fun i hi => by
      rw [bytesT4_congr (fun x h1 h2 => hd x (by simp [Layout.sizeofDigit] at *; omega)
        (by simp [Layout.sizeofDigit] at *; omega))]
      exact h.digits i hi }

/-- One `sw` of `v` into word `k` of an array. -/
theorem ArrAt.set {m : Mem} {base n : Nat} {f : Nat → Nat} (h : ArrAt m base n f) (k v : Nat)
    (hv : v < 2 ^ 32) :
    ArrAt (writeLog m [(base + 4 * k, 4, BitVec.ofNat 64 v)]) base n
      (fun j => if j = k then v else f j) := by
  intro j hj
  by_cases hjk : j = k
  · subst hjk; simp only [if_true]; exact bytesT4_sw_self m _ v hv
  · simp only [hjk, if_false]
    rw [bytesT4_sw_out _ _ _ _ (by omega)]; exact h j hj

/-- Memory agreeing on an array keeps it. -/
theorem ArrAt.of_agree {m m' : Mem} {base n : Nat} {f : Nat → Nat} (h : ArrAt m base n f)
    (heq : ∀ x, base ≤ x → x < base + 4 * n → m'[x]? = m[x]?) : ArrAt m' base n f :=
  fun j hj => by rw [bytesT4_congr (fun x h1 h2 => heq x (by omega) (by omega))]; exact h j hj

theorem ArrAt.congr {m : Mem} {base n : Nat} {f g : Nat → Nat} (h : ArrAt m base n f)
    (hfg : ∀ j, j < n → f j = g j) : ArrAt m base n g :=
  fun j hj => (hfg j hj) ▸ h j hj

/-! ## `sd` -/

theorem writeLog_sd (m : Mem) (a : Nat) (v : BitVec 64) :
    writeLog m [(a, 8, v)] = writeMap8 m a (sdData_val v) := rfl

theorem getElem?_sd_out (m : Mem) (a x : Nat) (v : BitVec 64) (h : x < a ∨ a + 8 ≤ x) :
    (writeLog m [(a, 8, v)])[x]? = m[x]? := by
  rw [writeLog_sd]
  simp only [writeMap8, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  have h0 : ¬ a = x := by omega
  have h1 : ¬ a + 1 = x := by omega
  have h2 : ¬ a + 2 = x := by omega
  have h3 : ¬ a + 3 = x := by omega
  have h4 : ¬ a + 4 = x := by omega
  have h5 : ¬ a + 5 = x := by omega
  have h6 : ¬ a + 6 = x := by omega
  have h7 : ¬ a + 7 = x := by omega
  simp [h0, h1, h2, h3, h4, h5, h6, h7]

theorem bytesT8_wm8_self (m : Mem) (a : Nat) (d : BitVec (8 * 8)) :
    bytesT8 (writeMap8 m a d) a = d := by
  simp only [bytesT8, writeMap8, Std.ExtHashMap.getElem?_insert, beq_iff_eq, Nat.add_left_cancel_iff,
    Nat.reduceEqDiff, ↓reduceIte, Option.getD_some, Nat.add_eq_left]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Tom.Machine.bv_append_eq, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h1 : i < 8
  · simp [h1]
  · by_cases h2 : i - 8 < 8
    · simp [h1, h2]; congr 1; omega
    · by_cases h3 : i - 8 - 8 < 8
      · simp [h1, h2, h3]; congr 1; omega
      · by_cases h4 : i - 8 - 8 - 8 < 8
        · simp [h1, h2, h3, h4]; congr 1; omega
        · by_cases h5 : i - 8 - 8 - 8 - 8 < 8
          · simp [h1, h2, h3, h4, h5]; congr 1; omega
          · by_cases h6 : i - 8 - 8 - 8 - 8 - 8 < 8
            · simp [h1, h2, h3, h4, h5, h6]; congr 1; omega
            · by_cases h7 : i - 8 - 8 - 8 - 8 - 8 - 8 < 8
              · simp [h1, h2, h3, h4, h5, h6, h7]; congr 1; omega
              · simp [h1, h2, h3, h4, h5, h6, h7, show i - 8 - 8 - 8 - 8 - 8 - 8 - 8 < 8 by omega]
                congr 1; omega

theorem bytesT8_sd_out (m : Mem) (a x : Nat) (v : BitVec 64) (h : x + 8 ≤ a ∨ a + 8 ≤ x) :
    bytesT8 (writeLog m [(a, 8, v)]) x = bytesT8 m x :=
  bytesT8_congr fun y h1 h2 => getElem?_sd_out m a y v (by omega)

theorem bytesT4_sd_out (m : Mem) (a x : Nat) (v : BitVec 64) (h : x + 4 ≤ a ∨ a + 8 ≤ x) :
    bytesT4 (writeLog m [(a, 8, v)]) x = bytesT4 m x :=
  bytesT4_congr fun y h1 h2 => getElem?_sd_out m a y v (by omega)

theorem sdData_val_id (v : BitVec 64) : sdData_val v = v := by
  apply BitVec.eq_of_toNat_eq
  simp [sdData_val, Sail.BitVec.extractLsb, Nat.mod_eq_of_lt v.isLt]

theorem bytesT8_sd_self (m : Mem) (a : Nat) (v : BitVec 64) :
    bytesT8 (writeLog m [(a, 8, v)]) a = v := by
  rw [writeLog_sd, bytesT8_wm8_self, sdData_val_id]

end Tom.Machine
