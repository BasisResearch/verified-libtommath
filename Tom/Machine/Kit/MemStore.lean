import Tom.Machine.Kit.Code
import Vsa.Sim.Mfr

/-!
# Byte and doubleword stores, and filled ranges

A `sb` is the write-log entry `(a, 1, v)` (byte `sbData v`), a `sd` the entry
`(a, 8, v)` (bytes `(sdData_val v).extractLsb' (8 i) 8`). `sbLog x v k` is the
log of `k` byte stores of `v` at `x + k - 1, …, x` (the order of newlib
`memset`'s `sb` table). `Filled m M lo hi b`: `M` holds the byte `b` on
`[lo, hi)` and agrees with `m` elsewhere; `Filled.sd`/`Filled.sbLog` extend
the range by a store.
-/

namespace Tom.Machine

open Vsa.Sim

/-- `k` byte stores of `v` at `x + k - 1` down to `x`. -/
def sbLog (x : Nat) (v : BitVec 64) : Nat → List WEntry
  | 0 => []
  | k + 1 => (x + k, 1, v) :: sbLog x v k

theorem outL_sbLog (x y : Nat) (v : BitVec 64) :
    ∀ k, (y < x ∨ x + k ≤ y) → OutL (sbLog x v k) y
  | 0, _ => trivial
  | k + 1, h => by
    show (y < x + k ∨ x + k + 1 ≤ y) ∧ OutL (sbLog x v k) y
    exact ⟨by omega, outL_sbLog x y v k (by omega)⟩

theorem getElem?_applyW_sb (m : Mem) (a y : Nat) (v : BitVec 64) :
    (applyW m (a, 1, v))[y]? = if y = a then some (sbData v) else m[y]? := by
  show (m.insert a (sbData v))[y]? = _
  rw [Std.ExtHashMap.getElem?_insert]
  by_cases h : y = a
  · subst h; simp
  · simp only [beq_iff_eq, show ¬ a = y from fun e => h e.symm, ite_false, h]

theorem writeLog_sbLog_in (x y : Nat) (v : BitVec 64) :
    ∀ (k : Nat) (M : Mem), x ≤ y → y < x + k → (writeLog M (sbLog x v k))[y]? = some (sbData v)
  | 0, _, _, h2 => absurd h2 (by omega)
  | k + 1, M, h1, h2 => by
    show (writeLog (applyW M (x + k, 1, v)) (sbLog x v k))[y]? = _
    by_cases hy : y < x + k
    · exact writeLog_sbLog_in x y v k _ h1 hy
    · rw [writeLog_out _ _ _ (outL_sbLog x y v k (by omega)), getElem?_applyW_sb]
      simp [show y = x + k by omega]

theorem writeLog_sbLog_out (x y : Nat) (v : BitVec 64) (k : Nat) (M : Mem)
    (h : y < x ∨ x + k ≤ y) : (writeLog M (sbLog x v k))[y]? = M[y]? :=
  writeLog_out _ _ _ (outL_sbLog x y v k h)

/-- A doubleword store, read inside. -/
theorem getElem?_applyW_sd_in (m : Mem) (a y : Nat) (v : BitVec 64) (h1 : a ≤ y) (h2 : y < a + 8) :
    (applyW m (a, 8, v))[y]? = some ((sdData_val v).extractLsb' (8 * (y - a)) 8) := by
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < 8 ∧ y = a + i := ⟨y - a, by omega, by omega⟩
  show (writeMap8 m a (sdData_val v))[a + i]? = _
  simp only [writeMap8, Std.ExtHashMap.getElem?_insert, beq_iff_eq, Nat.add_sub_cancel_left]
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  all_goals first | omega | simp

/-- `v`'s eight bytes are all `b`. -/
def SdFill (v : BitVec 64) (b : BitVec 8) : Prop :=
  ∀ i, i < 8 → (sdData_val v).extractLsb' (8 * i) 8 = b

theorem sdFill_zero : SdFill 0#64 0#8 := by
  intro i hi
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  all_goals first | omega | decide

theorem sbData_zero : sbData 0#64 = 0#8 := by decide

theorem sbData_byte' : ∀ c, c < 256 → sbData (BitVec.ofNat 64 c) = BitVec.ofNat 8 c := by
  decide +kernel

/-- `sb` of a byte value stores it. -/
theorem sbData_byte (c : Nat) (hc : c < 256) : sbData (BitVec.ofNat 64 c) = BitVec.ofNat 8 c :=
  sbData_byte' c hc

/-- A byte replicated into all eight bytes of a doubleword (newlib `memset`'s
`a1 |= a1 << 8; a1 |= a1 << 16; a1 |= a1 << 32`). -/
abbrev rep8 (c : Nat) : Nat := c * 72340172838076673

theorem sbData_rep' : ∀ c, c < 256 → sbData (BitVec.ofNat 64 (rep8 c)) = BitVec.ofNat 8 c := by
  decide +kernel

theorem sbData_rep (c : Nat) (hc : c < 256) : sbData (BitVec.ofNat 64 (rep8 c)) = BitVec.ofNat 8 c :=
  sbData_rep' c hc

theorem sdFill_rep' : ∀ c, c < 256 → ∀ i, i < 8 →
    (sdData_val (BitVec.ofNat 64 (rep8 c))).extractLsb' (8 * i) 8 = BitVec.ofNat 8 c := by
  decide +kernel

theorem sdFill_rep (c : Nat) (hc : c < 256) : SdFill (BitVec.ofNat 64 (rep8 c)) (BitVec.ofNat 8 c) :=
  sdFill_rep' c hc

/-- `M` holds `b` on `[lo, hi)` and agrees with `m` outside. -/
structure Filled (m M : Mem) (lo hi : Nat) (b : BitVec 8) : Prop where
  fill : ∀ y, lo ≤ y → y < hi → M[y]? = some b
  frame : ∀ y, y < lo ∨ hi ≤ y → M[y]? = m[y]?

theorem Filled.refl (m : Mem) (lo : Nat) (b : BitVec 8) : Filled m m lo lo b :=
  ⟨fun _ h1 h2 => absurd h2 (by omega), fun _ _ => rfl⟩

/-- Two doubleword stores of a `b`-filled `v` at `x`, `x + 8` extend `[lo, x)`. -/
theorem Filled.sd2 {m M : Mem} {lo x : Nat} {b : BitVec 8} {v : BitVec 64} (h : Filled m M lo x b)
    (hlo : lo ≤ x) (hv : SdFill v b) :
    Filled m (writeLog M [(x, 8, v), (x + 8, 8, v)]) lo (x + 16) b := by
  constructor
  · intro y h1 h2
    show (applyW (applyW M (x, 8, v)) (x + 8, 8, v))[y]? = _
    by_cases hy : x + 8 ≤ y
    · rw [getElem?_applyW_sd_in _ _ _ _ hy (by omega)]
      exact congrArg some (hv _ (by omega))
    · rw [applyW_out _ _ _ _ _ (by omega)]
      by_cases hy' : x ≤ y
      · rw [getElem?_applyW_sd_in _ _ _ _ hy' (by omega)]
        exact congrArg some (hv _ (by omega))
      · rw [applyW_out _ _ _ _ _ (by omega)]
        exact h.fill y h1 (by omega)
  · intro y hy
    have ho : OutL [(x, 8, v), (x + 8, 8, v)] y := by
      show (y < x ∨ x + 8 ≤ y) ∧ (y < x + 8 ∨ x + 8 + 8 ≤ y) ∧ True
      exact ⟨by omega, by omega, trivial⟩
    rw [writeLog_out _ _ _ ho]
    exact h.frame y (by omega)

/-- `k` byte stores of `v` at `[x, x + k)` extend `[lo, x)`. -/
theorem Filled.sb {m M : Mem} {lo x : Nat} {b : BitVec 8} {v : BitVec 64} (h : Filled m M lo x b)
    (hlo : lo ≤ x) (hv : sbData v = b) (k : Nat) :
    Filled m (writeLog M (sbLog x v k)) lo (x + k) b := by
  constructor
  · intro y h1 h2
    by_cases hy : x ≤ y
    · rw [writeLog_sbLog_in x y v k M hy h2, hv]
    · rw [writeLog_sbLog_out x y v k M (by omega)]
      exact h.fill y h1 (by omega)
  · intro y hy
    rw [writeLog_sbLog_out x y v k M (by omega)]
    exact h.frame y (by omega)

/-- Code outside the stored range is kept. -/
theorem Filled.code {m M : Mem} {lo hi : Nat} {b : BitVec 8} {base : Nat} {ws : List (BitVec 32)}
    (h : Filled m M lo hi b) (hc : CodeAt m base ws)
    (hoff : hi ≤ base ∨ base + 4 * ws.length ≤ lo) : CodeAt M base ws :=
  hc.of_eq fun a h1 h2 => h.frame a (by omega)

end Tom.Machine
