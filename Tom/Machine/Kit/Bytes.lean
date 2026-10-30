import Tom.Machine.Kit.Frame
import Tom.Machine.Kit.MemStore

/-!
# Reading back stores of copied bytes

A struct copy (`mp_exch`, `*a = *b`) is a run of `ld`/`sd` pairs: the value
stored is `bytesT8 m0 x`, the doubleword at the source. Its bytes are the
source's bytes (`bytesT8_extract`), so a word read inside the stored
doubleword is the word at the same offset of the source
(`bytesT4_log_sd`). `bytesT8_log` (`Kit/Frame.lean`) reads back the whole
doubleword, `bytesT4_log_sw` a stored word. Each reads the `k`-th entry of
a write log through the later entries off it, as `bytesT8_log` does.
-/

namespace Tom.Machine

open Vsa.Sim

/-- Byte `j` of a doubleword read. -/
theorem bytesT8_extract (m : Mem) (x j : Nat) (hj : j < 8) :
    (bytesT8 m x).extractLsb' (8 * j) 8 = (m[x + j]?).getD 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [bytesT8, BitVec.getLsbD_extractLsb', Tom.Machine.bv_append_eq, BitVec.getLsbD_append]
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals first | omega | (simp only [hi, decide_true, Bool.true_and]; (repeat' split) <;> first | omega | (congr 1; omega))

/-- Two total word reads agree when their bytes do. -/
theorem bytesT4_congrD {M m : Mem} {a b : Nat}
    (h : ∀ j, j < 4 → (M[a + j]?).getD 0 = (m[b + j]?).getD 0) : bytesT4 M a = bytesT4 m b := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega); have h3 := h 3 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [bytesT4, h0, h1, h2, h3]

/-- Byte `j` of the `k`-th entry of a log, a doubleword store, read through the later entries. -/
theorem getD_log_sd : ∀ (log : List WEntry) (m : Mem) (k a j : Nat) (v : BitVec 64), j < 8 →
    (log.drop k).head? = some (a, 8, v) → OutL (log.drop (k + 1)) (a + j) →
    ((writeLog m log)[a + j]?).getD 0 = v.extractLsb' (8 * j) 8
  | [], _, _, _, _, _, _, h, _ => by simp at h
  | e :: log, m, 0, a, j, v, hj, h, hout => by
      simp only [List.drop_zero, List.head?_cons, Option.some.injEq] at h
      subst h
      show ((writeLog (applyW m (a, 8, v)) log)[a + j]?).getD 0 = _
      have hout' : OutL log (a + j) := hout
      rw [writeLog_out _ _ _ hout', getElem?_applyW_sd_in m a (a + j) v (by omega) (by omega),
        sdData_val_id, Nat.add_sub_cancel_left]
      rfl
  | _ :: log, _, k + 1, a, j, v, hj, h, hout => getD_log_sd log _ k a j v hj h hout

/-- A word at offset `o` inside the `k`-th entry, an `sd` of the doubleword at `x` of `m0`:
the word at `x + o` of `m0`. -/
theorem bytesT4_log_sd (log : List WEntry) (m m0 : Mem) (k a x o : Nat) (ho : o + 4 ≤ 8)
    (h : (log.drop k).head? = some (a, 8, bytesT8 m0 x)) (hout : OutLRange (log.drop (k + 1)) (a + o) 4) :
    bytesT4 (writeLog m log) (a + o) = bytesT4 m0 (x + o) :=
  bytesT4_congrD fun j hj => by
    rw [show a + o + j = a + (o + j) by omega,
      getD_log_sd log m k a (o + j) _ (by omega) h (outL_of_range hout (by omega) (by omega)),
      bytesT8_extract m0 x (o + j) (by omega), show x + (o + j) = x + o + j by omega]

/-- The `k`-th entry of a log, a word store of `n`, read back through the later entries. -/
theorem bytesT4_log_sw : ∀ (log : List WEntry) (m : Mem) (k a n : Nat), n < 2 ^ 32 →
    (log.drop k).head? = some (a, 4, BitVec.ofNat 64 n) → OutLRange (log.drop (k + 1)) a 4 →
    bytesT4 (writeLog m log) a = BitVec.ofNat 32 n
  | [], _, _, _, _, _, h, _ => by simp at h
  | e :: log, m, 0, a, n, hn, h, hout => by
      simp only [List.drop_zero, List.head?_cons, Option.some.injEq] at h
      subst h
      show bytesT4 (writeLog (writeLog m [(a, 4, BitVec.ofNat 64 n)]) log) a = _
      have hout' : OutLRange log a 4 := hout
      rw [bytesT4_congr fun y h1 h2 => writeLog_out _ log y (outL_of_range hout' h1 h2)]
      exact bytesT4_sw_self m a n hn
  | _ :: log, _, k + 1, a, n, hn, h, hout => bytesT4_log_sw log _ k a n hn h hout

end Tom.Machine
