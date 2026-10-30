import Tom.Machine.Kit.MemStore
import Tom.Machine.Kit.Arr

/-!
# Copies: byte and doubleword loads stored elsewhere

A copy loop loads from a source `s` and stores what it loaded at a
destination `d` at the same offset. `CopyOn m M d s S`: for every offset `i`
with `S i`, `M` holds at `d + i` the byte `m` holds at `s + i` (read totally,
as the load reads it), and `M` agrees with `m` off those destination bytes.
`Copied m M d s t` is the prefix case `S i := i < t`.

`CopyOn.sb`/`CopyOn.sd` extend `S` by one `sb` (an `lbu`'d byte) or one `sd`
(an `ld`'d doubleword) at any offset, so stores in any order compose (the
unrolled 72-byte block of newlib `memcpy`); `CopyOn.mono` renormalises `S`.
`rd1` is the load data of an `lbu` (its `MemFacts` by `lbu_pin`/
`lbu_pin_frame`), `sbData_zext`/`bytesT8_lane` say what the store of a loaded
value writes (`sbData_zext` is `Vsa/Sim/MemcpySpec.lean`'s, restated here so the
Kit does not import that file's per-site layer).
-/

namespace Tom.Machine

open Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- The copy of the offsets `S` of `s` to `d` (see the module doc). -/
structure CopyOn (m M : Mem) (d s : Nat) (S : Nat → Prop) : Prop where
  copy : ∀ i, S i → M[d + i]? = some ((m[s + i]?).getD 0)
  frame : ∀ y, (∀ i, S i → y ≠ d + i) → M[y]? = m[y]?

/-- The copy of the first `t` bytes. -/
abbrev Copied (m M : Mem) (d s t : Nat) : Prop := CopyOn m M d s (· < t)

theorem Copied.zero (m : Mem) (d s : Nat) : Copied m m d s 0 :=
  ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩

theorem CopyOn.mono {m M : Mem} {d s : Nat} {S S' : Nat → Prop} (h : CopyOn m M d s S)
    (e : ∀ i, S i ↔ S' i) : CopyOn m M d s S' :=
  ⟨fun i hi => h.copy i ((e i).2 hi), fun y hy => h.frame y fun i hi => hy i ((e i).1 hi)⟩

/-- Off the destination prefix `[d, d + t)` memory is `m`'s. -/
theorem Copied.out {m M : Mem} {d s t y : Nat} (h : Copied m M d s t) (hy : y < d ∨ d + t ≤ y) :
    M[y]? = m[y]? :=
  h.frame y fun i hi => by omega

/-- One `sb` of the byte `m` holds at `s + o`, at `d + o`. -/
theorem CopyOn.sb {m M : Mem} {d s : Nat} {S : Nat → Prop} (h : CopyOn m M d s S) (o : Nat)
    {v : BitVec 64} (hv : sbData v = (m[s + o]?).getD 0) :
    CopyOn m (applyW M (d + o, 1, v)) d s (fun i => S i ∨ i = o) := by
  constructor
  · intro i hi
    rw [getElem?_applyW_sb]
    by_cases e : i = o
    · subst e; simp [hv]
    · simp only [show d + i ≠ d + o by omega, ↓reduceIte]
      exact h.copy i (hi.resolve_right e)
  · intro y hy
    simp only [getElem?_applyW_sb, hy o (Or.inr rfl), ↓reduceIte]
    exact h.frame y fun i hi => hy i (Or.inl hi)

/-- One `sd` of the eight bytes `m` holds at `s + o`, at `d + o`. -/
theorem CopyOn.sd {m M : Mem} {d s : Nat} {S : Nat → Prop} (h : CopyOn m M d s S) (o : Nat)
    {v : BitVec 64} (hv : ∀ j, j < 8 → (sdData_val v).extractLsb' (8 * j) 8 = (m[s + o + j]?).getD 0) :
    CopyOn m (applyW M (d + o, 8, v)) d s (fun i => S i ∨ (o ≤ i ∧ i < o + 8)) := by
  constructor
  · intro i hi
    by_cases e : o ≤ i ∧ i < o + 8
    · rw [getElem?_applyW_sd_in _ _ _ _ (by omega) (by omega),
        show d + i - (d + o) = i - o by omega, hv _ (by omega),
        show s + o + (i - o) = s + i by omega]
    · rw [applyW_out _ _ _ _ _ (by omega)]
      exact h.copy i (hi.resolve_right e)
  · intro y hy
    have h1 : y < d + o ∨ d + o + 8 ≤ y := by
      by_cases hl : d + o ≤ y
      · by_cases hr : y < d + o + 8
        · exact absurd (show y = d + (y - d) by omega) (hy (y - d) (Or.inr ⟨by omega, by omega⟩))
        · omega
      · omega
    rw [applyW_out _ _ _ _ _ h1]
    exact h.frame y fun i hi => hy i (Or.inl hi)

/-- Code off the destination prefix is kept. -/
theorem Copied.code {m M : Mem} {d s t : Nat} {base : Nat} {ws : List (BitVec 32)}
    (h : Copied m M d s t) (hc : CodeAt m base ws)
    (hoff : d + t ≤ base ∨ base + 4 * ws.length ≤ d) : CodeAt M base ws :=
  hc.of_eq fun a h1 h2 => h.out (by omega)

/-! ## What the loads read and the stores write -/

/-- The load data of an `lbu` at `a`. -/
def rd1 (m : Mem) (a : Nat) : List (BitVec 8) := [(m[a]?).getD 0]

/-- An `lbu`'s byte pin. -/
theorem lbu_pin {m : Mem} {ea a : Nat} (h : ea = a) : (m[ea]?).getD 0 = (rd1 m a).getD 0 0#8 := by
  subst h; rfl

/-- An `lbu`'s byte pin from the segment's entry memory `M0`, when the byte
was not stored to inside the segment (`h`, closed by `code_frame`). -/
theorem lbu_pin_frame {m M0 : Mem} {ea a : Nat} (hea : ea = a)
    (h : ∀ x, a ≤ x → x < a + 1 → m[x]? = M0[x]?) : (m[ea]?).getD 0 = (rd1 M0 a).getD 0 0#8 := by
  subst hea; simp only [rd1, List.getD_cons_zero]; rw [h ea (by omega) (by omega)]

/-- The byte an `sb` of an `lbu`'d value stores. -/
theorem sbData_zext (b : BitVec 8) : sbData (zero_extend (m := 64) (b : BitVec (8 * 1))) = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [sbData, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  have hlt : b.toNat < 2 ^ 8 := b.isLt
  have key : ∀ W : Nat, (2 : Nat) ^ W = 2 ^ 8 → (BitVec.ofNat W (b.toNat % 2 ^ 64)).toNat = b.toNat := by
    intro W hW
    rw [BitVec.toNat_ofNat, hW, Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt hlt]
  exact key _ (by decide)

/-- Byte `j` of eight appended bytes. -/
theorem lane8 (x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 8) :
    ∀ j, j < 8 → (((((((x7.append x6).append x5).append x4).append x3).append x2).append x1).append
      x0).extractLsb' (8 * j) 8 = [x0, x1, x2, x3, x4, x5, x6, x7].getD j 0 := by
  intro j hj
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals first
    | omega
    | (apply BitVec.eq_of_getElem_eq; intro i hi
       simp only [BitVec.getElem_extractLsb', BitVec.append_eq, BitVec.getLsbD_append,
         List.getD_cons_zero, List.getD_cons_succ]
       rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
       all_goals first | omega | simp [BitVec.getLsbD_eq_getElem])

/-- Byte `j` of an `ld`'d doubleword, stored by `sd`. -/
theorem bytesT8_lane (M : Mem) (a : Nat) :
    ∀ j, j < 8 → (sdData_val (bytesT8 M a)).extractLsb' (8 * j) 8 = (M[a + j]?).getD 0 := by
  intro j hj
  rw [sdData_val_id, bytesT8, lane8 _ _ _ _ _ _ _ _ j hj]
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals first | omega | rfl

/-- The value an `lbu` of the byte at `a` writes. -/
def ldb (M : Mem) (a : Nat) : BitVec 64 := zero_extend (m := 64) (((M[a]?).getD 0 : BitVec 8) : BitVec (8 * 1))

/-- One more byte of a prefix copy (`lbu` from `s + t`, `sb` at `d + t`), the
source byte off the copied prefix. -/
theorem Copied.byte {m M : Mem} {d s t : Nat} (h : Copied m M d s t) (hsrc : s + t < d ∨ d + t ≤ s + t) :
    Copied m (writeLog M [(d + t, 1, ldb M (s + t))]) d s (t + 1) := by
  have hv : sbData (ldb M (s + t)) = (m[s + t]?).getD 0 := by
    rw [ldb, sbData_zext, h.out hsrc]
  exact (h.sb t hv).mono fun i => by omega

/-- Eight more bytes of a prefix copy (`ld` from `s + t`, `sd` at `d + t`), the
source doubleword off the copied prefix. -/
theorem Copied.dword {m M : Mem} {d s t : Nat} (h : Copied m M d s t)
    (hsrc : s + t + 8 ≤ d ∨ d + t ≤ s + t) :
    Copied m (writeLog M [(d + t, 8, bytesT8 M (s + t))]) d s (t + 8) := by
  have hv : ∀ j, j < 8 → (sdData_val (bytesT8 M (s + t))).extractLsb' (8 * j) 8 =
      (m[s + t + j]?).getD 0 := fun j hj => by
    rw [bytesT8_lane M _ j hj, h.out (by omega)]
  exact (h.sd t hv).mono fun i => by omega

/-- Off the destination range `[d, d + n)` memory is `m`'s, when `S` is inside it. -/
theorem CopyOn.out {m M : Mem} {d s n y : Nat} {S : Nat → Prop} (h : CopyOn m M d s S)
    (hS : ∀ i, S i → i < n) (hy : y < d ∨ d + n ≤ y) : M[y]? = m[y]? :=
  h.frame y fun i hi => by have := hS i hi; omega

/-- `CopyOn.sd` at an address given by an equation. -/
theorem CopyOn.sd' {m M : Mem} {d s : Nat} {S : Nat → Prop} (h : CopyOn m M d s S) {a o : Nat}
    (ha : a = d + o) {v : BitVec 64}
    (hv : ∀ j, j < 8 → (sdData_val v).extractLsb' (8 * j) 8 = (m[s + o + j]?).getD 0) :
    CopyOn m (applyW M (a, 8, v)) d s (fun i => S i ∨ (o ≤ i ∧ i < o + 8)) := by
  subst ha; exact h.sd o hv

/-- `Copied.byte` with the byte loaded from a memory `M0` that agrees with
`m` on it, at addresses given by equations. -/
theorem Copied.byte' {m M M0 : Mem} {d s t a b : Nat} (h : Copied m M d s t) (ha : a = d + t)
    (hb : b = s + t) (hv : M0[b]? = m[b]?) :
    Copied m (writeLog M [(a, 1, ldb M0 b)]) d s (t + 1) := by
  subst ha hb
  have hv' : sbData (ldb M0 (s + t)) = (m[s + t]?).getD 0 := by rw [ldb, sbData_zext, hv]
  exact (h.sb t hv').mono fun i => by omega

/-- `Copied.dword` with the doubleword loaded from a memory `M0` that agrees
with `m` on it, at addresses given by equations. -/
theorem Copied.dword' {m M M0 : Mem} {d s t a b : Nat} (h : Copied m M d s t) (ha : a = d + t)
    (hb : b = s + t) (hv : ∀ j, j < 8 → M0[b + j]? = m[b + j]?) :
    Copied m (writeLog M [(a, 8, bytesT8 M0 b)]) d s (t + 8) := by
  subst ha hb
  have hv' : ∀ j, j < 8 → (sdData_val (bytesT8 M0 (s + t))).extractLsb' (8 * j) 8 =
      (m[s + t + j]?).getD 0 := fun j hj => by rw [bytesT8_lane M0 _ j hj, hv j hj]
  exact (h.sd t hv').mono fun i => by omega

end Tom.Machine
