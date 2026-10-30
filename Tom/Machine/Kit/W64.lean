import Tom.Machine.Kit.Meet
import Tom.Machine.Kit.Copy
import Tom.Spec.Mont

/-!
# An `mp_word` array over the digit-array kind

`s_mp_montgomery_reduce_fast` keeps its columns `W[MP_WARRAY]` as 64-bit words
(`ld`/`sd`). Over `Kit/Meet.lean`'s digit-array kind (`Kind.mpD`, 32-bit
words) word `i` is the digits `2 i` (low half) and `2 i + 1` (high half):

* `Dig.ld`: an `ld` of word `i` reads `w64 g i`;
* `ArrAt.set8`, `St.seqD8`: an `sd` of `v` into word `i` sets the two halves
  (`St.seqD` for doublewords);
* `h32 W`: the halves of a word function `W` (`w64_h32`, `h32_upd`).
-/

namespace Tom.Machine

open Vsa.Sim Vsa.Logic Tom.Mont

/-- Word `i` of a digit array of halves. -/
def w64 (g : Nat → Nat) (i : Nat) : Nat := g (2 * i) + 4294967296 * g (2 * i + 1)

/-- The halves of the words `W`. -/
def h32 (W : Nat → Nat) (j : Nat) : Nat :=
  if j % 2 = 0 then W (j / 2) % 4294967296 else W (j / 2) / 4294967296 % 4294967296

theorem h32_lt (W : Nat → Nat) (j : Nat) : h32 W j < 2 ^ 32 := by
  unfold h32; split <;> exact Nat.mod_lt _ (by decide)

theorem w64_h32 (W : Nat → Nat) (i : Nat) (h : W i < 2 ^ 64) : w64 (h32 W) i = W i := by
  unfold w64 h32
  rw [if_pos (by omega), if_neg (by omega), show 2 * i / 2 = i by omega, show (2 * i + 1) / 2 = i by omega]
  omega

theorem toNat_halves (x : BitVec 64) :
    x.toNat = (x.extractLsb' 0 32).toNat + 4294967296 * (x.extractLsb' 32 32).toNat := by
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  have := x.isLt
  omega

/-- **An `ld` of a word**: its two halves. -/
theorem bytesT8_of_halves {M : Mem} {a lo hi : Nat} (h0 : bytesT4 M a = BitVec.ofNat 32 lo)
    (h1 : bytesT4 M (a + 4) = BitVec.ofNat 32 hi) (hlo : lo < 2 ^ 32) (hhi : hi < 2 ^ 32) :
    bytesT8 M a = BitVec.ofNat 64 (lo + 4294967296 * hi) := by
  rw [bytesT4_lo] at h0; rw [bytesT4_hi] at h1
  apply BitVec.eq_of_toNat_eq
  rw [toNat_halves, h0, h1]
  simp only [BitVec.toNat_ofNat]
  omega

theorem Dig.ld {M : Mem} {dp n : Nat} {g : Nat → Nat} (d : Dig M dp n g) {i : Nat} (hi : 2 * i + 1 < n)
    (hg0 : g (2 * i) < 2 ^ 32) (hg1 : g (2 * i + 1) < 2 ^ 32) : bytesT8 M (dp + 8 * i) = BitVec.ofNat 64 (w64 g i) := by
  have h0 := d.arr (2 * i) (by omega); have h1 := d.arr (2 * i + 1) (by omega)
  rw [show dp + 4 * (2 * i) = dp + 8 * i by omega] at h0
  rw [show dp + 4 * (2 * i + 1) = dp + 8 * i + 4 by omega] at h1
  exact bytesT8_of_halves h0 h1 hg0 hg1

/-- **An `sd` of a word**: the halves of `v`. -/
theorem ArrAt.set8 {m : Mem} {base n : Nat} {f : Nat → Nat} (h : ArrAt m base n f) (i v : Nat) :
    ArrAt (writeLog m [(base + 8 * i, 8, BitVec.ofNat 64 v)]) base n
      (upd (upd f (2 * i) (v % 4294967296)) (2 * i + 1) (v / 4294967296 % 4294967296)) := by
  intro j hj
  have hs := bytesT8_sd_self m (base + 8 * i) (BitVec.ofNat 64 v)
  by_cases h0 : j = 2 * i
  · subst h0
    simp only [upd, show ¬ 2 * i = 2 * i + 1 by omega, if_false, if_true]
    rw [show base + 4 * (2 * i) = base + 8 * i by omega, bytesT4_lo, hs]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one, BitVec.toNat_ofNat]
    omega
  · by_cases h1 : j = 2 * i + 1
    · subst h1
      simp only [upd, if_true]
      rw [show base + 4 * (2 * i + 1) = base + 8 * i + 4 by omega, bytesT4_hi, hs]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
      omega
    · simp only [upd, h0, h1, if_false]
      rw [bytesT4_sd_out _ _ _ _ (by omega)]; exact h j hj

theorem h32_upd (W : Nat → Nat) (i v : Nat) :
    upd (upd (h32 W) (2 * i) (v % 4294967296)) (2 * i + 1) (v / 4294967296 % 4294967296) = h32 (upd W i v) := by
  funext j; unfold upd h32
  by_cases h1 : j = 2 * i + 1
  · subst h1; simp [show (2 * i + 1) % 2 = 1 by omega, show (2 * i + 1) / 2 = i by omega]
  · by_cases h0 : j = 2 * i
    · subst h0; simp [show 2 * i ≠ 2 * i + 1 by omega, show 2 * i / 2 = i by omega]
    · rw [if_neg h1, if_neg h0]
      have : j / 2 ≠ i := by omega
      simp only [this, if_false]

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind} {m M : Mem}
  {pc pc' : BitVec 64} {L0 L L' K : GRegs} {o : Array String} {Q : Vsa.Machine.Config → Prop}

/-- **A segment that stores word `i`** (`sd`) of the digit array `r`, then the rest. -/
theorem St.seqD8 (h : St ρ isW W κ m M) (r : ι) {dp n i v : Nat} {f : Nat → Nat} (hk : κ r = .mpD dp n f)
    (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M [(dp + 8 * i, 8, BitVec.ofNat 64 v)]) K o))
    (hi : 2 * i + 1 < n)
    (k : ∀ M', St ρ isW W (Kind.set κ r (.mpD dp n (upd (upd f (2 * i) (v % 4294967296)) (2 * i + 1)
      (v / 4294967296 % 4294967296)))) m M' → Triple (At pc' L' M' K o) Q)
    (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q := by
  refine Triple.pre ?_ hL
  have hf := (h.wit r).1; rw [hk] at hf
  have hd := (h.wit r).2; rw [hk] at hd
  have hsub : Iv.Sub ⟨dp + 8 * i, 8⟩ (ρ r) :=
    Iv.Sub.trans (J := ⟨dp, 4 * n⟩) ⟨by simp only; omega, by simp only; omega⟩ hf
  refine Triple.seq hseg (k _ (h.step (Frm.store (w := r) ⟨hsub, trivial⟩) (by simp [hw]) hW
    (fun r' hr' => ?_) (fun r' hr' => ?_)))
  · simp only [List.mem_singleton] at hr'; subst hr'
    simp only [Kind.set, if_true, Kind.Fits, Kind.Wit]
    exact ⟨hf, { ram := hd.ram, al := hd.al, arr := hd.arr.set8 i v }⟩
  · simp only [List.mem_singleton] at hr'; simp [Kind.set, hr']

/-- `St.seqD8` with the store's address spelled otherwise (`dp + 8 * i + 8` for word `i + 1`): the
word's index `i` given, the address by an equation (the generated `"d8"` store rule). -/
theorem St.seqD8' (h : St ρ isW W κ m M) (r : ι) {dp n a v : Nat} (i : Nat) {f : Nat → Nat}
    (hk : κ r = .mpD dp n f) (ha : a = dp + 8 * i)
    (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M [(a, 8, BitVec.ofNat 64 v)]) K o))
    (hi : 2 * i + 1 < n)
    (k : ∀ M', St ρ isW W (Kind.set κ r (.mpD dp n (upd (upd f (2 * i) (v % 4294967296)) (2 * i + 1)
      (v / 4294967296 % 4294967296)))) m M' → Triple (At pc' L' M' K o) Q)
    (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q := by
  subst ha; exact h.seqD8 r hk hseg hi k hw hW hL

end

end Tom.Machine
