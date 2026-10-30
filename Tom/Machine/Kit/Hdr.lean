import Tom.Machine.Kit.Frame
import Tom.Machine.Kit.Mem

/-!
# An `mp_int`'s struct without its digits

`HdrAt m p dp used alloc sign`: the struct at `p` holds these fields and the
digit pointer `dp` (the four non-digit fields of `MpAt`). A function that
stores into the struct between digit loops (`b->used := …`, `++b->used`,
`b->sign := …`) carries its struct as an `HdrAt` and its digits as an
`ArrAt` (an `ArrFrm` at loop join points), and puts them back together as
an `MpAt` at the end (`HdrAt.mpAt`). The struct is read only in its own
region (`HdrAt.reads`); `HdrAt.set_used`/`set_sign` are the two stores.
-/

namespace Tom.Machine

open Vsa.Sim

/-- The struct at `p`: `used`, `alloc`, `sign`, the digit pointer `dp`. -/
structure HdrAt (m : Mem) (p dp used alloc sign : Nat) : Prop where
  used : bytesT4 m (p + Layout.offUsed) = BitVec.ofNat 32 used
  alloc : bytesT4 m (p + Layout.offAlloc) = BitVec.ofNat 32 alloc
  sign : bytesT4 m (p + Layout.offSign) = BitVec.ofNat 32 sign
  dpv : bytesT8 m (p + Layout.offDp) = BitVec.ofNat 64 dp

theorem MpAt.hdr {m : Mem} {p dp : Nat} {a : MpInt} (h : MpAt m p dp a) : HdrAt m p dp a.used a.alloc a.sign :=
  ⟨h.used, h.alloc, h.sign, h.dpv⟩

/-- The struct and the digits make an `mp_int`. -/
theorem HdrAt.mpAt {m : Mem} {p dp : Nat} {a : MpInt} (h : HdrAt m p dp a.used a.alloc a.sign)
    (hd : ArrAt m dp a.alloc a.digit) : MpAt m p dp a :=
  { used := h.used, alloc := h.alloc, sign := h.sign, dpv := h.dpv
    digits := fun i hi => by simpa [Layout.sizeofDigit] using hd i hi }

theorem HdrAt.of_agree {m m' : Mem} {p dp u al s : Nat} (h : HdrAt m p dp u al s)
    (hs : ∀ x, p ≤ x → x < p + 24 → m'[x]? = m[x]?) : HdrAt m' p dp u al s :=
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
        (by simp [Layout.offDp] at *; omega))]; exact h.dpv }

theorem HdrAt.reads {ι : Type} {ρ : ι → Iv} {r : ι} {p dp u al s : Nat} (hs : Iv.Sub ⟨p, 24⟩ (ρ r)) :
    Reads ρ [r] (fun M => HdrAt M p dp u al s) :=
  Reads.of_sub hs fun _ _ h hv => hv.of_agree fun x h1 h2 => h x h1 h2

/-- Storing `used := n`. -/
theorem HdrAt.set_used {m : Mem} {p dp u al s : Nat} (h : HdrAt m p dp u al s) (n : Nat) (hn : n < 2 ^ 32) :
    HdrAt (writeLog m [(p, 4, BitVec.ofNat 64 n)]) p dp n al s :=
  { used := by simp only [Layout.offUsed, Nat.add_zero]; exact bytesT4_sw_self m p n hn
    alloc := by rw [bytesT4_sw_out _ _ _ _ (by simp [Layout.offAlloc])]; exact h.alloc
    sign := by rw [bytesT4_sw_out _ _ _ _ (by simp [Layout.offSign])]; exact h.sign
    dpv := by rw [bytesT8_sw_out _ _ _ _ (by simp [Layout.offDp])]; exact h.dpv }

/-- Storing `sign := s'`. -/
theorem HdrAt.set_sign {m : Mem} {p dp u al s : Nat} (h : HdrAt m p dp u al s) (s' : Nat) (hs : s' < 2 ^ 32) :
    HdrAt (writeLog m [(p + 8, 4, BitVec.ofNat 64 s')]) p dp u al s' :=
  { used := by rw [bytesT4_sw_out _ _ _ _ (by simp [Layout.offUsed])]; exact h.used
    alloc := by rw [bytesT4_sw_out _ _ _ _ (by simp [Layout.offAlloc])]; exact h.alloc
    sign := by simp only [Layout.offSign]; exact bytesT4_sw_self m (p + 8) s' hs
    dpv := by rw [bytesT8_sw_out _ _ _ _ (by simp [Layout.offDp])]; exact h.dpv }

end Tom.Machine
