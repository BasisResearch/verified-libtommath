import Tom.Spec.MpInt
import Tom.Machine.Kit.At
import Vsa.Sim.MemLoadTotal

/-!
# `mp_int` in machine memory

`MpAt m p dp a`: the struct at `p` holds `a`'s `used`, `alloc` and `sign`
and the digit pointer `dp`, and `dp[0 .. alloc)` holds `a`'s digits. All
reads are total (`bytesT4`/`bytesT8`, `Vsa.Sim.MemLoadTotal`), which is how
the Sail model reads memory. Offsets come from `Tom/Layout.lean`.

`Ram lo len`: a range the segment layer may load from and store to (RAM
below `2^32`, off the HTIF mailbox). `MpGeom p dp alloc`: the struct and its
digit array are such ranges, aligned and disjoint.

`rd4 m a`/`rd8 m a`: the bytes a load at `a` reads, as the load data of a
segment (`lds`), so its `LPins4`/`LPins8` fact holds by `rfl`.
-/

namespace Tom.Machine

open Vsa.Sim

/-- `a` at `p`, digits at `dp`. -/
structure MpAt (m : Mem) (p dp : Nat) (a : MpInt) : Prop where
  used : bytesT4 m (p + Layout.offUsed) = BitVec.ofNat 32 a.used
  alloc : bytesT4 m (p + Layout.offAlloc) = BitVec.ofNat 32 a.alloc
  sign : bytesT4 m (p + Layout.offSign) = BitVec.ofNat 32 a.sign
  dpv : bytesT8 m (p + Layout.offDp) = BitVec.ofNat 64 dp
  digits : ∀ i, i < a.alloc → bytesT4 m (dp + Layout.sizeofDigit * i) = BitVec.ofNat 32 (a.digit i)

/-- RAM the segment layer may load from and store to. -/
structure Ram (lo len : Nat) : Prop where
  lo_ge : 0x80000000 ≤ lo
  hi_le : lo + len ≤ 0x100000000
  off : lo + len + 8 ≤ tohostAddr ∨ tohostAddr + 16 ≤ lo

/-- The geometry of an `mp_int` with `alloc` digits. -/
structure MpGeom (p dp alloc : Nat) : Prop where
  st : Ram p Layout.sizeofMpInt
  st_al : p % 8 = 0
  ds : Ram dp (Layout.sizeofDigit * alloc)
  ds_al : dp % 4 = 0
  disj : p + Layout.sizeofMpInt ≤ dp ∨ dp + Layout.sizeofDigit * alloc ≤ p

/-- The bytes a 4-byte load at `a` reads. -/
def rd4 (m : Mem) (a : Nat) : List (BitVec 8) :=
  [(m[a]?).getD 0, (m[a + 1]?).getD 0, (m[a + 2]?).getD 0, (m[a + 3]?).getD 0]

/-- The bytes an 8-byte load at `a` reads. -/
def rd8 (m : Mem) (a : Nat) : List (BitVec 8) :=
  [(m[a]?).getD 0, (m[a + 1]?).getD 0, (m[a + 2]?).getD 0, (m[a + 3]?).getD 0,
   (m[a + 4]?).getD 0, (m[a + 5]?).getD 0, (m[a + 6]?).getD 0, (m[a + 7]?).getD 0]

theorem lpins4_rd4 (m : Mem) (a : Nat) : LPins4 m a (rd4 m a) := ⟨rfl, rfl, rfl, rfl⟩

theorem lpins8_rd8 (m : Mem) (a : Nat) : LPins8 m a (rd8 m a) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A load's value from `rd4` data, folded back to the total read. -/
theorem rd4_bytes (m : Mem) (a : Nat) :
    @Eq (BitVec (8 + 8 + 8 + 8)) ((rd4 m a)[3]?.getD 0#8 ++ (rd4 m a)[2]?.getD 0#8 ++
      (rd4 m a)[1]?.getD 0#8 ++ (rd4 m a)[0]?.getD 0#8) (bytesT4 m a) := rfl

theorem rd8_bytes (m : Mem) (a : Nat) :
    @Eq (BitVec (8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)) ((rd8 m a)[7]?.getD 0#8 ++ (rd8 m a)[6]?.getD 0#8 ++
      (rd8 m a)[5]?.getD 0#8 ++ (rd8 m a)[4]?.getD 0#8 ++ (rd8 m a)[3]?.getD 0#8 ++
      (rd8 m a)[2]?.getD 0#8 ++ (rd8 m a)[1]?.getD 0#8 ++ (rd8 m a)[0]?.getD 0#8) (bytesT8 m a) := rfl

theorem rd4_bytesD (m : Mem) (a : Nat) :
    @Eq (BitVec (8 + 8 + 8 + 8)) ((rd4 m a).getD 3 0#8 ++ (rd4 m a).getD 2 0#8 ++
      (rd4 m a).getD 1 0#8 ++ (rd4 m a).getD 0 0#8) (bytesT4 m a) := rfl

theorem rd8_bytesD (m : Mem) (a : Nat) :
    @Eq (BitVec (8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)) ((rd8 m a).getD 7 0#8 ++ (rd8 m a).getD 6 0#8 ++
      (rd8 m a).getD 5 0#8 ++ (rd8 m a).getD 4 0#8 ++ (rd8 m a).getD 3 0#8 ++
      (rd8 m a).getD 2 0#8 ++ (rd8 m a).getD 1 0#8 ++ (rd8 m a).getD 0 0#8) (bytesT8 m a) := rfl

theorem rd8_bytesD' (m : Mem) (a : Nat) :
    @Eq (BitVec (8 * 8)) ((rd8 m a).getD 7 0#8 ++ (rd8 m a).getD 6 0#8 ++
      (rd8 m a).getD 5 0#8 ++ (rd8 m a).getD 4 0#8 ++ (rd8 m a).getD 3 0#8 ++
      (rd8 m a).getD 2 0#8 ++ (rd8 m a).getD 1 0#8 ++ (rd8 m a).getD 0 0#8) (bytesT8 m a) := rfl

theorem lpins4_rd4_of {m : Mem} {a b : Nat} (h : a = b) : LPins4 m a (rd4 m b) := h ▸ lpins4_rd4 m a

theorem lpins8_rd8_of {m : Mem} {a b : Nat} (h : a = b) : LPins8 m a (rd8 m b) := h ▸ lpins8_rd8 m a

/-- A load's pins from the segment's entry memory `M0`, when the bytes it
reads were not stored to inside the segment (`h`, closed by `code_frame`). -/
theorem lpins4_rd4_frame {m M0 : Mem} {ea a : Nat} (hea : ea = a)
    (h : ∀ x, a ≤ x → x < a + 4 → m[x]? = M0[x]?) : LPins4 m ea (rd4 M0 a) := by
  subst hea
  exact ⟨by rw [h ea (by omega) (by omega)]; rfl, by rw [h (ea + 1) (by omega) (by omega)]; rfl,
    by rw [h (ea + 2) (by omega) (by omega)]; rfl, by rw [h (ea + 3) (by omega) (by omega)]; rfl⟩

theorem lpins8_rd8_frame {m M0 : Mem} {ea a : Nat} (hea : ea = a)
    (h : ∀ x, a ≤ x → x < a + 8 → m[x]? = M0[x]?) : LPins8 m ea (rd8 M0 a) := by
  subst hea
  exact ⟨by rw [h ea (by omega) (by omega)]; rfl, by rw [h (ea + 1) (by omega) (by omega)]; rfl,
    by rw [h (ea + 2) (by omega) (by omega)]; rfl, by rw [h (ea + 3) (by omega) (by omega)]; rfl,
    by rw [h (ea + 4) (by omega) (by omega)]; rfl, by rw [h (ea + 5) (by omega) (by omega)]; rfl,
    by rw [h (ea + 6) (by omega) (by omega)]; rfl, by rw [h (ea + 7) (by omega) (by omega)]; rfl⟩

end Tom.Machine
