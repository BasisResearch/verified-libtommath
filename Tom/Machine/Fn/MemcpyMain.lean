import Tom.Machine.Fn.Memcpy
import Tom.Machine.Img

/-!
# newlib `memcpy` on the machine: the loops and the contract

The segments are `Fn/Memcpy.lean`'s. Every loop head carries the copy so far
as `Kit/MemCopy.lean`'s `Copied` (`CSt`: some memory holding the first `t`
bytes of `s` at `d`, `At` the head). The byte loop and the word loop run a
known number of times (`Triple.countup`); the head and the 72-byte block loop
stop on a condition of the cursor, so they are `Triple.countdown` on a fuel
that bounds the bytes left (`HdInv.fuel`, `BkInv.fuel`). The 72-byte block
stores its doublewords out of order (`0, 8, 64, 16, …, 56`): in between, the
copy is `CopyOn` a prefix and the slot `[q + 64, q + 72)` (`Gap`).

`correct`: from the entry, for all `n` and all alignments of `d` and `s`,
`memcpy(d, s, n)` returns to `ra` with `a0 = d`, the `n` bytes of `s` at `d`
(read totally, as a load reads them), memory unchanged elsewhere, and the
callee-saved registers kept.
-/

namespace Tom.Machine.Fn.Memcpy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

/-- What `memcpy(d, s, n)` leaves: the `n` bytes of `s` at `d`, memory
unchanged elsewhere. -/
structure Post (m : Mem) (d s n : Nat) (M : Mem) : Prop where
  copy : ∀ i, i < n → M[d + i]? = some ((m[s + i]?).getD 0)
  frame : ∀ x, x < d ∨ d + n ≤ x → M[x]? = m[x]?

/-- The return state: at `ra` with `a0 = d`, the callee-saved registers `w`. -/
def Ret (ra : BitVec 64) (w : Abi) (outp : Array String) (m : Mem) (d s n : Nat)
    (c : Vsa.Machine.Config) : Prop :=
  ∃ M, At ra (retL ra d) M w.keep outp c ∧ Post m d s n M

theorem Post.of_copied {m M : Mem} {d s n : Nat} (h : Copied m M d s n) : Post m d s n M :=
  ⟨h.copy, fun _ hx => h.out hx⟩

/-- The segments' `Room` through a copy inside `[d, d + n)`. -/
theorem Room.of {m M : Mem} {d s n : Nat} {S : Nat → Prop} (hR : Room m d s n)
    (h : CopyOn m M d s S) (hS : ∀ i, S i → i < n) : Room M d s n :=
  { hR with
    code := hR.code.of_eq fun a h1 h2 => h.out hS (by have := hR.code_off; rw [code_len] at h2; omega) }

/-- Copied so far `t` bytes, parked at `pc` with registers `L`. -/
abbrev CSt (m : Mem) (d s t : Nat) (pc : BitVec 64) (L : GRegs) (w : Abi) (outp : Array String)
    (c : Vsa.Machine.Config) : Prop :=
  ∃ M, Copied m M d s t ∧ At pc L M w.keep outp c

/-- The source bytes off the copied prefix are `m`'s. -/
theorem src_out {m M : Mem} {d s n t x : Nat} (hR : Room m d s n) (h : Copied m M d s t)
    (ht : t ≤ n) (hx : s ≤ x) (hx' : x < s + n) : M[x]? = m[x]? :=
  h.out (by have := hR.disj; omega)

/-! ## The byte loop and the exit test -/

/-- **The byte loop** from `t < n` bytes copied. -/
theorem bytes (ra : BitVec 64) (w : Abi) (outp : Array String) (m : Mem) (d s n : Nat)
    (hR : Room m d s n) (hra : ra.toNat % 4 = 0) :
    ∀ t, t < n → Triple (CSt m d s t 0x80009500#64 (cur ra d s n t) w outp) (Ret ra w outp m d s n) := by
  intro t ht
  have hn : 0 < n := by omega
  refine Triple.countup (P := fun t => CSt m d s t 0x80009500#64 (cur ra d s n t) w outp) ?_ ?_ t ht
  · intro i hi
    refine Triple.exists_pre fun M => Triple.of_pure fun hC => ?_
    refine Triple.rmap (fun c h => ⟨_, hC.byte' rfl rfl (src_out hR hC (by omega) (by omega) (by omega)), h⟩)
      (bl_step ra d s n i w outp M (hR.of hC fun _ h => by omega) hi)
  · refine Triple.exists_pre fun M => Triple.of_pure fun hC => ?_
    refine Triple.rmap (fun c h => ⟨_, h, Post.of_copied ?_⟩)
      (bx_step ra d s n (n - 1) w outp M (hR.of hC fun _ h => by omega) (by omega) hra)
    have := hC.byte' rfl rfl (src_out hR hC (by omega) (by omega) (by omega))
    rwa [show n - 1 + 1 = n by omega] at this

/-- **The exit test** (`94f0`) with `t ≤ n` bytes copied. -/
theorem fin (ra : BitVec 64) (w : Abi) (outp : Array String) (m : Mem) (d s n t : Nat)
    (hR : Room m d s n) (hra : ra.toNat % 4 = 0) (ht : t ≤ n) :
    Triple (CSt m d s t 0x800094f0#64 (cur ra d s n t) w outp) (Ret ra w outp m d s n) := by
  refine Triple.exists_pre fun M => Triple.of_pure fun hC => ?_
  have hR' := hR.of hC fun _ h => by omega
  by_cases hn : t = n
  · subst hn
    exact Triple.rmap (fun c h => ⟨M, h, Post.of_copied hC⟩) (j0_step ra d s t w outp M hR' hra)
  · exact Triple.seq (Triple.rmap (fun c h => ⟨M, hC, h⟩) (j1_step ra d s n t w outp M hR' (by omega)))
      (bytes ra w outp m d s n hR hra t (by omega))

/-! ## The word loop -/

/-- **The word loop** from `q0` (`d + q0` 8-aligned, below the 8-aligned end
`e`), then the exit test. -/
theorem words (ra : BitVec 64) (w : Abi) (outp : Array String) (m : Mem) (d s n q0 : Nat)
    (hR : Room m d s n) (hra : ra.toNat % 4 = 0) (ha : (d + q0) % 8 = 0)
    (hq : d + q0 < d + n - (d + n) % 8) :
    ∀ i, i < (d + n - (d + n) % 8 - (d + q0)) / 8 →
      Triple (CSt m d s (q0 + 8 * i) 0x800094c0#64 (wL ra d s n q0 (q0 + 8 * i)) w outp)
        (Ret ra w outp m d s n) := by
  have hR3 := ram_bounds hR.rd
  refine Triple.countup (n := (d + n - (d + n) % 8 - (d + q0)) / 8)
    (P := fun i => CSt m d s (q0 + 8 * i) 0x800094c0#64 (wL ra d s n q0 (q0 + 8 * i)) w outp) ?_ ?_
  · intro i hi
    refine Triple.exists_pre fun M => Triple.of_pure fun hC => ?_
    have hC' := hC.dword' rfl rfl fun j hj => src_out hR hC (by omega) (by omega) (by omega)
    rw [show q0 + 8 * i + 8 = q0 + 8 * (i + 1) by omega] at hC'
    refine Triple.rmap (fun c h => ⟨_, hC', ?_⟩)
      (wl_step ra d s n q0 (q0 + 8 * i) w outp M (hR.of hC fun _ h => by omega) (by omega) (by omega))
    rwa [show q0 + 8 * i + 8 = q0 + 8 * (i + 1) by omega] at h
  · refine Triple.exists_pre fun M => Triple.of_pure fun hC => ?_
    have hC' := hC.dword' rfl rfl fun j hj => src_out hR hC (by omega) (by omega) (by omega)
    have hRM := hR.of hC fun _ h => by omega
    refine Triple.seq (wx_step ra d s n q0 _ w outp M hRM (by omega) (by omega))
      (Triple.seq (we_step ra d s n q0 _ w outp _ (hR.of hC' fun _ h => by omega) ha hq) ?_)
    refine Triple.lmap (fun c h => ⟨_, ?_, h⟩) (fin ra w outp m d s n _ hR hra (by omega))
    rwa [show q0 + 8 * ((d + n - (d + n) % 8 - (d + q0)) / 8 - 1) + 8 = d + n - (d + n) % 8 - d by
      omega] at hC'

/-- **The word loop's test** (`94b4`) at `q` (`d + q` 8-aligned, at most the
8-aligned end). -/
theorem fsel (ra : BitVec 64) (w : Abi) (outp : Array String) (m : Mem) (d s n q : Nat)
    (hR : Room m d s n) (hra : ra.toNat % 4 = 0) (ha : (d + q) % 8 = 0)
    (hq : d + q ≤ d + n - (d + n) % 8) :
    Triple (CSt m d s q 0x800094b4#64 (fL ra d s n q) w outp) (Ret ra w outp m d s n) := by
  refine Triple.exists_pre fun M => Triple.of_pure fun hC => ?_
  have hRM := hR.of hC fun _ h => by omega
  by_cases he : d + q = d + n - (d + n) % 8
  · exact Triple.seq (Triple.rmap (fun c h => ⟨M, hC, h⟩) (fn_step ra d s n q w outp M hRM he))
      (fin ra w outp m d s n q hR hra (by omega))
  · refine Triple.seq (Triple.rmap (fun c h => ⟨M, ?_, h⟩) (fw_step ra d s n q w outp M hRM (by omega)))
      (words ra w outp m d s n q hR hra ha (by omega) 0 (by omega))
    simpa using hC

/-! ## The 72-byte blocks -/

/-- Inside a block: the prefix `[0, a)` and the slot `[q + 64, q + 72)` copied. -/
abbrev Gap (m M : Mem) (d s q a : Nat) : Prop :=
  CopyOn m M d s (fun i => i < a ∨ (q + 64 ≤ i ∧ i < q + 72))

/-- The doublewords of a block, from its entry memory `M0`. -/
theorem lane {m M0 : Mem} {d s n q : Nat} (hR : Room m d s n) (hC : Copied m M0 d s q) (k : Nat)
    (hk : q + k + 8 ≤ n) :
    ∀ j, j < 8 → (sdData_val (bv M0 s q k)).extractLsb' (8 * j) 8 = (m[s + (q + k) + j]?).getD 0 :=
  fun j hj => by
    rw [bv, bytesT8_lane M0 _ j hj, show s + q + k + j = s + (q + k) + j by omega,
      src_out hR hC (by omega) (by omega) (by omega)]

/-- **One block** (`9518`–`9568`): 72 bytes from `q`. -/
theorem block (ra : BitVec 64) (w : Abi) (outp : Array String) (m : Mem) (d s n q : Nat)
    (hR : Room m d s n) (ha : (d + q) % 8 = 0) (hb : 64 < d + n - (d + n) % 8 - (d + q)) :
    Triple (CSt m d s q 0x80009518#64 (bigL ra d s n q) w outp)
      (CSt m d s (q + 72) 0x80009568#64 (bk4L ra d s n q) w outp) := by
  refine Triple.exists_pre fun M0 => Triple.of_pure fun hC => ?_
  have hq : q + 72 ≤ n := by omega
  have hR0 := hR.of hC fun _ h => by omega
  -- `9538`: the first store, at `q`
  have h1 : Copied m (writeLog M0 [(d + q, 8, bv M0 s q 0)]) d s (q + 8) :=
    hC.dword' rfl rfl fun j hj => src_out hR hC (by omega) (by omega) (by omega)
  -- `9544`: `q + 8`, `q + 64`, `q + 16`
  have h2 : Gap m (writeLog (writeLog M0 [(d + q, 8, bv M0 s q 0)])
      [(d + q + 8, 8, bv M0 s q 8), (d + q + 64, 8, bv M0 s q 64), (d + q + 16, 8, bv M0 s q 16)])
      d s q (q + 24) :=
    (((h1.sd' (o := q + 8) (by omega) (lane hR hC 8 (by omega))).sd' (o := q + 64) (by omega)
      (lane hR hC 64 (by omega))).sd' (o := q + 16) (by omega) (lane hR hC 16 (by omega))).mono
      fun i => by omega
  have hR2 := hR.of h2 fun _ h => by omega
  -- `9550`: `q + 24`, `q + 32`
  have h3 : Gap m (writeLog (writeLog (writeLog M0 [(d + q, 8, bv M0 s q 0)])
      [(d + q + 8, 8, bv M0 s q 8), (d + q + 64, 8, bv M0 s q 64), (d + q + 16, 8, bv M0 s q 16)])
      [(d + q + 24, 8, bv M0 s q 24), (d + q + 32, 8, bv M0 s q 32)]) d s q (q + 40) :=
    ((h2.sd' (o := q + 24) (by omega) (lane hR hC 24 (by omega))).sd' (o := q + 32) (by omega)
      (lane hR hC 32 (by omega))).mono fun i => by omega
  have hR3 := hR.of h3 fun _ h => by omega
  -- `955c`: `q + 40`, `q + 48`, `q + 56`
  have h4 : Copied m (writeLog (writeLog (writeLog (writeLog M0 [(d + q, 8, bv M0 s q 0)])
      [(d + q + 8, 8, bv M0 s q 8), (d + q + 64, 8, bv M0 s q 64), (d + q + 16, 8, bv M0 s q 16)])
      [(d + q + 24, 8, bv M0 s q 24), (d + q + 32, 8, bv M0 s q 32)])
      [(d + q + 40, 8, bv M0 s q 40), (d + q + 48, 8, bv M0 s q 48), (d + q + 56, 8, bv M0 s q 56)])
      d s (q + 72) :=
    (((h3.sd' (o := q + 40) (by omega) (lane hR hC 40 (by omega))).sd' (o := q + 48) (by omega)
      (lane hR hC 48 (by omega))).sd' (o := q + 56) (by omega) (lane hR hC 56 (by omega))).mono
      fun i => by omega
  refine Triple.seq (big1_step ra d s n q w outp M0 hR0 hb) ?_
  refine Triple.seq (big2a_step ra d s n q w outp M0 hR0 ha hb) ?_
  refine Triple.seq (big2b_step ra d s n q w outp M0 _ (hR.of h1 fun _ h => by omega) ha hb) ?_
  refine Triple.seq (big3a_step ra d s n q w outp M0 _ hR2 ha hb) ?_
  exact Triple.rmap (fun c h => ⟨_, h4, h⟩) (big3b_step ra d s n q w outp M0 _ hR3 ha hb)

/-- The block loop's invariant at `q` with fuel `j`. -/
structure BkInv (d n q j : Nat) : Prop where
  al : (d + q) % 8 = 0
  more : 64 < d + n - (d + n) % 8 - (d + q)
  fuel : d + n - (d + n) % 8 - (d + q) ≤ 72 * j + 64

/-- **The block loop** at `q` with fuel `j`, then the word loop's test. -/
theorem blocks (ra : BitVec 64) (w : Abi) (outp : Array String) (m : Mem) (d s n : Nat)
    (hR : Room m d s n) (hra : ra.toNat % 4 = 0) :
    ∀ j, Triple (fun c => ∃ q, BkInv d n q j ∧ CSt m d s q 0x80009518#64 (bigL ra d s n q) w outp c)
      (Ret ra w outp m d s n) := by
  refine Triple.countdown ?_ ?_
  · intro j
    refine Triple.exists_pre fun q => Triple.of_pure fun hI => ?_
    have := hI.al; have := hI.more; have := hI.fuel
    refine Triple.seq (block ra w outp m d s n q hR hI.al hI.more) ?_
    refine Triple.exists_pre fun M => Triple.of_pure fun hC => ?_
    have hRM := hR.of hC fun _ h => by
      have := hR.rd.hi_le; omega
    by_cases hb : 64 < d + n - (d + n) % 8 - (d + q + 72)
    · exact Triple.rmap (fun c h => Or.inr ⟨q + 72, ⟨by omega, by omega, by omega⟩, M, hC, h⟩)
        (big3c_step ra d s n q w outp M hRM hb)
    · exact Triple.rmap (fun _ h => Or.inl h) (Triple.seq (Triple.rmap (fun c h => ⟨M, hC, h⟩)
        (big3cx_step ra d s n q w outp M hRM (by omega)))
        (fsel ra w outp m d s n (q + 72) hR hra (by omega) (by omega)))
  · exact Triple.exists_pre fun q => Triple.of_pure fun hI => by have := hI.more; have := hI.fuel; omega

/-- **The word setup** (`94a4`) at `q` (`d + q` 8-aligned): the block loop or
the word loop's test. -/
theorem gsel (ra : BitVec 64) (w : Abi) (outp : Array String) (m : Mem) (d s n q : Nat)
    (hR : Room m d s n) (hra : ra.toNat % 4 = 0) (ha : (d + q) % 8 = 0) (hq : q ≤ n) :
    Triple (CSt m d s q 0x800094a4#64 (cur ra d s n q) w outp) (Ret ra w outp m d s n) := by
  refine Triple.exists_pre fun M => Triple.of_pure fun hC => ?_
  have hRM := hR.of hC fun _ h => by omega
  by_cases hb : 64 < d + n - (d + n) % 8 - (d + q)
  · refine Triple.seq (Triple.rmap (fun c h => ⟨q, ⟨ha, hb, ?_⟩, M, hC, h⟩)
      (gb_step ra d s n q w outp M hRM hq ha hb))
      (blocks ra w outp m d s n hR hra (d + n - (d + n) % 8 - (d + q)))
    omega
  · exact Triple.seq (Triple.rmap (fun c h => ⟨M, hC, h⟩) (gf_step ra d s n q w outp M hRM hq ha (by omega)))
      (fsel ra w outp m d s n q hR hra ha (by omega))

/-! ## The head -/

/-- The head's invariant at `q` with fuel `j`. -/
structure HdInv (d n q j : Nat) : Prop where
  un : (d + q) % 8 ≠ 0
  room : q + (8 - (d + q) % 8) ≤ n
  fuel : 8 - (d + q) % 8 ≤ 2 * j

/-- **The head** (`9574`) at `q` with fuel `j`: bytes up to an 8-aligned `d + q`,
then the word setup. -/
theorem head (ra : BitVec 64) (w : Abi) (outp : Array String) (m : Mem) (d s n : Nat)
    (hR : Room m d s n) (hra : ra.toNat % 4 = 0) :
    ∀ j, Triple (fun c => ∃ q, HdInv d n q j ∧ CSt m d s q 0x80009574#64 (cur ra d s n q) w outp c)
      (Ret ra w outp m d s n) := by
  refine Triple.countdown ?_ ?_
  · intro j
    refine Triple.exists_pre fun q => Triple.of_pure fun hI => ?_
    have := hI.un; have := hI.room; have := hI.fuel
    refine Triple.exists_pre fun M => Triple.of_pure fun hC => ?_
    have hRM := hR.of hC fun _ h => by omega
    have hC1 := hC.byte' rfl rfl (src_out hR hC (by omega) (by omega) (by omega))
    by_cases h1 : (d + q + 1) % 8 = 0
    · exact Triple.rmap (fun _ h => Or.inl h) (Triple.seq (Triple.rmap (fun c h => ⟨_, hC1, h⟩)
        (h1_step ra d s n q w outp M hRM (by omega) h1))
        (gsel ra w outp m d s n (q + 1) hR hra (by omega) (by omega)))
    have hC2 := hC1.byte' (show d + q + 1 = d + (q + 1) by omega) (show s + q + 1 = s + (q + 1) by omega)
      (src_out hR hC (by omega) (by omega) (by omega))
    rw [show q + 1 + 1 = q + 2 by omega] at hC2
    by_cases h2 : (d + q + 2) % 8 = 0
    · exact Triple.rmap (fun _ h => Or.inl h) (Triple.seq (Triple.rmap (fun c h => ⟨_, hC2, h⟩)
        (h2_step ra d s n q w outp M hRM (by omega) h2))
        (gsel ra w outp m d s n (q + 2) hR hra (by omega) (by omega)))
    · exact Triple.rmap (fun c h => Or.inr ⟨q + 2, ⟨by omega, by omega, by omega⟩, _, hC2, h⟩)
        (h3_step ra d s n q w outp M hRM (by omega) h1 h2)
  · exact Triple.exists_pre fun q => Triple.of_pure fun hI => by
      have := hI.un; have := hI.fuel; omega

/-! ## The function -/

/-- `memcpy`'s entry address. -/
abbrev entry : BitVec 64 := 0x80009480#64

/-- What `memcpy(d, s, n)` needs: the image's code, both ranges in RAM, apart,
and the destination off `memcpy`'s code. -/
structure Pre (m : Mem) (d s n : Nat) : Prop where
  img : Img m
  rd : Ram d n
  rs : Ram s n
  disj : d + n ≤ s ∨ s + n ≤ d
  code_off : d + n ≤ memcpyBase ∨ memcpyBase + 4 * memcpyCode.length ≤ d

/-- The byte path (`94f8`), from nothing copied. -/
theorem small (ra : BitVec 64) (w : Abi) (outp : Array String) (m : Mem) (d s n : Nat)
    (hR : Room m d s n) (hra : ra.toNat % 4 = 0) :
    Triple (At 0x800094f8#64 (smL ra d s n) m w.keep outp) (Ret ra w outp m d s n) := by
  by_cases hn : n = 0
  · subst hn
    exact Triple.rmap (fun c h => ⟨m, h, Post.of_copied (Copied.zero m d s)⟩) (b0_step ra d s w outp m hR hra)
  · exact Triple.seq (Triple.rmap (fun c h => ⟨m, Copied.zero m d s, h⟩) (b1_step ra d s n w outp m hR (by omega)))
      (bytes ra w outp m d s n hR hra 0 (by omega))

/-- **newlib `memcpy(d, s, n)` on the machine.** From its entry with `a0 = d`,
`a1 = s`, `a2 = n`, the return address `ra` and the callee-saved registers
`w`, for any `n` and any alignment of `d` and `s`, the machine runs `memcpy`
to `ra`, keeping `w`, with `a0 = d`, the `n` bytes of `s` at `d`, and memory
unchanged elsewhere. -/
theorem correct (ra : BitVec 64) (w : Abi) (outp : Array String) (m : Mem) (d s n : Nat)
    (hra : ra.toNat % 4 = 0) (hP : Pre m d s n) :
    Triple (At entry (entL ra d s n) m w.keep outp) (Ret ra w outp m d s n) := by
  have hR : Room m d s n := ⟨hP.img.memcpy, hP.rd, hP.rs, hP.disj, by have := hP.code_off; rw [code_len] at this; omega⟩
  by_cases hal : s % 8 = d % 8
  · refine Triple.seq (a_step ra d s n w outp m hR hal) (Triple.seq (n8_step ra d s n w outp m hR) ?_)
    by_cases h8 : n < 8
    · simp only [h8, ↓reduceIte]
      exact Triple.seq (sb_step ra d s n w outp m hR) (small ra w outp m d s n hR hra)
    simp only [h8, ↓reduceIte]
    by_cases hd : d % 8 = 0
    · exact Triple.seq (Triple.rmap (fun c h => ⟨m, Copied.zero m d s, h⟩) (sg_step ra d s n w outp m hR hd))
        (gsel ra w outp m d s n 0 hR hra (by omega) (by omega))
    · exact Triple.seq (Triple.rmap (fun c h => ⟨0, ⟨by omega, by omega, by omega⟩, m, Copied.zero m d s, h⟩)
        (sh_step ra d s n w outp m hR hd)) (head ra w outp m d s n hR hra 4)
  · exact Triple.seq (x_step ra d s n w outp m hR hal) (small ra w outp m d s n hR hra)

/-! ## For the callers -/

/-- A word array copied: `k` words at `s` are at `d` when `4 k ≤ n`. -/
theorem Post.arr {m M : Mem} {d s n k : Nat} {f : Nat → Nat} (h : Post m d s n M)
    (ha : ArrAt m s k f) (hk : 4 * k ≤ n) : ArrAt M d k f := by
  intro j hj
  have e : ∀ i, i < 4 → M[d + 4 * j + i]? = some ((m[s + 4 * j + i]?).getD 0) := fun i hi => by
    rw [show d + 4 * j + i = d + (4 * j + i) by omega, show s + 4 * j + i = s + (4 * j + i) by omega]
    exact h.copy _ (by omega)
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
  have e3 := e 3 (by decide)
  simp only [Nat.add_zero] at e0
  rw [← ha j hj]
  simp only [bytesT4, e0, e1, e2, e3, Option.getD_some]

end Tom.Machine.Fn.Memcpy
