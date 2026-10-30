import Tom.Machine.Seg.Clamp
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Arith
import Tom.Machine.Kit.Loop
import Tom.Spec.Ops
import Tom.Spec.MpIntU
import Tom.Machine.Kit.Mem

/-!
# `mp_clamp` on the machine

`mp_clamp` at `0x80004fd8` in `c/tommath-arith.elf`:
```
4fd8 lw a5,0(a0); blez a5,500c          -- used
4fe0 ld a4,16(a0); slli a3,a5,2; add a4,a4,a3; j 4ff8
4ff0 sw a5,0(a0); beqz a5,5010          -- --used, stop at 0
4ff8 lw a3,-4(a4); addiw a5,a5,-1; addi a4,a4,-4; beqz a3,4ff0   -- loop head
5008 ret
500c bnez a5,5014
5010 sw zero,8(a0)                      -- sign := MP_ZPOS
5014 ret
```
At the loop head with counter `n` (`a5 = n`, `a4 = dp + 4n`), memory holds
`used = n`. The segments are `Tom.Machine.Seg.clamp*`.
-/


namespace Tom.Machine.Fn.Clamp

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

/-- Registers at the loop head with counter `n`. -/
def headL (ra : BitVec 64) (p dp n : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 p), (14, BitVec.ofNat 64 (dp + 4 * n)), (15, BitVec.ofNat 64 n)]

/-- `Ram` and `tohostAddr` as plain bounds, for `omega`. -/
theorem ram_bounds {lo len : Nat} (h : Ram lo len) :
    0x80000000 ≤ lo ∧ lo + len ≤ 0x100000000 ∧ (lo + len + 8 ≤ 0x80018880 ∨ 0x80018890 ≤ lo) :=
  ⟨h.lo_ge, h.hi_le, h.off⟩

/-- The loop's back edge: digit `k` is zero and `k ≥ 1`, so `used := k` is
stored and the loop goes on at counter `k`. -/
theorem body_step (ra : BitVec 64) (v : Abi) (outp : Array String) (p dp k : Nat) (M : Mem)
    (hc : CodeAt M mpClampBase mpClampCode) (hp : Ram p 24) (hpa : p % 8 = 0)
    (hd : Ram (dp + 4 * k) 4) (hcode : p + 24 ≤ mpClampBase ∨ mpClampBase + 64 ≤ p)
    (hk : 1 ≤ k) (hk' : k < 2 ^ 31) (hz : bytesT4 M (dp + 4 * k) = 0) :
    Triple (At 0x80004ff8#64 (headL ra p dp (k + 1)) M v.keep outp)
      (At 0x80004ff8#64 (headL ra p dp k) (writeLog M [(p, 4, BitVec.ofNat 64 k)]) v.keep outp) := by
  have ⟨hp1, hp2, hp3⟩ := ram_bounds hp
  have ⟨hd1, hd2, hd3⟩ := ram_bounds hd
  have hcb : mpClampBase = 0x80004fd8 := rfl
  have hcl : mpClampCode.length = 16 := rfl
  refine Triple.conseq (seg_at clampBody (pc1 := 0x80004ff8#64)
      (L1 := [(14, BitVec.ofNat 64 (dp + 4 * k)), (15, BitVec.ofNat 64 k), (13, 0#64), (1, ra),
        (10, BitVec.ofNat 64 p)])
      (lg := [(p, 4, BitVec.ofNat 64 k)]) [rd4 M (dp + 4 * k)] [1, 10, 14, 15] abiKeys ?_ ?_ ?_ ?_)
    (fun _ h => h) (fun _ h => h.weaken ?_)
  · tom_facts hc
    · leaf_nf [headL]
      have ha : (dp + 4 * (k + 1) + 18446744073709551612) % 18446744073709551616 = dp + 4 * k := by
        omega
      rw [ha]; simp only [tohostAddr]
      exact ⟨⟨by omega, by omega, by omega⟩, lpins4_rd4 _ _⟩
    · leaf_nf [headL]
      show (BitVec.signExtend 64 (bytesT4 M (dp + 4 * k)) == 0#64) = true
      rw [hz]; rfl
    · leaf_nf [headL]
      simp only [StoreWin, tohostAddr]
      omega
    · code_frame [headL]
    · leaf_nf [headL]
      rw [addiw_ofNat (k + 1) 18446744073709551615 k (by omega) (by omega)]
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      omega
  · seg_nf [clampBody]
  · seg_nf [clampBody, headL]
    refine ⟨?_, ?_, ?_⟩
    · rw [ofNat_add_ofNat]; exact ofNat_eq_ofNat (by omega)
    · simp only [Sail.BitVec.extractLsb]; exact addiw_ofNat _ _ _ (by omega) (by omega)
    · show BitVec.signExtend 64 (bytesT4 M (dp + 4 * k)) = 0#64
      rw [hz]; rfl
  · seg_nf [clampBody, headL]
    refine ⟨by omega, ?_⟩
    simp only [Sail.BitVec.extractLsb]; exact addiw_ofNat _ _ _ (by omega) (by omega)
  · intro q hq
    simp only [headL, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl <;> simp

/-- The loop's exit on a nonzero digit `k`: return with `used = k + 1`. -/
theorem exitNZ_step (ra : BitVec 64) (v : Abi) (outp : Array String) (p dp k d : Nat) (M : Mem)
    (hc : CodeAt M mpClampBase mpClampCode) (hra : ra.toNat % 4 = 0)
    (hd : Ram (dp + 4 * k) 4) (hk' : k < 2 ^ 31)
    (hdig : bytesT4 M (dp + 4 * k) = BitVec.ofNat 32 d) (hd0 : d ≠ 0) (hdl : d < 2 ^ 31) :
    Triple (At 0x80004ff8#64 (headL ra p dp (k + 1)) M v.keep outp)
      (At ra [(1, ra), (10, BitVec.ofNat 64 p)] M v.keep outp) := by
  have ⟨hd1, hd2, hd3⟩ := ram_bounds hd
  have hsub : ∀ q ∈ [(1, ra), (10, BitVec.ofNat 64 p)], q ∈ [(14, BitVec.ofNat 64 (dp + 4 * k)),
      (15, BitVec.ofNat 64 k), (13, BitVec.ofNat 64 d), (1, ra), (10, BitVec.ofNat 64 p)] := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl <;> simp
  refine Triple.conseq (seg_at clampExitNZ (pc1 := ra)
      (L1 := [(14, BitVec.ofNat 64 (dp + 4 * k)), (15, BitVec.ofNat 64 k), (13, BitVec.ofNat 64 d),
        (1, ra), (10, BitVec.ofNat 64 p)])
      (lg := []) [rd4 M (dp + 4 * k)] [1, 10, 14, 15] abiKeys ?_ ?_ ?_ ?_)
    (fun _ h => h) (fun _ h => h.weaken hsub)
  · tom_facts hc
    · leaf_nf [headL]
      have ha : (dp + 4 * (k + 1) + 18446744073709551612) % 18446744073709551616 = dp + 4 * k := by
        omega
      rw [ha]; simp only [tohostAddr]
      exact ⟨⟨by omega, by omega, by omega⟩, lpins4_rd4 _ _⟩
    · leaf_nf [headL]
      show (BitVec.signExtend 64 (bytesT4 M (dp + 4 * k)) == 0#64) = false
      rw [hdig, signExtend_ofNat32 _ hdl]
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      omega
    · leaf_nf [headL]
      rw [ret_target ra hra]; exact hra
  · seg_nf [clampExitNZ, headL]
    exact ret_target' ra hra
  · seg_nf [clampExitNZ, headL]
    refine ⟨?_, ?_, ?_⟩
    · rw [ofNat_add_ofNat]; exact ofNat_eq_ofNat (by omega)
    · simp only [Sail.BitVec.extractLsb]; exact addiw_ofNat _ _ _ (by omega) (by omega)
    · show BitVec.signExtend 64 (bytesT4 M (dp + 4 * k)) = _
      rw [hdig, signExtend_ofNat32 _ hdl]
  · seg_nf [clampExitNZ, headL]

/-- The loop's exit at counter `1` on a zero digit `0`: store `used := 0`,
then `sign := MP_ZPOS`, and return. -/
theorem exitZ_step (ra : BitVec 64) (v : Abi) (outp : Array String) (p dp : Nat) (M : Mem)
    (hc : CodeAt M mpClampBase mpClampCode) (hra : ra.toNat % 4 = 0)
    (hp : Ram p 24) (hpa : p % 8 = 0) (hd : Ram dp 4)
    (hcode : p + 24 ≤ mpClampBase ∨ mpClampBase + 64 ≤ p) (hz : bytesT4 M dp = 0) :
    Triple (At 0x80004ff8#64 (headL ra p dp 1) M v.keep outp)
      (At ra [(1, ra), (10, BitVec.ofNat 64 p)] (writeLog M [(p, 4, 0#64), (p + 8, 4, 0#64)])
        v.keep outp) := by
  have ⟨hp1, hp2, hp3⟩ := ram_bounds hp
  have ⟨hd1, hd2, hd3⟩ := ram_bounds hd
  have hcb : mpClampBase = 0x80004fd8 := rfl
  have hcl : mpClampCode.length = 16 := rfl
  refine Triple.conseq (seg_at clampExitZ (pc1 := ra)
      (L1 := [(14, BitVec.ofNat 64 dp), (15, 0#64), (13, 0#64), (1, ra), (10, BitVec.ofNat 64 p)])
      (lg := [(p, 4, 0#64), (p + 8, 4, 0#64)]) [rd4 M dp] [1, 10, 14, 15] abiKeys ?_ ?_ ?_ ?_)
    (fun _ h => h) (fun _ h => h.weaken (by simp))
  · tom_facts hc
    all_goals first | (code_frame [headL]; done) | skip
    · leaf_nf [headL]
      have ha : (dp + 4 * 1 + 18446744073709551612) % 18446744073709551616 = dp := by omega
      rw [ha]; simp only [tohostAddr]
      exact ⟨⟨by omega, by omega, by omega⟩, lpins4_rd4 _ _⟩
    · leaf_nf [headL]
      show (BitVec.signExtend 64 (bytesT4 M dp) == 0#64) = true
      rw [hz]; rfl
    · leaf_nf [headL]
      simp only [StoreWin, tohostAddr]
      omega
    · leaf_nf [headL]
      rfl
    · leaf_nf [headL]
      simp only [StoreWin, tohostAddr]
      omega
    · leaf_nf [headL]
      rw [ret_target ra hra]; exact hra
  · seg_nf [clampExitZ, headL]
    exact ret_target' ra hra
  · seg_nf [clampExitZ, headL]
    refine ⟨?_, rfl, ?_⟩
    · rw [ofNat_add_ofNat]; exact ofNat_eq_ofNat (by omega)
    · show BitVec.signExtend 64 (bytesT4 M dp) = 0#64
      rw [hz]; rfl
  · seg_nf [clampExitZ, headL]
    exact ⟨⟨by omega, rfl⟩, by omega⟩

/-- Entry with `used = 0`: store `sign := MP_ZPOS` and return. -/
theorem zero_step (ra : BitVec 64) (v : Abi) (outp : Array String) (p : Nat) (M : Mem)
    (hc : CodeAt M mpClampBase mpClampCode) (hra : ra.toNat % 4 = 0)
    (hp : Ram p 24) (hpa : p % 8 = 0)
    (hcode : p + 24 ≤ mpClampBase ∨ mpClampBase + 64 ≤ p) (hu : bytesT4 M p = BitVec.ofNat 32 0) :
    Triple (At 0x80004fd8#64 [(1, ra), (10, BitVec.ofNat 64 p)] M v.keep outp)
      (At ra [(1, ra), (10, BitVec.ofNat 64 p)] (writeLog M [(p + 8, 4, 0#64)]) v.keep outp) := by
  have ⟨hp1, hp2, hp3⟩ := ram_bounds hp
  have hcb : mpClampBase = 0x80004fd8 := rfl
  have hcl : mpClampCode.length = 16 := rfl
  have hv : BitVec.signExtend 64 (bytesT4 M p) = 0#64 := by rw [hu]; rfl
  refine Triple.conseq (seg_at clampZero (pc1 := ra)
      (L1 := [(15, 0#64), (1, ra), (10, BitVec.ofNat 64 p)])
      (lg := [(p + 8, 4, 0#64)]) [rd4 M p] [1, 10] abiKeys ?_ ?_ ?_ ?_)
    (fun _ h => h) (fun _ h => h.weaken (by simp))
  · tom_facts hc
    all_goals first | (code_frame []; done) | skip
    · leaf_nf []
      simp only [tohostAddr]
      exact ⟨⟨by omega, by omega, by omega⟩, lpins4_rd4_of (by omega)⟩
    · leaf_nf []
      show zopz0zKzJ_s 0#64 (BitVec.signExtend 64 (bytesT4 M p)) = true
      rw [hv]; rfl
    · leaf_nf []
      show (BitVec.signExtend 64 (bytesT4 M p) != 0#64) = false
      rw [hv]; rfl
    · leaf_nf []
      simp only [StoreWin, tohostAddr]
      omega
    · leaf_nf []
      rw [ret_target ra hra]; exact hra
  · seg_nf [clampZero]
    exact ret_target' ra hra
  · seg_nf [clampZero]
    exact hv
  · seg_nf [clampZero]
    omega

/-- Entry with `used = u ≥ 1`: load `dp`, go to the loop head at counter `u`. -/
theorem enter_step (ra : BitVec 64) (v : Abi) (outp : Array String) (p dp u : Nat) (M : Mem)
    (hc : CodeAt M mpClampBase mpClampCode) (hp : Ram p 24) (hpa : p % 8 = 0)
    (hu : bytesT4 M p = BitVec.ofNat 32 u) (hu1 : 1 ≤ u) (hu2 : u < 2 ^ 31)
    (hdp : bytesT8 M (p + 16) = BitVec.ofNat 64 dp) :
    Triple (At 0x80004fd8#64 [(1, ra), (10, BitVec.ofNat 64 p)] M v.keep outp)
      (At 0x80004ff8#64 (headL ra p dp u) M v.keep outp) := by
  have ⟨hp1, hp2, hp3⟩ := ram_bounds hp
  have hv : BitVec.signExtend 64 (bytesT4 M p) = BitVec.ofNat 64 u := by
    rw [hu, signExtend_ofNat32 _ hu2]
  refine Triple.conseq (seg_at clampEnter (pc1 := 0x80004ff8#64)
      (L1 := [(14, BitVec.ofNat 64 (dp + 4 * u)), (13, BitVec.ofNat 64 (4 * u)),
        (15, BitVec.ofNat 64 u), (1, ra), (10, BitVec.ofNat 64 p)])
      (lg := []) [rd4 M p, rd8 M (p + 16)] [1, 10] abiKeys ?_ ?_ ?_ ?_)
    (fun _ h => h) (fun _ h => h.weaken (by simp [headL]))
  · tom_facts hc
    all_goals first | (code_frame []; done) | skip
    · leaf_nf []
      simp only [tohostAddr]
      exact ⟨⟨by omega, by omega, by omega⟩, lpins4_rd4_of (by omega)⟩
    · leaf_nf []
      simp only [rd4_bytesD, hv]
      rw [bge_zero_ofNat u (by omega)]
      simp only [decide_eq_false_iff_not]; omega
    · leaf_nf []
      simp only [tohostAddr]
      exact ⟨⟨by omega, by omega, by omega⟩, lpins8_rd8_of (by omega)⟩
  · seg_nf [clampEnter]
  · seg_nf [clampEnter]
    simp only [rd4_bytes, rd8_bytes, hv, hdp]
    have hsh : Sail.BitVec.extractLsb (2#6) 5 0 = BitVec.ofNat 6 2 := by decide
    rw [hsh, shl_ofNat u 2 (by omega), ofNat_add_ofNat]
    exact ⟨ofNat_eq_ofNat (by omega), ofNat_eq_ofNat (by omega), trivial⟩
  · seg_nf [clampEnter]

/-! ## The function -/

/-- `mp_clamp`'s entry address. -/
abbrev entry : BitVec 64 := 0x80004fd8#64

/-- What `mp_clamp(a)` needs: `a` at `p` with its digits at `dp`, shaped,
the code in memory, and the struct off the code. -/
structure Pre (m : Mem) (p dp : Nat) (a : MpInt) : Prop where
  repr : MpAt m p dp a
  shape : a.Shape
  geom : MpGeom p dp a.alloc
  code : CodeAt m mpClampBase mpClampCode
  code_off : p + 24 ≤ mpClampBase ∨ mpClampBase + 64 ≤ p

/-- `Pre` with `a` only `ShapeU`: the code reads `dp[i]` for `i < used` only, so the digits at
and above `used` may be stale. -/
structure PreU (m : Mem) (p dp : Nat) (a : MpInt) : Prop where
  repr : MpAt m p dp a
  shape : a.ShapeU
  geom : MpGeom p dp a.alloc
  code : CodeAt m mpClampBase mpClampCode
  code_off : p + 24 ≤ mpClampBase ∨ mpClampBase + 64 ≤ p

theorem Pre.toU {m : Mem} {p dp : Nat} {a : MpInt} (h : Pre m p dp a) : PreU m p dp a :=
  ⟨h.repr, h.shape.toU, h.geom, h.code, h.code_off⟩

/-- What it leaves: `a'` at `p` with `ClampPost a a'`, the code, and memory
unchanged outside `used`/`alloc`/`sign`. -/
structure Post (m : Mem) (p dp : Nat) (a a' : MpInt) (M : Mem) : Prop where
  repr : MpAt M p dp a'
  clamp : ClampPost a a'
  code : CodeAt M mpClampBase mpClampCode
  frame : ∀ x, x < p ∨ p + 12 ≤ x → M[x]? = m[x]?

/-- The return state. -/
def Ret (ra : BitVec 64) (v : Abi) (outp : Array String) (m : Mem) (p dp : Nat) (a : MpInt)
    (c : Vsa.Machine.Config) : Prop :=
  ∃ a' M, At ra [(1, ra), (10, BitVec.ofNat 64 p)] M v.keep outp c ∧ Post m p dp a a' M

/-- The loop invariant at counter `n`: memory `M` holds `a` with `used = n`,
and the digits from `n` to `a.used` are zero. -/
structure Head (m : Mem) (p dp : Nat) (a : MpInt) (n : Nat) (M : Mem) : Prop where
  repr : MpAt M p dp { a with used := n }
  code : CodeAt M mpClampBase mpClampCode
  frame : ∀ x, x < p ∨ p + 4 ≤ x → M[x]? = m[x]?
  n_pos : 1 ≤ n
  n_le : n ≤ a.used
  zeros : ∀ i, n ≤ i → i < a.used → a.digit i = 0

theorem code_sw {M : Mem} {a : Nat} {v : BitVec 64} (h : CodeAt M mpClampBase mpClampCode)
    (ha : a + 4 ≤ mpClampBase ∨ mpClampBase + 64 ≤ a) :
    CodeAt (writeLog M [(a, 4, v)]) mpClampBase mpClampCode :=
  h.of_eq fun x h1 h2 => getElem?_sw_out M a x v (by
    have : mpClampCode.length = 16 := rfl
    simp only [this, show mpClampBase = 0x80004fd8 from rfl] at h1 h2 ha; omega)

theorem ram_sub {lo len : Nat} (h : Ram lo len) (off w : Nat) (hw : off + w ≤ len) :
    Ram (lo + off) w :=
  ⟨by have := h.lo_ge; omega, by have := h.hi_le; omega, by have := h.off; omega⟩

/-- The loop, from counter `j + 1` to the return. -/
theorem loop (ra : BitVec 64) (v : Abi) (outp : Array String) (p dp : Nat) (a : MpInt) (m : Mem)
    (hra : ra.toNat % 4 = 0) (hP : PreU m p dp a) :
    ∀ j, Triple (fun c => ∃ M, Head m p dp a (j + 1) M ∧
        At 0x80004ff8#64 (headL ra p dp (j + 1)) M v.keep outp c)
      (Ret ra v outp m p dp a) := by
  have hs := hP.shape
  have hg := hP.geom
  have ⟨hp1, hp2, hp3⟩ := ram_bounds hg.st
  have ⟨hd1, hd2, hd3⟩ := ram_bounds hg.ds
  simp only [Layout.sizeofMpInt, Layout.sizeofDigit] at hp2 hp3 hd2 hd3
  have hpa := hg.st_al
  have hal := hs.alloc_lt
  have hul := hs.used_le
  have hcode := hP.code_off
  have hdl : ∀ i, a.digit i < 2 ^ 31 := fun i => Nat.lt_trans (hs.digit_lt i) (by decide)
  -- the nonzero exit, at counter `k + 1`
  have exitNZ : ∀ k M, Head m p dp a (k + 1) M → a.digit k ≠ 0 →
      Triple (At 0x80004ff8#64 (headL ra p dp (k + 1)) M v.keep outp) (Ret ra v outp m p dp a) := by
    intro k M hH hk
    have hka : k < a.alloc := by have := hH.n_le; omega
    refine Triple.conseq (exitNZ_step ra v outp p dp k (a.digit k) M hH.code hra
      (ram_sub hg.ds (4 * k) 4 (by simp only [Layout.sizeofDigit]; omega)) (by omega)
      (hH.repr.digits k hka) hk (hdl k)) (fun _ h => h) (fun c h => ?_)
    have hcl : ClampPost a { a with used := k + 1 } :=
      { digits := rfl, alloc := rfl,
        used := (clampUsed_eq a.digit (k + 1) (Or.inr (by simpa using hk)) a.used hH.n_le
          hH.zeros).symm,
        sign := by simp }
    exact ⟨{ a with used := k + 1 }, M, h,
      { repr := hH.repr, clamp := hcl, code := hH.code,
        frame := fun x hx => hH.frame x (by omega) }⟩
  refine Triple.countdown (P := fun j c => ∃ M, Head m p dp a (j + 1) M ∧
      At 0x80004ff8#64 (headL ra p dp (j + 1)) M v.keep outp c) ?_ ?_
  · intro i
    refine Triple.exists_pre fun M => Triple.of_pure fun hH => ?_
    have hia : i + 1 < a.alloc := by have := hH.n_le; omega
    by_cases hz : a.digit (i + 1) = 0
    · have h0 : bytesT4 M (dp + 4 * (i + 1)) = 0 := by
        have h1 := hH.repr.digits (i + 1) hia
        rw [show Layout.sizeofDigit = 4 from rfl] at h1
        rw [h1]; show BitVec.ofNat 32 (a.digit (i + 1)) = 0; rw [hz]; rfl
      refine Triple.conseq (body_step ra v outp p dp (i + 1) M hH.code hg.st hpa
        (ram_sub hg.ds (4 * (i + 1)) 4 (by simp only [Layout.sizeofDigit]; omega)) hcode
        (by omega) (by omega) h0) (fun _ h => h) (fun c h => Or.inr ⟨_, ?_, h⟩)
      exact { repr := by simpa using hH.repr.set_used hg (i + 1) (by omega)
              code := code_sw hH.code (by omega)
              frame := fun x hx => by rw [getElem?_sw_out _ _ _ _ (by omega)]; exact hH.frame x hx
              n_pos := by omega
              n_le := by have := hH.n_le; omega
              zeros := fun x h1 h2 => by
                rcases Nat.lt_or_eq_of_le h1 with h1 | rfl
                · exact hH.zeros x (by omega) h2
                · exact hz }
    · exact Triple.conseq (exitNZ (i + 1) M hH hz) (fun _ h => h) (fun _ h => Or.inl h)
  · -- counter 1
    refine Triple.exists_pre fun M => Triple.of_pure fun hH => ?_
    by_cases hz : a.digit 0 = 0
    · -- exit at counter 1 on a zero digit 0: used := 0, sign := MP_ZPOS
      have hn := hH.n_le
      have h0 : bytesT4 M dp = 0 := by
        have h1 := hH.repr.digits 0 (by show 0 < a.alloc; omega)
        rw [show dp + Layout.sizeofDigit * 0 = dp by simp] at h1
        rw [h1]; show BitVec.ofNat 32 (a.digit 0) = 0; rw [hz]; rfl
      have hd0 : Ram dp 4 := by
        have := ram_sub hg.ds 0 4 (by simp only [Layout.sizeofDigit]; omega)
        simpa using this
      refine Triple.conseq (exitZ_step ra v outp p dp M hH.code hra hg.st hpa hd0 hcode h0)
        (fun _ h => h) (fun c h => ?_)
      have hlog : writeLog M [(p, 4, (0#64 : BitVec 64)), (p + 8, 4, 0#64)] =
          writeLog (writeLog M [(p, 4, BitVec.ofNat 64 0)]) [(p + 8, 4, BitVec.ofNat 64 0)] :=
        writeLog_append M [(p, 4, 0#64)] [(p + 8, 4, 0#64)]
      have hrep := (hH.repr.set_used hg 0 (by decide)).set_sign hg 0 (by decide)
      have hcl : ClampPost a { a with used := 0, sign := 0 } :=
        { digits := rfl, alloc := rfl,
          used := (clampUsed_eq a.digit 0 (Or.inl rfl) a.used (Nat.zero_le _)
            (fun i _ hi => by
              rcases Nat.eq_zero_or_pos i with rfl | hi0
              · exact hz
              · exact hH.zeros i (by omega) hi)).symm,
          sign := rfl }
      rw [hlog] at h
      refine ⟨{ a with used := 0, sign := 0 }, _, h,
        { repr := hrep, clamp := hcl, code := code_sw (code_sw hH.code (by omega)) (by omega),
          frame := fun x hx => ?_ }⟩
      rw [getElem?_sw_out _ _ _ _ (by omega), getElem?_sw_out _ _ _ _ (by omega)]
      exact hH.frame x (by omega)
    · exact exitNZ 0 M hH hz

/-- **`mp_clamp` on the machine.** From its entry with `a0 = p`, the return
address `ra` and the callee-saved registers `v`, the machine runs `mp_clamp`
to `ra`, keeping `v`, with `a'` at `p` such that `ClampPost a a'`
(`ClampPost.spec`: `a'` valid, `mag a' = mag a`), only `used`/`sign` written,
and the code intact. -/
theorem correctU (ra : BitVec 64) (v : Abi) (outp : Array String) (p dp : Nat) (a : MpInt)
    (m : Mem) (hra : ra.toNat % 4 = 0) (hP : PreU m p dp a) :
    Triple (At entry [(1, ra), (10, BitVec.ofNat 64 p)] m v.keep outp)
      (Ret ra v outp m p dp a) := by
  have hs := hP.shape
  have hg := hP.geom
  have ⟨hp1, hp2, hp3⟩ := ram_bounds hg.st
  have ⟨hd1, hd2, hd3⟩ := ram_bounds hg.ds
  simp only [Layout.sizeofMpInt, Layout.sizeofDigit] at hp2 hp3 hd2 hd3
  have hcode := hP.code_off
  have hu : bytesT4 m p = BitVec.ofNat 32 a.used := by simpa [Layout.offUsed] using hP.repr.used
  have hdp : bytesT8 m (p + 16) = BitVec.ofNat 64 dp := by simpa [Layout.offDp] using hP.repr.dpv
  by_cases h0 : a.used = 0
  · refine Triple.conseq (zero_step ra v outp p m hP.code hra hg.st hg.st_al hcode (h0 ▸ hu))
      (fun _ h => h) (fun c h => ?_)
    have hcl : ClampPost a { a with sign := 0 } :=
      { digits := rfl, alloc := rfl, used := by simp [h0, clampUsed], sign := by simp [h0]; rfl }
    exact ⟨{ a with sign := 0 }, _, h,
      { repr := hP.repr.set_sign hg 0 (by decide), clamp := hcl,
        code := code_sw hP.code (by omega),
        frame := fun x hx => getElem?_sw_out _ _ _ _ (by omega) }⟩
  · have hH : Head m p dp a (a.used - 1 + 1) m :=
      { repr := by rw [Nat.sub_add_cancel (by omega)]; exact hP.repr
        code := hP.code, frame := fun _ _ => rfl, n_pos := by omega, n_le := by omega,
        zeros := fun i h1 h2 => by omega }
    refine Triple.seq (enter_step ra v outp p dp a.used m hP.code hg.st hg.st_al hu (by omega)
      (by have := hs.alloc_lt; have := hs.used_le; omega) hdp) ?_
    refine Triple.conseq (loop ra v outp p dp a m hra hP (a.used - 1)) (fun c h => ⟨m, hH, ?_⟩)
      (fun _ h => h)
    rwa [Nat.sub_add_cancel (by omega)]

theorem correct (ra : BitVec 64) (v : Abi) (outp : Array String) (p dp : Nat) (a : MpInt)
    (m : Mem) (hra : ra.toNat % 4 = 0) (hP : Pre m p dp a) :
    Triple (At entry [(1, ra), (10, BitVec.ofNat 64 p)] m v.keep outp)
      (Ret ra v outp m p dp a) :=
  correctU ra v outp p dp a m hra hP.toU

/-- `mp_clamp` on the machine, against the specification: the returned
`mp_int` is valid and has the same magnitude (and so, by its sign, the same
value, `ClampPost.spec`). -/
theorem correct_spec (ra : BitVec 64) (v : Abi) (outp : Array String) (p dp : Nat) (a : MpInt)
    (m : Mem) (hra : ra.toNat % 4 = 0) (hP : Pre m p dp a)
    (hsign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg) :
    Triple (At entry [(1, ra), (10, BitVec.ofNat 64 p)] m v.keep outp)
      (fun c => ∃ a' M, At ra [(1, ra), (10, BitVec.ofNat 64 p)] M v.keep outp c ∧
        MpAt M p dp a' ∧ a'.Valid ∧ a'.mag = a.mag) :=
  Triple.conseq (correct ra v outp p dp a m hra hP) (fun _ h => h) fun _ ⟨a', M, hat, hpost⟩ =>
    ⟨a', M, hat, hpost.repr, (hpost.clamp.spec hP.shape hsign).1, (hpost.clamp.spec hP.shape hsign).2⟩

end Tom.Machine.Fn.Clamp
