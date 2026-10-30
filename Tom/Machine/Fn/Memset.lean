import Tom.Machine.Seg.Memset
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Bits
import Tom.Machine.Kit.Jalr
import Tom.Machine.Kit.Loop
import Tom.Machine.Kit.MemStore

/-!
# newlib `memset` on the machine

`memset` at `0x800093a4` in `c/tommath-arith.elf` (55 instructions, newlib's
`memset.S`; `experiments/disasm.txt`):
```
93a4 li t1,15; mv a4,a0; bgeu t1,a2,93e0      -- n ≤ 15: the tail
93b0 andi a5,a4,15; bnez a5,9454               -- d unaligned: the head
93b8 bnez a1,9434                              -- c ≠ 0: replicate
93bc andi a3,a2,-16; andi a2,a2,15; add a3,a3,a4
93c8 sd a1,0(a4); sd a1,8(a4); addi a4,a4,16; bltu a4,a3,93c8   -- 16-byte loop
93d8 bnez a2,93e0; ret
93e0 sub a3,t1,a2; slli a3,a3,2; auipc t0,0; add a3,a3,t0; jr 12(a3)   -- computed jump
93f4 sb a1,14(a4) … 942c sb a1,0(a4); 9430 ret                       -- the sb table
9434 zext.b a1,a1; a1 |= a1<<8; a1 |= a1<<16; a1 |= a1<<32; j 93bc
9454 slli a3,a5,2; auipc t0,0; add a3,a3,t0; mv t0,ra; jalr -104(a3)  -- head: table at 16 - r
9468 mv ra,t0; addi a5,a5,-16; sub a4,a4,a5; add a2,a2,a5; bgeu t1,a2,93e0; j 93b8
```
The segments are `Tom.Machine.Seg.memset*` (`experiments/segs/memset.json`).
The table is one chain per `sb` (`sb_step`) and `tab` composes them by
induction on the entry; the computed jumps are `jr`/`jalr` with symbolic
targets, closed by case analysis on the residual length (`jt_step`,
`head_call`). The linking `jalr` is `Kit/Jalr.lean`'s `jalr_at`. The table is
stated over `tabL` (`ra`, `a1`, `a4`) with the caller's other pins in `keep`
(`At.reshape`), so both callers use it. The loop is `Triple.countdown` with
`Head`; memory is `Kit/MemStore.lean`'s `Filled`.
-/


namespace Tom.Machine.Fn.Memset

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

/-- `Ram` and `tohostAddr` as plain bounds, for `omega`. -/
theorem ram_bounds {lo len : Nat} (h : Ram lo len) :
    0x80000000 ≤ lo ∧ lo + len ≤ 0x100000000 ∧ (lo + len + 8 ≤ 0x80018880 ∨ 0x80018890 ≤ lo) :=
  ⟨h.lo_ge, h.hi_le, h.off⟩

theorem ram_sub {lo len : Nat} (h : Ram lo len) (off w : Nat) (hw : off + w ≤ len) :
    Ram (lo + off) w :=
  ⟨by have := h.lo_ge; omega, by have := h.hi_le; omega, by have := h.off; omega⟩

/-- The code occupies `[memsetBase, memsetBase + 220)`. -/
theorem code_len : memsetCode.length = 55 := rfl

/-! ## The `sb` table -/

/-- Registers the table reads: `ra`, the fill value `a1`, the base `a4`. -/
def tabL (r v : BitVec 64) (x : Nat) : GRegs := [(1, r), (11, v), (14, BitVec.ofNat 64 x)]

/-- One table entry, as a `seg_at` (`sb_seg chain`). -/
local macro "sb_seg " c:ident : tactic => `(tactic|
  (refine seg_at $c (L1 := tabL _ _ _) [] [1, 11, 14] (keysG _) ?_ ?_ ?_ ?_ rfl rfl (by decide)
      (frameOK_nowrite _ _ rfl (by assumption)) (by decide)
   · tom_facts (by assumption : CodeAt _ memsetBase memsetCode)
     leaf_nf [tabL]
     simp only [StoreWin, tohostAddr] at *
     omega
   · rfl
   · seg_nf [$c:ident, tabL]
   · seg_nf [$c:ident, tabL]
     omega))

/-- One table entry: `sb a1, j(a4)` at `0x8000942c - 4 j`. -/
theorem sb_step (j : Nat) (hj : j < 15) (r v : BitVec 64) (x : Nat) (E : GRegs)
    (outp : Array String) (M : Mem) (hc : CodeAt M memsetBase memsetCode) (hx : Ram (x + j) 1)
    (hE : KeysOK (keysG E)) :
    Triple (At (BitVec.ofNat 64 (0x8000942c - 4 * j)) (tabL r v x) M E outp)
      (At (BitVec.ofNat 64 (0x80009430 - 4 * j)) (tabL r v x) (writeLog M [(x + j, 1, v)]) E
        outp) := by
  have ⟨h1, h2, h3⟩ := ram_bounds hx
  match j, hj with
  | 0, _ => sb_seg memsetSb0
  | 1, _ => sb_seg memsetSb1
  | 2, _ => sb_seg memsetSb2
  | 3, _ => sb_seg memsetSb3
  | 4, _ => sb_seg memsetSb4
  | 5, _ => sb_seg memsetSb5
  | 6, _ => sb_seg memsetSb6
  | 7, _ => sb_seg memsetSb7
  | 8, _ => sb_seg memsetSb8
  | 9, _ => sb_seg memsetSb9
  | 10, _ => sb_seg memsetSb10
  | 11, _ => sb_seg memsetSb11
  | 12, _ => sb_seg memsetSb12
  | 13, _ => sb_seg memsetSb13
  | 14, _ => sb_seg memsetSb14

/-- The table's `ret`. -/
theorem ret_step (r v : BitVec 64) (x : Nat) (E : GRegs) (outp : Array String) (M : Mem)
    (hc : CodeAt M memsetBase memsetCode) (hr : r.toNat % 4 = 0) (hE : KeysOK (keysG E)) :
    Triple (At 0x80009430#64 (tabL r v x) M E outp) (At r (tabL r v x) M E outp) := by
  refine seg_at memsetRet (L1 := tabL r v x) (lg := []) [] [1, 11, 14] (keysG E) ?_ ?_ ?_ ?_
    rfl rfl (by decide) (frameOK_nowrite _ _ rfl hE) (by decide)
  · tom_facts hc
    leaf_nf [tabL]
    rw [ret_target r hr]; exact hr
  · seg_nf [memsetRet, tabL]
    exact ret_target' r hr
  · seg_nf [memsetRet, tabL]
  · seg_nf [memsetRet, tabL]

/-- **The table from entry `k`**: bytes `k - 1` down to `0` of `[x, x + k)`,
then `ret` to `r`. -/
theorem tab (r v : BitVec 64) (x : Nat) (E : GRegs) (outp : Array String)
    (hr : r.toNat % 4 = 0) (hE : KeysOK (keysG E)) :
    ∀ (k : Nat) (M : Mem), k ≤ 15 → CodeAt M memsetBase memsetCode → Ram x k →
      (x + k ≤ memsetBase ∨ memsetBase + 220 ≤ x) →
      Triple (At (BitVec.ofNat 64 (0x80009430 - 4 * k)) (tabL r v x) M E outp)
        (At r (tabL r v x) (writeLog M (sbLog x v k)) E outp)
  | 0, M, _, hc, _, _ => ret_step r v x E outp M hc hr hE
  | k + 1, M, hk, hc, hx, hoff => by
    have hc' : CodeAt (writeLog M [(x + k, 1, v)]) memsetBase memsetCode :=
      hc.writeLog fun a h1 h2 => by
        show (a < x + k ∨ x + k + 1 ≤ a) ∧ True
        rw [code_len] at h2
        exact ⟨by omega, trivial⟩
    have hpc : 0x80009430 - 4 * (k + 1) = 0x8000942c - 4 * k := by omega
    rw [hpc]
    exact Triple.seq (sb_step k (by omega) r v x E outp M hc (ram_sub hx k 1 (by omega)) hE)
      (tab r v x E outp hr hE k _ (by omega) hc' ⟨hx.lo_ge, by have := hx.hi_le; omega, by have := hx.off; omega⟩ (by omega))

/-! ## The computed jump into the table (`n ≤ 15` bytes left) -/

/-- Registers at `0x800093e0` with `k` bytes left at `x`. -/
def jtL (ra : BitVec 64) (d : Nat) (v : BitVec 64) (k x : Nat) : GRegs :=
  [(1, ra), (6, 15#64), (10, BitVec.ofNat 64 d), (11, v), (12, BitVec.ofNat 64 k),
   (14, BitVec.ofNat 64 x)]

/-- `a3 := (15 - k) << 2; t0 := auipc; jr 12(a3 + t0)`: the table entry for `k`. -/
theorem jt_step (ra : BitVec 64) (d : Nat) (v : BitVec 64) (k x : Nat) (w : Abi)
    (outp : Array String) (M : Mem) (hc : CodeAt M memsetBase memsetCode) (hk : k ≤ 15) :
    Triple (At 0x800093e0#64 (jtL ra d v k x) M w.keep outp)
      (At (BitVec.ofNat 64 (0x80009430 - 4 * k)) (tabL ra v x) M
        ((10, BitVec.ofNat 64 d) :: w.keep) outp) := by
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
      k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  refine Triple.conseq (seg_at memsetJt (pc1 := BitVec.ofNat 64 (0x80009430 - 4 * k)) (lg := [])
      [] [1, 6, 10, 11, 12, 14] abiKeys ?_ ?_ rfl ?_) (fun _ h => h) (fun _ h => h.reshape ?_ ?_)
  · tom_facts hc
    leaf_nf [jtL]
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> decide
  · seg_nf [memsetJt, jtL]
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> decide
  · seg_nf [memsetJt, jtL]
  · intro p hp
    simp only [tabL, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> seg_nf [memsetJt, jtL]
  · intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · seg_nf [memsetJt, jtL]
    · exact List.mem_append_right _ hp

/-- **The tail**: `k ≤ 15` bytes at `x` by the computed jump into the table,
then `ret`. -/
theorem tail (ra : BitVec 64) (d : Nat) (v : BitVec 64) (k x : Nat) (w : Abi)
    (outp : Array String) (M : Mem) (hra : ra.toNat % 4 = 0) (hc : CodeAt M memsetBase memsetCode)
    (hk : k ≤ 15) (hx : Ram x k) (hoff : x + k ≤ memsetBase ∨ memsetBase + 220 ≤ x) :
    Triple (At 0x800093e0#64 (jtL ra d v k x) M w.keep outp)
      (At ra [(1, ra), (10, BitVec.ofNat 64 d)] (writeLog M (sbLog x v k)) w.keep outp) :=
  Triple.seq (jt_step ra d v k x w outp M hc hk)
    (Triple.conseq (tab ra v x ((10, BitVec.ofNat 64 d) :: w.keep) outp hra
        (show KeysOK (10 :: abiKeys) by decide) k M hk hc hx hoff)
      (fun _ h => h)
      (fun _ h => h.reshape (by simp [tabL]) (fun p hp =>
        List.mem_append_right _ (List.mem_cons_of_mem _ hp))))

/-! ## The 16-byte loop -/

/-- Registers at the loop head `0x800093c8`: `a4 = x` up to `a3 = e`, `k` bytes
after `e`. -/
def loopL (ra : BitVec 64) (d : Nat) (v : BitVec 64) (k e x : Nat) : GRegs :=
  [(14, BitVec.ofNat 64 x), (13, BitVec.ofNat 64 e), (12, BitVec.ofNat 64 k), (11, v),
   (6, 15#64), (1, ra), (10, BitVec.ofNat 64 d)]

/-- One iteration that comes back: `sd a1, 0(a4); sd a1, 8(a4); a4 += 16`,
`a4 < a3`. -/
theorem body_step (ra : BitVec 64) (d : Nat) (v : BitVec 64) (k e x : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hc : CodeAt M memsetBase memsetCode) (hx : Ram x 16) (hxa : x % 8 = 0)
    (hoff : x + 16 ≤ memsetBase ∨ memsetBase + 220 ≤ x) (hlt : x + 16 < e) (he : e ≤ 2 ^ 32) :
    Triple (At 0x800093c8#64 (loopL ra d v k e x) M w.keep outp)
      (At 0x800093c8#64 (loopL ra d v k e (x + 16)) (writeLog M [(x, 8, v), (x + 8, 8, v)])
        w.keep outp) := by
  have ⟨h1, h2, h3⟩ := ram_bounds hx
  have hcb : memsetBase = 0x800093a4 := rfl
  have hcl := code_len
  refine seg_at memsetLoop (L1 := loopL ra d v k e (x + 16)) [] [14, 13, 12, 11, 6, 1, 10] abiKeys
    ?_ ?_ ?_ ?_
  · tom_facts hc
    all_goals first | (code_frame [loopL]; done) | skip
    all_goals first | (leaf_nf [loopL]; simp only [StoreWin, tohostAddr] at h3 ⊢; omega) | skip
    · leaf_nf [loopL]
      rw [ofNat_add_ofNat, ltu_ofNat _ _ (by omega) (by omega)]
      simp only [decide_eq_true_eq]; omega
  · seg_nf [memsetLoop]
  · seg_nf [memsetLoop, loopL]
    rw [ofNat_add_ofNat]
  · seg_nf [memsetLoop, loopL]
    omega

/-- The last iteration, `k ≠ 0` bytes left: on to the computed jump. -/
theorem exitT_step (ra : BitVec 64) (d : Nat) (v : BitVec 64) (k x : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hc : CodeAt M memsetBase memsetCode) (hx : Ram x 16) (hxa : x % 8 = 0)
    (hoff : x + 16 ≤ memsetBase ∨ memsetBase + 220 ≤ x) (hk : k ≠ 0) (hk' : k < 16) :
    Triple (At 0x800093c8#64 (loopL ra d v k (x + 16) x) M w.keep outp)
      (At 0x800093e0#64 (jtL ra d v k (x + 16)) (writeLog M [(x, 8, v), (x + 8, 8, v)])
        w.keep outp) := by
  have ⟨h1, h2, h3⟩ := ram_bounds hx
  have hcb : memsetBase = 0x800093a4 := rfl
  have hcl := code_len
  refine Triple.conseq (seg_at memsetLoopExitT (L1 := loopL ra d v k (x + 16) (x + 16)) []
    [14, 13, 12, 11, 6, 1, 10] abiKeys ?_ ?_ ?_ ?_) (fun _ h => h)
    (fun _ h => h.weaken (by simp [jtL, loopL]))
  · tom_facts hc
    all_goals first | (code_frame [loopL]; done) | skip
    all_goals first | (leaf_nf [loopL]; simp only [StoreWin, tohostAddr] at h3 ⊢; omega) | skip
    · leaf_nf [loopL]
      rw [ofNat_add_ofNat, ltu_ofNat _ _ (by omega) (by omega)]
      simp
    · leaf_nf [loopL]
      rw [bne_zero_ofNat _ (by omega)]
      simpa using hk
  · seg_nf [memsetLoopExitT]
  · seg_nf [memsetLoopExitT, loopL]
    rw [ofNat_add_ofNat]
  · seg_nf [memsetLoopExitT, loopL]
    omega

/-- The last iteration with no bytes left: return. -/
theorem exitR_step (ra : BitVec 64) (d : Nat) (v : BitVec 64) (x : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hc : CodeAt M memsetBase memsetCode) (hra : ra.toNat % 4 = 0) (hx : Ram x 16)
    (hxa : x % 8 = 0) (hoff : x + 16 ≤ memsetBase ∨ memsetBase + 220 ≤ x) :
    Triple (At 0x800093c8#64 (loopL ra d v 0 (x + 16) x) M w.keep outp)
      (At ra [(1, ra), (10, BitVec.ofNat 64 d)] (writeLog M [(x, 8, v), (x + 8, 8, v)])
        w.keep outp) := by
  have ⟨h1, h2, h3⟩ := ram_bounds hx
  have hcb : memsetBase = 0x800093a4 := rfl
  have hcl := code_len
  refine Triple.conseq (seg_at memsetLoopExitR (L1 := loopL ra d v 0 (x + 16) (x + 16)) []
    [14, 13, 12, 11, 6, 1, 10] abiKeys ?_ ?_ ?_ ?_) (fun _ h => h)
    (fun _ h => h.weaken (by simp [loopL]))
  · tom_facts hc
    all_goals first | (code_frame [loopL]; done) | skip
    all_goals first | (leaf_nf [loopL]; simp only [StoreWin, tohostAddr] at h3 ⊢; omega) | skip
    · leaf_nf [loopL]
      rw [ofNat_add_ofNat, ltu_ofNat _ _ (by omega) (by omega)]
      simp
    · leaf_nf [loopL]
      rfl
    · leaf_nf [loopL]
      rw [ret_target ra hra]; exact hra
  · seg_nf [memsetLoopExitR, loopL]
    exact ret_target' ra hra
  · seg_nf [memsetLoopExitR, loopL]
    rw [ofNat_add_ofNat]
  · seg_nf [memsetLoopExitR, loopL]
    omega

/-! ## Contract -/

/-- `memset`'s entry address. -/
abbrev entry : BitVec 64 := 0x800093a4#64

/-- The memory part of what `memset` needs: the code in memory, `[d, d + n)`
RAM off the code. -/
structure Room (m : Mem) (d n : Nat) : Prop where
  code : CodeAt m memsetBase memsetCode
  ram : Ram d n
  code_off : d + n ≤ memsetBase ∨ memsetBase + 4 * memsetCode.length ≤ d

/-- What it leaves: `[d, d + n)` filled with `b`, memory unchanged elsewhere,
the code. -/
structure Post (m : Mem) (d n : Nat) (b : BitVec 8) (M : Mem) : Prop where
  fill : ∀ i, i < n → M[d + i]? = some b
  frame : ∀ x, x < d ∨ d + n ≤ x → M[x]? = m[x]?
  code : CodeAt M memsetBase memsetCode

/-- The return state: `a0 = d`. -/
def Ret (ra : BitVec 64) (w : Abi) (outp : Array String) (m : Mem) (d n : Nat) (b : BitVec 8)
    (c : Vsa.Machine.Config) : Prop :=
  ∃ M, At ra [(1, ra), (10, BitVec.ofNat 64 d)] M w.keep outp c ∧ Post m d n b M

theorem Post.of_filled {m M : Mem} {d n : Nat} {b : BitVec 8} (hP : Room m d n)
    (h : Filled m M d (d + n) b) : Post m d n b M :=
  { fill := fun i hi => h.fill (d + i) (by omega) (by omega)
    frame := fun x hx => h.frame x hx
    code := h.code hP.code (by have := hP.code_off; omega) }

/-- The tail from `x`, `[d, x)` zero already, `x + k = d + n`. -/
theorem finish_tail (ra : BitVec 64) (w : Abi) (outp : Array String) (m M : Mem) (d n k x : Nat)
    (v : BitVec 64) (b : BitVec 8) (hb : sbData v = b)
    (hra : ra.toNat % 4 = 0) (hP : Room m d n) (hF : Filled m M d x b) (hdx : d ≤ x)
    (hk : k ≤ 15) (hxk : x + k = d + n) :
    Triple (At 0x800093e0#64 (jtL ra d v k x) M w.keep outp) (Ret ra w outp m d n b) := by
  have hr := hP.ram
  have hoff := hP.code_off
  have hcl := code_len
  have hcb : memsetBase = 0x800093a4 := rfl
  refine Triple.conseq (tail ra d v k x w outp M hra (hF.code hP.code (by omega)) hk
    ⟨by have := hr.lo_ge; omega, by have := hr.hi_le; omega, by have := hr.off; omega⟩
    (by omega)) (fun _ h => h) (fun c h => ⟨_, h, Post.of_filled hP ?_⟩)
  rw [← hxk]
  exact hF.sb hdx hb k

/-- The loop invariant at the head with `j + 1` iterations to go before `e`. -/
structure Head (m M : Mem) (d e j : Nat) (b : BitVec 8) : Prop where
  room : d + 16 * (j + 1) ≤ e
  fill : Filled m M d (e - 16 * (j + 1)) b

/-- **The loop**, from `j + 1` iterations before `e` (`e ≡ 0 mod 16`, `k ≤ 15`
bytes after it, `e + k = d + n`). -/
theorem loop (ra : BitVec 64) (w : Abi) (outp : Array String) (m : Mem) (d n k e : Nat)
    (v : BitVec 64) (b : BitVec 8) (hv : SdFill v b) (hb : sbData v = b)
    (hra : ra.toNat % 4 = 0) (hP : Room m d n) (hk : k ≤ 15) (hek : e + k = d + n)
    (he : e % 16 = 0) :
    ∀ j, Triple (fun c => ∃ M, Head m M d e j b ∧
        At 0x800093c8#64 (loopL ra d v k e (e - 16 * (j + 1))) M w.keep outp c)
      (Ret ra w outp m d n b) := by
  have hr := hP.ram
  have ⟨h1, h2, h3⟩ := ram_bounds hr
  have hoff := hP.code_off
  have hcl := code_len
  have hcb : memsetBase = 0x800093a4 := rfl
  refine Triple.countdown ?_ ?_
  · intro i
    refine Triple.exists_pre fun M => Triple.of_pure fun hH => ?_
    have hH1 := hH.room
    refine Triple.conseq (body_step ra d v k e (e - 16 * (i + 1 + 1)) w outp M
        (hH.fill.code hP.code (by omega)) (ram_sub hr (e - 16 * (i + 1 + 1) - d) 16 (by omega) |>
          fun h => by rwa [show d + (e - 16 * (i + 1 + 1) - d) = e - 16 * (i + 1 + 1) by omega] at h)
        (by omega) (by omega) (by omega) (by omega)) (fun _ h => h) (fun c h => Or.inr ⟨writeLog M [(e - 16 * (i + 1 + 1), 8, v),
          (e - 16 * (i + 1 + 1) + 8, 8, v)], ?_, ?_⟩)
    · exact { room := by omega
              fill := by
                have := hH.fill.sd2 (by omega) hv
                rwa [show e - 16 * (i + 1 + 1) + 16 = e - 16 * (i + 1) by omega] at this }
    · rwa [show e - 16 * (i + 1 + 1) + 16 = e - 16 * (i + 1) by omega] at h
  · refine Triple.exists_pre fun M => Triple.of_pure fun hH => ?_
    have hH1 := hH.room
    obtain ⟨x, hx⟩ : ∃ x, x + 16 = e := ⟨e - 16, by omega⟩
    subst hx
    have hx16 : Ram x 16 := by
      have := ram_sub hr (x - d) 16 (by omega)
      rwa [show d + (x - d) = x by omega] at this
    have hF : Filled m (writeLog M [(x, 8, v), (x + 8, 8, v)]) d (x + 16) b :=
      (show Filled m M d x b by simpa using hH.fill).sd2 (by omega) hv
    have hcM := hH.fill.code hP.code (by omega)
    rw [show x + 16 - 16 * (0 + 1) = x by omega]
    by_cases hk0 : k = 0
    · subst hk0
      refine Triple.conseq (exitR_step ra d v x w outp M hcM hra hx16 (by omega) (by omega))
        (fun _ h => h) (fun c h => ⟨_, h, Post.of_filled hP ?_⟩)
      rwa [show x + 16 = d + n by omega] at hF
    · exact Triple.seq (exitT_step ra d v k x w outp M hcM hx16 (by omega) (by omega) hk0 (by omega))
        (finish_tail ra w outp m _ d n k (x + 16) v b hb hra hP hF (by omega) hk (by omega))

/-! ## The entry -/

/-- Registers at the entry: `ra`, `a0 = d`, `a1 = v`, `a2 = n`. -/
def entryL (ra : BitVec 64) (d : Nat) (v : BitVec 64) (n : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 d), (11, v), (12, BitVec.ofNat 64 n)]

theorem li15 : (0#64 + 15#64 : BitVec 64) = BitVec.ofNat 64 15 := rfl

/-- `n ≤ 15`: straight to the computed jump. -/
theorem small_step (ra : BitVec 64) (d : Nat) (v : BitVec 64) (n : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hc : CodeAt M memsetBase memsetCode) (hn : n ≤ 15) :
    Triple (At entry (entryL ra d v n) M w.keep outp)
      (At 0x800093e0#64 (jtL ra d v n d) M w.keep outp) := by
  refine Triple.conseq (seg_at memsetEnterSmall
    (L1 := [(14, BitVec.ofNat 64 d), (6, 15#64), (1, ra), (10, BitVec.ofNat 64 d), (11, v),
      (12, BitVec.ofNat 64 n)]) (lg := []) [] [1, 10, 11, 12] abiKeys ?_ ?_ ?_ ?_) (fun _ h => h)
    (fun _ h => h.weaken (by simp [jtL]))
  · tom_facts hc
    leaf_nf [entryL]
    rw [li15, geu_ofNat _ _ (by omega) (by omega)]
    simpa using hn
  · seg_nf [memsetEnterSmall]
  · seg_nf [memsetEnterSmall, entryL]
  · seg_nf [memsetEnterSmall]

/-- `n ≥ 16`, `d ≡ 0 mod 16`: to the loop head. -/
theorem al_step (ra : BitVec 64) (d n : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hc : CodeAt M memsetBase memsetCode) (hn : 16 ≤ n) (hn' : d + n < 2 ^ 64) (hd : d % 16 = 0) :
    Triple (At entry (entryL ra d 0#64 n) M w.keep outp)
      (At 0x800093c8#64 (loopL ra d 0#64 (n % 16) (n - n % 16 + d) d) M w.keep outp) := by
  refine Triple.conseq (seg_at memsetEnterAl
    (L1 := [(13, BitVec.ofNat 64 (n - n % 16 + d)), (12, BitVec.ofNat 64 (n % 16)),
      (15, BitVec.ofNat 64 (d % 16)), (14, BitVec.ofNat 64 d), (6, 15#64), (1, ra),
      (10, BitVec.ofNat 64 d), (11, 0#64)]) (lg := []) [] [1, 10, 11, 12] abiKeys ?_ ?_ ?_ ?_)
    (fun _ h => h) (fun _ h => h.weaken (by simp [loopL]))
  · tom_facts hc
    · leaf_nf [entryL]
      rw [li15, geu_ofNat _ _ (by omega) (by omega)]
      simp; omega
    · leaf_nf [entryL]
      rw [BitVec.add_zero, and15_ofNat, bne_zero_ofNat _ (by omega)]
      simpa using hd
    · leaf_nf [entryL]
      rfl
  · seg_nf [memsetEnterAl, Vsa.Sim.endPCM]
  · seg_nf [memsetEnterAl, entryL]
    rw [andm16_ofNat, and15_ofNat, and15_ofNat, ofNat_add_ofNat]
    exact ⟨ofNat_eq_ofNat (by omega), rfl, rfl⟩
  · seg_nf [memsetEnterAl]

/-- Registers at the head-alignment call `0x80009464`, `r = d mod 16 ≠ 0`. -/
def unL (ra : BitVec 64) (d : Nat) (v : BitVec 64) (n r : Nat) : GRegs :=
  [(5, ra), (13, BitVec.ofNat 64 (4 * r + 0x80009458)), (15, BitVec.ofNat 64 r),
   (14, BitVec.ofNat 64 d), (6, 15#64), (1, ra), (10, BitVec.ofNat 64 d), (11, v),
   (12, BitVec.ofNat 64 n)]

/-- `n ≥ 16`, `d ≢ 0 mod 16`: set up the call into the table. -/
theorem un_step (ra : BitVec 64) (d : Nat) (v : BitVec 64) (n r : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hc : CodeAt M memsetBase memsetCode) (hn : 16 ≤ n) (hn' : d + n < 2 ^ 64)
    (hr : d % 16 = r) (hr0 : r ≠ 0) :
    Triple (At entry (entryL ra d v n) M w.keep outp)
      (At 0x80009464#64 (unL ra d v n r) M w.keep outp) := by
  subst hr
  refine seg_at memsetEnterUn (L1 := unL ra d v n (d % 16)) (lg := []) [] [1, 10, 11, 12] abiKeys
    ?_ ?_ ?_ ?_
  · tom_facts hc
    · leaf_nf [entryL]
      rw [li15, geu_ofNat _ _ (by omega) (by omega)]
      simp; omega
    · leaf_nf [entryL]
      rw [BitVec.add_zero, and15_ofNat, bne_zero_ofNat _ (by omega)]
      simpa using hr0
  · seg_nf [memsetEnterUn, Vsa.Sim.endPCM]
  · seg_nf [memsetEnterUn, entryL, unL]
    have hsh : Sail.BitVec.extractLsb (2#6) 5 0 = BitVec.ofNat 6 2 := by decide
    rw [and15_ofNat, hsh, shl_ofNat _ 2 (by omega)]
    simp only [imm20Of, BitVec.reduceExtractLsb', BitVec.reduceAppend, BitVec.reduceSignExtend,
      BitVec.add_zero]
    rw [ofNat_add_ofNat]
    exact ⟨ofNat_eq_ofNat (by omega), trivial⟩
  · seg_nf [memsetEnterUn]

/-- Registers back from the table at `0x80009468` (`ra` the link, `t0` the
caller's `ra`). -/
def hrL (ra : BitVec 64) (d : Nat) (v : BitVec 64) (n r : Nat) : GRegs :=
  [(1, 0x80009468#64), (5, ra), (6, 15#64), (10, BitVec.ofNat 64 d), (11, v),
   (12, BitVec.ofNat 64 n), (14, BitVec.ofNat 64 d), (15, BitVec.ofNat 64 r)]

theorem keysG_append : ∀ (A B : GRegs), keysG (A ++ B) = keysG A ++ keysG B
  | [], _ => rfl
  | (n, _) :: A, B => congrArg (n :: ·) (keysG_append A B)

theorem sub_app {A B K : GRegs} (h : ∀ p ∈ B, p ∈ A ++ K) : ∀ p ∈ B ++ K, p ∈ A ++ K :=
  fun p hp => (List.mem_append.1 hp).elim (h p) (List.mem_append_right _)

/-- `jalr -104(a3)` into the table at entry `16 - r`: bytes `[d, d + 16 - r)`,
back at `0x80009468`. -/
theorem head_call (ra : BitVec 64) (d : Nat) (v : BitVec 64) (n r : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hc : CodeAt M memsetBase memsetCode) (hr1 : 1 ≤ r) (hr15 : r ≤ 15) (hx : Ram d (16 - r))
    (hoff : d + (16 - r) ≤ memsetBase ∨ memsetBase + 220 ≤ d) :
    Triple (At 0x80009464#64 (unL ra d v n r) M w.keep outp)
      (At 0x80009468#64 (hrL ra d v n r) (writeLog M (sbLog d v (16 - r))) w.keep outp) := by
  have htgt : Sail.BitVec.update (srcVal 13 (unL ra d v n r) + sign_extend (m := 64) (0xf98#12)) 0 0#1
      = BitVec.ofNat 64 (0x80009430 - 4 * (16 - r)) := by
    simp only [srcVal, lookupG, unL, ↓reduceIte, Nat.reduceEqDiff, Option.getD_some]
    have hcase : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨
        r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> decide
  have hlink : Sail.BitVec.addInt (0x80009464#64 : BitVec 64) 4 = 0x80009468#64 := by decide
  have hw := hc.word (a := (0x80009464#64 : BitVec 64).toNat) (w := 0xf98680e7#32) (by decide)
  have hk : keysG ([(5, ra), (6, 15#64), (10, BitVec.ofNat 64 d), (12, BitVec.ofNat 64 n),
      (15, BitVec.ofNat 64 r)] ++ w.keep) = [5, 6, 10, 12, 15] ++ abiKeys := by
    rw [keysG_append]; rfl
  refine Triple.seq (Triple.conseq (jalr_at (L := unL ra d v n r) (m := M) (keep := w.keep)
      (outp := outp) (L' := [(5, ra), (13, BitVec.ofNat 64 (4 * r + 0x80009458)),
      (15, BitVec.ofNat 64 r), (14, BitVec.ofNat 64 d), (6, 15#64), (10, BitVec.ofNat 64 d),
      (11, v), (12, BitVec.ofNat 64 n)]) (rs1 := 13) (imm := 0xf98#12) hw (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3) (by decide) (by simp [unL, keysG]) (by omega)
      (by rw [htgt]; simp only [BitVec.toNat_ofNat]; omega) (by simp [unL])
      (show ∀ n ∈ [5, 13, 15, 14, 6, 10, 11, 12], 2 ≤ n ∧ n ≤ 31 by decide)
      (show ∀ n ∈ abiKeys, 2 ≤ n ∧ n ≤ 31 by decide))
    (fun _ h => h) (fun c h => ?_))
    (Triple.conseq (tab 0x80009468#64 v d ([(5, ra), (6, 15#64), (10, BitVec.ofNat 64 d),
        (12, BitVec.ofNat 64 n), (15, BitVec.ofNat 64 r)] ++ w.keep) outp (by decide)
        (hk ▸ (by decide : KeysOK ([5, 6, 10, 12, 15] ++ abiKeys))) (16 - r) M (by omega) hc hx hoff)
      (fun _ h => h) (fun _ h => h.reshape (by simp [hrL, tabL])
        (fun p hp => List.mem_append_right _ (List.mem_append_right _ hp))))
  rw [htgt, hlink] at h
  exact h.reshape (by simp [tabL]) (sub_app (by simp))

theorem addneg_ofNat (n r : Nat) (h : 16 ≤ n + r) :
    BitVec.ofNat 64 n + (BitVec.ofNat 64 r + 18446744073709551600#64) =
      BitVec.ofNat 64 (n + r - 16) := by
  rw [ofNat_add_ofNat, ofNat_add_ofNat]
  exact ofNat_eq_ofNat (by omega)

theorem subneg_ofNat (d r : Nat) (hr : r ≤ 16) (hd : d + 16 < 2 ^ 64) :
    BitVec.ofNat 64 d - (BitVec.ofNat 64 r + 18446744073709551600#64) =
      BitVec.ofNat 64 (d + 16 - r) := by
  rw [ofNat_add_ofNat, BitVec.sub_eq_iff_eq_add, ofNat_add_ofNat]
  exact ofNat_eq_ofNat (by omega)

/-- Back from the head, `n + r - 16 ≤ 15` bytes left: to the computed jump. -/
theorem hrT_step (ra : BitVec 64) (d : Nat) (v : BitVec 64) (n r : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hc : CodeAt M memsetBase memsetCode) (hr15 : r ≤ 15) (hn16 : 16 ≤ n) (hn : n + r ≤ 31)
    (hd : d + n < 2 ^ 64) :
    Triple (At 0x80009468#64 (hrL ra d v n r) M w.keep outp)
      (At 0x800093e0#64 (jtL ra d v (n + r - 16) (d + 16 - r)) M w.keep outp) := by
  refine Triple.conseq (seg_at memsetHeadRetT
    (L1 := [(12, BitVec.ofNat 64 (n + r - 16)), (14, BitVec.ofNat 64 (d + 16 - r)),
      (15, BitVec.ofNat 64 r + 18446744073709551600#64), (1, ra), (5, ra), (6, 15#64),
      (10, BitVec.ofNat 64 d), (11, v)]) (lg := []) [] [1, 5, 6, 10, 11, 12, 14, 15] abiKeys
    ?_ ?_ ?_ ?_) (fun _ h => h) (fun _ h => h.weaken (by simp [jtL]))
  · tom_facts hc
    leaf_nf [hrL]
    rw [addneg_ofNat _ _ (by omega), geu_ofNat _ _ (by omega) (by omega)]
    simp; omega
  · seg_nf [memsetHeadRetT]
  · seg_nf [memsetHeadRetT, hrL]
    exact ⟨addneg_ofNat _ _ (by omega), subneg_ofNat _ _ (by omega) (by omega)⟩
  · seg_nf [memsetHeadRetT]

/-- Back from the head, `n + r - 16 ≥ 16` bytes left: to the loop head. -/
theorem hrL_step (ra : BitVec 64) (d n r : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hc : CodeAt M memsetBase memsetCode) (hr15 : r ≤ 15) (hn : 32 ≤ n + r)
    (hd : d + n + 16 < 2 ^ 64) :
    Triple (At 0x80009468#64 (hrL ra d 0#64 n r) M w.keep outp)
      (At 0x800093c8#64 (loopL ra d 0#64 ((n + r - 16) % 16)
        (n + r - 16 - (n + r - 16) % 16 + (d + 16 - r)) (d + 16 - r)) M w.keep outp) := by
  refine Triple.conseq (seg_at memsetHeadRetL
    (L1 := [(13, BitVec.ofNat 64 (n + r - 16 - (n + r - 16) % 16 + (d + 16 - r))),
      (12, BitVec.ofNat 64 ((n + r - 16) % 16)), (14, BitVec.ofNat 64 (d + 16 - r)),
      (15, BitVec.ofNat 64 r + 18446744073709551600#64), (1, ra), (5, ra), (6, 15#64),
      (10, BitVec.ofNat 64 d), (11, 0#64)]) (lg := []) [] [1, 5, 6, 10, 11, 12, 14, 15] abiKeys
    ?_ ?_ ?_ ?_) (fun _ h => h) (fun _ h => h.weaken (by simp [loopL]))
  · tom_facts hc
    · leaf_nf [hrL]
      rw [addneg_ofNat _ _ (by omega), geu_ofNat _ _ (by omega) (by omega)]
      simp; omega
    · leaf_nf [hrL]
      rfl
  · seg_nf [memsetHeadRetL, Vsa.Sim.endPCM]
  · seg_nf [memsetHeadRetL, hrL]
    rw [addneg_ofNat _ _ (by omega), subneg_ofNat _ _ (by omega) (by omega), andm16_ofNat,
      and15_ofNat, ofNat_add_ofNat]
    exact ⟨ofNat_eq_ofNat (by omega), ofNat_eq_ofNat (by omega), rfl⟩
  · seg_nf [memsetHeadRetL]

/-- The fill-byte replication `a1 := rep8 c` in the segment normal form. -/
local macro "rep_nf " c:term:max hc:term:max : tactic => `(tactic|
  (have h8 : Sail.BitVec.extractLsb (8#6) 5 0 = BitVec.ofNat 6 8 := by decide
   have h16 : Sail.BitVec.extractLsb (16#6) 5 0 = BitVec.ofNat 6 16 := by decide
   have h32 : Sail.BitVec.extractLsb (32#6) 5 0 = BitVec.ofNat 6 32 := by decide
   rw [and255_ofNat $c $hc, h8, h16, h32, shl_ofNat $c 8 (by omega),
     or_shl_ofNat $c 8 (by omega) (by omega), shl_ofNat _ 16 (by omega),
     or_shl_ofNat _ 16 (by omega) (by omega), shl_ofNat _ 32 (by omega),
     or_shl_ofNat _ 32 (by omega) (by omega)]))

/-- `n ≥ 16`, `d ≡ 0 mod 16`, `c ≠ 0`: replicate `c`, to the loop head. -/
theorem alC_step (ra : BitVec 64) (d c n : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hc : CodeAt M memsetBase memsetCode) (hn : 16 ≤ n) (hn' : d + n < 2 ^ 64) (hd : d % 16 = 0)
    (hc0 : c ≠ 0) (hc8 : c < 256) :
    Triple (At entry (entryL ra d (BitVec.ofNat 64 c) n) M w.keep outp)
      (At 0x800093c8#64 (loopL ra d (BitVec.ofNat 64 (rep8 c)) (n % 16) (n - n % 16 + d) d) M
        w.keep outp) := by
  refine Triple.conseq (seg_at memsetEnterAlC
    (L1 := [(13, BitVec.ofNat 64 (n - n % 16 + d)), (12, BitVec.ofNat 64 (n % 16)),
      (11, BitVec.ofNat 64 (rep8 c)), (15, BitVec.ofNat 64 (d % 16)), (14, BitVec.ofNat 64 d),
      (6, 15#64), (1, ra), (10, BitVec.ofNat 64 d)]) (lg := []) [] [1, 10, 11, 12] abiKeys
      ?_ ?_ ?_ ?_)
    (fun _ h => h) (fun _ h => h.weaken (by simp [loopL]))
  · tom_facts hc
    · leaf_nf [entryL]
      rw [li15, geu_ofNat _ _ (by omega) (by omega)]
      simp; omega
    · leaf_nf [entryL]
      rw [BitVec.add_zero, and15_ofNat, bne_zero_ofNat _ (by omega)]
      simpa using hd
    · leaf_nf [entryL]
      rw [bne_zero_ofNat _ (by omega)]
      simpa using hc0
  · seg_nf [memsetEnterAlC, Vsa.Sim.endPCM]
  · seg_nf [memsetEnterAlC, entryL]
    rep_nf c hc8
    rw [andm16_ofNat, and15_ofNat, and15_ofNat, ofNat_add_ofNat]
    repeat' apply And.intro
    all_goals
      first | rfl | exact ofNat_eq_ofNat (by omega) | (simp only [rep8]; exact ofNat_eq_ofNat (by omega))
  · seg_nf [memsetEnterAlC]

/-- Back from the head, `n + r - 16 ≥ 16` bytes left, `c ≠ 0`: replicate `c`, to
the loop head. -/
theorem hrLC_step (ra : BitVec 64) (d c n r : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hc : CodeAt M memsetBase memsetCode) (hr15 : r ≤ 15) (hn : 32 ≤ n + r)
    (hd : d + n + 16 < 2 ^ 64) (hc0 : c ≠ 0) (hc8 : c < 256) :
    Triple (At 0x80009468#64 (hrL ra d (BitVec.ofNat 64 c) n r) M w.keep outp)
      (At 0x800093c8#64 (loopL ra d (BitVec.ofNat 64 (rep8 c)) ((n + r - 16) % 16)
        (n + r - 16 - (n + r - 16) % 16 + (d + 16 - r)) (d + 16 - r)) M w.keep outp) := by
  refine Triple.conseq (seg_at memsetHeadRetLC
    (L1 := [(13, BitVec.ofNat 64 (n + r - 16 - (n + r - 16) % 16 + (d + 16 - r))),
      (12, BitVec.ofNat 64 ((n + r - 16) % 16)), (11, BitVec.ofNat 64 (rep8 c)),
      (14, BitVec.ofNat 64 (d + 16 - r)),
      (15, BitVec.ofNat 64 r + 18446744073709551600#64), (1, ra), (5, ra), (6, 15#64),
      (10, BitVec.ofNat 64 d)]) (lg := []) [] [1, 5, 6, 10, 11, 12, 14, 15] abiKeys
    ?_ ?_ ?_ ?_) (fun _ h => h) (fun _ h => h.weaken (by simp [loopL]))
  · tom_facts hc
    · leaf_nf [hrL]
      rw [addneg_ofNat _ _ (by omega), geu_ofNat _ _ (by omega) (by omega)]
      simp; omega
    · leaf_nf [hrL]
      rw [bne_zero_ofNat _ (by omega)]
      simpa using hc0
  · seg_nf [memsetHeadRetLC, Vsa.Sim.endPCM]
  · seg_nf [memsetHeadRetLC, hrL]
    rep_nf c hc8
    rw [addneg_ofNat _ _ (by omega), subneg_ofNat _ _ (by omega) (by omega), andm16_ofNat,
      and15_ofNat, ofNat_add_ofNat]
    repeat' apply And.intro
    all_goals
      first | rfl | exact ofNat_eq_ofNat (by omega) | (simp only [rep8]; exact ofNat_eq_ofNat (by omega))
  · seg_nf [memsetHeadRetLC]

/-! ## The function -/

/-- What `memset(d, c, n)` needs: a byte `c`, the code in memory, `[d, d + n)`
RAM off the code. -/
structure Pre (m : Mem) (d c n : Nat) : Prop where
  byte : c < 256
  code : CodeAt m memsetBase memsetCode
  ram : Ram d n
  code_off : d + n ≤ memsetBase ∨ memsetBase + 4 * memsetCode.length ≤ d

/-- **newlib `memset(d, c, n)` on the machine.** From its entry with `a0 = d`,
`a1 = c`, `a2 = n`, the return address `ra` and the callee-saved registers `w`,
the machine runs `memset` to `ra`, keeping `w`, with `a0 = d`, `[d, d + n)`
filled with the byte `c`, memory unchanged elsewhere, and the code intact. -/
theorem correct (ra : BitVec 64) (w : Abi) (outp : Array String) (m : Mem) (d c n : Nat)
    (hra : ra.toNat % 4 = 0) (hP : Pre m d c n) :
    Triple (At entry (entryL ra d (BitVec.ofNat 64 c) n) m w.keep outp)
      (Ret ra w outp m d n (BitVec.ofNat 8 c)) := by
  have hP' : Room m d n := ⟨hP.code, hP.ram, hP.code_off⟩
  have hc8 := hP.byte
  have hr := hP.ram
  have ⟨h1, h2, h3⟩ := ram_bounds hr
  have hoff := hP.code_off
  have hcl := code_len
  have hcb : memsetBase = 0x800093a4 := rfl
  have hbyte := sbData_byte c hc8
  by_cases hsmall : n ≤ 15
  · exact Triple.seq (small_step ra d _ n w outp m hP.code hsmall)
      (finish_tail ra w outp m m d n n d _ _ hbyte hra hP' (Filled.refl m d _) (Nat.le_refl _)
        hsmall rfl)
  -- the loop from `x` (`[d, x)` filled), entered with `a1 = v`
  have toLoop : ∀ (v : BitVec 64) (x : Nat) (M : Mem), SdFill v (BitVec.ofNat 8 c) →
      sbData v = BitVec.ofNat 8 c → Filled m M d x (BitVec.ofNat 8 c) → d ≤ x → x % 16 = 0 →
      x + 16 ≤ d + n →
      Triple (At 0x800093c8#64 (loopL ra d v ((d + n - x) % 16) (d + n - x - (d + n - x) % 16 + x)
          x) M w.keep outp) (Ret ra w outp m d n (BitVec.ofNat 8 c)) := by
    intro v x M hv hb hF hdx hx hxn
    have hJ : d + n - x - (d + n - x) % 16 + x - 16 * ((d + n - x - (d + n - x) % 16) / 16 - 1 + 1)
        = x := by omega
    refine Triple.conseq (loop ra w outp m d n ((d + n - x) % 16)
      (d + n - x - (d + n - x) % 16 + x) v _ hv hb hra hP' (by omega) (by omega) (by omega)
      ((d + n - x - (d + n - x) % 16) / 16 - 1)) (fun c h => ⟨M, ?_, ?_⟩) (fun _ h => h)
    · exact { room := by omega, fill := by rw [hJ]; exact hF }
    · rwa [hJ]
  by_cases hal : d % 16 = 0
  · -- aligned: the loop from `d`
    have he : d + n - d = n := by omega
    by_cases hc0 : c = 0
    · subst hc0
      have := toLoop 0#64 d m sdFill_zero sbData_zero (Filled.refl m d _) (Nat.le_refl _) hal
        (by omega)
      rw [he] at this
      exact Triple.seq (al_step ra d n w outp m hP.code (by omega) (by omega) hal) this
    · have := toLoop _ d m (sdFill_rep c hc8) (sbData_rep c hc8) (Filled.refl m d _)
        (Nat.le_refl _) hal (by omega)
      rw [he] at this
      exact Triple.seq (alC_step ra d c n w outp m hP.code (by omega) (by omega) hal hc0 hc8) this
  -- unaligned: `16 - r` bytes through the table first, `r = d mod 16`
  have hF1 := (Filled.refl m d (BitVec.ofNat 8 c)).sb (Nat.le_refl _) hbyte (16 - d % 16)
  rw [show d + (16 - d % 16) = d + 16 - d % 16 by omega] at hF1
  have hc1 := hF1.code hP.code (by omega)
  refine Triple.seq (un_step ra d _ n (d % 16) w outp m hP.code (by omega) (by omega) rfl hal)
    (Triple.seq (head_call ra d _ n (d % 16) w outp m hP.code (by omega) (by omega)
      (ram_sub hr 0 (16 - d % 16) (by omega) |> fun h => by simpa using h) (by omega)) ?_)
  by_cases hT : n + d % 16 ≤ 31
  · exact Triple.seq (hrT_step ra d _ n (d % 16) w outp _ hc1 (by omega) (by omega) hT (by omega))
      (finish_tail ra w outp m _ d n (n + d % 16 - 16) (d + 16 - d % 16) _ _ hbyte hra hP' hF1
        (by omega) (by omega) (by omega))
  · -- the loop from `d + 16 - r`
    have he : d + n - (d + 16 - d % 16) = n + d % 16 - 16 := by omega
    by_cases hc0 : c = 0
    · subst hc0
      have := toLoop 0#64 _ _ sdFill_zero sbData_zero hF1 (by omega) (by omega) (by omega)
      rw [he] at this
      exact Triple.seq (hrL_step ra d n (d % 16) w outp _ hc1 (by omega) (by omega) (by omega)) this
    · have := toLoop _ _ _ (sdFill_rep c hc8) (sbData_rep c hc8) hF1 (by omega) (by omega)
        (by omega)
      rw [he] at this
      exact Triple.seq (hrLC_step ra d c n (d % 16) w outp _ hc1 (by omega) (by omega) (by omega)
        hc0 hc8) this

/-- `memset(d, 0, n)`, the case libtommath calls (`MP_ZERO_DIGITS`). -/
theorem correct_zero (ra : BitVec 64) (w : Abi) (outp : Array String) (m : Mem) (d n : Nat)
    (hra : ra.toNat % 4 = 0) (hP : Pre m d 0 n) :
    Triple (At entry (entryL ra d 0#64 n) m w.keep outp) (Ret ra w outp m d n 0#8) :=
  correct ra w outp m d 0 n hra hP

end Tom.Machine.Fn.Memset
