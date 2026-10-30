import Tom.Machine.Seg.CmpMag
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Arith
import Tom.Machine.Kit.Loop
import Tom.Machine.Kit.Mem
import Tom.Machine.Kit.Auto
import Tom.Spec.Ops

/-!
# `mp_cmp_mag` on the machine

`mp_cmp_mag` at `0x80000764` in `c/tommath-arith.elf`:
```
764 lw a3,0(a0); lw a5,0(a1); blt a5,a3,7bc     -- b->used < a->used: MP_GT
770 li a4,-1; blt a3,a5,7c0                     -- a->used < b->used: MP_LT
778 blez a3,7c8                                 -- both 0: MP_EQ
77c ld a5,16(a0); ld a4,16(a1); slli a2,a3,2; addi a2,a2,-4; add a5,a5,a2
790 slli a1,a3,2; add a4,a4,a2; sub a1,a5,a1; j 7a8
7a0 bltu a2,a3,7d4                              -- da < db: MP_LT
7a4 beq a1,a5,7c8                               -- past digit 0: MP_EQ
7a8 lw a2,0(a5); lw a3,0(a4); addi a5,a5,-4; addi a4,a4,-4; bgeu a3,a2,7a0   -- loop head
7bc li a4,1; 7c0 mv a0,a4; ret
7c8 li a4,0; mv a0,a4; ret
7d4 li a4,-1; mv a0,a4; ret
```
At the loop head at index `i`, `a5 = adp + 4i`, `a4 = bdp + 4i` and
`a1 = adp - 4`. No store: memory is unchanged.
-/


namespace Tom.Machine.Fn.CmpMag

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

/-- `mp_cmp_mag`'s entry address. -/
abbrev entry : BitVec 64 := 0x80000764#64

/-- Registers at entry. -/
def entryL (ra : BitVec 64) (pa pb : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)]

/-- Registers at the loop head at index `i`. -/
def headL (ra : BitVec 64) (adp bdp i : Nat) : GRegs :=
  [(1, ra), (11, BitVec.ofNat 64 (adp - 4)), (14, BitVec.ofNat 64 (bdp + 4 * i)),
   (15, BitVec.ofNat 64 (adp + 4 * i))]

/-- Registers at the return with result `r`. -/
def retL (ra r : BitVec 64) : GRegs := [(1, ra), (10, r)]


/-- The `used` loads of the entry. -/
structure UsedRead (m : Mem) (pa pb ua ub : Nat) : Prop where
  ra : Ram pa 24
  rb : Ram pb 24
  ua_v : bytesT4 m pa = BitVec.ofNat 32 ua
  ub_v : bytesT4 m pb = BitVec.ofNat 32 ub
  ua_lt : ua < 2 ^ 31
  ub_lt : ub < 2 ^ 31

theorem UsedRead.sx {m : Mem} {pa pb ua ub : Nat} (h : UsedRead m pa pb ua ub) :
    BitVec.signExtend 64 (bytesT4 m pa) = BitVec.ofNat 64 ua ∧
      BitVec.signExtend 64 (bytesT4 m pb) = BitVec.ofNat 64 ub :=
  ⟨by rw [h.ua_v, signExtend_ofNat32 _ h.ua_lt], by rw [h.ub_v, signExtend_ofNat32 _ h.ub_lt]⟩

/-- `b->used < a->used`: return `MP_GT`. -/
theorem gt_step (ra : BitVec 64) (v : Abi) (outp : Array String) (pa pb ua ub : Nat) (m : Mem)
    (hc : CodeAt m mpCmpMagBase mpCmpMagCode) (hra : ra.toNat % 4 = 0)
    (hu : UsedRead m pa pb ua ub) (hlt : ub < ua) :
    Triple (At entry (entryL ra pa pb) m v.keep outp) (At ra (retL ra 1#64) m v.keep outp) := by
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hu.ra
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hu.rb
  have ⟨hsa, hsb⟩ := hu.sx
  have := hu.ua_lt; have := hu.ub_lt
  refine Triple.conseq (seg_at cmpGT (pc1 := ra)
      (L1 := [(10, 1#64), (14, 1#64), (15, BitVec.ofNat 64 ub), (13, BitVec.ofNat 64 ua), (1, ra),
        (11, BitVec.ofNat 64 pb)])
      (lg := []) [rd4 m pa, rd4 m pb] [1, 10, 11] abiKeys ?_ ?_ ?_ ?_)
    (fun _ h => h) (fun _ h => h.weaken (by simp [retL]))
  · tom_facts hc
    all_goals leaf_auto [entryL] [hsa, hsb]
  · seg_nf [cmpGT, entryL]; exact ret_target' ra hra
  · seg_nf [cmpGT, entryL]
    simp only [rd4_bytes, hsa, hsb]
    exact ⟨trivial, trivial⟩
  · seg_nf [cmpGT, entryL]

/-- The all-ones word (`li a4,-1`). -/
abbrev neg1 : BitVec 64 := 0xffffffffffffffff#64

/-- `a->used < b->used`: return `MP_LT`. -/
theorem lt_step (ra : BitVec 64) (v : Abi) (outp : Array String) (pa pb ua ub : Nat) (m : Mem)
    (hc : CodeAt m mpCmpMagBase mpCmpMagCode) (hra : ra.toNat % 4 = 0)
    (hu : UsedRead m pa pb ua ub) (hlt : ua < ub) :
    Triple (At entry (entryL ra pa pb) m v.keep outp) (At ra (retL ra neg1) m v.keep outp) := by
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hu.ra
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hu.rb
  have ⟨hsa, hsb⟩ := hu.sx
  have := hu.ua_lt; have := hu.ub_lt
  refine Triple.conseq (seg_at cmpLT (pc1 := ra)
      (L1 := [(10, neg1), (14, neg1), (15, BitVec.ofNat 64 ub), (13, BitVec.ofNat 64 ua), (1, ra),
        (11, BitVec.ofNat 64 pb)])
      (lg := []) [rd4 m pa, rd4 m pb] [1, 10, 11] abiKeys ?_ ?_ ?_ ?_)
    (fun _ h => h) (fun _ h => h.weaken (by simp [retL]))
  · tom_facts hc
    all_goals leaf_auto [entryL] [hsa, hsb]
  · seg_nf [cmpLT, entryL]; exact ret_target' ra hra
  · seg_nf [cmpLT, entryL]
    simp only [rd4_bytes, hsa, hsb]
    exact ⟨trivial, trivial⟩
  · seg_nf [cmpLT, entryL]

/-- Both `used` zero: return `MP_EQ`. -/
theorem zero_step (ra : BitVec 64) (v : Abi) (outp : Array String) (pa pb : Nat) (m : Mem)
    (hc : CodeAt m mpCmpMagBase mpCmpMagCode) (hra : ra.toNat % 4 = 0)
    (hu : UsedRead m pa pb 0 0) :
    Triple (At entry (entryL ra pa pb) m v.keep outp) (At ra (retL ra 0#64) m v.keep outp) := by
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hu.ra
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hu.rb
  have ⟨hsa, hsb⟩ := hu.sx
  refine Triple.conseq (seg_at cmpZero (pc1 := ra)
      (L1 := [(10, 0#64), (14, 0#64), (15, BitVec.ofNat 64 0), (13, BitVec.ofNat 64 0), (1, ra),
        (11, BitVec.ofNat 64 pb)])
      (lg := []) [rd4 m pa, rd4 m pb] [1, 10, 11] abiKeys ?_ ?_ ?_ ?_)
    (fun _ h => h) (fun _ h => h.weaken (by simp [retL]))
  · tom_facts hc
    all_goals leaf_auto [entryL] [hsa, hsb]
  · seg_nf [cmpZero, entryL]; exact ret_target' ra hra
  · seg_nf [cmpZero, entryL]
    simp only [rd4_bytes, hsa, hsb]
    exact ⟨trivial, trivial⟩
  · seg_nf [cmpZero, entryL]

/-- Equal nonzero `used`: load the digit pointers and go to the loop head at
index `u - 1`. -/
theorem enter_step (ra : BitVec 64) (v : Abi) (outp : Array String) (pa pb u adp bdp : Nat)
    (m : Mem) (hc : CodeAt m mpCmpMagBase mpCmpMagCode) (hu : UsedRead m pa pb u u) (hu1 : 1 ≤ u)
    (hda : bytesT8 m (pa + 16) = BitVec.ofNat 64 adp) (hdb : bytesT8 m (pb + 16) = BitVec.ofNat 64 bdp)
    (hra : Ram adp (4 * u)) (hrb : Ram bdp (4 * u)) :
    Triple (At entry (entryL ra pa pb) m v.keep outp)
      (At 0x800007a8#64 (headL ra adp bdp (u - 1)) m v.keep outp) := by
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hu.ra
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hu.rb
  have ⟨hA1, hA2, hA3⟩ := ram_bounds hra
  have ⟨hB1, hB2, hB3⟩ := ram_bounds hrb
  have ⟨hsa, hsb⟩ := hu.sx
  have := hu.ua_lt
  refine Triple.conseq (seg_at cmpEnter (pc1 := 0x800007a8#64)
      (L1 := [(11, BitVec.ofNat 64 (adp - 4)), (14, BitVec.ofNat 64 (bdp + 4 * (u - 1))),
        (15, BitVec.ofNat 64 (adp + 4 * (u - 1))), (12, BitVec.ofNat 64 (4 * (u - 1))),
        (13, BitVec.ofNat 64 u), (1, ra), (10, BitVec.ofNat 64 pa)])
      (lg := []) [rd4 m pa, rd4 m pb, rd8 m (pa + 16), rd8 m (pb + 16)] [1, 10, 11] abiKeys
      ?_ ?_ ?_ ?_)
    (fun _ h => h) (fun _ h => h.weaken (by simp [headL]))
  · tom_facts hc
    all_goals leaf_auto [entryL] [hsa, hsb, hda, hdb]
  · seg_nf [cmpEnter, entryL]
  · seg_nf [cmpEnter, entryL]
    simp only [rd4_bytes, rd8_bytes, hsa, hda, hdb]
    have hsh : Sail.BitVec.extractLsb (2#6) 5 0 = BitVec.ofNat 6 2 := by decide
    rw [hsh, shl_ofNat u 2 (by omega)]
    refine ⟨by bv_nat, by bv_nat, by bv_nat, by bv_nat, trivial⟩
  · seg_nf [cmpEnter, entryL]

/-- The two digit loads at the loop head at index `i`. -/
structure DigRead (m : Mem) (adp bdp i da db : Nat) : Prop where
  ra : Ram (adp + 4 * i) 4
  rb : Ram (bdp + 4 * i) 4
  da_v : bytesT4 m (adp + 4 * i) = BitVec.ofNat 32 da
  db_v : bytesT4 m (bdp + 4 * i) = BitVec.ofNat 32 db
  da_lt : da < 2 ^ 31
  db_lt : db < 2 ^ 31

theorem DigRead.sx {m : Mem} {adp bdp i da db : Nat} (h : DigRead m adp bdp i da db) :
    BitVec.signExtend 64 (bytesT4 m (adp + 4 * i)) = BitVec.ofNat 64 da ∧
      BitVec.signExtend 64 (bytesT4 m (bdp + 4 * i)) = BitVec.ofNat 64 db :=
  ⟨by rw [h.da_v, signExtend_ofNat32 _ h.da_lt], by rw [h.db_v, signExtend_ofNat32 _ h.db_lt]⟩

/-- Digit `i` of `a` is larger: return `MP_GT`. -/
theorem dgt_step (ra : BitVec 64) (v : Abi) (outp : Array String) (adp bdp i da db : Nat) (m : Mem)
    (hc : CodeAt m mpCmpMagBase mpCmpMagCode) (hra : ra.toNat % 4 = 0)
    (hd : DigRead m adp bdp i da db) (hgt : db < da) :
    Triple (At 0x800007a8#64 (headL ra adp bdp i) m v.keep outp) (At ra (retL ra 1#64) m v.keep outp) := by
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hd.ra
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hd.rb
  have ⟨hsa, hsb⟩ := hd.sx
  have := hd.da_lt; have := hd.db_lt
  refine Triple.conseq (seg_at cmpDGT (pc1 := ra)
      (L1 := [(10, 1#64), (14, 1#64), (15, BitVec.ofNat 64 (adp + 4 * i - 4)), (13, BitVec.ofNat 64 db), (12, BitVec.ofNat 64 da), (1, ra), (11, BitVec.ofNat 64 (adp - 4))])
      (lg := []) [rd4 m (adp + 4 * i), rd4 m (bdp + 4 * i)] [1, 11, 14, 15] abiKeys ?_ ?_ ?_ ?_)
    (fun _ h => h) (fun _ h => h.weaken (by simp [retL]))
  · tom_facts hc
    all_goals leaf_auto [headL] [hsa, hsb]
  · seg_nf [cmpDGT, headL]; exact ret_target' ra hra
  · seg_nf [cmpDGT, headL]
    simp only [rd4_bytes, hsa, hsb]
    regs_close
  · seg_nf [cmpDGT, headL]

/-- Digit `i` of `a` is smaller: return `MP_LT`. -/
theorem dlt_step (ra : BitVec 64) (v : Abi) (outp : Array String) (adp bdp i da db : Nat) (m : Mem)
    (hc : CodeAt m mpCmpMagBase mpCmpMagCode) (hra : ra.toNat % 4 = 0)
    (hd : DigRead m adp bdp i da db) (hlt : da < db) :
    Triple (At 0x800007a8#64 (headL ra adp bdp i) m v.keep outp) (At ra (retL ra neg1) m v.keep outp) := by
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hd.ra
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hd.rb
  have ⟨hsa, hsb⟩ := hd.sx
  have := hd.da_lt; have := hd.db_lt
  refine Triple.conseq (seg_at cmpDLT (pc1 := ra)
      (L1 := [(10, neg1), (14, neg1), (15, BitVec.ofNat 64 (adp + 4 * i - 4)), (13, BitVec.ofNat 64 db), (12, BitVec.ofNat 64 da), (1, ra), (11, BitVec.ofNat 64 (adp - 4))])
      (lg := []) [rd4 m (adp + 4 * i), rd4 m (bdp + 4 * i)] [1, 11, 14, 15] abiKeys ?_ ?_ ?_ ?_)
    (fun _ h => h) (fun _ h => h.weaken (by simp [retL]))
  · tom_facts hc
    all_goals leaf_auto [headL] [hsa, hsb]
  · seg_nf [cmpDLT, headL]; exact ret_target' ra hra
  · seg_nf [cmpDLT, headL]
    simp only [rd4_bytes, hsa, hsb]
    regs_close
  · seg_nf [cmpDLT, headL]

/-- Equal digits at index `0`: return `MP_EQ`. -/
theorem dend_step (ra : BitVec 64) (v : Abi) (outp : Array String) (adp bdp i da db : Nat) (m : Mem)
    (hc : CodeAt m mpCmpMagBase mpCmpMagCode) (hra : ra.toNat % 4 = 0)
    (hd : DigRead m adp bdp i da db) (heq : da = db) (hi : i = 0) :
    Triple (At 0x800007a8#64 (headL ra adp bdp i) m v.keep outp) (At ra (retL ra 0#64) m v.keep outp) := by
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hd.ra
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hd.rb
  have ⟨hsa, hsb⟩ := hd.sx
  have := hd.da_lt; have := hd.db_lt
  refine Triple.conseq (seg_at cmpDEnd (pc1 := ra)
      (L1 := [(10, 0#64), (14, 0#64), (15, BitVec.ofNat 64 (adp + 4 * i - 4)), (13, BitVec.ofNat 64 db), (12, BitVec.ofNat 64 da), (1, ra), (11, BitVec.ofNat 64 (adp - 4))])
      (lg := []) [rd4 m (adp + 4 * i), rd4 m (bdp + 4 * i)] [1, 11, 14, 15] abiKeys ?_ ?_ ?_ ?_)
    (fun _ h => h) (fun _ h => h.weaken (by simp [retL]))
  · tom_facts hc
    all_goals leaf_auto [headL] [hsa, hsb]
  · seg_nf [cmpDEnd, headL]; exact ret_target' ra hra
  · seg_nf [cmpDEnd, headL]
    simp only [rd4_bytes, hsa, hsb]
    regs_close
  · seg_nf [cmpDEnd, headL]

/-- Equal digits at index `i ≥ 1`: go on at index `i - 1`. -/
theorem dnext_step (ra : BitVec 64) (v : Abi) (outp : Array String) (adp bdp i da db : Nat) (m : Mem)
    (hc : CodeAt m mpCmpMagBase mpCmpMagCode) (hd : DigRead m adp bdp i da db) (heq : da = db)
    (hi : 1 ≤ i) :
    Triple (At 0x800007a8#64 (headL ra adp bdp i) m v.keep outp)
      (At 0x800007a8#64 (headL ra adp bdp (i - 1)) m v.keep outp) := by
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hd.ra
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hd.rb
  have ⟨hsa, hsb⟩ := hd.sx
  have := hd.da_lt; have := hd.db_lt
  refine Triple.conseq (seg_at cmpDNext (pc1 := 0x800007a8#64)
      (L1 := [(14, BitVec.ofNat 64 (bdp + 4 * (i - 1))), (15, BitVec.ofNat 64 (adp + 4 * (i - 1))),
        (13, BitVec.ofNat 64 db), (12, BitVec.ofNat 64 da), (1, ra), (11, BitVec.ofNat 64 (adp - 4))])
      (lg := []) [rd4 m (adp + 4 * i), rd4 m (bdp + 4 * i)] [1, 11, 14, 15] abiKeys ?_ ?_ ?_ ?_)
    (fun _ h => h) (fun _ h => h.weaken (by simp [headL]))
  · tom_facts hc
    all_goals leaf_auto [headL] [hsa, hsb]
  · seg_nf [cmpDNext, headL]
  · seg_nf [cmpDNext, headL]
    simp only [rd4_bytes, hsa, hsb]
    regs_close
  · seg_nf [cmpDNext, headL]

/-! ## The function -/

/-- The result register for an ordering. -/
def res (o : Ordering) : BitVec 64 := BitVec.ofInt 64 (ordCode o)

theorem res_gt : res .gt = 1#64 := by decide
theorem res_lt : res .lt = neg1 := by decide
theorem res_eq : res .eq = 0#64 := by decide

/-- What `mp_cmp_mag(a, b)` needs: both `mp_int`s valid, in memory with their
geometry, and the code in memory. -/
structure Pre (m : Mem) (pa adp pb bdp : Nat) (a b : MpInt) : Prop where
  ra : MpAt m pa adp a
  rb : MpAt m pb bdp b
  va : a.Valid
  vb : b.Valid
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  code : CodeAt m mpCmpMagBase mpCmpMagCode

/-- `mp_cmp_mag`'s loop reads only the shape (digits below `2^28`, `used ≤ alloc < 2^31`): `Pre`
with `Shape` operands (`mp_div`'s step 3.2 compares `t1` with `t2 = [x[i-2], x[i-1], x[i]]`,
`used = 3` and not clamped, `Tom/Spec/DivKnuth.lean` `cmpMag_three`). -/
structure PreS (m : Mem) (pa adp pb bdp : Nat) (a b : MpInt) : Prop where
  ra : MpAt m pa adp a
  rb : MpAt m pb bdp b
  sa : a.Shape
  sb : b.Shape
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  code : CodeAt m mpCmpMagBase mpCmpMagCode

theorem PreS.dig {m : Mem} {pa adp pb bdp : Nat} {a b : MpInt} (h : PreS m pa adp pb bdp a b)
    (i : Nat) (hia : i < a.alloc) (hib : i < b.alloc) :
    DigRead m adp bdp i (a.digit i) (b.digit i) :=
  { ra := ⟨by have := h.ga.ds.lo_ge; omega,
          by have := h.ga.ds.hi_le; simp only [Layout.sizeofDigit] at this; omega,
          by have := h.ga.ds.off; simp only [Layout.sizeofDigit] at this; omega⟩
    rb := ⟨by have := h.gb.ds.lo_ge; omega,
          by have := h.gb.ds.hi_le; simp only [Layout.sizeofDigit] at this; omega,
          by have := h.gb.ds.off; simp only [Layout.sizeofDigit] at this; omega⟩
    da_v := h.ra.digits i hia
    db_v := h.rb.digits i hib
    da_lt := Nat.lt_trans (h.sa.digit_lt i) (by decide)
    db_lt := Nat.lt_trans (h.sb.digit_lt i) (by decide) }

theorem Pre.toS {m : Mem} {pa adp pb bdp : Nat} {a b : MpInt} (h : Pre m pa adp pb bdp a b) :
    PreS m pa adp pb bdp a b := ⟨h.ra, h.rb, h.va.toShape, h.vb.toShape, h.ga, h.gb, h.code⟩

/-- The loop from index `j`, with the digits above `j` (below `u`) equal. -/
theorem loop (ra : BitVec 64) (v : Abi) (outp : Array String) (pa adp pb bdp : Nat) (a b : MpInt)
    (m : Mem) (hra : ra.toNat % 4 = 0) (hP : PreS m pa adp pb bdp a b) (u : Nat)
    (hua : u ≤ a.alloc) (hub : u ≤ b.alloc) :
    ∀ j, j < u → (∀ k, j < k → k < u → a.digit k = b.digit k) →
      Triple (At 0x800007a8#64 (headL ra adp bdp j) m v.keep outp)
        (At ra (retL ra (res (cmpTop a.digit b.digit u))) m v.keep outp) := by
  intro j
  induction j with
  | zero =>
    intro hj he
    have hd := hP.dig 0 (by omega) (by omega)
    have hskip : cmpTop a.digit b.digit u = cmpTop a.digit b.digit 1 :=
      cmpTop_skip _ _ 1 u (by omega) (fun k h1 h2 => he k (by omega) h2)
    rw [hskip]
    simp only [cmpTop]
    by_cases hgt : b.digit 0 < a.digit 0
    · simp only [gt_iff_lt, hgt, ↓reduceIte, res_gt]; exact dgt_step ra v outp adp bdp 0 _ _ m hP.code hra hd hgt
    · by_cases hlt : a.digit 0 < b.digit 0
      · simp only [gt_iff_lt, hgt, hlt, ↓reduceIte, res_lt]; exact dlt_step ra v outp adp bdp 0 _ _ m hP.code hra hd hlt
      · simp only [gt_iff_lt, hgt, hlt, ↓reduceIte, res_eq]
        exact dend_step ra v outp adp bdp 0 _ _ m hP.code hra hd (by omega) rfl
  | succ j ih =>
    intro hj he
    have hd := hP.dig (j + 1) (by omega) (by omega)
    have hskip : cmpTop a.digit b.digit u = cmpTop a.digit b.digit (j + 2) :=
      cmpTop_skip _ _ (j + 2) u (by omega) (fun k h1 h2 => he k (by omega) h2)
    by_cases hgt : b.digit (j + 1) < a.digit (j + 1)
    · rw [hskip]; simp only [cmpTop]; simp only [gt_iff_lt, hgt, ↓reduceIte, res_gt]
      exact dgt_step ra v outp adp bdp (j + 1) _ _ m hP.code hra hd hgt
    · by_cases hlt : a.digit (j + 1) < b.digit (j + 1)
      · rw [hskip]; simp only [cmpTop]; simp only [gt_iff_lt, hgt, hlt, ↓reduceIte, res_lt]
        exact dlt_step ra v outp adp bdp (j + 1) _ _ m hP.code hra hd hlt
      · have heq : a.digit (j + 1) = b.digit (j + 1) := by omega
        refine Triple.seq (dnext_step ra v outp adp bdp (j + 1) _ _ m hP.code hd heq (by omega)) ?_
        exact ih (by omega) (fun k h1 h2 => by
          rcases Nat.lt_or_eq_of_le h1 with h1 | h1
          · exact he k h1 h2
          · subst h1; exact heq)

/-- **`mp_cmp_mag` of two shaped integers**: `a0` is the structural comparison `cmpMag a b`
(`used` first, then the digits from the top), `compare |a| |b|` only when both are valid. -/
theorem correctS (ra : BitVec 64) (v : Abi) (outp : Array String) (pa adp pb bdp : Nat)
    (a b : MpInt) (m : Mem) (hra : ra.toNat % 4 = 0) (hP : PreS m pa adp pb bdp a b) :
    Triple (At entry (entryL ra pa pb) m v.keep outp)
      (At ra (retL ra (res (cmpMag a b))) m v.keep outp) := by
  have hla := hP.sa.alloc_lt
  have hlb := hP.sb.alloc_lt
  have hua := hP.sa.used_le
  have hub := hP.sb.used_le
  have hu : UsedRead m pa pb a.used b.used :=
    { ra := by have := hP.ga.st; simpa [Layout.sizeofMpInt] using this
      rb := by have := hP.gb.st; simpa [Layout.sizeofMpInt] using this
      ua_v := by simpa [Layout.offUsed] using hP.ra.used
      ub_v := by simpa [Layout.offUsed] using hP.rb.used
      ua_lt := by omega
      ub_lt := by omega }
  show Triple _ (At ra (retL ra (res (cmpMag a b))) m v.keep outp)
  unfold cmpMag
  by_cases hgt : a.used > b.used
  · simp only [gt_iff_lt, hgt, ↓reduceIte, res_gt]; exact gt_step ra v outp pa pb _ _ m hP.code hra hu hgt
  · by_cases hlt : a.used < b.used
    · simp only [gt_iff_lt, hgt, hlt, ↓reduceIte, res_lt]; exact lt_step ra v outp pa pb _ _ m hP.code hra hu hlt
    · simp only [gt_iff_lt, hgt, hlt, ↓reduceIte]
      have he : a.used = b.used := by omega
      by_cases h0 : a.used = 0
      · rw [h0]; simp only [cmpTop]; rw [res_eq]
        have hb0 : b.used = 0 := by omega
        rw [h0, hb0] at hu
        exact zero_step ra v outp pa pb m hP.code hra hu
      · have hda : bytesT8 m (pa + 16) = BitVec.ofNat 64 adp := by
          simpa [Layout.offDp] using hP.ra.dpv
        have hdb : bytesT8 m (pb + 16) = BitVec.ofNat 64 bdp := by
          simpa [Layout.offDp] using hP.rb.dpv
        have hrA : Ram adp (4 * a.used) := by
          have h := hP.ga.ds; simp only [Layout.sizeofDigit] at h
          exact ⟨h.lo_ge, by have := h.hi_le; omega, by have := h.off; omega⟩
        have hrB : Ram bdp (4 * a.used) := by
          have h := hP.gb.ds; simp only [Layout.sizeofDigit] at h
          exact ⟨h.lo_ge, by have := h.hi_le; omega, by have := h.off; omega⟩
        refine Triple.seq (enter_step ra v outp pa pb a.used adp bdp m hP.code
          (he ▸ hu) (by omega) hda hdb hrA hrB) ?_
        exact loop ra v outp pa adp pb bdp a b m hra hP a.used hua (by omega) (a.used - 1)
          (by omega) (fun k h1 h2 => by omega)

/-- **`mp_cmp_mag` on the machine.** From its entry with `a0 = pa`, `a1 = pb`,
the machine returns to `ra`, keeping the callee-saved registers and memory,
with `a0` the `mp_ord` code of `compare |a| |b|`. -/
theorem correct (ra : BitVec 64) (v : Abi) (outp : Array String) (pa adp pb bdp : Nat)
    (a b : MpInt) (m : Mem) (hra : ra.toNat % 4 = 0) (hP : Pre m pa adp pb bdp a b) :
    Triple (At entry (entryL ra pa pb) m v.keep outp)
      (At ra (retL ra (BitVec.ofInt 64 (ordCode (compare a.mag b.mag)))) m v.keep outp) := by
  rw [← cmpMag_eq hP.va hP.vb]
  exact correctS ra v outp pa adp pb bdp a b m hra hP.toS

end Tom.Machine.Fn.CmpMag
