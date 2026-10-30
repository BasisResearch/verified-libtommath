import Tom.Machine.Seg.Memcpy
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Bits
import Tom.Machine.Kit.Alu1
import Tom.Machine.Kit.Loop
import Tom.Machine.Kit.MemCopy
import Vsa.Sim.TripleCat

/-!
# newlib `memcpy` on the machine: the segments

`memcpy` at `0x80009480` in `c/tommath-arith.elf` (74 instructions, newlib's
`memcpy.c` for RV64; `experiments/disasm.txt`):
```
9480 a5 := (s ^ d) & 7; a7 := d + n; bnez a5, 94f8        -- misaligned: bytes
9490 sltiu a2, a2, 8; bnez a2, 94f8                       -- n < 8: bytes
9498 a5 := d & 7; a4 := d; bnez a5, 9574                  -- d unaligned: the head
94a4 a2 := a7 & -8; a3 := a2 - a4; a5 := 64; blt a5, a3, 9518   -- > 64 bytes: blocks
94b4 a3 := a1; a5 := a4; bgeu a4, a2, 94f0                -- no words
94c0 ld a6, 0(a3); a5 += 8; a3 += 8; sd a6, -8(a5); bltu a5, a2, 94c0   -- the word loop
94d4 a2 := (a2 - 1 - a4) & -8; a1 += 8 + a2; a4 += 8 + a2
94f0 bltu a4, a7, 9500; 94f4 ret
94f8 a4 := d; bgeu a0, a7, 94f4                           -- n = 0
9500 lbu a5, 0(a1); a4 += 1; a1 += 1; sb a5, -1(a4); bne a7, a4, 9500; ret   -- the byte loop
9518 9 × ld from a1, 9 × sd to a4; a4 += 72; a3 := a2 - a4; a1 += 72;
     blt a5, a3, 9518; j 94b4                             -- the 72-byte block loop
9574 lbu; a4 += 1; a5 := a4 & 7; sb; a1 += 1; beqz a5, 94a4   -- the head, two bytes a turn
958c lbu; a4 += 1; a5 := a4 & 7; sb; a1 += 1; bnez a5, 9574; j 94a4
```
The segments are `Tom.Machine.Seg.memcpy*` (`experiments/segs/memcpy.json`).
The `sltiu` at `9490` is not a segment kind: `n8_step` is `Kit/Alu1.lean`'s
`sltiu_at`. At the byte loop (`9500`), the head (`9574`), the word setup
(`94a4`) and the exit test (`94f0`) the registers are the same, `cur`: the
cursors `a1 = s + t`, `a4 = d + t` after `t` bytes copied. Memory is
`Kit/MemCopy.lean`'s `Copied`: the first `t` bytes of `s` at `d`.

Chains are cut so that none has more than three stores or follows a store by a
long block: the word loop's exit is `memcpyWX` (to `94d4`) and `memcpyWE`, the
72-byte block is `memcpyBig1` (eight loads), `Big2a`, `Big2b`, `Big3a`, `Big3b`
(the nine stores, three at most each) and `Big3c`/`Big3cX` (the test). Uncut,
the block's code-frame leaves exceed the declaration's heartbeats, and the
word loop's exit (seven instructions after a store, in one chain) runs out of
memory in `tom_facts`'s leaves.
-/


namespace Tom.Machine.Fn.Memcpy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

/-- The code occupies `[memcpyBase, memcpyBase + 296)`. -/
theorem code_len : memcpyCode.length = 74 := rfl

theorem code_base : memcpyBase = 0x80009480 := rfl

/-! ## Arithmetic of the guards and the cursors -/

/-- `andi rd, rs, 7`. -/
theorem and7_ofNat (x : Nat) : BitVec.ofNat 64 x &&& 7#64 = BitVec.ofNat 64 (x % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat]
  rw [show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `andi rd, rs, -8`. -/
theorem andm8_ofNat (x : Nat) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x &&& 18446744073709551608#64 = BitVec.ofNat 64 (x - x % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
  have hy : x - x % 8 = (x >>> 3) <<< 3 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]; omega
  rw [show (18446744073709551608 : Nat) % 2 ^ 64 = (2 ^ 61 - 1) <<< 3 by decide, hy,
    Nat.mod_eq_of_lt (a := (x >>> 3) <<< 3) (by rw [← hy]; omega)]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases h3 : 3 ≤ i
  · rw [show 3 + (i - 3) = i by omega]
    by_cases h64 : i < 64
    · simp [h3, show i - 3 < 61 by omega]
    · have : x.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · simp [h3]

/-- The misalignment test `bnez ((s ^ d) & 7)`. -/
theorem xor7_bne (s d : Nat) (hs : s < 2 ^ 64) (hd : d < 2 ^ 64) :
    ((BitVec.ofNat 64 s ^^^ BitVec.ofNat 64 d) &&& 7#64 != 0#64) = decide (s % 8 ≠ d % 8) := by
  have e : (BitVec.ofNat 64 s ^^^ BitVec.ofNat 64 d) &&& 7#64 =
      BitVec.ofNat 64 ((s % 8) ^^^ (d % 8)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_xor]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd]
    rw [show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
      Nat.xor_mod_two_pow]
    have := Nat.xor_lt_two_pow (n := 3) (Nat.mod_lt s (by decide)) (Nat.mod_lt d (by decide))
    exact (Nat.mod_eq_of_lt (by omega)).symm
  have key : ∀ a, a < 8 → ∀ b, b < 8 →
      (BitVec.ofNat 64 (a ^^^ b) != 0#64) = decide (a ≠ b) := by decide
  rw [e, key _ (Nat.mod_lt s (by decide)) _ (Nat.mod_lt d (by decide))]

/-- The `n < 8` test (`sltiu a2, a2, 8`). -/
theorem sltiu8 (n : Nat) (hn : n < 2 ^ 64) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u (BitVec.ofNat 64 n) (sign_extend (m := 64) (8#12))))
      = if n < 8 then 1#64 else 0#64 := by
  rw [sltu_val, show (sign_extend (m := 64) (8#12) : BitVec 64) = BitVec.ofNat 64 8 from by decide]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.reducePow, Nat.reduceMod]

/-- The block-loop test `blt 64, e - x`. -/
theorem blt64 (e x : Nat) (hx : x ≤ e) (he : e < 2 ^ 63) :
    zopz0zI_s (BitVec.ofNat 64 64) (BitVec.ofNat 64 e - BitVec.ofNat 64 x) = decide (64 < e - x) := by
  rw [ofNat_sub_ofNat _ _ hx (by omega), blt_ofNat _ _ (by decide) (by omega)]

/-- The word loop's exit: `(e - 1 - x) & -8 = e - x - 8` when `8 ∣ e - x > 0`. -/
theorem wexit (e x : Nat) (hx : x < e) (he : e < 2 ^ 64) (h8 : (e - x) % 8 = 0) :
    (BitVec.ofNat 64 e + 18446744073709551615#64 - BitVec.ofNat 64 x) &&& 18446744073709551608#64 =
      BitVec.ofNat 64 (e - x - 8) := by
  have h1 : BitVec.ofNat 64 e + 18446744073709551615#64 - BitVec.ofNat 64 x =
      BitVec.ofNat 64 (e - 1 - x) := by
    apply BitVec.eq_of_toNat_eq
    simp only [Tom.Machine.toNat_add', Tom.Machine.toNat_sub', Tom.Machine.toNat_ofNat']
    omega
  rw [h1, andm8_ofNat _ (by omega)]
  exact ofNat_eq_ofNat (by omega)

/-- One leaf of a `memcpy` segment: `leaf_auto`, or an `lbu`'s pin (`rd1`). -/
syntax "cp_leaf" " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| cp_leaf [$ds,*] [$es,*]) => `(tactic|
      first
      | leaf_auto [$ds,*] [$es,*]
      | (leaf_nf [$ds,*]
         try simp only [Tom.Machine.ofNat_add_ofNat, Tom.Machine.toNat_ofNat_add, Tom.Machine.toNat_ofNat']
         simp only [Vsa.Sim.tohostAddr]
         refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
         first
         | exact Tom.Machine.lbu_pin (by omega)
         | (refine Tom.Machine.lbu_pin_frame (by omega) ?_
            code_frame [$ds,*]))
      | (leaf_nf [$ds,*]
         try simp only [$es,*]
         simp (disch := omega) only [BitVec.zero_add, Tom.Machine.ofNat_add_ofNat,
           Tom.Machine.Fn.Memcpy.and7_ofNat, Tom.Machine.Fn.Memcpy.andm8_ofNat,
           Tom.Machine.Fn.Memcpy.blt64, Tom.Machine.bltu_ofNat', Tom.Machine.bgeu_ofNat',
           Tom.Machine.ofNat_beq', bne, decide_eq_true_eq, decide_eq_false_iff_not,
           Bool.not_eq_true', Bool.not_eq_false', beq_self_eq_true, Bool.not_true]
         all_goals omega))

/-- `seg_step` with `cp_leaf` for the leaves (`cp_step`), and for a segment
without stores, the post memory the entry's (`cp_step0`). -/
syntax "cp_step " term:max ppSpace term:max ppSpace term:max ppSpace term:max ppSpace term:max
  " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term:max : tactic
syntax "cp_step0 " term:max ppSpace term:max ppSpace term:max ppSpace term:max ppSpace term:max
  " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term:max : tactic

/-- The four goals of `seg_at'`. -/
syntax "cp_goals " term:max " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term:max : tactic
macro_rules
  | `(tactic| cp_goals $_bs [$l1,*] [$l2,*] [$ds,*] [$_ps,*] [$es,*] $hc) => `(tactic|
      (· tom_facts $hc
         all_goals cp_leaf [$ds,*] [$es,*]
       · seg_nfo [$l1,*]
         try (try val_nf [$es,*]
              exact Tom.Machine.ret_target' _ (by assumption))
       · sub_auto [$l2,*] [$es,*]
         try (repeat' (apply And.intro)
              all_goals first | exact True.intro | omega | bv_nat | rfl)
       · seg_nfo [$l1,*]
         try val_nf [$es,*]
         try simp only [Tom.Machine.rd1, List.getD_cons_zero, Tom.Machine.ldb]
         try (repeat' (apply And.intro)
              all_goals first | exact True.intro | omega | bv_nat | rfl)))
macro_rules
  | `(tactic| cp_step $bs $pc $lds $ks $kk [$ds,*] [$ps,*] [$es,*] $hc) => do
      let b ← `(Lean.Parser.Tactic.simpLemma| $bs:term)
      let l1 : Array (Lean.TSyntax ``Lean.Parser.Tactic.simpLemma) := #[b] ++ ds.getElems
      let l2 := l1 ++ ps.getElems
      `(tactic|
        (refine Tom.Machine.seg_at' $bs (pc1 := $pc) $lds $ks $kk ?_ ?_ ?_ ?_
         cp_goals $bs [$l1,*] [$l2,*] [$ds,*] [$ps,*] [$es,*] $hc))
macro_rules
  | `(tactic| cp_step0 $bs $pc $lds $ks $kk [$ds,*] [$ps,*] [$es,*] $hc) => do
      let b ← `(Lean.Parser.Tactic.simpLemma| $bs:term)
      let l1 : Array (Lean.TSyntax ``Lean.Parser.Tactic.simpLemma) := #[b] ++ ds.getElems
      let l2 := l1 ++ ps.getElems
      `(tactic|
        (refine Tom.Machine.seg_at' $bs (pc1 := $pc) (lg := []) $lds $ks $kk ?_ ?_ ?_ ?_
         cp_goals $bs [$l1,*] [$l2,*] [$ds,*] [$ps,*] [$es,*] $hc))

/-! ## The byte loop -/

/-- Registers at `9500`, `9574`, `94a4`, `94f0`: `t` bytes copied. -/
def cur (ra : BitVec 64) (d s n t : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 d), (11, BitVec.ofNat 64 (s + t)), (14, BitVec.ofNat 64 (d + t)),
   (17, BitVec.ofNat 64 (d + n))]

/-- The registers `memcpy` returns with. -/
def retL (ra : BitVec 64) (d : Nat) : GRegs := [(1, ra), (10, BitVec.ofNat 64 d)]

/-- What every segment needs: the code, both ranges in RAM, the destination
off the code. -/
structure Room (M : Mem) (d s n : Nat) : Prop where
  code : CodeAt M memcpyBase memcpyCode
  rd : Ram d n
  rs : Ram s n
  disj : d + n ≤ s ∨ s + n ≤ d
  code_off : d + n ≤ memcpyBase ∨ memcpyBase + 296 ≤ d

macro "cp_ctx" : tactic => `(tactic|
  (facts_ctx
   have := code_len
   have := code_base))

/-- One byte, back to the loop head. -/
theorem bl_step (ra : BitVec 64) (d s n t : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (ht : t + 1 < n) :
    Triple (At 0x80009500#64 (cur ra d s n t) M w.keep outp)
      (At 0x80009500#64 (cur ra d s n (t + 1)) (writeLog M [(d + t, 1, ldb M (s + t))])
        w.keep outp) := by
  cp_ctx
  cp_step memcpyBL 0x80009500#64 [rd1 M (s + t)] [1, 10, 11, 14, 17] abiKeys [cur] [cur] [] hR.code

/-- The last byte, and `ret`. -/
theorem bx_step (ra : BitVec 64) (d s n t : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (ht : t + 1 = n) (hra : ra.toNat % 4 = 0) :
    Triple (At 0x80009500#64 (cur ra d s n t) M w.keep outp)
      (At ra (retL ra d) (writeLog M [(d + t, 1, ldb M (s + t))]) w.keep outp) := by
  cp_ctx
  cp_step memcpyBX ra [rd1 M (s + t)] [1, 10, 11, 14, 17] abiKeys [cur] [retL] [] hR.code

/-! ## The entry -/

/-- Registers at the entry: `ra`, `a0 = d`, `a1 = s`, `a2 = n`. -/
def entL (ra : BitVec 64) (d s n : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 d), (11, BitVec.ofNat 64 s), (12, BitVec.ofNat 64 n)]

/-- Registers at `94f8`, the byte path: `a7 = d + n`. -/
def smL (ra : BitVec 64) (d s n : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 d), (11, BitVec.ofNat 64 s), (17, BitVec.ofNat 64 (d + n))]

/-- Registers at the `sltiu` (`9490`). -/
def aL (ra : BitVec 64) (d s n : Nat) : GRegs :=
  [(12, BitVec.ofNat 64 n), (1, ra), (10, BitVec.ofNat 64 d), (11, BitVec.ofNat 64 s),
   (17, BitVec.ofNat 64 (d + n))]

/-- Registers after the `sltiu` (`9494`): `a2 = (n < 8)`. -/
def nL (ra : BitVec 64) (d s n : Nat) (b : BitVec 64) : GRegs :=
  [(12, b), (1, ra), (10, BitVec.ofNat 64 d), (11, BitVec.ofNat 64 s), (17, BitVec.ofNat 64 (d + n))]

/-- `s`, `d` misaligned to each other: to the byte path. -/
theorem x_step (ra : BitVec 64) (d s n : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (hal : s % 8 ≠ d % 8) :
    Triple (At 0x80009480#64 (entL ra d s n) M w.keep outp)
      (At 0x800094f8#64 (smL ra d s n) M w.keep outp) := by
  cp_ctx
  have hg : ((BitVec.ofNat 64 s ^^^ BitVec.ofNat 64 d) &&& 7#64 != 0#64) = true := by
    rw [xor7_bne _ _ (by omega) (by omega)]; simpa using hal
  cp_step0 memcpyX 0x800094f8#64 ([] : List (List (BitVec 8))) [1, 10, 11, 12] abiKeys [entL] [smL] [hg] hR.code

/-- `s`, `d` aligned to each other: to the `sltiu`. -/
theorem a_step (ra : BitVec 64) (d s n : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (hal : s % 8 = d % 8) :
    Triple (At 0x80009480#64 (entL ra d s n) M w.keep outp)
      (At 0x80009490#64 (aL ra d s n) M w.keep outp) := by
  cp_ctx
  have hg : ((BitVec.ofNat 64 s ^^^ BitVec.ofNat 64 d) &&& 7#64 != 0#64) = false := by
    rw [xor7_bne _ _ (by omega) (by omega)]; simpa using hal
  cp_step0 memcpyA 0x80009490#64 ([] : List (List (BitVec 8))) [1, 10, 11, 12] abiKeys [entL] [aL] [hg] hR.code

/-- The `sltiu a2, a2, 8` at `9490` (`Kit/Alu1.lean`). -/
theorem n8_step (ra : BitVec 64) (d s n : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) :
    Triple (At 0x80009490#64 (aL ra d s n) M w.keep outp)
      (At 0x80009494#64 (nL ra d s n (if n < 8 then 1#64 else 0#64)) M w.keep outp) := by
  have hn : n < 2 ^ 64 := by have := hR.rd.hi_le; omega
  have h := sltiu_at (pc := 0x80009490#64) (w := 0x00863613#32) (imm := 8#12) (rd := 12) (rs1 := 12)
    (L := aL ra d s n) (keep := w.keep) (outp := outp)
    (hR.code.word (a := (0x80009490#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
    (fun s h1 h2 h3 => decodeW s h1 h2 h3)
    ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩
    (by decide) (Or.inr (by simp [keysG, aL])) (by decide) (by simp [keysG, aL])
    (show ∀ n ∈ abiKeys, 1 ≤ n ∧ n ≤ 31 by decide) (show 12 ∉ abiKeys by decide)
  have hpc : Sail.BitVec.addInt (0x80009490#64 : BitVec 64) 4 = 0x80009494#64 := by decide
  rw [hpc, show srcVal 12 (aL ra d s n) = BitVec.ofNat 64 n from by simp [srcVal, lookupG, aL],
    sltiu8 n hn] at h
  exact Triple.rmap (fun _ h' => h'.reshape (by simp [aL, nL, eraseG]) (fun p hp => by simp [hp])) h

/-- `n < 8`: to the byte path. -/
theorem sb_step (ra : BitVec 64) (d s n : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) :
    Triple (At 0x80009494#64 (nL ra d s n 1#64) M w.keep outp)
      (At 0x800094f8#64 (smL ra d s n) M w.keep outp) := by
  cp_ctx
  cp_step0 memcpySB 0x800094f8#64 ([] : List (List (BitVec 8))) [12, 1, 10, 11, 17] abiKeys [nL] [smL] [] hR.code

/-- `n ≥ 8`, `d` unaligned: to the head. -/
theorem sh_step (ra : BitVec 64) (d s n : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (hd : d % 8 ≠ 0) :
    Triple (At 0x80009494#64 (nL ra d s n 0#64) M w.keep outp)
      (At 0x80009574#64 (cur ra d s n 0) M w.keep outp) := by
  cp_ctx
  have hg : (BitVec.ofNat 64 d &&& 7#64 != 0#64) = true := by
    rw [and7_ofNat, bne_zero_ofNat _ (by omega)]; simpa using hd
  cp_step0 memcpySH 0x80009574#64 ([] : List (List (BitVec 8))) [12, 1, 10, 11, 17] abiKeys [nL] [cur] [hg] hR.code

/-- `n ≥ 8`, `d` aligned: to the word setup. -/
theorem sg_step (ra : BitVec 64) (d s n : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (hd : d % 8 = 0) :
    Triple (At 0x80009494#64 (nL ra d s n 0#64) M w.keep outp)
      (At 0x800094a4#64 (cur ra d s n 0) M w.keep outp) := by
  cp_ctx
  have hg : (BitVec.ofNat 64 d &&& 7#64 != 0#64) = false := by
    rw [and7_ofNat, bne_zero_ofNat _ (by omega)]; simpa using hd
  cp_step0 memcpySG 0x800094a4#64 ([] : List (List (BitVec 8))) [12, 1, 10, 11, 17] abiKeys [nL] [cur] [hg] hR.code

/-- The byte path with `n = 0`: `ret`. -/
theorem b0_step (ra : BitVec 64) (d s : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s 0) (hra : ra.toNat % 4 = 0) :
    Triple (At 0x800094f8#64 (smL ra d s 0) M w.keep outp) (At ra (retL ra d) M w.keep outp) := by
  cp_ctx
  cp_step0 memcpyB0 ra ([] : List (List (BitVec 8))) [1, 10, 11, 17] abiKeys [smL] [retL] [] hR.code

/-- The byte path with `n > 0`: to the byte loop. -/
theorem b1_step (ra : BitVec 64) (d s n : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (hn : 0 < n) :
    Triple (At 0x800094f8#64 (smL ra d s n) M w.keep outp)
      (At 0x80009500#64 (cur ra d s n 0) M w.keep outp) := by
  cp_ctx
  cp_step0 memcpyB1 0x80009500#64 ([] : List (List (BitVec 8))) [1, 10, 11, 17] abiKeys [smL] [cur] [] hR.code

/-! ## The exit test (`94f0`) -/

theorem j1_step (ra : BitVec 64) (d s n t : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (ht : t < n) :
    Triple (At 0x800094f0#64 (cur ra d s n t) M w.keep outp)
      (At 0x80009500#64 (cur ra d s n t) M w.keep outp) := by
  cp_ctx
  cp_step0 memcpyJ1 0x80009500#64 ([] : List (List (BitVec 8))) [1, 10, 11, 14, 17] abiKeys [cur] [cur] [] hR.code

theorem j0_step (ra : BitVec 64) (d s n : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (hra : ra.toNat % 4 = 0) :
    Triple (At 0x800094f0#64 (cur ra d s n n) M w.keep outp) (At ra (retL ra d) M w.keep outp) := by
  cp_ctx
  cp_step0 memcpyJ0 ra ([] : List (List (BitVec 8))) [1, 10, 11, 14, 17] abiKeys [cur] [retL] [] hR.code

/-! ## The head: bytes up to an 8-aligned `d + t` -/

/-- One byte, `d + t + 1` aligned: to the word setup. -/
theorem h1_step (ra : BitVec 64) (d s n t : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (ht : t + 1 ≤ n) (ha : (d + t + 1) % 8 = 0) :
    Triple (At 0x80009574#64 (cur ra d s n t) M w.keep outp)
      (At 0x800094a4#64 (cur ra d s n (t + 1)) (writeLog M [(d + t, 1, ldb M (s + t))])
        w.keep outp) := by
  cp_ctx
  cp_step memcpyH1 0x800094a4#64 [rd1 M (s + t)] [1, 10, 11, 14, 17] abiKeys [cur] [cur] [] hR.code

/-- Two bytes, `d + t + 2` aligned: to the word setup. -/
theorem h2_step (ra : BitVec 64) (d s n t : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (ht : t + 2 ≤ n) (ha : (d + t + 2) % 8 = 0) :
    Triple (At 0x80009574#64 (cur ra d s n t) M w.keep outp)
      (At 0x800094a4#64 (cur ra d s n (t + 2))
        (writeLog M [(d + t, 1, ldb M (s + t)), (d + t + 1, 1, ldb M (s + t + 1))]) w.keep outp) := by
  cp_ctx
  cp_step memcpyH2 0x800094a4#64 [rd1 M (s + t), rd1 M (s + t + 1)] [1, 10, 11, 14, 17] abiKeys
    [cur] [cur] [] hR.code

/-- Two bytes, `d + t + 2` unaligned: back to the head. -/
theorem h3_step (ra : BitVec 64) (d s n t : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (ht : t + 2 ≤ n) (ha1 : (d + t + 1) % 8 ≠ 0) (ha : (d + t + 2) % 8 ≠ 0) :
    Triple (At 0x80009574#64 (cur ra d s n t) M w.keep outp)
      (At 0x80009574#64 (cur ra d s n (t + 2))
        (writeLog M [(d + t, 1, ldb M (s + t)), (d + t + 1, 1, ldb M (s + t + 1))]) w.keep outp) := by
  cp_ctx
  cp_step memcpyH3 0x80009574#64 [rd1 M (s + t), rd1 M (s + t + 1)] [1, 10, 11, 14, 17] abiKeys
    [cur] [cur] [] hR.code

/-! ## The word setup (`94a4`) and the 72-byte blocks (`9518`) -/

/-- Registers at `94b4`: `a2 = e`, the 8-aligned end `d + n - (d + n) % 8`. -/
def fL (ra : BitVec 64) (d s n q : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 d), (11, BitVec.ofNat 64 (s + q)), (14, BitVec.ofNat 64 (d + q)),
   (17, BitVec.ofNat 64 (d + n)), (12, BitVec.ofNat 64 (d + n - (d + n) % 8))]

/-- Registers at the block loop head `9518`: `a3 = e - a4`, `a5 = 64`. -/
def bigL (ra : BitVec 64) (d s n q : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 d), (11, BitVec.ofNat 64 (s + q)), (14, BitVec.ofNat 64 (d + q)),
   (17, BitVec.ofNat 64 (d + n)), (12, BitVec.ofNat 64 (d + n - (d + n) % 8)),
   (13, BitVec.ofNat 64 (d + n - (d + n) % 8 - (d + q))), (15, 64#64)]

/-- Registers at the word loop head `94c0`: `a1`, `a4` at the loop's start
`q0`, the cursors `a3 = s + q`, `a5 = d + q`. -/
def wL (ra : BitVec 64) (d s n q0 q : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 d), (11, BitVec.ofNat 64 (s + q0)), (14, BitVec.ofNat 64 (d + q0)),
   (17, BitVec.ofNat 64 (d + n)), (12, BitVec.ofNat 64 (d + n - (d + n) % 8)),
   (13, BitVec.ofNat 64 (s + q)), (15, BitVec.ofNat 64 (d + q))]

/-- The doubleword at `s + q + k` of the block's entry memory `M0`. -/
abbrev bv (M0 : Mem) (s q k : Nat) : BitVec 64 := bytesT8 M0 (s + q + k)

/-- Registers at `9538`: the block's first eight doublewords loaded. -/
def bk1L (ra : BitVec 64) (d s n q : Nat) (M0 : Mem) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 d), (11, BitVec.ofNat 64 (s + q)), (14, BitVec.ofNat 64 (d + q)),
   (17, BitVec.ofNat 64 (d + n)), (12, BitVec.ofNat 64 (d + n - (d + n) % 8)), (15, 64#64),
   (13, bv M0 s q 0), (5, bv M0 s q 8), (31, bv M0 s q 16), (30, bv M0 s q 24), (29, bv M0 s q 32),
   (28, bv M0 s q 40), (6, bv M0 s q 48), (16, bv M0 s q 56)]

/-- Registers at `9544`: `a4` past the block, the ninth doubleword in `a3`. -/
def bk2aL (ra : BitVec 64) (d s n q : Nat) (M0 : Mem) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 d), (11, BitVec.ofNat 64 (s + q)),
   (14, BitVec.ofNat 64 (d + q + 72)), (17, BitVec.ofNat 64 (d + n)),
   (12, BitVec.ofNat 64 (d + n - (d + n) % 8)), (15, 64#64), (13, bv M0 s q 64), (5, bv M0 s q 8),
   (31, bv M0 s q 16), (30, bv M0 s q 24), (29, bv M0 s q 32), (28, bv M0 s q 40), (6, bv M0 s q 48),
   (16, bv M0 s q 56)]

/-- Registers at `9550`. -/
def bk2L (ra : BitVec 64) (d s n q : Nat) (M0 : Mem) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 d), (11, BitVec.ofNat 64 (s + q)),
   (14, BitVec.ofNat 64 (d + q + 72)), (17, BitVec.ofNat 64 (d + n)),
   (12, BitVec.ofNat 64 (d + n - (d + n) % 8)), (15, 64#64),
   (30, bv M0 s q 24), (29, bv M0 s q 32), (28, bv M0 s q 40), (6, bv M0 s q 48), (16, bv M0 s q 56)]

/-- Registers at `955c`: `a3 = e - a4`. -/
def bk3L (ra : BitVec 64) (d s n q : Nat) (M0 : Mem) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 d), (11, BitVec.ofNat 64 (s + q)),
   (14, BitVec.ofNat 64 (d + q + 72)), (17, BitVec.ofNat 64 (d + n)),
   (12, BitVec.ofNat 64 (d + n - (d + n) % 8)), (15, 64#64),
   (13, BitVec.ofNat 64 (d + n - (d + n) % 8 - (d + q + 72))),
   (28, bv M0 s q 40), (6, bv M0 s q 48), (16, bv M0 s q 56)]

/-- Registers at `9568`. -/
def bk4L (ra : BitVec 64) (d s n q : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 d), (11, BitVec.ofNat 64 (s + q)),
   (14, BitVec.ofNat 64 (d + q + 72)), (17, BitVec.ofNat 64 (d + n)),
   (12, BitVec.ofNat 64 (d + n - (d + n) % 8)), (15, 64#64),
   (13, BitVec.ofNat 64 (d + n - (d + n) % 8 - (d + q + 72)))]

/-- More than 64 bytes of words: to the block loop. -/
theorem gb_step (ra : BitVec 64) (d s n q : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (hq : q ≤ n) (ha : (d + q) % 8 = 0)
    (hb : 64 < d + n - (d + n) % 8 - (d + q)) :
    Triple (At 0x800094a4#64 (cur ra d s n q) M w.keep outp)
      (At 0x80009518#64 (bigL ra d s n q) M w.keep outp) := by
  cp_ctx
  have hE : BitVec.ofNat 64 (d + n) &&& 18446744073709551608#64 =
      BitVec.ofNat 64 (d + n - (d + n) % 8) := andm8_ofNat _ (by omega)
  cp_step0 memcpyGB 0x80009518#64 ([] : List (List (BitVec 8))) [1, 10, 11, 14, 17] abiKeys [cur]
    [bigL] [hE] hR.code

/-- At most 64 bytes of words: to the word loop's test. -/
theorem gf_step (ra : BitVec 64) (d s n q : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (hq : q ≤ n) (ha : (d + q) % 8 = 0)
    (hb : d + n - (d + n) % 8 - (d + q) ≤ 64) :
    Triple (At 0x800094a4#64 (cur ra d s n q) M w.keep outp)
      (At 0x800094b4#64 (fL ra d s n q) M w.keep outp) := by
  cp_ctx
  have hE : BitVec.ofNat 64 (d + n) &&& 18446744073709551608#64 =
      BitVec.ofNat 64 (d + n - (d + n) % 8) := andm8_ofNat _ (by omega)
  cp_step0 memcpyGF 0x800094b4#64 ([] : List (List (BitVec 8))) [1, 10, 11, 14, 17] abiKeys [cur]
    [fL] [hE] hR.code

/-- The block's eight loads. -/
theorem big1_step (ra : BitVec 64) (d s n q : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (hb : 64 < d + n - (d + n) % 8 - (d + q)) :
    Triple (At 0x80009518#64 (bigL ra d s n q) M w.keep outp)
      (At 0x80009538#64 (bk1L ra d s n q M) M w.keep outp) := by
  cp_ctx
  cp_step0 memcpyBig1 0x80009538#64 [rd8 M (s + q), rd8 M (s + q + 8), rd8 M (s + q + 16),
    rd8 M (s + q + 24), rd8 M (s + q + 32), rd8 M (s + q + 40), rd8 M (s + q + 48), rd8 M (s + q + 56)]
    [1, 10, 11, 14, 17, 12, 13, 15] abiKeys [bigL] [bk1L] [] hR.code

/-- The first store and the ninth load. -/
theorem big2a_step (ra : BitVec 64) (d s n q : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (ha : (d + q) % 8 = 0) (hb : 64 < d + n - (d + n) % 8 - (d + q)) :
    Triple (At 0x80009538#64 (bk1L ra d s n q M) M w.keep outp)
      (At 0x80009544#64 (bk2aL ra d s n q M) (writeLog M [(d + q, 8, bv M s q 0)]) w.keep outp) := by
  cp_ctx
  cp_step memcpyBig2a 0x80009544#64 [rd8 M (s + q + 64)]
    [1, 10, 11, 14, 17, 12, 15, 13, 5, 31, 30, 29, 28, 6, 16] abiKeys [bk1L] [bk2aL] [] hR.code

/-- Three stores. -/
theorem big2b_step (ra : BitVec 64) (d s n q : Nat) (w : Abi) (outp : Array String) (M0 M : Mem)
    (hR : Room M d s n) (ha : (d + q) % 8 = 0) (hb : 64 < d + n - (d + n) % 8 - (d + q)) :
    Triple (At 0x80009544#64 (bk2aL ra d s n q M0) M w.keep outp)
      (At 0x80009550#64 (bk2L ra d s n q M0)
        (writeLog M [(d + q + 8, 8, bv M0 s q 8), (d + q + 64, 8, bv M0 s q 64),
          (d + q + 16, 8, bv M0 s q 16)]) w.keep outp) := by
  cp_ctx
  cp_step memcpyBig2b 0x80009550#64 ([] : List (List (BitVec 8)))
    [1, 10, 11, 14, 17, 12, 15, 13, 5, 31, 30, 29, 28, 6, 16] abiKeys [bk2aL] [bk2L] [] hR.code

/-- `a3 := e - a4`, two stores. -/
theorem big3a_step (ra : BitVec 64) (d s n q : Nat) (w : Abi) (outp : Array String) (M0 M : Mem)
    (hR : Room M d s n) (ha : (d + q) % 8 = 0) (hb : 64 < d + n - (d + n) % 8 - (d + q)) :
    Triple (At 0x80009550#64 (bk2L ra d s n q M0) M w.keep outp)
      (At 0x8000955c#64 (bk3L ra d s n q M0)
        (writeLog M [(d + q + 24, 8, bv M0 s q 24), (d + q + 32, 8, bv M0 s q 32)]) w.keep outp) := by
  cp_ctx
  cp_step memcpyBig3a 0x8000955c#64 ([] : List (List (BitVec 8)))
    [1, 10, 11, 14, 17, 12, 15, 30, 29, 28, 6, 16] abiKeys [bk2L] [bk3L] [] hR.code

/-- The last three stores. -/
theorem big3b_step (ra : BitVec 64) (d s n q : Nat) (w : Abi) (outp : Array String) (M0 M : Mem)
    (hR : Room M d s n) (ha : (d + q) % 8 = 0) (hb : 64 < d + n - (d + n) % 8 - (d + q)) :
    Triple (At 0x8000955c#64 (bk3L ra d s n q M0) M w.keep outp)
      (At 0x80009568#64 (bk4L ra d s n q)
        (writeLog M [(d + q + 40, 8, bv M0 s q 40), (d + q + 48, 8, bv M0 s q 48),
          (d + q + 56, 8, bv M0 s q 56)]) w.keep outp) := by
  cp_ctx
  cp_step memcpyBig3b 0x80009568#64 ([] : List (List (BitVec 8)))
    [1, 10, 11, 14, 17, 12, 15, 13, 28, 6, 16] abiKeys [bk3L] [bk4L] [] hR.code

/-- More than 64 bytes left: back to the block loop. -/
theorem big3c_step (ra : BitVec 64) (d s n q : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (hb : 64 < d + n - (d + n) % 8 - (d + q + 72)) :
    Triple (At 0x80009568#64 (bk4L ra d s n q) M w.keep outp)
      (At 0x80009518#64 (bigL ra d s n (q + 72)) M w.keep outp) := by
  cp_ctx
  cp_step0 memcpyBig3c 0x80009518#64 ([] : List (List (BitVec 8)))
    [1, 10, 11, 14, 17, 12, 15, 13] abiKeys [bk4L] [bigL] [] hR.code

/-- At most 64 bytes left: on to the word loop's test. -/
theorem big3cx_step (ra : BitVec 64) (d s n q : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (hb : d + n - (d + n) % 8 - (d + q + 72) ≤ 64) :
    Triple (At 0x80009568#64 (bk4L ra d s n q) M w.keep outp)
      (At 0x800094b4#64 (fL ra d s n (q + 72)) M w.keep outp) := by
  cp_ctx
  cp_step0 memcpyBig3cX 0x800094b4#64 ([] : List (List (BitVec 8)))
    [1, 10, 11, 14, 17, 12, 15, 13] abiKeys [bk4L] [fL] [] hR.code

/-! ## The word loop (`94c0`) -/

/-- Words left: to the word loop. -/
theorem fw_step (ra : BitVec 64) (d s n q : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (hq : d + q < d + n - (d + n) % 8) :
    Triple (At 0x800094b4#64 (fL ra d s n q) M w.keep outp)
      (At 0x800094c0#64 (wL ra d s n q q) M w.keep outp) := by
  cp_ctx
  cp_step0 memcpyFW 0x800094c0#64 ([] : List (List (BitVec 8))) [1, 10, 11, 14, 17, 12] abiKeys [fL]
    [wL] [] hR.code

/-- No words left: to the exit test. -/
theorem fn_step (ra : BitVec 64) (d s n q : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (hq : d + q = d + n - (d + n) % 8) :
    Triple (At 0x800094b4#64 (fL ra d s n q) M w.keep outp)
      (At 0x800094f0#64 (cur ra d s n q) M w.keep outp) := by
  cp_ctx
  cp_step0 memcpyFN 0x800094f0#64 ([] : List (List (BitVec 8))) [1, 10, 11, 14, 17, 12] abiKeys [fL]
    [cur] [] hR.code

/-- One word, back to the loop head. -/
theorem wl_step (ra : BitVec 64) (d s n q0 q : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (ha : (d + q) % 8 = 0) (hq : d + q + 8 < d + n - (d + n) % 8) :
    Triple (At 0x800094c0#64 (wL ra d s n q0 q) M w.keep outp)
      (At 0x800094c0#64 (wL ra d s n q0 (q + 8)) (writeLog M [(d + q, 8, bytesT8 M (s + q))])
        w.keep outp) := by
  cp_ctx
  cp_step memcpyWL 0x800094c0#64 [rd8 M (s + q)] [1, 10, 11, 14, 17, 12, 13, 15] abiKeys [wL] [wL] []
    hR.code

/-- The last word. -/
theorem wx_step (ra : BitVec 64) (d s n q0 q : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (ha : (d + q) % 8 = 0) (hq : d + q + 8 = d + n - (d + n) % 8) :
    Triple (At 0x800094c0#64 (wL ra d s n q0 q) M w.keep outp)
      (At 0x800094d4#64 (wL ra d s n q0 (q + 8)) (writeLog M [(d + q, 8, bytesT8 M (s + q))])
        w.keep outp) := by
  cp_ctx
  cp_step memcpyWX 0x800094d4#64 [rd8 M (s + q)] [1, 10, 11, 14, 17, 12, 13, 15] abiKeys [wL] [wL] []
    hR.code

/-- After the words: the cursors to the 8-aligned end `e`, on to the exit test. -/
theorem we_step (ra : BitVec 64) (d s n q0 q : Nat) (w : Abi) (outp : Array String) (M : Mem)
    (hR : Room M d s n) (ha0 : (d + q0) % 8 = 0) (hq0 : d + q0 < d + n - (d + n) % 8) :
    Triple (At 0x800094d4#64 (wL ra d s n q0 q) M w.keep outp)
      (At 0x800094f0#64 (cur ra d s n (d + n - (d + n) % 8 - d)) M w.keep outp) := by
  cp_ctx
  refine Tom.Machine.seg_at' memcpyWE (pc1 := 0x800094f0#64) (lg := []) ([] : List (List (BitVec 8)))
    [1, 10, 11, 14, 17, 12, 13, 15] abiKeys ?_ ?_ ?_ ?_
  · tom_facts hR.code
  · seg_nfo [memcpyWE, wL]
  · simp only [memcpyWE, wL, cur, SubL]
    seg_nfo [memcpyWE, wL, cur]
    simp only [Option.some.injEq]
    have hw := wexit (d + n - (d + n) % 8) (d + q0) hq0 (by omega) (by omega)
    rw [hw, ofNat_add_ofNat, ofNat_add_ofNat, ofNat_add_ofNat, ofNat_add_ofNat]
    exact ⟨ofNat_eq_ofNat (by omega), ofNat_eq_ofNat (by omega)⟩
  · seg_nfo [memcpyWE, wL]

end Tom.Machine.Fn.Memcpy
