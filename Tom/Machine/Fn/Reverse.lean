import Tom.Machine.Seg.Reverse
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Word
import Vsa.Sim.TripleCat

/-!
# `s_mp_reverse` on the machine: the segments

`s_mp_reverse(s, len)` at `0x80004528` (15 instructions, no frame):
```
4528 addi a2,a1,-1; beqz a2,4560                         -- len == 1: nothing to do
4530 addi a5,a0,-1; add a1,a5,a1; li a5,0                -- a1 = s + len - 1, ix = 0
453c lbu a3,0(a1); lbu a4,0(a0); addi a5,a5,1; sb a3,0(a0); sb a4,0(a1)   -- loop head
4550 sub a4,a2,a5; addi a0,a0,1; addi a1,a1,-1; bltu a5,a4,453c
4560 ret
```
At the loop head at `ix = k`: `a0 = s + k`, `a1 = s + len - 1 - k`, `a2 = len - 1`.
The byte loads are closed by `lbu_leaf` (`leaf_auto` has the word loads only).
-/


namespace Tom.Machine.Fn.Reverse

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "rv_ctx" : tactic => `(tactic|
  (facts_ctx
   have : sMpReverseBase = 0x80004528 := rfl
   have : sMpReverseCode.length = 15 := rfl))

/-- A byte load's pins from the segment's entry memory `M0`. -/
theorem lpins1_frame {m M0 : Mem} {ea a : Nat} (hea : ea = a)
    (h : ∀ x, a ≤ x → x < a + 1 → m[x]? = M0[x]?) : (m[ea]?).getD 0 = [(M0[a]?).getD 0].getD 0 0#8 := by
  subst hea; rw [h ea (by omega) (by omega)]; rfl

def entryL (ra : BitVec 64) (s n : Nat) : GRegs := [(1, ra), (10, BitVec.ofNat 64 s), (11, BitVec.ofNat 64 n)]

/-- The loop head at `ix = k`. -/
def headL (ra : BitVec 64) (s n k : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 (s + k)), (11, BitVec.ofNat 64 (s + (n - 1 - k))), (12, BitVec.ofNat 64 (n - 1)),
   (15, BitVec.ofNat 64 k)]

/-- The two byte stores of iteration `k`. -/
def swapLog (M : Mem) (s n k : Nat) : List WEntry :=
  [(s + k, 1, zero_extend (m := 64) ((M[s + (n - 1 - k)]?).getD 0)),
   (s + (n - 1 - k), 1, zero_extend (m := 64) ((M[s + k]?).getD 0))]

/-- The array: in RAM, off the code. -/
structure AFacts (s n : Nat) : Prop where
  rs : Ram s n
  n_pos : 1 ≤ n
  code_off : s + n ≤ sMpReverseBase ∨ sMpReverseBase + 60 ≤ s

section
variable (ra : BitVec 64) (v : Abi) (outp : Array String) (s n : Nat) (hf : AFacts s n)
include hf

theorem one_step (m : Mem) (hc : CodeAt m sMpReverseBase sMpReverseCode) (hra : ra.toNat % 4 = 0) (hn : n = 1) :
    Triple (At 0x80004528#64 (entryL ra s n) m v.keep outp) (At ra [(1, ra)] (writeLog m []) v.keep outp) := by
  rv_ctx
  seg_step rvOne ra ([] : List (List (BitVec 8))) [1, 10, 11] abiKeys [entryL] [] [] hc

theorem enter_step (m : Mem) (hc : CodeAt m sMpReverseBase sMpReverseCode) (hn : 2 ≤ n) :
    Triple (At 0x80004528#64 (entryL ra s n) m v.keep outp) (At 0x8000453c#64 (headL ra s n 0) (writeLog m []) v.keep outp) := by
  rv_ctx
  seg_step rvEnter 0x8000453c#64 ([] : List (List (BitVec 8))) [1, 10, 11] abiKeys [entryL] [headL] [] hc

theorem next_step (M : Mem) (hc : CodeAt M sMpReverseBase sMpReverseCode) (k : Nat) (hk : k < n - 1 - k)
    (hk1 : k + 1 < n - 1 - (k + 1)) :
    Triple (At 0x8000453c#64 (headL ra s n k) M v.keep outp)
      (At 0x8000453c#64 (headL ra s n (k + 1)) (writeLog M (swapLog M s n k)) v.keep outp) := by
  rv_ctx
  refine Tom.Machine.seg_at' rvNext (pc1 := 0x8000453c#64) [[(M[s + (n - 1 - k)]?).getD 0], [(M[s + k]?).getD 0]]
    [1, 10, 11, 12, 15] abiKeys ?_ ?_ ?_ ?_
  · tom_facts hc
    all_goals first | (leaf_auto [headL] []; done) |
      (leaf_nf [headL]
       simp only [Vsa.Sim.tohostAddr]
       refine ⟨⟨by omega, by omega, by omega⟩, lpins1_frame (by omega) ?_⟩
       first | exact fun _ _ _ => rfl | code_frame [headL])
  · seg_nfo [rvNext, headL]
  · sub_auto [rvNext, headL] []
  · seg_nfo [rvNext, headL]
    try val_nf []
    try regs_close
    all_goals simp only [swapLog, List.getD_cons_zero, Nat.mod_eq_of_lt (show s + k < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (show s + (n - 1 - k) < 18446744073709551616 by omega)]

theorem exit_step (M : Mem) (hc : CodeAt M sMpReverseBase sMpReverseCode) (hra : ra.toNat % 4 = 0) (k : Nat)
    (hk : k < n - 1 - k) (hk1 : ¬ k + 1 < n - 1 - (k + 1)) :
    Triple (At 0x8000453c#64 (headL ra s n k) M v.keep outp)
      (At ra [(1, ra)] (writeLog M (swapLog M s n k)) v.keep outp) := by
  rv_ctx
  refine Tom.Machine.seg_at' rvExit (pc1 := ra) [[(M[s + (n - 1 - k)]?).getD 0], [(M[s + k]?).getD 0]]
    [1, 10, 11, 12, 15] abiKeys ?_ ?_ ?_ ?_
  · tom_facts hc
    all_goals first | (leaf_auto [headL] []; done) |
      (leaf_nf [headL]
       simp only [Vsa.Sim.tohostAddr]
       refine ⟨⟨by omega, by omega, by omega⟩, lpins1_frame (by omega) ?_⟩
       first | exact fun _ _ _ => rfl | code_frame [headL])
  · seg_nfo [rvExit, headL]
    exact Tom.Machine.ret_target' _ hra
  · sub_auto [rvExit, headL] []
  · seg_nfo [rvExit, headL]
    try val_nf []
    try regs_close
    all_goals simp only [swapLog, List.getD_cons_zero, Nat.mod_eq_of_lt (show s + k < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (show s + (n - 1 - k) < 18446744073709551616 by omega)]

end

end Tom.Machine.Fn.Reverse
