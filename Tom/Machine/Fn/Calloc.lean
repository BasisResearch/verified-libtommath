import Tom.Machine.Seg.Calloc
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Jal
import Tom.Machine.Kit.Alu1
import Vsa.Sim.TripleCat

/-!
# `calloc(n, sz)` on the machine: the segments

`calloc` (`0x8000777c`, 5 instructions) loads `_impure_ptr` and jumps to
`_calloc_r(reent, n, sz)` (`0x80007790`, 102 instructions). On the path
`n, sz < 2 ^ 32` (`srai`/`srli` by 32 give zero) it saves `s0`/`ra`, calls
`__muldi3(n, sz)` (`7c4`) and `_malloc_r(reent, n * sz)` (`7d0`); on NULL it
returns 0 (`callocN`); otherwise it reads the chunk header at `p - 8`, computes
the capacity `cap = (hdr & ~3) - 8` and zeroes `[p, p + cap)`: inline for
`cap ∈ {24, 40, 56, 72}` (`callocZ*`), by `memset(p, 0, cap)` beyond
(`callocS`, `callocT`).
-/


namespace Tom.Machine.Fn.Calloc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

/-- `__global_pointer$`. -/
abbrev gpv : BitVec 64 := 0x80019090#64
/-- `&_impure_data`. -/
abbrev reent : BitVec 64 := 0x800190c8#64

macro "calloc_ctx" : tactic => `(tactic|
  (facts_ctx
   have : callocBase = 0x8000777c := rfl
   have : callocCode.length = 5 := rfl
   have : callocRBase = 0x80007790 := rfl
   have : callocRCode.length = 102 := rfl))

/-- `seg_step` whose write log is closed by address arithmetic (`omega`). -/
syntax "cseg " term:max ppSpace term:max ppSpace term:max ppSpace term:max ppSpace term:max
  " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term:max : tactic
macro_rules
  | `(tactic| cseg $bs $pc $lds $ks $kk [$ds,*] [$ps,*] [$es,*] $hc) => do
      let b ← `(Lean.Parser.Tactic.simpLemma| $bs:term)
      let l1 : Array (Lean.TSyntax ``Lean.Parser.Tactic.simpLemma) := #[b] ++ ds.getElems
      let l2 := l1 ++ ps.getElems
      `(tactic|
        (refine Tom.Machine.seg_at' $bs (pc1 := $pc) $lds $ks $kk ?_ ?_ ?_ ?_
         · tom_facts $hc
           all_goals leaf_auto [$ds,*] [$es,*]
         · seg_nfo [$l1,*]
           try (try val_nf [$es,*]
                exact Tom.Machine.ret_target' _ (by assumption))
         · sub_auto [$l2,*] [$es,*]
         · seg_nfo [$l1,*]
           try val_nf [$es,*]
           first
           | regs_close
           | (simp only [$ps,*, List.cons.injEq, Prod.mk.injEq, and_true, List.nil_append,
                List.cons_append]
              omega)))

/-- At `calloc`'s entry (`sp`, `gp`, `s0` carried). -/
def wL (ra s0 : BitVec 64) (sp n sz : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (3, gpv), (8, s0), (10, BitVec.ofNat 64 n), (11, BitVec.ofNat 64 sz)]

/-- At `_calloc_r`'s entry. -/
def rL (ra s0 : BitVec 64) (sp n sz : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (3, gpv), (8, s0), (10, reent), (11, BitVec.ofNat 64 n),
   (12, BitVec.ofNat 64 sz)]

/-- `calloc`: `_impure_ptr`, then `j _calloc_r`. -/
theorem w_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp n sz : Nat) (m : Mem)
    (hc : CodeAt m callocBase callocCode) (himp : bytesT8 m 0x80019510 = reent) :
    Triple (At 0x8000777c#64 (wL ra s0 sp n sz) m v.keepR outp)
      (At 0x80007790#64 (rL ra s0 sp n sz) m v.keepR outp) := by
  refine Triple.rmap (Q := At 0x80007790#64 (rL ra s0 sp n sz) (writeLog m []) v.keepR outp) (fun c h => by rw [writeLog_nil] at h; exact h) ?_
  calloc_ctx
  seg_step callocW 0x80007790#64 [rd8 m 0x80019510] [1, 2, 3, 8, 10, 11] abiKeysR
    [wL] [rL] [himp] hc

theorem sra32 (n : Nat) (hn : n < 2 ^ 32) :
    shift_bits_right_arith (BitVec.ofNat 64 n) (32#6) = 0#64 := by
  unfold shift_bits_right_arith
  have hm : (BitVec.ofNat 64 n).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat]; omega
  rw [BitVec.sshiftRight_eq_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.toNatInt, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem srl32z (n : Nat) (hn : n < 2 ^ 32) :
    Sail.shift_bits_right (BitVec.ofNat 64 n) (32#6) = 0#64 := by
  rw [show (32#6 : BitVec 6) = BitVec.ofNat 6 32 from rfl, srl64_ofNat n 32 (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- At the `__muldi3` call (`7c4`): `a0 = n`, `a1 = sz` (zero-extended), the frame saved. -/
def pL (ra : BitVec 64) (sp n sz : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (3, gpv), (8, reent), (10, BitVec.ofNat 64 n),
   (11, BitVec.ofNat 64 sz)]

/-- The frame stores. -/
def pLog (ra s0 : BitVec 64) (sp : Nat) : List WEntry := [(sp - 16, 8, s0), (sp - 8, 8, ra)]

/-- `_calloc_r`'s prologue, `n, sz < 2 ^ 32`: the frame, the products' operands. -/
theorem p_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp n sz : Nat) (m : Mem)
    (hc : CodeAt m callocRBase callocRCode) (hsp1 : 0x87800220 ≤ sp) (hsp2 : sp ≤ 0x100000000)
    (hal : sp % 16 = 0) (hn : n < 2 ^ 32) (hsz : sz < 2 ^ 32) :
    Triple (At 0x80007790#64 (rL ra s0 sp n sz) m v.keepR outp)
      (At 0x800077c4#64 (pL ra sp n sz) (writeLog m (pLog ra s0 sp)) v.keepR outp) := by
  calloc_ctx
  refine Tom.Machine.seg_at' callocP (pc1 := 0x800077c4#64) ([] : List (List (BitVec 8))) [1, 2, 3, 8, 10, 11, 12] abiKeysR ?_ ?_ ?_ ?_
  · tom_facts hc
    all_goals first
      | leaf_auto [rL] []
      | (leaf_nf [rL]
         simp only [shamtOf, BitVec.reduceExtractLsb', BitVec.reduceExtractLsb]
         first | (rw [sra32 n hn]; rfl) | (rw [srl32z sz hsz]; rfl))
  · seg_nfo [callocP, rL]
  · sub_auto [callocP, rL, pL] []
  · seg_nfo [callocP, rL]
    try val_nf []
    simp only [pLog, List.cons.injEq, Prod.mk.injEq, and_true]
    omega

/-- After `__muldi3`: `a0 = n * sz`. -/
def qL (sp : Nat) (N : Nat) : GRegs :=
  [(1, 0x800077c8#64), (2, BitVec.ofNat 64 (sp - 32)), (8, reent), (10, BitVec.ofNat 64 N)]

/-- At the `_malloc_r` call (`7d0`). -/
def mL (sp : Nat) (N : Nat) : GRegs :=
  [(1, 0x800077c8#64), (2, BitVec.ofNat 64 (sp - 32)), (8, reent), (10, reent), (11, BitVec.ofNat 64 N)]

theorem m_step (v : Abi) (outp : Array String) (sp N : Nat) (m : Mem)
    (hc : CodeAt m callocRBase callocRCode) :
    Triple (At 0x800077c8#64 (qL sp N) m v.keepR outp)
      (At 0x800077d0#64 (mL sp N) m v.keepR outp) := by
  refine Triple.rmap (Q := At 0x800077d0#64 (mL sp N) (writeLog m []) v.keepR outp) (fun c h => by rw [writeLog_nil] at h; exact h) ?_
  calloc_ctx
  seg_step callocM 0x800077d0#64 ([] : List (List (BitVec 8))) [1, 2, 8, 10] abiKeysR [qL] [mL] [] hc

/-- After `_malloc_r` (`7d4`): `a0 = q`. -/
def aL (sp : Nat) (q : Nat) : GRegs :=
  [(1, 0x800077d4#64), (2, BitVec.ofNat 64 (sp - 32)), (10, BitVec.ofNat 64 q)]

/-- At the return: `a0 = r`, `sp`, `s0` restored. -/
def retL (ra s0 : BitVec 64) (sp r : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 r)]

/-- NULL: return 0. -/
theorem n_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M callocRBase callocRCode) (hsp1 : 0x87800220 ≤ sp) (hsp2 : sp ≤ 0x100000000)
    (hal : sp % 16 = 0) (hra : ra.toNat % 4 = 0)
    (h8 : bytesT8 M (sp - 8) = ra) (h16 : bytesT8 M (sp - 16) = s0) :
    Triple (At 0x800077d4#64 (aL sp 0) M v.keepR outp)
      (At ra (retL ra s0 sp 0) M v.keepR outp) := by
  refine Triple.rmap (Q := At ra (retL ra s0 sp 0) (writeLog M []) v.keepR outp) (fun c h => by rw [writeLog_nil] at h; exact h) ?_
  calloc_ctx
  seg_step callocN ra [rd8 M (sp - 8), rd8 M (sp - 16)] [1, 2, 10] abiKeysR [aL] [retL] [h8, h16] hc

/-- At `7f0` (`cap ≤ 72`): `a0 = q`, `a2 = cap`, `a3 = 72`. -/
def hL (sp q cap : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (10, BitVec.ofNat 64 q), (12, BitVec.ofNat 64 cap), (13, 72#64),
   (15, BitVec.ofNat 64 q)]

theorem h_step (v : Abi) (outp : Array String) (sp q cap : Nat) (M : Mem)
    (hc : CodeAt M callocRBase callocRCode) (hq1 : 0x80019d20 ≤ q) (hq2 : q < 0x87800000)
    (hcap : (bytesT8 M (q - 8) &&& 0xfffffffffffffffc#64) + 0xfffffffffffffff8#64 = BitVec.ofNat 64 cap)
    (hc72 : cap ≤ 72) :
    Triple (At 0x800077d4#64 (aL sp q) M v.keepR outp)
      (At 0x800077f0#64 (hL sp q cap) M v.keepR outp) := by
  refine Triple.rmap (Q := At 0x800077f0#64 (hL sp q cap) (writeLog M []) v.keepR outp) (fun c h => by rw [writeLog_nil] at h; exact h) ?_
  calloc_ctx
  seg_step callocH 0x800077f0#64 [rd8 M (q - 8)] [1, 2, 10] abiKeysR [aL] [hL] [hcap] hc

/-- At `81c`/`860` (three more zero stores at `a4`). -/
def zL (sp q a4 : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (14, BitVec.ofNat 64 a4), (15, BitVec.ofNat 64 q)]

/-- At `860`/`904`: `a0 = q`. -/
def e10L (sp q : Nat) : GRegs := [(2, BitVec.ofNat 64 (sp - 32)), (10, BitVec.ofNat 64 q), (15, BitVec.ofNat 64 q)]

/-- At `828` (the epilogue). -/
def eL (sp q : Nat) : GRegs := [(2, BitVec.ofNat 64 (sp - 32)), (15, BitVec.ofNat 64 q)]

/-- Zero doublewords from `a`: two, three, four, six. -/
def z2 (a : Nat) : List WEntry := [(a, 8, 0#64), (a + 8, 8, 0#64)]
def z3 (a : Nat) : List WEntry := [(a, 8, 0#64), (a + 8, 8, 0#64), (a + 16, 8, 0#64)]
def z4 (a : Nat) : List WEntry := [(a, 8, 0#64), (a + 8, 8, 0#64), (a + 16, 8, 0#64), (a + 24, 8, 0#64)]
def z6 (a : Nat) : List WEntry :=
  [(a, 8, 0#64), (a + 8, 8, 0#64), (a + 16, 8, 0#64), (a + 24, 8, 0#64), (a + 32, 8, 0#64),
   (a + 40, 8, 0#64)]

theorem h24_step (v : Abi) (outp : Array String) (sp q cap : Nat) (M : Mem)
    (hc : CodeAt M callocRBase callocRCode) (hc39 : cap ≤ 39) :
    Triple (At 0x800077f0#64 (hL sp q cap) M v.keepR outp)
      (At 0x8000781c#64 (zL sp q q) M v.keepR outp) := by
  refine Triple.rmap (Q := At 0x8000781c#64 (zL sp q q) (writeLog M []) v.keepR outp) (fun c h => by rw [writeLog_nil] at h; exact h) ?_
  calloc_ctx
  seg_step callocH24 0x8000781c#64 ([] : List (List (BitVec 8))) [2, 10, 12, 13, 15] abiKeysR [hL] [zL] [] hc

theorem h40_step (v : Abi) (outp : Array String) (sp q cap : Nat) (M : Mem)
    (hc : CodeAt M callocRBase callocRCode) (hq1 : 0x80019d20 ≤ q) (hq2 : q + 16 ≤ 0x87800000)
    (hqa : q % 16 = 0) (hc39 : 39 < cap) (hc55 : cap ≤ 55) :
    Triple (At 0x800077f0#64 (hL sp q cap) M v.keepR outp)
      (At 0x80007860#64 (e10L sp q) (writeLog M (z2 q)) v.keepR outp) := by
  calloc_ctx
  cseg callocH40 0x80007860#64 ([] : List (List (BitVec 8))) [2, 10, 12, 13, 15] abiKeysR [hL]
    [e10L, z2] [] hc

theorem h56_step (v : Abi) (outp : Array String) (sp q cap : Nat) (M : Mem)
    (hc : CodeAt M callocRBase callocRCode) (hq1 : 0x80019d20 ≤ q) (hq2 : q + 32 ≤ 0x87800000)
    (hqa : q % 16 = 0) (hc55 : 55 < cap) (hc72 : cap ≠ 72) (hcl : cap < 2 ^ 32) :
    Triple (At 0x800077f0#64 (hL sp q cap) M v.keepR outp)
      (At 0x8000781c#64 (zL sp q (q + 32)) (writeLog M (z4 q)) v.keepR outp) := by
  calloc_ctx
  cseg callocH56 0x8000781c#64 ([] : List (List (BitVec 8))) [2, 10, 12, 13, 15] abiKeysR [hL]
    [zL, z4] [] hc

theorem h72_step (v : Abi) (outp : Array String) (sp q : Nat) (M : Mem)
    (hc : CodeAt M callocRBase callocRCode) (hq1 : 0x80019d20 ≤ q) (hq2 : q + 32 ≤ 0x87800000)
    (hqa : q % 16 = 0) :
    Triple (At 0x800077f0#64 (hL sp q 72) M v.keepR outp)
      (At 0x80007904#64 (e10L sp q) (writeLog M (z4 q)) v.keepR outp) := by
  calloc_ctx
  cseg callocH72 0x80007904#64 ([] : List (List (BitVec 8))) [2, 10, 12, 13, 15] abiKeysR [hL]
    [e10L, z4] [] hc

theorem j72_step (v : Abi) (outp : Array String) (sp q : Nat) (M : Mem)
    (hc : CodeAt M callocRBase callocRCode) (hq1 : 0x80019d20 ≤ q) (hq2 : q + 48 ≤ 0x87800000)
    (hqa : q % 16 = 0) :
    Triple (At 0x80007904#64 (e10L sp q) M v.keepR outp)
      (At 0x8000781c#64 (zL sp q (q + 48)) (writeLog M [(q + 32, 8, 0#64), (q + 40, 8, 0#64)])
        v.keepR outp) := by
  calloc_ctx
  cseg callocJ72 0x8000781c#64 ([] : List (List (BitVec 8))) [2, 10, 15] abiKeysR [e10L] [zL] [] hc

theorem z3_step (v : Abi) (outp : Array String) (sp q a : Nat) (M : Mem)
    (hc : CodeAt M callocRBase callocRCode) (ha1 : 0x80019d20 ≤ a) (ha2 : a + 24 ≤ 0x87800000)
    (haa : a % 8 = 0) :
    Triple (At 0x8000781c#64 (zL sp q a) M v.keepR outp)
      (At 0x80007828#64 (eL sp q) (writeLog M (z3 a)) v.keepR outp) := by
  calloc_ctx
  cseg callocZ3 0x80007828#64 ([] : List (List (BitVec 8))) [2, 14, 15] abiKeysR [zL] [eL, z3] [] hc

theorem z3b_step (v : Abi) (outp : Array String) (sp q : Nat) (M : Mem)
    (hc : CodeAt M callocRBase callocRCode) (hq1 : 0x80019d20 ≤ q) (hq2 : q + 40 ≤ 0x87800000)
    (hqa : q % 16 = 0) :
    Triple (At 0x80007860#64 (e10L sp q) M v.keepR outp)
      (At 0x80007828#64 (eL sp q) (writeLog M (z3 (q + 16))) v.keepR outp) := by
  calloc_ctx
  cseg callocZ3b 0x80007828#64 ([] : List (List (BitVec 8))) [2, 10, 15] abiKeysR [e10L] [eL, z3] [] hc

/-- The epilogue: `a0 = q`, `ra`, `s0`, `sp` restored, return. -/
theorem e_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp q : Nat) (M : Mem)
    (hc : CodeAt M callocRBase callocRCode) (hsp1 : 0x87800220 ≤ sp) (hsp2 : sp ≤ 0x100000000)
    (hal : sp % 16 = 0) (hra : ra.toNat % 4 = 0)
    (h8 : bytesT8 M (sp - 8) = ra) (h16 : bytesT8 M (sp - 16) = s0) :
    Triple (At 0x80007828#64 (eL sp q) M v.keepR outp)
      (At ra (retL ra s0 sp q) M v.keepR outp) := by
  refine Triple.rmap (Q := At ra (retL ra s0 sp q) (writeLog M []) v.keepR outp) (fun c h => by rw [writeLog_nil] at h; exact h) ?_
  calloc_ctx
  seg_step callocE ra [rd8 M (sp - 8), rd8 M (sp - 16)] [2, 15] abiKeysR [eL] [retL] [h8, h16] hc

/-- `cap > 72`: to the `memset` path (`83c`). -/
theorem h0_step (v : Abi) (outp : Array String) (sp q cap : Nat) (M : Mem)
    (hc : CodeAt M callocRBase callocRCode) (hq1 : 0x80019d20 ≤ q) (hq2 : q < 0x87800000)
    (hcap : (bytesT8 M (q - 8) &&& 0xfffffffffffffffc#64) + 0xfffffffffffffff8#64 = BitVec.ofNat 64 cap)
    (hc72 : 72 < cap) (hcl : cap < 2 ^ 32) :
    Triple (At 0x800077d4#64 (aL sp q) M ((8, reent) :: v.keepR) outp)
      (At 0x8000783c#64 (hL sp q cap) M ((8, reent) :: v.keepR) outp) := by
  refine Triple.rmap (Q := At 0x8000783c#64 (hL sp q cap) (writeLog M []) ((8, reent) :: v.keepR) outp) (fun c h => by rw [writeLog_nil] at h; exact h) ?_
  calloc_ctx
  seg_step callocH0 0x8000783c#64 [rd8 M (q - 8)] [1, 2, 10] (8 :: abiKeysR) [aL] [hL] [hcap] hc

/-- At the `memset(q, 0, cap)` call (`844`). -/
def sL (sp q cap : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (10, BitVec.ofNat 64 q), (11, 0#64), (12, BitVec.ofNat 64 cap)]

theorem s_step (v : Abi) (outp : Array String) (sp q cap : Nat) (M : Mem)
    (hc : CodeAt M callocRBase callocRCode) (hsp1 : 0x87800220 ≤ sp) (hsp2 : sp ≤ 0x100000000)
    (hal : sp % 16 = 0) :
    Triple (At 0x8000783c#64 (hL sp q cap) M ((8, reent) :: v.keepR) outp)
      (At 0x80007844#64 (sL sp q cap) (writeLog M [(sp - 32, 8, BitVec.ofNat 64 q)]) ((8, reent) :: v.keepR) outp) := by
  calloc_ctx
  cseg callocS 0x80007844#64 ([] : List (List (BitVec 8))) [2, 10, 12, 13, 15] (8 :: abiKeysR) [hL] [sL] [] hc

/-- After `memset` (`848`): reload `q`, the epilogue. -/
theorem t_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp q : Nat) (M : Mem)
    (hc : CodeAt M callocRBase callocRCode) (hsp1 : 0x87800220 ≤ sp) (hsp2 : sp ≤ 0x100000000)
    (hal : sp % 16 = 0) (hra : ra.toNat % 4 = 0) (hq : bytesT8 M (sp - 32) = BitVec.ofNat 64 q)
    (h8 : bytesT8 M (sp - 8) = ra) (h16 : bytesT8 M (sp - 16) = s0) :
    Triple (At 0x80007848#64 [(2, BitVec.ofNat 64 (sp - 32))] M v.keepR outp)
      (At ra (retL ra s0 sp q) M v.keepR outp) := by
  refine Triple.rmap (Q := At ra (retL ra s0 sp q) (writeLog M []) v.keepR outp) (fun c h => by rw [writeLog_nil] at h; exact h) ?_
  calloc_ctx
  seg_step callocT ra [rd8 M (sp - 32), rd8 M (sp - 8), rd8 M (sp - 16)] [2] abiKeysR [] [retL]
    [hq, h8, h16] hc

end Tom.Machine.Fn.Calloc
