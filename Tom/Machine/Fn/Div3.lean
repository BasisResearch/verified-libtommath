import Tom.Machine.Seg.Div3
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.AutoEq
import Tom.Machine.Kit.Keep
import Tom.Machine.Kit.Shift
import Vsa.Sim.TripleCat
import Tom.Spec.DivD

/-!
# `s_mp_div_3` on the machine: the segments

`s_mp_div_3(a, c, d)` at `0x80006640` (85 instructions). The frame (`s0..s2`,
`ra`; `d` spilled at `8(sp)`), `mp_init_size(&q, a->used)` at `6668` (`q`'s
struct at `24(sp)`); `MP_MEM` to the epilogue (`div3M`); `q.used`, `q.sign`,
then the digit loop from the top (`div3S`; `a->used = 0`: `div3Z`). One
iteration at `66d0` (index `ix`, remainder `w < 3`): `W = (w << 28) | a[ix]`;
`W ≤ 2` stores `0` (`div3Hl`, `div3Zc`/`div3Zx`); otherwise the estimate
`t = (W · 0x5555555) >> 28` by shifts and adds (`div3Hh`, `div3Eo`), one
fix-up subtraction when `W - 3t > 2` (`div3Ef`, `div3F`), the store
(`div3Sc`/`div3Sx`). After the loop `*d = w` (`div3D1`/`div3D0`, `div3Z1`/`div3Z0`),
`mp_clamp(&q)`, `mp_exch(&q, c)`, `mp_clear(&q)` (`div3T`, `div3X`, `div3C`),
the epilogue (`div3E`). The chains are cut at every branch so that no leaf
carries the whole iteration (the whole-iteration chains exhaust 12 GB).
-/


namespace Tom.Machine.Fn.Div3
open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "div3_ctx" : tactic => `(tactic|
  (facts_ctx
   have : sMpDiv3Base = 0x80006640 := rfl
   have : sMpDiv3Code.length = 85 := rfl))


/-- `leaf_auto` with equations `es2` also after the value normal form (a
register value built by `slli`/`or` that `val_nf` must expose first). -/
syntax "leaf_auto3" " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| leaf_auto3 [$ds,*] [$es,*] [$fs,*]) => `(tactic|
      first
      | (leaf_nf [$ds,*]
         try simp only [Tom.Machine.rd4_bytesD, Tom.Machine.rd8_bytesD, Tom.Machine.rd4_bytes,
           Tom.Machine.rd8_bytes, Tom.Machine.rd8_bytesD']
         try simp only [$es,*]
         try simp only [Vsa.Sim.shamtOf, BitVec.reduceExtractLsb, BitVec.reduceExtractLsb']
         try val_nf [$es,*]
         try simp only [$fs,*]
         try val_nf [$es,*]
         try simp only [$fs,*]
         all_goals simp (disch := omega) only [Tom.Machine.ofNat_add_ofNat, Tom.Machine.blt_ofNat,
           Tom.Machine.bltu_ofNat', Tom.Machine.bgeu_ofNat', Tom.Machine.bge_zero_ofNat, Tom.Machine.bge_ofNat,
           Tom.Machine.ofNat_beq', bne, decide_eq_true_eq, decide_eq_false_iff_not,
           Bool.not_eq_true', Bool.not_eq_false', beq_self_eq_true, Bool.not_true, $fs,*]
         all_goals omega)
      | leaf_auto [$ds,*] [$es,*])

/-- `seg_step` with the post-normal-form equations `es2` (`leaf_auto3`). -/
syntax "seg_step3 " term:max ppSpace term:max ppSpace term:max ppSpace term:max ppSpace term:max
  " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term:max : tactic
macro_rules
  | `(tactic| seg_step3 $bs $pc $lds $ks $kk [$ds,*] [$ps,*] [$es,*] [$fs,*] $hc) => do
      let b ← `(Lean.Parser.Tactic.simpLemma| $bs:term)
      let l1 : Array (Lean.TSyntax ``Lean.Parser.Tactic.simpLemma) := #[b] ++ ds.getElems
      let l2 := l1 ++ ps.getElems
      `(tactic|
        (refine Tom.Machine.seg_at' $bs (pc1 := $pc) $lds $ks $kk ?_ ?_ ?_ ?_
         · tom_facts $hc
           all_goals leaf_auto3 [$ds,*] [$es,*] [$fs,*]
         · seg_nfo [$l1,*]
           try (try val_nf [$es,*]
                exact Tom.Machine.ret_target' _ (by assumption))
         · try simp only [$l2,*]
           simp only [Tom.Machine.SubL]
           seg_nfo [$l2,*]
           try simp only [Option.some.injEq]
           try val_nf [$es,*]
           try simp only [$fs,*]
           try val_nf [$es,*]
           try simp only [$fs,*]
           try regs_close
         · seg_nfo [$l1,*]
           try val_nf [$es,*]
           try simp only [$fs,*]
           try val_nf [$es,*]
           try simp only [$fs,*]
           try regs_close))


/-- Equations kept out of `assumption`/`omega`'s reach (rewrite rules only). -/
structure Hide3 (p q r : Prop) : Prop where
  a : p
  b : q
  c : r

/-! ## Register lists at the join points -/

/-- At the loop head (`66d0`): index `ix`, remainder `w`. -/
def lL (sp pa pc pd adp qdp w ix : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 80)), (8, 0#64), (9, BitVec.ofNat 64 pa), (18, BitVec.ofNat 64 pc),
   (12, BitVec.ofNat 64 pd), (13, 2#64), (6, 0xffffffffffffffff#64), (10, BitVec.ofNat 64 (adp + 4 * ix)),
   (11, BitVec.ofNat 64 (qdp + 4 * ix)), (15, BitVec.ofNat 64 w), (16, BitVec.ofNat 64 ix)]

/-- Inside an iteration: the digit `t` (`a4`) and the remainder `r` (`a5`). -/
def cL (sp pa pc pd adp qdp ix t r : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 80)), (8, 0#64), (9, BitVec.ofNat 64 pa), (18, BitVec.ofNat 64 pc),
   (12, BitVec.ofNat 64 pd), (13, 2#64), (6, 0xffffffffffffffff#64), (10, BitVec.ofNat 64 (adp + 4 * ix)),
   (11, BitVec.ofNat 64 (qdp + 4 * ix)), (16, BitVec.ofNat 64 ix), (14, BitVec.ofNat 64 t), (15, BitVec.ofNat 64 r)]

/-- After the loop (`6744`): the remainder `w`. -/
def xL (sp pa pc pd w : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 80)), (8, 0#64), (9, BitVec.ofNat 64 pa), (18, BitVec.ofNat 64 pc),
   (12, BitVec.ofNat 64 pd), (15, BitVec.ofNat 64 w)]

/-! ## Arithmetic -/

theorem bv_mod {x y : Nat} (h : x % 2 ^ 64 = y % 2 ^ 64) : BitVec.ofNat 64 x = BitVec.ofNat 64 y := by
  apply BitVec.eq_of_toNat_eq; simpa using h

/-- `(w << 28) | d`. -/
theorem zext_or (d w : Nat) (hd : d < 268435456) (hw : w < 3) :
    zero_extend (m := 64) (BitVec.ofNat 32 d) ||| BitVec.ofNat 64 (w * 268435456) =
      BitVec.ofNat 64 (w * 268435456 + d) := by
  apply BitVec.eq_of_toNat_eq
  simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show d < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show w * 268435456 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show w * 268435456 + d < 2 ^ 64 by omega)]
  have h := Nat.shiftLeft_add_eq_or_of_lt (i := 28) (show d < 2 ^ 28 by omega) w
  simp only [Nat.shiftLeft_eq, Nat.reducePow] at h; rw [Nat.or_comm]; exact h.symm

/-- The estimate `(W b) >> 28`. -/
abbrev est (W : Nat) : Nat := W * 89478485 / 268435456

/-- The shift-and-add chain of `W * 89478485`. -/
theorem mul_chain (W : Nat) : ((W * 4 + W) * 4 + W + ((W * 4 + W) * 4 + W) * 64) * 4 + W +
    (((W * 4 + W) * 4 + W + ((W * 4 + W) * 4 + W) * 64) * 4 + W) * 16384 = W * 89478485 := by omega

/-- `3 est ≤ W < 3 est + 6` (`div3Est_c`). -/
theorem est_bounds {W : Nat} (h : W < 805306368) : 3 * est W ≤ W ∧ W < 3 * est W + 6 := by
  have := Tom.div3Est_c (W := W) (by simp only [Tom.radix_eq]; omega)
  simp only [Nat.shiftRight_eq_div_pow, Layout.digitBits] at this
  exact ⟨this.2.1, this.2.2⟩

/-- `W - 3 t` (`sub`, wrapping) for `3 t ≤ W`. -/
theorem bv_sub3 {W t : Nat} (h : 3 * t ≤ W) (hW : W < 805306368) :
    BitVec.ofNat 64 (18446744073709551616 - (t * 2 + t) % 18446744073709551616 + W) = BitVec.ofNat 64 (W - 3 * t) := by
  apply bv_mod
  rw [Nat.mod_eq_of_lt (show t * 2 + t < 18446744073709551616 by omega),
    show 18446744073709551616 - (t * 2 + t) + W = (W - 3 * t) + 18446744073709551616 by omega, Nat.add_mod_right]

theorem bgeu2 {r : Nat} (h : r < 2 ^ 64) : zopz0zKzJ_u (2#64) (BitVec.ofNat 64 r) = decide (r ≤ 2) := by
  rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bgeu_ofNat', Nat.mod_eq_of_lt (show 2 < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt h]

theorem bltu2 {r : Nat} (h : r < 2 ^ 64) : zopz0zI_u (2#64) (BitVec.ofNat 64 r) = decide (2 < r) := by
  rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, bltu_ofNat', Nat.mod_eq_of_lt (show 2 < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt h]

/-! ## The loop -/

/-- An iteration's digit read. -/
structure LFacts (M : Mem) (adp ix d : Nat) : Prop where
  ra_d : Ram (adp + 4 * ix) 4
  d_v : bytesT4 M (adp + 4 * ix) = BitVec.ofNat 32 d
  d_lt : d < 268435456

/-- `W = (w << 28) | a[ix] ≤ 2`: the digit is `0`, to `66bc`. -/
theorem hl_step (v : Abi) (outp : Array String) (sp pa pc pd adp qdp w ix d : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hf : LFacts M adp ix d) (hw : w < 3)
    (hW : w * 268435456 + d ≤ 2) :
    Triple (At 0x800066d0#64 (lL sp pa pc pd adp qdp w ix) M v.keepR2 outp)
      (At 0x800066bc#64 (cL sp pa pc pd adp qdp ix 0 (w * 268435456 + d)) (writeLog M []) v.keepR2 outp) := by
  div3_ctx
  have := hf.ra_d
  have e4 := zext_or d w hf.d_lt hw
  seg_step3 div3Hl 0x800066bc#64 [rd4 M (adp + 4 * ix)]
    [2, 8, 9, 18, 12, 13, 6, 10, 11, 15, 16] abiKeysR2 [lL] [cL] [hf.d_v] [e4] hc

/-- `W > 2`: to the estimate (`66e4`). -/
theorem hh_step (v : Abi) (outp : Array String) (sp pa pc pd adp qdp w ix d : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hf : LFacts M adp ix d) (hw : w < 3)
    (hW : 2 < w * 268435456 + d) :
    Triple (At 0x800066d0#64 (lL sp pa pc pd adp qdp w ix) M v.keepR2 outp)
      (At 0x800066e4#64 (cL sp pa pc pd adp qdp ix 0 (w * 268435456 + d)) (writeLog M []) v.keepR2 outp) := by
  div3_ctx
  have := hf.ra_d
  have e4 := zext_or d w hf.d_lt hw
  have hb : w * 268435456 + d < 2 ^ 64 := by omega
  seg_step3 div3Hh 0x800066e4#64 [rd4 M (adp + 4 * ix)]
    [2, 8, 9, 18, 12, 13, 6, 10, 11, 15, 16] abiKeysR2 [lL] [cL] [hf.d_v] [e4, bgeu2 hb] hc

/-- The estimate, `W - 3t ≤ 2`: `t = W / 3`, `r = W % 3`, to the store (`672c`). -/
theorem eo_step (v : Abi) (outp : Array String) (sp pa pc pd adp qdp ix W : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hWl : W < 805306368) (hr : W - 3 * est W ≤ 2) :
    Triple (At 0x800066e4#64 (cL sp pa pc pd adp qdp ix 0 W) M v.keepR2 outp)
      (At 0x8000672c#64 (cL sp pa pc pd adp qdp ix (W / 3) (W % 3)) (writeLog M []) v.keepR2 outp) := by
  div3_ctx
  have hb := est_bounds hWl
  have k2 : W * 89478485 % 18446744073709551616 = W * 89478485 := Nat.mod_eq_of_lt (by omega)
  have k3 : W * 89478485 / 268435456 = W / 3 := by simp only [est] at hb hr; omega
  have hS : Hide3 (BitVec.ofNat 64 (18446744073709551616 - (W / 3 * 2 + W / 3) % 18446744073709551616 + W) =
      BitVec.ofNat 64 (W % 3)) (W % 3 < 2 ^ 64) True :=
    ⟨by rw [bv_sub3 (by omega) hWl, show W - 3 * (W / 3) = W % 3 by omega], by omega, trivial⟩
  clear hr hb
  seg_step3 div3Eo 0x8000672c#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 18, 12, 13, 6, 10, 11, 16, 14, 15] abiKeysR2 [cL] [] [] [mul_chain, k2, k3, hS.a, bgeu2 hS.b] hc

/-- The estimate, `W - 3t > 2`: to the fix-up (`6720`) with `t = W / 3 - 1`, `r = W % 3 + 3`. -/
theorem ef_step (v : Abi) (outp : Array String) (sp pa pc pd adp qdp ix W : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hWl : W < 805306368) (hr : 2 < W - 3 * est W) :
    Triple (At 0x800066e4#64 (cL sp pa pc pd adp qdp ix 0 W) M v.keepR2 outp)
      (At 0x80006720#64 (cL sp pa pc pd adp qdp ix (W / 3 - 1) (W % 3 + 3)) (writeLog M []) v.keepR2 outp) := by
  div3_ctx
  have hb := est_bounds hWl
  have k2 : W * 89478485 % 18446744073709551616 = W * 89478485 := Nat.mod_eq_of_lt (by omega)
  have k3 : W * 89478485 / 268435456 = W / 3 - 1 := by simp only [est] at hb hr; omega
  have hS : Hide3 (BitVec.ofNat 64 (18446744073709551616 - ((W / 3 - 1) * 2 + (W / 3 - 1)) % 18446744073709551616 + W) =
      BitVec.ofNat 64 (W % 3 + 3)) (W % 3 + 3 < 2 ^ 64) True :=
    ⟨by rw [bv_sub3 (by simp only [est] at hb hr; omega) hWl]; congr 1; simp only [est] at hb hr; omega, by omega, trivial⟩
  clear hr hb
  seg_step3 div3Ef 0x80006720#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 18, 12, 13, 6, 10, 11, 16, 14, 15] abiKeysR2 [cL] [] [] [mul_chain, k2, k3, hS.a, bgeu2 hS.b] hc

/-- The fix-up: `t + 1`, `r - 3` (once: `r - 3 ≤ 2`), to the store. -/
theorem f_step (v : Abi) (outp : Array String) (sp pa pc pd adp qdp ix t R : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hR : R ≤ 2) (ht : t < 2 ^ 32) :
    Triple (At 0x80006720#64 (cL sp pa pc pd adp qdp ix t (R + 3)) M v.keepR2 outp)
      (At 0x8000672c#64 (cL sp pa pc pd adp qdp ix (t + 1) R) (writeLog M []) v.keepR2 outp) := by
  div3_ctx
  have e1 : BitVec.ofNat 64 (R + 3 + 18446744073709551613) = BitVec.ofNat 64 R := bv_mod (by omega)
  have hb : R < 2 ^ 64 := by omega
  seg_step3 div3F 0x8000672c#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 18, 12, 13, 6, 10, 11, 16, 14, 15] abiKeysR2 [cL] [] [] [e1, bltu2 hb] hc

/-- The store target. -/
structure QFacts (qdp ix : Nat) : Prop where
  rq : Ram (qdp + 4 * ix) 4
  q_al : qdp % 4 = 0
  code_q : qdp + 4 * ix + 4 ≤ sMpDiv3Base ∨ sMpDiv3Base + 340 ≤ qdp + 4 * ix

/-- Store `t` at `q[k + 1]`, back to the head at `k`. -/
theorem sc_step (v : Abi) (outp : Array String) (sp pa pc pd adp qdp k t r : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hf : QFacts qdp (k + 1)) (ht : t < 2 ^ 31) (hk : k + 1 < 2 ^ 31)
    (ha : 4 ≤ adp + 4 * (k + 1)) :
    Triple (At 0x8000672c#64 (cL sp pa pc pd adp qdp (k + 1) t r) M v.keepR2 outp)
      (At 0x800066d0#64 (lL sp pa pc pd adp qdp r k) (writeLog M [(qdp + 4 * (k + 1), 4, BitVec.ofNat 64 t)])
        v.keepR2 outp) := by
  div3_ctx
  have := hf.rq
  have e1 : BitVec.ofNat 64 (adp + 4 * (k + 1) + 18446744073709551612) = BitVec.ofNat 64 (adp + 4 * k) := bv_mod (by omega)
  have e2 : BitVec.ofNat 64 (qdp + 4 * (k + 1) + 18446744073709551612) = BitVec.ofNat 64 (qdp + 4 * k) := bv_mod (by omega)
  have e3 : BitVec.ofNat 64 ((k + 1 + 18446744073709551615) % 4294967296 % 4294967296) = BitVec.ofNat 64 k := bv_mod (by omega)
  have e5 : t % 4294967296 = t := Nat.mod_eq_of_lt (by omega)
  have e6 := signExtend_ofNat32 t ht
  seg_step3 div3Sc 0x800066d0#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 18, 12, 13, 6, 10, 11, 16, 14, 15] abiKeysR2 [cL] [lL] [] [e1, e2, e3, e5, e6] hc

/-- `addiw a6, a6, -1` at `ix = 0` is `t1 = -1`: the loop's exit. -/
theorem exit_m1 : (BitVec.signExtend 64 (BitVec.ofNat 32 (18446744073709551615 % 4294967296)) !=
    18446744073709551615#64) = false := by decide

theorem exit_m1' : (BitVec.signExtend 64 (BitVec.ofNat 32 (18446744073709551615 % 4294967296)) ==
    18446744073709551615#64) = true := by decide

/-- Store `t` at `q[0]`: the loop's end. -/
theorem sx_step (v : Abi) (outp : Array String) (sp pa pc pd adp qdp t r : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hf : QFacts qdp 0) (ht : t < 2 ^ 31) :
    Triple (At 0x8000672c#64 (cL sp pa pc pd adp qdp 0 t r) M v.keepR2 outp)
      (At 0x80006744#64 (xL sp pa pc pd r) (writeLog M [(qdp + 4 * 0, 4, BitVec.ofNat 64 t)]) v.keepR2 outp) := by
  div3_ctx
  have := hf.rq
  have e5 : t % 4294967296 = t := Nat.mod_eq_of_lt (by omega)
  have e6 := signExtend_ofNat32 t ht
  seg_step3 div3Sx 0x80006744#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 18, 12, 13, 6, 10, 11, 16, 14, 15] abiKeysR2 [cL] [xL] [] [e5, e6, exit_m1] hc

/-- `W ≤ 2`: store `0` at `q[k + 1]`, back to the head at `k` with `w = W`. -/
theorem zc_step (v : Abi) (outp : Array String) (sp pa pc pd adp qdp k W : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hf : QFacts qdp (k + 1)) (hk : k + 1 < 2 ^ 31)
    (ha : 4 ≤ adp + 4 * (k + 1)) :
    Triple (At 0x800066bc#64 (cL sp pa pc pd adp qdp (k + 1) 0 W) M v.keepR2 outp)
      (At 0x800066d0#64 (lL sp pa pc pd adp qdp W k) (writeLog M [(qdp + 4 * (k + 1), 4, 0#64)])
        v.keepR2 outp) := by
  div3_ctx
  have := hf.rq
  have e1 : BitVec.ofNat 64 (adp + 4 * (k + 1) + 18446744073709551612) = BitVec.ofNat 64 (adp + 4 * k) := bv_mod (by omega)
  have e2 : BitVec.ofNat 64 (qdp + 4 * (k + 1) + 18446744073709551612) = BitVec.ofNat 64 (qdp + 4 * k) := bv_mod (by omega)
  have e3 : BitVec.ofNat 64 ((k + 1 + 18446744073709551615) % 4294967296 % 4294967296) = BitVec.ofNat 64 k := bv_mod (by omega)
  seg_step3 div3Zc 0x800066d0#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 18, 12, 13, 6, 10, 11, 16, 14, 15] abiKeysR2 [cL] [lL] [] [e1, e2, e3] hc

/-- `W ≤ 2` at `q[0]`: the loop's end. -/
theorem zx_step (v : Abi) (outp : Array String) (sp pa pc pd adp qdp W : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hf : QFacts qdp 0) :
    Triple (At 0x800066bc#64 (cL sp pa pc pd adp qdp 0 0 W) M v.keepR2 outp)
      (At 0x80006744#64 (xL sp pa pc pd W) (writeLog M [(qdp + 4 * 0, 4, 0#64)]) v.keepR2 outp) := by
  div3_ctx
  have := hf.rq
  seg_step3 div3Zx 0x80006744#64 ([] : List (List (BitVec 8)))
    [2, 8, 9, 18, 12, 13, 6, 10, 11, 16, 14, 15] abiKeysR2 [cL] [xL] [] [exit_m1'] hc

/-! ## Straight-line code -/

def entry : BitVec 64 := 0x80006640#64

/-- The entry (`s0`, `s1`, `s2` carried: the function saves them). -/
def entryL (ra s0 s1 s2 : BitVec 64) (sp pa pc pd : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (18, s2), (10, BitVec.ofNat 64 pa),
   (11, BitVec.ofNat 64 pc), (12, BitVec.ofNat 64 pd)]

/-- The saved registers (`[sp - 32, sp)`). -/
def frameLog (ra s0 s1 s2 : BitVec 64) (sp : Nat) : List WEntry :=
  [(sp - 32, 8, s2), (sp - 24, 8, s1), (sp - 16, 8, s0), (sp - 8, 8, ra)]

/-- At `6664`: `a0 = &q`, `a1 = a->used`. -/
def p1L (ra s0 : BitVec 64) (sp pa pc pd ua : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 80)), (8, s0), (9, BitVec.ofNat 64 pa), (18, BitVec.ofNat 64 pc),
   (10, BitVec.ofNat 64 (sp - 56)), (11, BitVec.ofNat 64 ua), (12, BitVec.ofNat 64 pd)]

structure FFacts (M : Mem) (sp pa ua : Nat) : Prop where
  rs : Ram (sp - 80) 80
  sp_al : sp % 16 = 0
  sp_ge : 80 ≤ sp
  ra_ : Ram pa 24
  ua_v : bytesT4 M pa = BitVec.ofNat 32 ua
  ua_lt : ua < 2 ^ 31
  code_off : sp ≤ sMpDiv3Base ∨ sMpDiv3Base + 340 ≤ sp - 80
  pa_off : pa + 24 ≤ sp - 80 ∨ sp ≤ pa

theorem p1_step (ra s0 s1 s2 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pc pd ua : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hf : FFacts M sp pa ua) :
    Triple (At entry (entryL ra s0 s1 s2 sp pa pc pd) M v.keepR2 outp)
      (At 0x80006664#64 (p1L ra s0 sp pa pc pd ua) (writeLog M (frameLog ra s0 s1 s2 sp)) v.keepR2 outp) := by
  div3_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 ua := by
    rw [hf.ua_v, signExtend_ofNat32 _ hf.ua_lt]
  seg_step div3P1 0x80006664#64 [rd4 M pa] [1, 2, 8, 9, 18, 10, 11, 12] abiKeysR2
    [entry, entryL, frameLog] [p1L] [h1] hc

/-- At the `mp_init_size(&q, a->used)` call (`6668`). -/
def iL (ra s0 : BitVec 64) (sp pa pc ua : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 80)), (8, s0), (9, BitVec.ofNat 64 pa), (18, BitVec.ofNat 64 pc),
   (10, BitVec.ofNat 64 (sp - 56)), (11, BitVec.ofNat 64 ua)]

theorem p2_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa pc pd ua : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hf : FFacts M sp pa ua) :
    Triple (At 0x80006664#64 (p1L ra s0 sp pa pc pd ua) M v.keepR2 outp)
      (At 0x80006668#64 (iL ra s0 sp pa pc ua) (writeLog M [(sp - 72, 8, BitVec.ofNat 64 pd)]) v.keepR2 outp) := by
  div3_ctx
  have := hf.rs
  seg_step div3P2 0x80006668#64 ([] : List (List (BitVec 8))) [1, 2, 8, 9, 18, 10, 11, 12] abiKeysR2
    [p1L] [iL] [] hc

/-- After `mp_init_size`: `a0 = r`. -/
def rL (sp pa pc : Nat) (r : BitVec 64) : GRegs :=
  [(1, 0x8000666c#64), (2, BitVec.ofNat 64 (sp - 80)), (9, BitVec.ofNat 64 pa), (18, BitVec.ofNat 64 pc),
   (10, r)]

/-- At the epilogue (`676c`), result `r` in `s0`. -/
def eL (sp : Nat) (r : BitVec 64) : GRegs := [(2, BitVec.ofNat 64 (sp - 80)), (8, r)]

/-- `MP_MEM`: to the epilogue. -/
theorem m_step (v : Abi) (outp : Array String) (sp pa pc : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) :
    Triple (At 0x8000666c#64 (rL sp pa pc 0xfffffffffffffffe#64) M v.keepR2 outp)
      (At 0x8000676c#64 (eL sp 0xfffffffffffffffe#64) (writeLog M []) v.keepR2 outp) := by
  div3_ctx
  seg_step div3M 0x8000676c#64 ([] : List (List (BitVec 8))) [1, 2, 9, 18, 10] abiKeysR2 [rL] [eL] [] hc

/-- At `6690`: `a5 = a->used`, `a6 = a->used - 1`, `a2 = d`. -/
def sL (sp pa pc pd ua : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 80)), (8, 0#64), (9, BitVec.ofNat 64 pa), (18, BitVec.ofNat 64 pc),
   (12, BitVec.ofNat 64 pd), (15, BitVec.ofNat 64 ua), (16, BitVec.ofNat 64 (ua - 1))]

/-- The header reads after `mp_init_size`. -/
structure HFacts (M : Mem) (sp pa ua sg pd : Nat) : Prop where
  rs : Ram (sp - 80) 80
  sp_al : sp % 16 = 0
  sp_ge : 80 ≤ sp
  ra_ : Ram pa 24
  ua_v : bytesT4 M pa = BitVec.ofNat 32 ua
  ua_lt : ua < 2 ^ 31
  sg_v : bytesT4 M (pa + 8) = BitVec.ofNat 32 sg
  sg_lt : sg < 2 ^ 31
  pd_v : bytesT8 M (sp - 72) = BitVec.ofNat 64 pd
  code_off : sp ≤ sMpDiv3Base ∨ sMpDiv3Base + 340 ≤ sp - 80
  pa_off : pa + 24 ≤ sp - 80 ∨ sp ≤ pa

/-- `a->used ≥ 1`: `q.used`, `q.sign` stored, to `6690`. -/
theorem s1_step (v : Abi) (outp : Array String) (sp pa pc pd ua sg : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hf : HFacts M sp pa ua sg pd) (h1 : 1 ≤ ua) :
    Triple (At 0x8000666c#64 (rL sp pa pc 0#64) M v.keepR2 outp)
      (At 0x80006690#64 (sL sp pa pc pd ua)
        (writeLog M [(sp - 56, 4, BitVec.ofNat 64 ua), (sp - 56 + 8, 4, BitVec.ofNat 64 sg)]) v.keepR2 outp) := by
  div3_ctx
  have h1' : BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 ua := by
    rw [hf.ua_v, signExtend_ofNat32 _ hf.ua_lt]
  have h2 : BitVec.signExtend 64 (bytesT4 M (pa + 8)) = BitVec.ofNat 64 sg := by
    rw [hf.sg_v, signExtend_ofNat32 _ hf.sg_lt]
  have hpd : bytesT8 M (sp - 80 + 8) = BitVec.ofNat 64 pd := by rw [show sp - 80 + 8 = sp - 72 by omega]; exact hf.pd_v
  have e3 : BitVec.ofNat 64 ((ua + 18446744073709551615) % 4294967296 % 4294967296) = BitVec.ofNat 64 (ua - 1) :=
    bv_mod (by omega)
  seg_step div3S1 0x80006690#64 [rd4 M pa, rd4 M (pa + 8), rd8 M (sp - 80 + 8)]
    [1, 2, 9, 18, 10] abiKeysR2 [rL] [sL] [h1', h2, hpd, e3] hc

/-- The digit pointers. -/
structure PFacts (M : Mem) (sp pa adp qdp ua : Nat) : Prop where
  ra_ : Ram pa 24
  rs : Ram (sp - 80) 80
  sp_ge : 80 ≤ sp
  adp_v : bytesT8 M (pa + 16) = BitVec.ofNat 64 adp
  qdp_v : bytesT8 M (sp - 40) = BitVec.ofNat 64 qdp
  adp_ge : 4 ≤ adp
  qdp_ge : 4 ≤ qdp
  ua_ge : 1 ≤ ua
  ua_lt : ua < 2 ^ 31

/-- The loop's pointers, to the head at the top digit. -/
theorem s2_step (v : Abi) (outp : Array String) (sp pa pc pd adp qdp ua : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hf : PFacts M sp pa adp qdp ua) :
    Triple (At 0x80006690#64 (sL sp pa pc pd ua) M v.keepR2 outp)
      (At 0x800066d0#64 (lL sp pa pc pd adp qdp 0 (ua - 1)) (writeLog M []) v.keepR2 outp) := by
  div3_ctx
  have hq : bytesT8 M (sp - 80 + 40) = BitVec.ofNat 64 qdp := by rw [show sp - 80 + 40 = sp - 40 by omega]; exact hf.qdp_v
  have e1 : BitVec.ofNat 64 (adp + 18446744073709551612 + ua * 4) = BitVec.ofNat 64 (adp + 4 * (ua - 1)) :=
    bv_mod (by omega)
  have e2 : BitVec.ofNat 64 (qdp + 18446744073709551612 + ua * 4) = BitVec.ofNat 64 (qdp + 4 * (ua - 1)) :=
    bv_mod (by omega)
  seg_step div3S2 0x800066d0#64 [rd8 M (pa + 16), rd8 M (sp - 80 + 40)]
    [2, 8, 9, 18, 12, 15, 16] abiKeysR2 [sL] [lL] [hf.adp_v, hq, e1, e2] hc

/-- `a->used = 0`: `addiw a6, a5, -1` is `-1`. -/
theorem z_m1 : zopz0zI_s (BitVec.signExtend 64 (BitVec.ofNat 32 (18446744073709551615 % 4294967296))) 0#64 = true := by
  decide

/-- `a->used = 0`: `q.used = 0`, `q.sign`, past the loop (`6788`). -/
def zL (sp pa pc pd : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 80)), (8, 0#64), (9, BitVec.ofNat 64 pa), (18, BitVec.ofNat 64 pc),
   (12, BitVec.ofNat 64 pd)]

/-- The empty `a`'s reads. -/
structure ZFacts (M : Mem) (sp pa sg pd : Nat) : Prop where
  pa_off : pa + 24 ≤ sp - 80 ∨ sp ≤ pa
  rs : Ram (sp - 80) 80
  sp_al : sp % 16 = 0
  sp_ge : 80 ≤ sp
  ra_ : Ram pa 24
  ua_v : bytesT4 M pa = BitVec.ofNat 32 0
  sg_v : bytesT4 M (pa + 8) = BitVec.ofNat 32 sg
  sg_lt : sg < 2 ^ 31
  pd_v : bytesT8 M (sp - 72) = BitVec.ofNat 64 pd
  code_off : sp ≤ sMpDiv3Base ∨ sMpDiv3Base + 340 ≤ sp - 80

theorem z_step (v : Abi) (outp : Array String) (sp pa pc pd sg : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hf : ZFacts M sp pa sg pd) :
    Triple (At 0x8000666c#64 (rL sp pa pc 0#64) M v.keepR2 outp)
      (At 0x80006788#64 (zL sp pa pc pd)
        (writeLog M [(sp - 56, 4, BitVec.ofNat 64 0), (sp - 56 + 8, 4, BitVec.ofNat 64 sg)]) v.keepR2 outp) := by
  div3_ctx
  have h1' : BitVec.signExtend 64 (bytesT4 M pa) = BitVec.ofNat 64 0 := by
    rw [hf.ua_v, signExtend_ofNat32 _ (by decide)]
  have h2 : BitVec.signExtend 64 (bytesT4 M (pa + 8)) = BitVec.ofNat 64 sg := by
    rw [hf.sg_v, signExtend_ofNat32 _ hf.sg_lt]
  have hpd : bytesT8 M (sp - 80 + 8) = BitVec.ofNat 64 pd := by rw [show sp - 80 + 8 = sp - 72 by omega]; exact hf.pd_v
  seg_step3 div3Z 0x80006788#64 [rd4 M pa, rd4 M (pa + 8), rd8 M (sp - 80 + 8)]
    [1, 2, 9, 18, 10] abiKeysR2 [rL] [zL] [h1', h2, hpd] [z_m1] hc

/-- At `674c`, after `*d`. -/
def tL (sp pa pc : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 80)), (8, 0#64), (9, BitVec.ofNat 64 pa), (18, BitVec.ofNat 64 pc)]

/-- The remainder's slot. -/
structure DFacts (pd : Nat) : Prop where
  rd : Ram pd 4
  d_al : pd % 4 = 0
  code_d : pd + 4 ≤ sMpDiv3Base ∨ sMpDiv3Base + 340 ≤ pd

/-- `*d = w` (`d ≠ NULL`). -/
theorem d1_step (v : Abi) (outp : Array String) (sp pa pc pd w : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hf : DFacts pd) (hd : pd ≠ 0) :
    Triple (At 0x80006744#64 (xL sp pa pc pd w) M v.keepR2 outp)
      (At 0x8000674c#64 (tL sp pa pc) (writeLog M [(pd, 4, BitVec.ofNat 64 w)]) v.keepR2 outp) := by
  div3_ctx
  have := hf.rd
  seg_step div3D1 0x8000674c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 12, 15] abiKeysR2 [xL] [tL] [] hc

/-- `d == NULL`. -/
theorem d0_step (v : Abi) (outp : Array String) (sp pa pc w : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) :
    Triple (At 0x80006744#64 (xL sp pa pc 0 w) M v.keepR2 outp)
      (At 0x8000674c#64 (tL sp pa pc) (writeLog M []) v.keepR2 outp) := by
  div3_ctx
  seg_step div3D0 0x8000674c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 12, 15] abiKeysR2 [xL] [tL] [] hc

/-- `a->used = 0`, `d ≠ NULL`: `*d = 0`. -/
theorem z1_step (v : Abi) (outp : Array String) (sp pa pc pd : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hf : DFacts pd) (hd : pd ≠ 0) :
    Triple (At 0x80006788#64 (zL sp pa pc pd) M v.keepR2 outp)
      (At 0x8000674c#64 (tL sp pa pc) (writeLog M [(pd, 4, 0#64)]) v.keepR2 outp) := by
  div3_ctx
  have := hf.rd
  seg_step div3Z1 0x8000674c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 12] abiKeysR2 [zL] [tL] [] hc

/-- `a->used = 0`, `d == NULL`. -/
theorem z0_step (v : Abi) (outp : Array String) (sp pa pc : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) :
    Triple (At 0x80006788#64 (zL sp pa pc 0) M v.keepR2 outp)
      (At 0x8000674c#64 (tL sp pa pc) (writeLog M []) v.keepR2 outp) := by
  div3_ctx
  seg_step div3Z0 0x8000674c#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 12] abiKeysR2 [zL] [tL] [] hc

/-- At a call with `a0 = &q`. -/
def qL (sp pa pc : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 80)), (8, 0#64), (9, BitVec.ofNat 64 pa), (18, BitVec.ofNat 64 pc),
   (10, BitVec.ofNat 64 (sp - 56))]

/-- `c ≠ NULL`: to `mp_clamp(&q)` (`6754`). -/
theorem t_step (v : Abi) (outp : Array String) (sp pa pc : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hp : pc ≠ 0) (hp' : pc < 2 ^ 64) (hs : 80 ≤ sp) :
    Triple (At 0x8000674c#64 (tL sp pa pc) M v.keepR2 outp)
      (At 0x80006754#64 (qL sp pa pc) (writeLog M []) v.keepR2 outp) := by
  div3_ctx
  seg_step div3T 0x80006754#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18] abiKeysR2 [tL] [qL] [] hc

/-- At `mp_exch(&q, c)`. -/
def xcL (sp pa pc : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 80)), (8, 0#64), (9, BitVec.ofNat 64 pa), (18, BitVec.ofNat 64 pc),
   (10, BitVec.ofNat 64 (sp - 56)), (11, BitVec.ofNat 64 pc)]

/-- After `mp_clamp`: to `mp_exch(&q, c)` (`6760`). -/
theorem x_step (v : Abi) (outp : Array String) (sp pa pc : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hs : 80 ≤ sp) :
    Triple (At 0x80006758#64 (qL sp pa pc) M v.keepR2 outp)
      (At 0x80006760#64 (xcL sp pa pc) (writeLog M []) v.keepR2 outp) := by
  div3_ctx
  seg_step div3X 0x80006760#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18, 10] abiKeysR2 [qL] [xcL] [] hc

/-- After `mp_exch`: to `mp_clear(&q)` (`6768`). -/
theorem c_step (v : Abi) (outp : Array String) (sp pa pc : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hs : 80 ≤ sp) :
    Triple (At 0x80006764#64 (tL sp pa pc) M v.keepR2 outp)
      (At 0x80006768#64 (qL sp pa pc) (writeLog M []) v.keepR2 outp) := by
  div3_ctx
  seg_step div3C 0x80006768#64 ([] : List (List (BitVec 8))) [2, 8, 9, 18] abiKeysR2 [tL] [qL] [] hc

/-- The epilogue's frame reads. -/
structure EFacts (M : Mem) (ra s0 s1 s2 : BitVec 64) (sp : Nat) : Prop where
  rs : Ram (sp - 80) 80
  sp_al : sp % 16 = 0
  sp_ge : 80 ≤ sp
  ra_al : ra.toNat % 4 = 0
  ra_v : bytesT8 M (sp - 8) = ra
  s0_v : bytesT8 M (sp - 16) = s0
  s1_v : bytesT8 M (sp - 24) = s1
  s2_v : bytesT8 M (sp - 32) = s2

/-- Restore the frame, return `r`. -/
theorem e_step (ra s0 s1 s2 r : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M sMpDiv3Base sMpDiv3Code) (hf : EFacts M ra s0 s1 s2 sp) :
    Triple (At 0x8000676c#64 (eL sp r) M v.keepR2 outp)
      (At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (18, s2), (10, r)] (writeLog M []) v.keepR2 outp) := by
  div3_ctx
  have hra := hf.ra_al
  have h1 : bytesT8 M (sp - 80 + 72) = ra := by rw [show sp - 80 + 72 = sp - 8 by omega]; exact hf.ra_v
  have h2 : bytesT8 M (sp - 80 + 64) = s0 := by rw [show sp - 80 + 64 = sp - 16 by omega]; exact hf.s0_v
  have h3 : bytesT8 M (sp - 80 + 56) = s1 := by rw [show sp - 80 + 56 = sp - 24 by omega]; exact hf.s1_v
  have h4 : bytesT8 M (sp - 80 + 48) = s2 := by rw [show sp - 80 + 48 = sp - 32 by omega]; exact hf.s2_v
  seg_step_eq div3E ra [rd8 M (sp - 80 + 72), rd8 M (sp - 80 + 64), rd8 M (sp - 80 + 56), rd8 M (sp - 80 + 48)]
    [2, 8] abiKeysR2 [eL] [] [h1, h2, h3, h4] hc

end Tom.Machine.Fn.Div3
