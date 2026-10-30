import Tom.Machine.Fn.Libgcc
import Tom.Machine.Seg.Libgcc
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Jal

/-!
# `__moddi3` and `__divdi3` from any scratch state

`Fn/Libgcc.lean` has these two from ship-your-interpreter's `moddi3_spec` and
`divdi3_spec`, which need `a2`/`a3` defined at entry (they call the unsigned
core through `udivdi3_spec`). Here the signed wrappers are segments
(`experiments/segs/libgcc.json`) around the scratch-free unsigned contract
`Udivdi3.correctK`, so no scratch register is needed, and `__divdi3`'s
wrapping case `intMin / -1` is covered too (the result is `BitVec.sdiv`'s own
case split, `BitVec.sdiv_eq`/`srem_eq`).
-/

namespace Tom.Machine.Fn.Libgcc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa Vsa.Logic
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Sim (GRegs GHolds keysG gprReg noiseRegs FrameOK wrChain KeysOK)
open Tom.Machine Tom.Machine.Seg Tom.Machine.Api.Libgcc

/-! ## Signs and frames -/

theorem slt_zero (x : BitVec 64) : zopz0zI_s x 0#64 = x.msb := by
  simp [zopz0zI_s, BitVec.msb_eq_toInt]

theorem sge_zero (x : BitVec 64) : zopz0zKzJ_s x 0#64 = !x.msb := by
  rw [BitVec.msb_eq_toInt]; unfold zopz0zKzJ_s
  by_cases h : x.toInt < 0 <;> simp [h] <;> omega

theorem sgt_zero (x : BitVec 64) (h : x ≠ 0#64) : zopz0zI_s 0#64 x = !x.msb := by
  rw [BitVec.msb_eq_toInt]; unfold zopz0zI_s
  have : x.toInt ≠ 0 := toInt_ne_zero h
  by_cases hx : x.toInt < 0 <;> simp [hx] <;> omega

/-- A keep-set off `divWrites` is off every chain here. -/
theorem frameOK_K {K : GRegs} (hK : KeepOK divWrites K) (bs : List Vsa.Sim.BBlock)
    (hw : ∀ m ∈ wrChain bs, m ∈ divWrites) : FrameOK (keysG K) bs := by
  refine Tom.Machine.frameOK_of _ bs (fun m hm => ?_) (fun n hn => ⟨(hK n hn).1, fun hm => ?_⟩)
  · have := hw m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega
  · have h := (hK n hn).2.2 n (hw n hm)
    have := hw n hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd h (by decide)

theorem keys2 {K : GRegs} (hK : KeepOK divWrites K) : ∀ n ∈ keysG K, 2 ≤ n ∧ n ≤ 31 := by
  intro n hn
  refine ⟨?_, (hK n hn).1.2⟩
  have h1 := (hK n hn).1.1
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 1 := by omega
    subst this
    exact absurd ((hK 1 hn).2.2 1 (by simp)) (by decide)
  · exact h

/-! ## `__umoddi3`'s code, which `__divdi3`'s sign fix-ups run -/

/-- The words of `__umoddi3` (`[0x800175f4, 0x80017628)`), in `Img` (`Img.umoddi3`). -/
abbrev umodBase : Nat := Code.umoddi3Base
abbrev umodCode : List (BitVec 32) := Code.umoddi3Code

/-! ## Segments, calls and tails -/

set_option hygiene false in
/-- One wrapper segment (`wseg chain pc0 pc1 L L1 ks [eqs] hc,…`): `seg_at'` from
`At pc0 L m K outp` to `At pc1 L1 m K outp`, the keep-set by `frameOK_K hK`,
the leaves by `tom_facts` + `leaf_auto [] [eqs]`, a `jr t0` target by `hra`. -/
syntax "wseg " ident ppSpace term:max ppSpace term:max ppSpace term:max ppSpace term:max ppSpace
  term:max " [" Lean.Parser.Tactic.simpLemma,* "] " term,+ : tactic
set_option hygiene false in
macro_rules
  | `(tactic| wseg $c $pc0 $pc1 $L $L1 $ks [$es,*] $hcs,*) => `(tactic|
      (refine seg_at' $c (pc0 := $pc0) (pc1 := $pc1) (L := $L) (L1 := $L1) (m := m) (lg := [])
          (outp := outp) [] $ks (keysG K) ?_ ?_ ?_ ?_ rfl rfl (by decide) (frameOK_K hK _ (by decide))
          (by decide)
       · tom_facts $hcs,*
         all_goals leaf_auto [] [$es,*]
       · seg_nfo [$c:ident]
         try first | rfl | exact Tom.Machine.ret_target' _ hra
       · sub_auto [$c:ident] []
         all_goals try simp only [BitVec.zero_sub, and_self, and_true]
       · seg_nfo [$c:ident]))

/-- The keep-set of the unsigned core: the caller's `K` and `t0 = ra`. -/
theorem keepOK_t0 {K : GRegs} (hK : KeepOK divWrites K) (ra : BitVec 64) :
    KeepOK mulWrites ((5, ra) :: K) := by
  intro n hn
  simp only [keysG, List.mem_cons] at hn
  rcases hn with rfl | hn
  · decide
  · exact keepOK_sub hK (by decide) n hn

/-- `jal __udivdi3` at `pc` with `t0 = ra`, `a0 = a`, `a1 = b ≠ 0`: back at `pc + 4`
with `a0 = a / b`, `a1 = a % b`, `t0` and `K` kept. -/
theorem call_udiv {pc : BitVec 64} {w : BitVec 32} {imm : BitVec 21} (ret ra a b : BitVec 64)
    {K : GRegs} {outp : Array String} {m : Mem} (hm : Img m) (hb : b ≠ 0#64)
    (hK : KeepOK divWrites K)
    (hbytes : m[pc.toNat]? = some (w.extractLsb' 0 8) ∧ m[pc.toNat + 1]? = some (w.extractLsb' 8 8) ∧
      m[pc.toNat + 2]? = some (w.extractLsb' 16 8) ∧ m[pc.toNat + 3]? = some (w.extractLsb' 24 8))
    (hword : ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append (w.extractLsb' 8 8)).append
      (w.extractLsb' 0 8)) = w)
    (hnotrvc : Sail.BitVec.extractLsb ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append
      (w.extractLsb' 8 8)).append (w.extractLsb' 0 8)) 1 0 = (0b11#2 : BitVec 2))
    (hdec : ∀ s : SequentialState RegisterType trivialChoiceSource,
      s.regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa) →
      s.regs.get? Register.cur_privilege =
        some ((Privilege.Machine) : RegisterType Register.cur_privilege) →
      s.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg) →
      (ext_decode w).run s = .ok (instruction.JAL (imm, regidx.Regidx 0x01#5)) s)
    (hfetch : 0x80000000 ≤ pc.toNat ∧ Vsa.Sim.FetchOK pc.toNat ∧ pc.toNat % 4 = 0)
    (htgt : pc + sign_extend (m := 64) imm = udivdi3Entry) (hret : Sail.BitVec.addInt pc 4 = ret)
    (hret4 : ret.toNat % 4 = 0) :
    Triple (At pc [(5, ra), (10, a), (11, b)] m K outp)
      (At ret [(5, ra), (10, a / b), (11, a % b)] m K outp) := by
  refine Triple.seq (jal_at (L' := [(5, ra), (10, a), (11, b)]) hbytes hword hnotrvc hdec hfetch
    (by rw [htgt]; decide) (fun p hp => hp)
    (fun n hn => by simp only [keysG, List.mem_cons, List.not_mem_nil, or_false] at hn; omega)
    (keys2 hK)) ?_
  rw [htgt, hret]
  intro c h
  obtain ⟨c', hs, h'⟩ := Udivdi3.correctK hm hret4 hb (keepOK_t0 hK ra) c
    (h.reshape (L' := [(1, ret), (10, a), (11, b)]) (K' := (5, ra) :: K) (by simp)
      (fun p hp => by
        rcases List.mem_cons.1 hp with rfl | hp
        · simp
        · exact List.mem_append_right _ hp))
  exact ⟨c', hs, h'.reshape (by simp) (fun p hp => List.mem_append_right _ (List.mem_cons_of_mem _ hp))⟩

/-! ## `__moddi3` -/

section moddi3

variable (ra n d : BitVec 64) (K : GRegs) (outp : Array String) (m : Mem)
  (hc : CodeAt m Code.moddi3Base Code.moddi3Code) (hK : KeepOK divWrites K)

include hc hK

theorem mod_pp (hn : n.msb = false) (hd : d.msb = false) :
    Triple (At moddi3Entry [(1, ra), (10, n), (11, d)] m K outp)
      (At 0x80017634#64 [(5, ra), (10, n), (11, d)] m K outp) := by
  have : Code.moddi3Base = 0x80017628 := rfl
  wseg modPP moddi3Entry 0x80017634#64 [(1, ra), (10, n), (11, d)] [(5, ra), (10, n), (11, d)]
    [1, 10, 11] [slt_zero, sge_zero, hn, hd] hc

theorem mod_np (hn : n.msb = false) (hd : d.msb = true) :
    Triple (At moddi3Entry [(1, ra), (10, n), (11, d)] m K outp)
      (At 0x80017634#64 [(5, ra), (10, n), (11, -d)] m K outp) := by
  have : Code.moddi3Base = 0x80017628 := rfl
  wseg modNP moddi3Entry 0x80017634#64 [(1, ra), (10, n), (11, d)] [(5, ra), (10, n), (11, -d)]
    [1, 10, 11] [slt_zero, sge_zero, hn, hd] hc

theorem mod_nn (hn : n.msb = true) (hd : d.msb = true) :
    Triple (At moddi3Entry [(1, ra), (10, n), (11, d)] m K outp)
      (At 0x8001764c#64 [(5, ra), (10, -n), (11, -d)] m K outp) := by
  have : Code.moddi3Base = 0x80017628 := rfl
  wseg modNN moddi3Entry 0x8001764c#64 [(1, ra), (10, n), (11, d)] [(5, ra), (10, -n), (11, -d)]
    [1, 10, 11] [slt_zero, sge_zero, hn, hd] hc

theorem mod_pn (hn : n.msb = true) (hd : d.msb = false) :
    Triple (At moddi3Entry [(1, ra), (10, n), (11, d)] m K outp)
      (At 0x8001764c#64 [(5, ra), (10, -n), (11, d)] m K outp) := by
  have : Code.moddi3Base = 0x80017628 := rfl
  wseg modPN moddi3Entry 0x8001764c#64 [(1, ra), (10, n), (11, d)] [(5, ra), (10, -n), (11, d)]
    [1, 10, 11] [slt_zero, sge_zero, hn, hd] hc

/-- `mv a0,a1; jr t0` after the call at `634`. -/
theorem mod_t1 (q r : BitVec 64) (hra : ra.toNat % 4 = 0) :
    Triple (At 0x80017638#64 [(5, ra), (10, q), (11, r)] m K outp) (At ra [(10, r)] m K outp) := by
  have : Code.moddi3Base = 0x80017628 := rfl
  wseg modT1 0x80017638#64 ra [(5, ra), (10, q), (11, r)] [(10, r)] [5, 10, 11] [] hc

/-- `neg a0,a1; jr t0` after the call at `64c`. -/
theorem mod_t2 (q r : BitVec 64) (hra : ra.toNat % 4 = 0) :
    Triple (At 0x80017650#64 [(5, ra), (10, q), (11, r)] m K outp) (At ra [(10, -r)] m K outp) := by
  have : Code.moddi3Base = 0x80017628 := rfl
  wseg modT2 0x80017650#64 ra [(5, ra), (10, q), (11, r)] [(10, -r)] [5, 10, 11] [] hc

end moddi3

set_option hygiene false in
/-- `call_udiv` at a literal call site `pc` (word `w`, immediate `imm`, code `hc`). -/
macro "udiv_at " pc:term:max w:term:max imm:term:max ret:term:max hc:term:max : term =>
  `(call_udiv (pc := $pc) (w := $w) (imm := $imm) $ret _ _ _ hm (by assumption) hK
      (Tom.Machine.CodeAt.word $hc (a := ($pc : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => Vsa.Sim.decodeW s h1 h2 h3)
      ⟨by decide, Vsa.Sim.fetchOK_of_le (by simp [Vsa.Sim.tohostAddr]), by decide⟩ (by decide)
      (by decide) (by decide))

theorem neg_ne_zero {d : BitVec 64} (hd : d ≠ 0#64) : -d ≠ 0#64 := fun e =>
  hd (by simpa using e)

/-- **`__moddi3`** from any scratch state: `a0 := n.srem d`. -/
theorem moddi3_any : ∀ {m : Mem} {K : GRegs} {outp : Array String} {ra n d : BitVec 64},
    Img m → ra.toNat % 4 = 0 → d ≠ 0#64 → KeepOK divWrites K →
    Triple (At moddi3Entry [(1, ra), (10, n), (11, d)] m K outp) (At ra [(10, n.srem d)] m K outp) := by
  intro m K outp ra n d hm hra hd hK
  have hc := hm.moddi3
  have hd' := neg_ne_zero hd
  rw [BitVec.srem_eq]
  cases hsn : n.msb <;> cases hsd : d.msb
  · exact ((mod_pp ra n d K outp m hc hK hsn hsd).seq
      (udiv_at 0x80017634#64 0xf79ff0ef#32 0x1fff78#21 0x80017638#64 hc)).seq
      (mod_t1 ra K outp m hc hK _ _ hra)
  · exact ((mod_np ra n d K outp m hc hK hsn hsd).seq
      (udiv_at 0x80017634#64 0xf79ff0ef#32 0x1fff78#21 0x80017638#64 hc)).seq
      (mod_t1 ra K outp m hc hK _ _ hra)
  · exact ((mod_pn ra n d K outp m hc hK hsn hsd).seq
      (udiv_at 0x8001764c#64 0xf61ff0ef#32 0x1fff60#21 0x80017650#64 hc)).seq
      (mod_t2 ra K outp m hc hK _ _ hra)
  · exact ((mod_nn ra n d K outp m hc hK hsn hsd).seq
      (udiv_at 0x8001764c#64 0xf61ff0ef#32 0x1fff60#21 0x80017650#64 hc)).seq
      (mod_t2 ra K outp m hc hK _ _ hra)

/-! ## `__divdi3` -/

section divdi3

variable (ra n d : BitVec 64) (K : GRegs) (outp : Array String) (m : Mem)
  (hc : CodeAt m Code.divdi3Base Code.divdi3Code) (hu : CodeAt m umodBase umodCode)
  (hK : KeepOK divWrites K) (hd0 : d ≠ 0#64)

include hc hK

theorem div_pp (hn : n.msb = false) (hd : d.msb = false) :
    Triple (At divdi3Entry [(1, ra), (10, n), (11, d)] m K outp)
      (At udivdi3Entry [(1, ra), (10, n), (11, d)] m K outp) := by
  have : Code.divdi3Base = 0x800175a4 := rfl
  wseg divPP divdi3Entry udivdi3Entry [(1, ra), (10, n), (11, d)] [(1, ra), (10, n), (11, d)]
    [1, 10, 11] [slt_zero, sge_zero, hn, hd] hc

include hu hd0

theorem div_np (hn : n.msb = true) (hd : d.msb = false) :
    Triple (At divdi3Entry [(1, ra), (10, n), (11, d)] m K outp)
      (At 0x8001761c#64 [(5, ra), (10, -n), (11, d)] m K outp) := by
  have : Code.divdi3Base = 0x800175a4 := rfl
  have : umodBase = 0x800175f4 := rfl
  wseg divNP divdi3Entry 0x8001761c#64 [(1, ra), (10, n), (11, d)] [(5, ra), (10, -n), (11, d)]
    [1, 10, 11] [slt_zero, sge_zero, sgt_zero _ hd0, hn, hd] hc, hu

theorem div_nn (hn : n.msb = true) (hd : d.msb = true) :
    Triple (At divdi3Entry [(1, ra), (10, n), (11, d)] m K outp)
      (At udivdi3Entry [(1, ra), (10, -n), (11, -d)] m K outp) := by
  have : Code.divdi3Base = 0x800175a4 := rfl
  have : umodBase = 0x800175f4 := rfl
  wseg divNN divdi3Entry udivdi3Entry [(1, ra), (10, n), (11, d)] [(1, ra), (10, -n), (11, -d)]
    [1, 10, 11] [slt_zero, sge_zero, sgt_zero _ hd0, hn, hd] hc, hu

omit hd0 in
theorem div_pn (hn : n.msb = false) (hd : d.msb = true) :
    Triple (At divdi3Entry [(1, ra), (10, n), (11, d)] m K outp)
      (At 0x8001761c#64 [(5, ra), (10, n), (11, -d)] m K outp) := by
  have : Code.divdi3Base = 0x800175a4 := rfl
  have : umodBase = 0x800175f4 := rfl
  wseg divPN divdi3Entry 0x8001761c#64 [(1, ra), (10, n), (11, d)] [(5, ra), (10, n), (11, -d)]
    [1, 10, 11] [slt_zero, sge_zero, hn, hd] hc, hu

end divdi3

/-- `neg a0,a0; jr t0` after the call at `61c`. -/
theorem div_t (ra : BitVec 64) (K : GRegs) (outp : Array String) (m : Mem)
    (hu : CodeAt m umodBase umodCode) (hK : KeepOK divWrites K) (q r : BitVec 64)
    (hra : ra.toNat % 4 = 0) :
    Triple (At 0x80017620#64 [(5, ra), (10, q), (11, r)] m K outp) (At ra [(10, -q)] m K outp) := by
  have : umodBase = 0x800175f4 := rfl
  wseg divT 0x80017620#64 ra [(5, ra), (10, q), (11, r)] [(10, -q)] [5, 10, 11] [] hu

/-- The tail-called unsigned core, returning to the caller. -/
theorem div_core {m : Mem} {K : GRegs} {outp : Array String} {ra a b : BitVec 64} (hm : Img m)
    (hra : ra.toNat % 4 = 0) (hb : b ≠ 0#64) (hK : KeepOK divWrites K) :
    Triple (At udivdi3Entry [(1, ra), (10, a), (11, b)] m K outp) (At ra [(10, a / b)] m K outp) :=
  (Udivdi3.correctK hm hra hb (keepOK_sub hK (by decide))).rmap
    (fun _ h => h.weaken (by simp))

/-- **`__divdi3`** from any scratch state: `a0 := n.sdiv d`, the wrapping
`intMin / -1` included. -/
theorem divdi3_any : ∀ {m : Mem} {K : GRegs} {outp : Array String} {ra n d : BitVec 64},
    Img m → ra.toNat % 4 = 0 → d ≠ 0#64 → KeepOK divWrites K →
    Triple (At divdi3Entry [(1, ra), (10, n), (11, d)] m K outp) (At ra [(10, n.sdiv d)] m K outp) := by
  intro m K outp ra n d hm hra hd hK
  have hc := hm.divdi3
  have hu : CodeAt m umodBase umodCode := hm.umoddi3
  have hd' := neg_ne_zero hd
  rw [BitVec.sdiv_eq]
  cases hsn : n.msb <;> cases hsd : d.msb
  · exact (div_pp ra n d K outp m hc hK hsn hsd).seq (div_core hm hra hd hK)
  · exact ((div_pn ra n d K outp m hc hu hK hsn hsd).seq
      (udiv_at 0x8001761c#64 0xf91ff0ef#32 0x1fff90#21 0x80017620#64 hu)).seq
      (div_t ra K outp m hu hK _ _ hra)
  · exact ((div_np ra n d K outp m hc hu hK hd hsn hsd).seq
      (udiv_at 0x8001761c#64 0xf91ff0ef#32 0x1fff90#21 0x80017620#64 hu)).seq
      (div_t ra K outp m hu hK _ _ hra)
  · exact (div_nn ra n d K outp m hc hu hK hd hsn hsd).seq (div_core hm hra hd' hK)

namespace Moddi3

theorem correctK : Api.Libgcc.Moddi3.StatementK := moddi3_any

theorem correct : Api.Libgcc.Moddi3.Statement := by
  intro m v outp ra n d hm hra hd
  exact correctK hm hra hd (keepOK_abi v)

end Moddi3

namespace Divdi3

theorem correctK : Api.Libgcc.Divdi3.StatementK := divdi3_any

theorem correct : Api.Libgcc.Divdi3.Statement := by
  intro m v outp ra n d hm hra hd
  exact correctK hm hra hd (keepOK_abi v)

end Divdi3

end Tom.Machine.Fn.Libgcc
