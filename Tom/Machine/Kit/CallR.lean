import Tom.Machine.Kit.Run
import Tom.Machine.Kit.Jalr

/-!
# An allocating call through a register

`call_heap` (`Kit/MeetHeap.lean`) for `jalr ra, 0(rs1)` instead of `jal`: the target is the value
pinned for `rs1` in the register list, which must be the contract's entry (`htgt`, by computation;
`s_mp_exptmod_fast`'s `redux` through `s8`). The rest is `HContract.run`.
-/

namespace Tom.Machine

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa Vsa.Sim Vsa.Logic
open Sail.ConcurrencyInterfaceV1.PreSail

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι}

/-- **The allocating call rule through a register**: `jalr ra, 0(rs1)` at `pc` with `rs1` pinned to
`C.entry`, then the continuation at `ret = pc + 4` as `call_heap`'s. -/
theorem call_heapR (C : HContract) (p : C.P) (σ : C.R → ι) {κ : ι → Kind}
    {H0 : List (Nat × Nat)} {Wr0 : Nat → Prop} {m0 m M : Mem}
    (hSt : St ρ isW W κ m M) (hp : HP ρ isW H0 (C.hin p) Wr0 m0 m)
    {base : Nat} {code : List (BitVec 32)} (hc : CodeAt M base code)
    {pc : BitVec 64} (w : BitVec 32) (rs1 : Nat) (ret : BitVec 64) {L K : GRegs} {outp : Array String}
    {Q : Vsa.Machine.Config → Prop} (hres : C.Res p)
    (k : ∀ x M', C.Q p x →
      St (Iv.upd ρ (σ C.site) (C.site' p x)) isW W (Kind.pushH σ C.ws κ (C.out p x)) M' M' →
      HP (Iv.upd ρ (σ C.site) (C.site' p x)) isW H0 (C.hout p x) Wr0 m0 M' →
      Triple (At ret (C.rets p x ret ++ (Abi.ofL (((1, ret) :: dropRa L) ++ K)).keep) M' K outp) Q)
    (htgt : BitVec.update (srcVal rs1 L + sign_extend (m := 64) (0#12 : BitVec 12)) 0 0#1 = C.entry)
    (hsub : ∀ r, (C.lay p r).Sub (ρ (σ r)) := by intro r; cases r <;> iv_omega)
    (hk : ∀ r, C.kind p r = κ (σ r) := by intro r; cases r <;> rfl)
    (hwd : WordIn base code pc.toNat w = true := by decide +kernel)
    (hdec : ∀ s : SequentialState RegisterType trivialChoiceSource,
      s.regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa) →
      s.regs.get? Register.cur_privilege = some ((Privilege.Machine) : RegisterType Register.cur_privilege) →
      s.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg) →
      (ext_decode w).run s = .ok (instruction.JALR ((0#12 : BitVec 12), gprIdx rs1, regidx.Regidx 0x01#5)) s :=
        by exact fun s h1 h2 h3 => decodeW s h1 h2 h3)
    (hword : ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append (w.extractLsb' 8 8)).append
      (w.extractLsb' 0 8)) = w := by decide)
    (hnotrvc : Sail.BitVec.extractLsb ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append
      (w.extractLsb' 8 8)).append (w.extractLsb' 0 8)) 1 0 = (0b11#2 : BitVec 2) := by decide)
    (hrs : rs1 ∈ keysG L := by decide) (hrs31 : rs1 ≤ 31 := by decide)
    (hal : C.entry.toNat % 4 = 0 := by decide) (hret : Sail.BitVec.addInt pc 4 = ret := by decide)
    (hra : ret.toNat % 4 = 0 := by decide)
    (hfe : 0x80000000 ≤ pc.toNat ∧ FetchOK pc.toNat ∧ pc.toNat % 4 = 0 :=
      by exact ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩)
    (hsep : SepPres isW C.isW σ C.all = true := by decide) (hw : (C.ws.map σ).all isW = true := by decide)
    (hWw : W.all isW = true := by decide)
    (hLk : (keysG (dropRa L)).all (fun n => decide (2 ≤ n) && decide (n ≤ 31)) = true := by exact rfl)
    (hKk : (keysG K).all (fun n => decide (2 ≤ n) && decide (n ≤ 31)) = true := by exact rfl)
    (hargs : SubR ((1, ret) :: C.args p) (((1, ret) :: dropRa L) ++ K) := by exact rfl)
    (hkeys : abiKeys.all (fun n => (lookupG n (((1, ret) :: dropRa L) ++ K)).isSome) = true := by exact rfl)
    (hK' : ∀ x, SubR K (C.rets p x ret ++ (Abi.ofL (((1, ret) :: dropRa L) ++ K)).keep) := by
      intro _; exact rfl) :
    Triple (At pc L M K outp) Q := by
  have hj := jalr_at (L := L) (L' := dropRa L) (keep := K) (outp := outp) (m := M) (imm := 0#12) (hc.word hwd)
    hword hnotrvc hdec hfe hrs hrs31 (by rw [htgt]; exact hal) (fun _ h => (List.mem_filter.1 h).1)
    (fun n hn => by have := List.all_eq_true.1 hLk n hn; simpa using this)
    (fun n hn => by have := List.all_eq_true.1 hKk n hn; simpa using this)
  rw [htgt, hret] at hj
  exact Triple.seq hj (Triple.ex (C.run p σ hSt hp hres hra hsub hk hsep hw hWw hargs hkeys hK')
    fun x M' ⟨hq, hS', hP'⟩ => k x M' hq hS' hP')

end

end Tom.Machine
