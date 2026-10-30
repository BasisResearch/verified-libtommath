import Tom.Machine.Api.Std_capf
import Tom.Machine.Api.Std_capf2
import Tom.Machine.Api.Exptmod
import Tom.Machine.Kit.Widen
import Tom.Machine.Kit.TabState
import Tom.Spec.SMpExptmodFastMode

/-!
# `redux(x, n, mp)` growing `x`: `s_mp_exptmod_fast`'s reduction through `s8`

`s_mp_exptmod_fast` calls its reduction indirectly (`jalr s8`), `s8` set by the setup branch to one of
four routines, `rk md P->used`: `0` `s_mp_montgomery_reduce_fast` (`redmode == 0`, the compiled fast test
`2 P->used ≤ 510`), `3` `mp_montgomery_reduce` (`redmode == 0` otherwise), `1` `mp_dr_reduce`, `2`
`mp_reduce_2k`. All four grow `x` (`Api/MontRedFastG.lean`, `Api/MontRedGr.lean`, `Api/DrReduceG.lean`,
`Api/MpReduce2kG.lean`; regions, parameters and the allocating frame of `Api/ReduxG.lean`). `reduxG k` is
routine `k`'s contract on the deepest stack (the Montgomery routines' 4800 bytes), the residue of the
routine and its relation, read as the Spec's `redRel` of the mode (`kmd k`).
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap
open Tom.Machine.Api.MpReduce2k (P R)

/-- The routine `s8` points to for mode `md` and `P->used = u`. -/
def rk (md u : Nat) : Nat :=
  if md = 0 then (if 2 * u ≤ 510 then 0 else 3) else if md = 1 then 1 else 2

/-- Routine `k`'s entry. -/
def reduxGE : Nat → BitVec 64
  | 0 => MontRedFastG.entry
  | 1 => DrReduceG.entry
  | 2 => MpReduce2kG.entry
  | _ => MontRedGr.entry

/-- The mode routine `k` reduces in. -/
def kmd : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

theorem rk_fast {u : Nat} (h : 2 * u ≤ 510) : rk 0 u = 0 := by simp [rk, h]
theorem rk_slow {u : Nat} (h : ¬ 2 * u ≤ 510) : rk 0 u = 3 := by simp [rk, h]
theorem rk_one (u : Nat) : rk 1 u = 1 := by simp [rk]
theorem rk_ge2 {md u : Nat} (h : 2 ≤ md) : rk md u = 2 := by
  unfold rk; rw [if_neg (by omega), if_neg (by omega)]

/-- The stack: the Montgomery routines' (`mp_dr_reduce` 672, `mp_reduce_2k` 736). -/
abbrev Fg : Nat := 4800

def layRG (p : P) : R → Iv
  | .stk => ⟨p.sp - Fg, Fg⟩
  | r => MpReduce2k.lay p r

/-- Routine `k`'s residue. -/
def ResGK : Nat → P → Prop
  | 0, p => MontRedFastG.Res p
  | 1, p => DrReduceG.Res p
  | 2, p => MpReduce2kG.Res p
  | _, p => MontRedGr.Res p

structure RedGRes (k : Nat) (p : P) : Prop where
  stk : StkRes p.sp Fg
  k : ResGK k p

/-- What `x` holds after: shaped, live, placed; on `MP_OKAY` the mode's reduction. -/
def RQG (k : Nat) (p : P) (x : ReduxG.X) : Prop :=
  ReduxG.Out p (layRG p .aD) (SMpExptmodFastStep.redRel (kmd k) p.a p.n p.d) x

theorem nmag_pos {p : P} {k : Nat} (h : ResGK k p) : 0 < p.n.mag := by
  rcases k with _ | _ | _ | k
  · have h' : MontRedFastG.Res p := h
    have := h'.x_lt; exact Nat.pos_of_ne_zero fun e => by rw [e, Nat.zero_mul] at this; omega
  · exact (show DrReduceG.Res p from h).npos
  · exact (show MpReduce2kG.Res p from h).npos
  · have h' : MontRedGr.Res p := h
    have := h'.x_lt; exact Nat.pos_of_ne_zero fun e => by rw [e, Nat.zero_mul] at this; omega

theorem apos_k {p : P} {k : Nat} (h : ResGK k p) : 0 < p.a.alloc ∧ p.n.Valid := by
  rcases k with _ | _ | _ | k
  · have h' : MontRedFastG.Res p := h; exact ⟨h'.apos, h'.vn⟩
  · have h' : DrReduceG.Res p := h; exact ⟨h'.apos, h'.vn⟩
  · have h' : MpReduce2kG.Res p := h; exact ⟨h'.apos, h'.vn⟩
  · have h' : MontRedGr.Res p := h; exact ⟨h'.apos, h'.vn⟩

/-- **`redux` as routine `k`**, growing `x` (`Api/MpReduce2k.lean`'s regions). -/
def reduxG (k : Nat) : HContract where
  P := P
  X := ReduxG.X
  R := R
  all := [.stk, .aS, .aD, .nS, .nD, .code]
  hall := MpReduce2k.all
  entry := reduxGE k
  args := MpReduce2k.args
  rets := ReduxG.rets
  lay := layRG
  kind := MpReduce2k.kind
  out := ReduxG.out
  isW := MpReduce2k.isW
  ws := MpReduce2k.ws
  site := .aD
  site' := ReduxG.site'
  hin := ReduxG.hin
  hout := ReduxG.hout
  Res := RedGRes k
  Q := RQG k
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    obtain ⟨ok, q, a'⟩ := x
    cases r <;> simp_all [ReduxG.out, MpReduce2k.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    obtain ⟨ha, hvn⟩ := apos_k h.k
    have := MpInt.alloc_pos_of_mag hvn (nmag_pos h.k)
    cases r with
    | stk => exact .inl (show 0 < Fg by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | nD => exact .inl (show 0 < 4 * p.n.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (show 0 < 24 by decide)
  spec := by
    intro p m v outp ra hra hres hS hB hH hoff
    rcases k with _ | _ | _ | k
    · -- `s_mp_montgomery_reduce_fast`
      exact Triple.widenCv (fun hS' hB' hoff' => Fn.MontRedFastGG5.correct hra hres.k hS' hB' hH hoff') id
        (fun _ _ _ h => h) (fun _ h => h) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) .stk (by decide)
        (fun r e => by cases r <;> first | exact absurd rfl e | rfl) (Iv.sub_self _) rfl
        (fun ⟨_, _, _⟩ => rfl) (by show 0 < MontRedFastG.F; decide) hS hB hoff
    · -- `mp_dr_reduce`
      exact Triple.widenCv (fun hS' hB' hoff' => Fn.DrReduceGG5.correct hra hres.k hS' hB' hH hoff') id
        (fun _ _ _ h => h) (fun _ h => h) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) .stk (by decide)
        (fun r e => by cases r <;> first | exact absurd rfl e | rfl) (hres.stk.sub (by decide)) rfl
        (fun ⟨_, _, _⟩ => rfl) (by show 0 < DrReduceG.F; decide) hS hB hoff
    · -- `mp_reduce_2k`
      exact Triple.widenCv (fun hS' hB' hoff' => Fn.MpReduce2kGG5.correct hra hres.k hS' hB' hH hoff') id
        (fun _ _ _ h => h) (fun _ h => h) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) .stk (by decide)
        (fun r e => by cases r <;> first | exact absurd rfl e | rfl) (hres.stk.sub (by decide)) rfl
        (fun ⟨_, _, _⟩ => rfl) (by show 0 < MpReduce2kG.F; decide) hS hB hoff
    · -- `mp_montgomery_reduce`
      exact Triple.widenCv (fun hS' hB' hoff' => Fn.MontRedGrG5.correct hra hres.k hS' hB' hH hoff') id
        (fun _ _ _ h => h) (fun _ h => h) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) .stk (by decide)
        (fun r e => by cases r <;> first | exact absurd rfl e | rfl) (Iv.sub_self _) rfl
        (fun ⟨_, _, _⟩ => rfl) (by show 0 < MontRedGr.F; decide) hS hB hoff

/-! The record's fields that do not depend on the routine (for the caller's checks). -/
theorem reduxG_ws (k : Nat) : (reduxG k).ws = MpReduce2k.ws := rfl
theorem reduxG_out (k : Nat) : (reduxG k).out = ReduxG.out := rfl
theorem reduxG_kind (k : Nat) : (reduxG k).kind = MpReduce2k.kind := rfl
theorem reduxG_lay (k : Nat) : (reduxG k).lay = layRG := rfl
theorem reduxG_isW (k : Nat) : (reduxG k).isW = MpReduce2k.isW := rfl

open Sail LeanRV64DExecutable.Functions in
/-- **`jalr s8` reaches routine `k`** (`call_heapR`'s `htgt`). -/
theorem reduxG_tgt {k re : Nat} (h : BitVec.ofNat 64 re = reduxGE k) :
    BitVec.update (BitVec.ofNat 64 re + sign_extend (m := 64) (0#12 : BitVec 12)) 0 0#1 = (reduxG k).entry := by
  rw [h]
  rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · exact (by decide : BitVec.update (MontRedGr.entry + sign_extend (m := 64) (0#12 : BitVec 12)) 0 0#1 = MontRedGr.entry)

/-- Routine `k`'s entry is word-aligned (`call_heapR`'s `hal`). -/
theorem reduxG_al (k : Nat) : (reduxG k).entry.toNat % 4 = 0 := by
  rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · exact (by decide : MontRedGr.entry.toNat % 4 = 0)

/-- The routine's relation is the mode's. -/
theorem rp_redG {md u : Nat} {x n x' : MpInt} {d : Nat}
    (h : SMpExptmodFastStep.redRel (kmd (rk md u)) x n d x') : SMpExptmodFastStep.redRel md x n d x' := by
  rcases md with _ | _ | md
  · by_cases hu : 2 * u ≤ 510
    · rw [show rk 0 u = 0 by simp [rk, hu]] at h; exact h
    · rw [show rk 0 u = 3 by simp [rk, hu]] at h; exact h
  · exact h
  · rw [show rk (md + 2) u = 2 by simp [rk]] at h; exact h

open Tom.SMpExptmodFastStep Tom.WindowStep in
/-- **`redux`'s residue at `s_mp_exptmod_fast`'s calls**: `x` a product of two residues (at most
`2 P->used` digits, `|x| ≤ (|P| - 1)^2`), the setup's `Cond`, the C's `int`s on such a product. -/
theorem reduxG_res {md u : Nat} {p : P} (hu : p.n.used = u) (hc : Cond p.n md p.d) (hdr : md = 1 → 0 < p.n.digit 0)
    (hr2k : 2 ≤ md → Api.SMpExptmodFast.Exact2k p.n) (hstk : StkRes p.sp Fg) (hva : p.a.Valid)
    (hlt : p.a.mag ≤ (p.n.mag - 1) * (p.n.mag - 1)) (hau : p.a.used ≤ 2 * p.n.used) (hapos : 0 < p.a.alloc)
    (hbits : Layout.digitBits * (2 * p.n.used + 1) < 2 ^ 31) (aoff : OffHeap p.pa 24) (noff : OffHeap p.pn 24) :
    (reduxG (rk md u)).Res p := by
  subst hu
  show RedGRes (rk md p.n.used) p
  have hvn := hc.valid
  have hg := hc.gt1
  have hm := MpInt.mag_lt hvn.toShape
  have hb : 28 * (2 * p.n.used + 1) < 2 ^ 31 := hbits
  have hsq : p.a.mag < radix ^ p.n.used * radix ^ p.n.used :=
    Nat.lt_of_le_of_lt hlt (Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) (by omega))
  rcases md with _ | _ | md
  · obtain ⟨ho, hd⟩ := hc.mont rfl
    have hrho : (p.n.mag * p.d + 1) % radix = 0 := by
      have e := Tom.Mont.MpInt.mag_mod_radix hvn.toShape
      have hs := Tom.Mont.setupRho_spec _ (digit0_odd hvn.toShape ho)
      have hdm := Nat.div_add_mod p.n.mag radix
      rw [e] at hdm
      rw [hd, ← hdm, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_mul_mod_self_left]
      exact hs
    have hrl : p.d < radix := by rw [hd]; exact Tom.Mont.setupRho_lt _
    have hxl : p.a.mag < p.n.mag * radix ^ p.n.used :=
      Nat.lt_of_le_of_lt hlt (Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) (by omega))
    by_cases hu : 2 * p.n.used ≤ 510
    · rw [show rk 0 p.n.used = 0 by simp [rk, hu]]
      exact ⟨hstk, (⟨hstk, hva, hvn, hrho, hrl, hxl, by omega, hapos, aoff, noff⟩ : MontRedFastG.Res p)⟩
    · rw [show rk 0 p.n.used = 3 by simp [rk, hu]]
      exact ⟨hstk, (⟨hstk, hva, hvn, hrho, hrl, hxl, hapos, aoff, noff⟩ : MontRedGr.Res p)⟩
  · obtain ⟨_, hd⟩ := hc.dr rfl
    have h0 := hdr rfl
    rw [show rk 1 p.n.used = 1 by simp [rk]]
    exact ⟨hstk, (⟨hstk.mono (by decide), hva, hvn, by omega,
      by rw [hd]; unfold drSetupDigit; have := radix_pos; omega,
      by rw [Nat.two_mul, Nat.pow_add]; exact hsq, hapos, aoff, noff⟩ : DrReduceG.Res p)⟩
  · rw [show rk (md + 2) p.n.used = 2 by simp [rk]]
    have hs := hc.r2k (by omega)
    have hx := hr2k (by omega)
    exact ⟨hstk, (⟨hstk.mono (by decide), hva, hvn, by omega, by rw [hs.val]; exact Nat.mod_lt _ radix_pos,
      by rw [hs.val]; exact hx, by show 28 * p.n.used < 2 ^ 31; omega, by show 28 * p.a.used < 2 ^ 31; omega,
      hapos, aoff, noff⟩ : MpReduce2kG.Res p)⟩

end Tom.Machine.Std
