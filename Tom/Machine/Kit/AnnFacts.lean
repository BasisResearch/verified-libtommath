import Tom.Machine.Kit.Run
import Tom.Machine.Api.Std_r6c
import Tom.Machine.Api.Std_multi8

/-!
# Small generic facts annotation texts use

They were per-function helpers (`Fn/MpDivG5K.lean`, `Fn/ToomMulG5K.lean`, `Fn/MpSqrSG5K.lean`,
`Fn/Mul2HDG5K.lean`) used by several assemblies' annotations (`mdiv`, `mdivq`, `mdivr`, `mmod`, `tmul`,
`tmula`, `mul2hd`) or helpers:

* `WD1.seqOvl`, `WD2.seqOvl`: one digit store at `dp + 4` / `dp + 8` (`St.seqD` at `i = 1`, `2`): a
  raw step re-types the state (`have h : WD1 … := h`) and the generator's `"o"` rule's `h.seqOvl`
  resolves to them (the `"d"` rule parses only `dp + 4 * i`); `WSz.seqS`: a struct's sign stored as
  the word a `snez` leaves (`if x = 0 then 0 else 1` as a `BitVec`);
* `Std.ordNG_lt_eq`, `Std.ordNG_ne_lt`: `mp_cmp_mag`'s pinned word against `MP_LT`;
* `Std.StkRes.down`: a callee's stack residue below the caller's frame; `hdr_bd`: a struct's address
  bounds; `disj_frame`: a region off a deep stack window is off its top part (`omega` overruns the
  recursion depth on it);
* `ovl_ite`, `upd_ovl_ite`: a loop's overlay digit function (and a final carry digit) as one `if`;
* `al3`, `off3`, `soff3`, `apos3`: the three-block calls' residues, index by index.
-/

namespace Tom.Machine

open Vsa Vsa.Sim Vsa.Logic Tom.Machine.Api Tom.Machine.Api.Heap Tom.Machine.Std

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind} {m M : Mem}
  {pc pc' : BitVec 64} {L0 L L' K : GRegs} {o : Array String} {Q : Vsa.Machine.Config → Prop}

abbrev WD1 (ρ : ι → Iv) (isW : ι → Bool) (W : List ι) (κ : ι → Kind) (m M : Mem) : Prop := St ρ isW W κ m M
abbrev WD2 (ρ : ι → Iv) (isW : ι → Bool) (W : List ι) (κ : ι → Kind) (m M : Mem) : Prop := St ρ isW W κ m M
abbrev WSz (ρ : ι → Iv) (isW : ι → Bool) (W : List ι) (κ : ι → Kind) (m M : Mem) : Prop := St ρ isW W κ m M

theorem WD1.seqOvl (h : WD1 ρ isW W κ m M) (r : ι) {dp n v : Nat} {f : Nat → Nat} (hk : κ r = .mpD dp n f)
    (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M [(dp + 4, 4, BitVec.ofNat 64 v)]) K o))
    (hi : 1 < n) (hv : v < 2 ^ 32) (_ht : (0 : Nat) = 0)
    (k : ∀ M', St ρ isW W (Kind.set κ r (.mpD dp n (fun j => if j = 1 then v else f j))) m M' →
      Triple (At pc' L' M' K o) Q)
    (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q :=
  St.seqD h r (i := 1) hk hseg hi hv k hw hW hL

theorem WD2.seqOvl (h : WD2 ρ isW W κ m M) (r : ι) {dp n v : Nat} {f : Nat → Nat} (hk : κ r = .mpD dp n f)
    (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M [(dp + 8, 4, BitVec.ofNat 64 v)]) K o))
    (hi : 2 < n) (hv : v < 2 ^ 32) (_ht : (0 : Nat) = 0)
    (k : ∀ M', St ρ isW W (Kind.set κ r (.mpD dp n (fun j => if j = 2 then v else f j))) m M' →
      Triple (At pc' L' M' K o) Q)
    (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q :=
  St.seqD h r (i := 2) hk hseg hi hv k hw hW hL

theorem WSz.seqS (h : WSz ρ isW W κ m M) (r : ι) {p dp : Nat} {a : MpInt} {x : BitVec 64}
    (hk : κ r = .mpS p dp a)
    (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M [(p + 8, 4, if x = 0#64 then 0#64 else 1#64)]) K o))
    (_ht : 0 < 1)
    (k : ∀ M', St ρ isW W (Kind.set κ r (.mpS p dp { a with sign := if x = 0#64 then 0 else 1 })) m M' →
      Triple (At pc' L' M' K o) Q)
    (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q := by
  have e : (if x = 0#64 then 0#64 else 1#64) = BitVec.ofNat 64 (if x = 0#64 then 0 else 1) := by
    split <;> rfl
  rw [e] at hseg
  exact St.seqS h r hk hseg (by split <;> decide) k hw hW hL

end

theorem Std.ordNG_lt_eq {x y : Nat} (h : x < y) : ordNG (compare x y) = 18446744073709551615 := by
  rw [Nat.compare_eq_lt.2 h]; rfl

theorem Std.ordNG_ne_lt {x y : Nat} (h : ¬ x < y) : ordNG (compare x y) ≠ 18446744073709551615 := by
  intro he; apply h; apply Nat.compare_eq_lt.1
  revert he; cases compare x y <;> simp [ordNG]

/-- A struct's address bounds (from its header's geometry). -/
theorem hdr_bd {M : Mem} {p dp : Nat} {a : MpInt} (h : Hdr M p dp a) :
    0x80000000 ≤ p ∧ p + 24 ≤ 0x100000000 ∧ p % 8 = 0 := by
  have g := Hdr.geom h
  exact ⟨g.st.lo_ge, g.st.hi_le, g.st_al⟩

/-- A region off a deep stack window (`sp - 896 … sp`) is off its top part (by hand: `omega` overruns
the recursion depth on `x ≤ sp - 896 → x ≤ sp - 272`). -/
theorem disj_frame {x n sp : Nat} (hsp : 896 ≤ sp) (h : x + n ≤ sp - 896 ∨ sp - 896 + 896 ≤ x) :
    x + n ≤ sp - 272 ∨ sp ≤ x := by
  rcases h with h | h
  · exact .inl (Nat.le_trans h (Nat.sub_le_sub_left (by decide) sp))
  · exact .inr (by rw [Nat.sub_add_cancel hsp] at h; exact h)

/-- A residue's stack below a frame of `k` bytes. -/
theorem Std.StkRes.down {sp F G k : Nat} (h : StkRes sp F) (hk : k % 16 = 0) (hG : G + k ≤ F) : StkRes (sp - k) G :=
  ⟨by have := h.al; have := h.lo; omega, by have := h.lo; omega, by have := h.hi; omega⟩

/-- An overlay whose lower part agrees with `h` below `u`, as one `if` (a loop's digit function at
its exit, `mp_mul_2`'s `ovl (m2g a) A.digit a->used`). -/
theorem ovl_ite {g h old : Nat → Nat} {u : Nat} (hg : ∀ j, j < u → g j = h j) :
    ∀ j, ovl g old u j = if j < u then h j else old j := by
  intro j; simp only [ovl]; split
  · exact hg j ‹_›
  · rfl

/-- `ovl_ite` with one more digit `v = h u` stored at `u` (a final carry). -/
theorem upd_ovl_ite {g h old : Nat → Nat} {u v : Nat} (hg : ∀ j, j < u → g j = h j) (hv : h u = v) :
    ∀ j, Mont.upd (ovl g old u) u v j = if j < u + 1 then h j else old j := by
  intro j; simp only [Mont.upd, ovl]
  by_cases e : j = u
  · subst e; rw [if_pos rfl, if_pos (by omega), hv]
  · rw [if_neg e]; split
    · rw [if_pos (by omega)]; exact hg j ‹_›
    · rw [if_neg (by omega)]

/-! ## The three-block calls' residues, index by index -/

theorem al3 {a b c : Nat} (ha : a % 8 = 0) (hb : b % 8 = 0) (hc : c % 8 = 0) :
    ∀ i : Fin 3, [a, b, c].getD i 0 % 8 = 0
  | ⟨0, _⟩ => ha
  | ⟨1, _⟩ => hb
  | ⟨2, _⟩ => hc

theorem off3 {a b c : Nat} (ha : OffHeap a 24) (hb : OffHeap b 24) (hc : OffHeap c 24) :
    ∀ i : Fin 3, OffHeap ([a, b, c].getD i 0) 24
  | ⟨0, _⟩ => ha
  | ⟨1, _⟩ => hb
  | ⟨2, _⟩ => hc

theorem soff3 {x y w : Multi.Arg} (hx : OffHeap x.1 24) (hy : OffHeap y.1 24) (hw : OffHeap w.1 24) :
    ∀ i : Fin 3, OffHeap (argAt [x, y, w] i).1 24
  | ⟨0, _⟩ => hx
  | ⟨1, _⟩ => hy
  | ⟨2, _⟩ => hw

theorem apos3 {x y w : Multi.Arg} (hx : 0 < x.2.2.alloc) (hy : 0 < y.2.2.alloc) (hw : 0 < w.2.2.alloc) :
    ∀ i : Fin 3, 0 < (argAt [x, y, w] i).2.2.alloc
  | ⟨0, _⟩ => hx
  | ⟨1, _⟩ => hy
  | ⟨2, _⟩ => hw

end Tom.Machine
