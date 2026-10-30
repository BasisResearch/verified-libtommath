import Tom.Machine.Fn.Calloc
import Tom.Machine.Fn.AllocCap
import Tom.Machine.Fn.Memset
import Tom.Machine.Fn.Libgcc

/-!
# `calloc` on the machine: memory facts the assembly uses

Code and `_impure_ptr` across writes elsewhere, the zero doublewords of the
zeroing paths, the capacity word `_calloc_r` computes from the chunk header.
-/

namespace Tom.Machine.Fn.Calloc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc
open VsaIris.MallocFast

/-- The image's code and rodata survive writes off the text section. -/
theorem img_of {m M : Mem} (h : Img m) (hk : ∀ x, x < 0x80018880 → M[x]? = m[x]?) : Img M :=
  Img.reads (ρ := fun (_ : Unit) => textIv) (r := ()) (Iv.sub_self _) m M
    (fun x hx => hk x (by
      rcases hx with hx | hx
      · unfold Iv.In textIv textBase textLen at hx; simp only at hx; omega
      · exact hx.elim)) h

theorem impure_of {m M : Mem} (h : ImpureAt m)
    (hk : ∀ x, 0x80019510 ≤ x → x < 0x80019518 → M[x]? = m[x]?) : ImpureAt M := by
  intro i b hb
  have hi : i < 8 := by
    have := List.getElem?_eq_some_iff.1 hb
    exact this.1
  rw [hk _ (by unfold impurePtr; omega) (by unfold impurePtr; omega)]
  exact h i b hb

theorem impure_word {m : Mem} (h : ImpureAt m) : bytesT8 m 0x80019510 = reent := by
  have e : ∀ i b, impureBytes[i]? = some b → m[0x80019510 + i]? = some b := h
  simp only [bytesT8]
  rw [e 0 _ rfl, e 1 _ rfl, e 2 _ rfl, e 3 _ rfl, e 4 _ rfl, e 5 _ rfl, e 6 _ rfl, e 7 _ rfl]
  rfl

/-! ## Zero doublewords -/

theorem writeMap8_zero (M : Mem) (a x : Nat) (h1 : a ≤ x) (h2 : x < a + 8) :
    (writeMap8 M a (sdData_val 0#64))[x]? = some 0 := by
  have hz : ∀ i, BitVec.extractLsb' i 8 (sdData_val 0#64) = 0#8 := fun i => by
    simp [sdData_val, Sail.BitVec.extractLsb]
  simp only [writeMap8, Std.ExtHashMap.getElem?_insert, beq_iff_eq, hz]
  have : x = a ∨ x = a + 1 ∨ x = a + 2 ∨ x = a + 3 ∨ x = a + 4 ∨ x = a + 5 ∨ x = a + 6 ∨ x = a + 7 := by
    omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem outL_of {x : Nat} : ∀ {log : List WEntry}, (∀ e ∈ log, e.2.1 = 8) →
    ¬ (∃ e ∈ log, e.1 ≤ x ∧ x < e.1 + 8) → OutL log x
  | [], _, _ => trivial
  | d :: log, h8, hn => by
    refine ⟨?_, outL_of (fun e he => h8 e (List.mem_cons_of_mem _ he))
      (fun ⟨e, he, h1, h2⟩ => hn ⟨e, List.mem_cons_of_mem _ he, h1, h2⟩)⟩
    rw [h8 d (List.mem_cons_self ..)]
    rcases Nat.lt_or_ge x d.1 with h | h
    · exact .inl h
    · exact .inr (Nat.le_of_not_lt fun h' => hn ⟨d, List.mem_cons_self .., h, h'⟩)

/-- A byte under a zero doubleword of `log` (all entries zero doublewords) reads 0. -/
theorem writeLog_zero : ∀ (log : List WEntry) (M : Mem) (x : Nat),
    (∀ e ∈ log, e.2 = (8, 0#64)) → (∃ e ∈ log, e.1 ≤ x ∧ x < e.1 + 8) →
    (writeLog M log)[x]? = some 0
  | [], _, _, _, ⟨_, he, _⟩ => by cases he
  | e :: log, M, x, hz, hx => by
    show (writeLog (applyW M e) log)[x]? = some 0
    by_cases hl : ∃ e' ∈ log, e'.1 ≤ x ∧ x < e'.1 + 8
    · exact writeLog_zero log _ x (fun e' he' => hz e' (List.mem_cons_of_mem _ he')) hl
    · obtain ⟨e', he', h1, h2⟩ := hx
      have heq : e' = e := by
        rcases List.mem_cons.1 he' with h | h
        · exact h
        · exact absurd ⟨e', h, h1, h2⟩ hl
      subst heq
      have hout : OutL log x :=
        outL_of (fun d hd => by rw [hz d (List.mem_cons_of_mem _ hd)]) hl
      rw [writeLog_out _ _ _ hout]
      obtain ⟨a, w, d⟩ := e'
      have := hz _ (List.mem_cons_self ..)
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      exact writeMap8_zero M a x h1 h2

/-! ## The capacity word -/

theorem bytesT8_wordOf (M : Mem) (a : Nat) :
    bytesT8 M a = bytesVal .ld (wordOf (Fn.Alloc.img M) a) := by
  simp only [bytesVal, wordOf, Fn.Alloc.img, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq,
    List.getD_cons_succ, List.getD_cons_zero, bytesT8]

/-- `(hdr & ~3) - 8` from the header word. -/
theorem cap_word {x : BitVec 64} {sz : Nat} (h : x.toNat / 4 * 4 = sz) (h32 : 32 ≤ sz) :
    (x &&& 0xfffffffffffffffc#64) + 0xfffffffffffffff8#64 = BitVec.ofNat 64 (sz - 8) := by
  have e : (0xfffffffffffffffc#64 : BitVec 64) = BitVec.allOnes 64 <<< 2 := by decide
  rw [e]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, and_high_toNat x 2 (by decide)]
  simp only [BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-! ## Frames of the allocator calls, as word facts -/

/-- A word off the written set `W` of an allocator call is unchanged. -/
theorem _root_.Tom.Machine.Api.Alloc.Keep.word {W : Nat → Prop} {m M : Mem} (h : Keep W m M) {a : Nat}
    (ha : ∀ x, a ≤ x → x < a + 8 → ¬ W x) : bytesT8 M a = bytesT8 m a :=
  bytesT8_congr fun x h1 h2 => h x (ha x h1 h2)

/-- A word off `memset`'s range is unchanged. -/
theorem _root_.Tom.Machine.Fn.Memset.Post.word {m M : Mem} {d n : Nat} {b : BitVec 8}
    (h : Memset.Post m d n b M) {a : Nat} (ha : d + n ≤ a) : bytesT8 M a = bytesT8 m a :=
  bytesT8_congr fun x h1 _ => h.frame x (by omega)

/-- `M` equals `M2` off `[q, q + K)` and the frame slot `[sp - 32, sp - 24)`. -/
def Within (M2 M : Mem) (sp q K : Nat) : Prop :=
  ∀ x, ¬ (q ≤ x ∧ x < q + K) → ¬ (sp - 32 ≤ x ∧ x < sp - 24) → M[x]? = M2[x]?

/-- What a zeroing path leaves, from the memory `M2` `_malloc_r` returned: `[q, q + K)`
zero, nothing else written but (the `memset` path) the frame slot. -/
structure Zeroed (M2 M3 : Mem) (sp q K : Nat) : Prop where
  zero : ∀ x, q ≤ x → x < q + K → M3[x]? = some 0
  keep : Within M2 M3 sp q K

theorem writeLog_append (M : Mem) (l1 l2 : List WEntry) :
    writeLog (writeLog M l1) l2 = writeLog M (l1 ++ l2) := by
  simp only [writeLog, List.foldl_append]

/-- Doubleword stores inside `[q, q + K)` stay `Within`. -/
theorem within_log {M2 : Mem} {sp q K : Nat} (log : List WEntry) (h8 : ∀ e ∈ log, e.2.1 = 8)
    (hin : ∀ e ∈ log, q ≤ e.1 ∧ e.1 + 8 ≤ q + K) : Within M2 (writeLog M2 log) sp q K :=
  fun x hx _ => writeLog_out _ _ _ (outL_of h8
    (fun ⟨e, he, h1, h2⟩ => hx ⟨by have := hin e he; omega, by have := hin e he; omega⟩))

/-- A zero log covering `[q, q + K)` (doublewords from `q`). -/
theorem zeroed_of {M2 : Mem} {q K : Nat} (log : List WEntry)
    (hz : ∀ e ∈ log, e.2 = (8, 0#64))
    (hcov : ∀ x, q ≤ x → x < q + K → ∃ e ∈ log, e.1 ≤ x ∧ x < e.1 + 8)
    (hin : ∀ e ∈ log, q ≤ e.1 ∧ e.1 + 8 ≤ q + K) (sp : Nat) : Zeroed M2 (writeLog M2 log) sp q K :=
  { zero := fun x h1 h2 => writeLog_zero log M2 x hz (hcov x h1 h2)
    keep := within_log log (fun e he => by rw [hz e he]) hin }

/-- The frame facts every zeroing path carries. -/
structure PathCtx (M2 : Mem) (ra : BitVec 64) (sp q K : Nat) : Prop where
  hc : CodeAt M2 callocRBase callocRCode
  sp1 : 0x87800220 ≤ sp
  sp2 : sp ≤ 0x100000000
  spa : sp % 16 = 0
  hra : ra.toNat % 4 = 0
  q1 : 0x80019d20 ≤ q
  q2 : q + K ≤ 0x87800000
  qa : q % 16 = 0

theorem PathCtx.code {M2 M : Mem} {ra : BitVec 64} {sp q K : Nat} (P : PathCtx M2 ra sp q K)
    (h : Within M2 M sp q K) : CodeAt M callocRBase callocRCode :=
  have e1 : callocRBase = 0x80007790 := rfl
  have e2 : callocRCode.length = 102 := rfl
  have := P.q1; have := P.sp1
  P.hc.of_eq fun x h1 h2 => h x (by omega) (by omega)

theorem PathCtx.word {M2 M : Mem} {ra : BitVec 64} {sp q K : Nat} (P : PathCtx M2 ra sp q K)
    (h : Within M2 M sp q K) {a : Nat} (ha : q + K ≤ a) (hb : sp - 24 ≤ a) :
    bytesT8 M a = bytesT8 M2 a :=
  bytesT8_congr fun x h1 _ => h x (by omega) (by omega)

/-- `k` zero doublewords from `a`. -/
def zs (a : Nat) : Nat → List WEntry
  | 0 => []
  | k + 1 => zs a k ++ [(a + 8 * k, 8, 0#64)]

theorem zs_mem {a : Nat} : ∀ {k : Nat} {e : WEntry}, e ∈ zs a k → ∃ i, i < k ∧ e = (a + 8 * i, 8, 0#64)
  | 0, _, h => by simp [zs] at h
  | k + 1, e, h => by
    simp only [zs, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · obtain ⟨i, hi, rfl⟩ := zs_mem h; exact ⟨i, by omega, rfl⟩
    · exact ⟨k, by omega, rfl⟩

theorem mem_zs {a : Nat} : ∀ {k i : Nat}, i < k → ((a + 8 * i, 8, 0#64) : WEntry) ∈ zs a k
  | 0, _, h => absurd h (by omega)
  | k + 1, i, h => by
    simp only [zs, List.mem_append, List.mem_singleton]
    by_cases hi : i = k
    · exact .inr (by rw [hi])
    · exact .inl (mem_zs (by omega))

/-- A zero run `zs q k` covers `[q, q + 8 k)` exactly. -/
theorem zeroed_zs {M2 : Mem} {q k K : Nat} (hK : K = 8 * k) (sp : Nat) :
    Zeroed M2 (writeLog M2 (zs q k)) sp q K :=
  zeroed_of (zs q k) (fun e he => by obtain ⟨i, _, rfl⟩ := zs_mem he; rfl)
    (fun x h1 h2 => ⟨_, mem_zs (a := q) (i := (x - q) / 8) (by omega), by simp only; omega,
      by simp only; omega⟩)
    (fun e he => by obtain ⟨i, hi, rfl⟩ := zs_mem he; simp only; omega) sp

theorem z3_zs (a : Nat) : z3 a = zs a 3 := by simp [z3, zs]
theorem z23_zs (a : Nat) : z2 a ++ z3 (a + 16) = zs a 5 := by
  simp [z2, z3, zs, Nat.add_assoc]
theorem z43_zs (a : Nat) : z4 a ++ z3 (a + 32) = zs a 7 := by
  simp [z4, z3, zs, Nat.add_assoc]
theorem z423_zs (a : Nat) :
    z4 a ++ ([(a + 32, 8, 0#64), (a + 40, 8, 0#64)] ++ z3 (a + 48)) = zs a 9 := by
  simp [z4, z3, zs, Nat.add_assoc]

end Tom.Machine.Fn.Calloc
