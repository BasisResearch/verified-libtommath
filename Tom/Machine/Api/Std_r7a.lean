import Tom.Machine.Kit.ByteBuf
import Tom.Machine.Fn.ReverseMain
import Tom.Spec.ToRadixStepL

/-!
# The callee contracts (for `mp_to_radix`)

* `sMpReverseH`: `s_mp_reverse(s, n)` (`Api/Reverse.lean`, `Fn.Reverse.correct`) as an
  allocating contract over an enclosing byte buffer `[b, b + len)` (the caller's string): the
  buffer is the contract's site, kept in place, of kind `.frz m1` before (the caller's snapshot)
  and `.frz x` after, `x` the memory after the call; `Q` says the bytes `[s, s + n)` are reversed
  and the rest of the buffer kept (`ToRadixStepL.RevPost`). A plain `Contract` cannot carry
  this: its written regions' kinds after must be digit arrays, structs or untracked RAM
  (`out_ind`), none of which holds bytes; an `HContract`'s site may take any kind, because the
  caller's layout is re-placed at the site's interval (`HContract.after`). No allocation.
-/


namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-! ## `s_mp_reverse(s, n)` inside a buffer -/

inductive Rv | whole | code
  deriving DecidableEq

structure RvP where
  /-- The buffer `[b, b + len)` (the caller's region). -/
  b : Nat
  len : Nat
  /-- The reversed bytes `[s, s + n)`. -/
  s : Nat
  n : Nat
  /-- The buffer's contents before (the caller's snapshot). -/
  m1 : Mem
  H : List (Nat × Nat)

def Rv.lay (p : RvP) : Rv → Iv
  | .whole => ⟨p.b, p.len⟩
  | .code => textIv

def Rv.kind (p : RvP) : Rv → Kind
  | .whole => .frz p.m1
  | .code => .code

def Rv.out (_ : RvP) (x : Mem) : Rv → Kind
  | .whole => .frz x
  | .code => .code

def Rv.isW : Rv → Bool
  | .whole => true
  | .code => false

/-- What `s_mp_reverse(s, n)` needs: `n ≥ 1` (`Api/Reverse.lean`: the C's `len - 1u` wraps at
`0`), and the reversed bytes inside the buffer. -/
structure RvRes (p : RvP) : Prop where
  n_pos : 1 ≤ p.n
  lo : p.b ≤ p.s
  hi : p.s + p.n ≤ p.b + p.len

/-- The bytes `[s, s + n)` reversed, the rest of the buffer kept. -/
def Rv.Q (p : RvP) (x : Mem) : Prop :=
  ToRadixStepL.RevPost (p.s - p.b) p.n (bytesOf p.m1 p.b p.len) (bytesOf x p.b p.len)

def Rv.σ : Reverse.R → Rv
  | .arr => .whole
  | .code => .code

theorem getD_reverse' {l : List (BitVec 8)} {j : Nat} (h : j < l.length) :
    l.reverse.getD j 0 = l.getD (l.length - 1 - j) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse h, List.getD_eq_getElem?_getD]

theorem Rv.spec {p : RvP} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64} (hra : ra.toNat % 4 = 0)
    (hres : RvRes p) (hS : Sound (Rv.lay p) Rv.isW) (hB : Bundle (Rv.lay p) (Rv.kind p) m) (hH : AHeap m p.H)
    (hoff : ∀ r, Off (Rv.lay p r) p.H) :
    Triple (At (Reverse.entry) ((1, ra) :: [(10, BitVec.ofNat 64 p.s), (11, BitVec.ofNat 64 p.n)]) m v.keep outp)
      (fun cf => ∃ x M, At ra [(1, ra)] M v.keep outp cf ∧ Rv.Q p x ∧
        HPost (Rv.lay p) [Rv.whole] Rv.whole (Rv.out p x) ⟨p.b, p.len⟩ p.H p.H m M) := by
  obtain ⟨b, len, s, n, m1, H⟩ := p
  obtain ⟨hn, hlo, hhi⟩ := hres
  dsimp only at hn hlo hhi
  have hw := (hB .whole).2
  simp only [Rv.kind, Rv.lay, Kind.Wit] at hw
  obtain ⟨hram, hagree⟩ := hw
  have hag : ∀ x, b ≤ x → x < b + len → m[x]? = m1[x]? := fun x h1 h2 => hagree x ⟨h1, h2⟩
  have himg : Img m := (hB .code).2
  let l : List (BitVec 8) := (List.range n).map fun i => bytesT1 m (s + i)
  have hl : l.length = n := by simp [l]
  have hget : ∀ i, i < n → l.getD i 0 = bytesT1 m (s + i) := fun i hi => by
    simp [l, List.getD_eq_getElem?_getD, hi]
  have hsub : ∀ k, (Reverse.lay s n k).Sub (Rv.lay ⟨b, len, s, n, m1, H⟩ (Rv.σ k)) := by
    intro k; cases k
    · simp only [Reverse.lay, Rv.lay, Rv.σ, Iv.Sub]; omega
    · exact Iv.sub_self _
  have hpre : Reverse.Pre m s l ra :=
    { bytes := fun i hi => by rw [hget i (by omega)]
      n_pos := by omega
      rs := by rw [hl]; exact Ram.sub hram (by omega) (by omega)
      ra_al := hra, img := himg
      lay := by rw [hl]; exact hS.pull Rv.σ [.arr, .code] (fun k => by cases k <;> simp) hsub (by decide) }
  have ht := Fn.Reverse.correct (v := v) (outp := outp) hpre
  rw [hl] at ht
  refine Triple.rmap (fun cf ⟨M, hat, hpost⟩ => ⟨M, M, hat, ?_, ?_⟩) ht
  all_goals have hbt := hpost.bytes
  all_goals have hfm := hpost.frame
  all_goals rw [hl] at hfm
  · -- the bytes
    have hfr : ∀ x, ¬ (s ≤ x ∧ x < s + n) → M[x]? = m[x]? := fun x hx => hfm x fun h => hx (by
      rcases h with h | h
      · simpa [Reverse.lay, Iv.In] using h
      · exact h.elim)
    show ToRadixStepL.RevPost (s - b) n (bytesOf m1 b len) (bytesOf M b len)
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · unfold bytesOf
      rw [if_pos (by omega), if_pos (by omega)]
      have h1 := hbt j (by simp [hl]; omega)
      rw [getD_reverse' (by simp [hl]; omega), hl] at h1
      simp only [bytesT1] at h1 ⊢
      rw [show b + (s - b + j) = s + j by omega, h1, hget _ (by omega), show b + (s - b + (n - 1 - j)) = s + (n - 1 - j) by omega]
      simp only [bytesT1]; rw [hag _ (by omega) (by omega)]
    · unfold bytesOf; split
      · simp only [bytesT1]
        rw [hfr _ (by omega), hag _ (by omega) (by omega)]
      · rfl
  · -- the contract's post
    exact { wit := fun r hr hrs => by simp at hr; exact absurd hr hrs
            wsite := ⟨trivial, hram, fun _ _ => rfl⟩
            place := .keep
            frame := fun x hx => hfm x fun h => hx (.inl (by
              rcases h with h | h
              · simp only [Reverse.lay, Iv.In] at h; exact .inl ⟨by simp [Rv.lay]; omega, by simp [Rv.lay]; omega⟩
              · exact h.elim))
            heap := hH.frame fun a ha => hfm a fun h => by
              rcases h with h | h
              · simp only [Reverse.lay, Iv.In] at h
                exact (hoff .whole).pt a ⟨by simp [Rv.lay]; omega, by simp [Rv.lay]; omega⟩ ha
              · exact h.elim
            foot := fun _ h => .inl h
            off := hoff .whole }

/-- `s_mp_reverse(s, n)` as an allocating contract over the buffer `[b, b + len)`. -/
def sMpReverseH : HContract where
  P := RvP
  X := Mem
  R := Rv
  all := [.whole, .code]
  hall r := by cases r <;> simp
  entry := Reverse.entry
  args p := [(10, BitVec.ofNat 64 p.s), (11, BitVec.ofNat 64 p.n)]
  rets _ _ ra := [(1, ra)]
  lay := Rv.lay
  kind := Rv.kind
  out := Rv.out
  isW := Rv.isW
  ws := [.whole]
  site := .whole
  site' p _ := ⟨p.b, p.len⟩
  hin p := p.H
  hout p _ := p.H
  Res := RvRes
  Q := Rv.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by simp at hr; exact absurd hr hs
  pos p h r := by
    have := h.n_pos; have := h.hi; have := h.lo
    cases r with
    | whole => exact .inl (show 0 < p.len by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := fun hra hres hS hB hH hoff => Rv.spec hra hres hS hB hH hoff

end Tom.Machine.Std
