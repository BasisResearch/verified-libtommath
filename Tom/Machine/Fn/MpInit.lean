import Tom.Machine.Seg.MpInit
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Jal
import Tom.Machine.Kit.MemStore
import Tom.Machine.Kit.Frame
import Tom.Spec.Init

/-!
# `mp_init`, `mp_init_size` on the machine: the segments

`mp_init_size(a, size)` at `0x80001498` (29 instructions): `size < 0` returns
`MP_VAL` (`misVal`); otherwise save `s0`, `s1`, `ra`, take `n = max(3, size)`
(`misBig`/`misSmall`) and call `calloc(n, 4)` at `14c4`. After it, store the
result in `a->dp`; non-null: `used := 0`, `alloc := n`, `sign := 0`, `MP_OKAY`
(`misOK`); null: `MP_MEM` (`misN`); the epilogue `misE` restores the frame.

`mp_init(a)` at `0x800012fc` (20 instructions) is the same with `n = 32`
(`calloc(32, 4)` at `1314`; `used`/`alloc` by one `sd` of `32 << 32`).

`s0`, `s1` (`mp_init_size`) and `sp` are written and restored: they travel in
the pin list (`Abi.keepR1`, `Abi.keepR`).
-/


namespace Tom.Machine.Fn.MpInit

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mis_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpInitSizeBase = 0x80001498 := rfl
   have : mpInitSizeCode.length = 29 := rfl))

macro "mi_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpInitBase = 0x800012fc := rfl
   have : mpInitCode.length = 20 := rfl))

/-! ## `mp_init_size` -/

def sizeEntry : BitVec 64 := 0x80001498#64

/-- Registers at the entry: `ra`, `sp`, `s0`, `s1`, `a0 = a`, `a1 = size`. -/
def sizeL (ra s0 s1 : BitVec 64) (sp pa : Nat) (size : BitVec 64) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, BitVec.ofNat 64 pa), (11, size)]

/-- `size < 0`: `MP_VAL`. -/
theorem val_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa : Nat) (size : BitVec 64)
    (m : Mem) (hc : CodeAt m mpInitSizeBase mpInitSizeCode) (hra : ra.toNat % 4 = 0)
    (hs : zopz0zI_s size 0#64 = true) :
    Triple (At sizeEntry (sizeL ra s0 s1 sp pa size) m v.keepR1 outp)
      (At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, 0xfffffffffffffffd#64)]
        (writeLog m []) v.keepR1 outp) := by
  mis_ctx
  seg_step misVal ra ([] : List (List (BitVec 8))) [1, 2, 8, 9, 10, 11] abiKeysR1 [sizeEntry, sizeL] []
    [hs] hc

/-- At the `calloc(n, 4)` call (`14c4`). -/
def callL (ra : BitVec 64) (sp pa n : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 n),
   (10, BitVec.ofNat 64 n), (11, 4#64)]

/-- The frame stores: `s1`, `ra`, `s0`. -/
def frameLog (ra s0 s1 : BitVec 64) (sp : Nat) : List WEntry :=
  [(sp - 24, 8, s1), (sp - 8, 8, ra), (sp - 16, 8, s0)]

/-- The stack frame. -/
structure SFacts (sp : Nat) : Prop where
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  code_off : mpInitSizeBase + 116 ≤ sp - 32

/-- `3 ≤ size`: the frame, `n = size`. -/
theorem big_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa size : Nat) (m : Mem)
    (hc : CodeAt m mpInitSizeBase mpInitSizeCode) (hs : SFacts sp) (h3 : 3 ≤ size) (h31 : size < 2 ^ 31) :
    Triple (At sizeEntry (sizeL ra s0 s1 sp pa (BitVec.ofNat 64 size)) m v.keepR1 outp)
      (At 0x800014c4#64 (callL ra sp pa size) (writeLog m (frameLog ra s0 s1 sp)) v.keepR1 outp) := by
  mis_ctx
  have h1 : size % 4294967296 = size := Nat.mod_eq_of_lt (by omega)
  seg_step misBig 0x800014c4#64 ([] : List (List (BitVec 8))) [1, 2, 8, 9, 10, 11] abiKeysR1
    [sizeEntry, sizeL, frameLog] [callL] [h1] hc

/-- `size < 3`: the frame, `n = 3`. -/
theorem small_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa size : Nat) (m : Mem)
    (hc : CodeAt m mpInitSizeBase mpInitSizeCode) (hs : SFacts sp) (h3 : size < 3) :
    Triple (At sizeEntry (sizeL ra s0 s1 sp pa (BitVec.ofNat 64 size)) m v.keepR1 outp)
      (At 0x800014c4#64 (callL ra sp pa 3) (writeLog m (frameLog ra s0 s1 sp)) v.keepR1 outp) := by
  mis_ctx
  seg_step misSmall 0x800014c4#64 ([] : List (List (BitVec 8))) [1, 2, 8, 9, 10, 11] abiKeysR1
    [sizeEntry, sizeL, frameLog] [callL] [] hc

/-- Back from `calloc` (`14c8`) with `a0 = q`. -/
def backL (sp pa n q : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 n), (10, BitVec.ofNat 64 q)]

/-- At the epilogue (`14e0`) with `a0 = r`. -/
def epiL (sp pa n : Nat) (r : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 n), (10, r)]

/-- The struct stores of the non-null branch. -/
def okLog (pa q n : Nat) : List WEntry :=
  [(pa + 16, 8, BitVec.ofNat 64 q), (pa, 4, 0#64), (pa + 4, 4, BitVec.ofNat 64 n), (pa + 8, 4, 0#64)]

/-- The struct, off the code. -/
structure StFacts (pa : Nat) : Prop where
  rs : Ram pa 24
  al : pa % 8 = 0
  code_off : pa + 24 ≤ textBase ∨ textBase + textLen ≤ pa

theorem mod64 {x : Nat} (h : x < 2 ^ 64) : x % 18446744073709551616 = x := Nat.mod_eq_of_lt h

/-- `calloc` gave `q ≠ 0`: `dp := q`, `used := 0`, `alloc := n`, `sign := 0`, `MP_OKAY`. -/
theorem ok_step (v : Abi) (outp : Array String) (sp pa n q : Nat) (M : Mem)
    (hc : CodeAt M mpInitSizeBase mpInitSizeCode) (hp : StFacts pa)
    (hz : (BitVec.ofNat 64 q == 0#64) = false) :
    Triple (At 0x800014c8#64 (backL sp pa n q) M v.keepR1 outp)
      (At 0x800014e0#64 (epiL sp pa n 0#64) (writeLog M (okLog pa q n)) v.keepR1 outp) := by
  mis_ctx
  have := hp.code_off; unfold textBase textLen at this
  have h0 := mod64 (x := pa) (by omega)
  have h4 := mod64 (x := pa + 4) (by omega)
  have h8 := mod64 (x := pa + 8) (by omega)
  have h16 := mod64 (x := pa + 16) (by omega)
  seg_step misOK 0x800014e0#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10] abiKeysR1 [backL, okLog]
    [epiL] [hz, h0, h4, h8, h16] hc

/-- `calloc` gave `NULL`: `dp := NULL`, `MP_MEM`. -/
theorem null_step (v : Abi) (outp : Array String) (sp pa n : Nat) (M : Mem)
    (hc : CodeAt M mpInitSizeBase mpInitSizeCode) (hp : StFacts pa) :
    Triple (At 0x800014c8#64 (backL sp pa n 0) M v.keepR1 outp)
      (At 0x800014e0#64 (epiL sp pa n 0xfffffffffffffffe#64) (writeLog M [(pa + 16, 8, 0#64)])
        v.keepR1 outp) := by
  mis_ctx
  have := hp.code_off; unfold textBase textLen at this
  have h16 := mod64 (x := pa + 16) (by omega)
  seg_step misN 0x800014e0#64 ([] : List (List (BitVec 8))) [2, 8, 9, 10] abiKeysR1 [backL]
    [epiL] [h16] hc

/-- The epilogue: restore `ra`, `s0`, `s1`, `sp`; return `r`. -/
theorem epi_step (ra s0 s1 : BitVec 64) (v : Abi) (outp : Array String) (sp pa n : Nat) (r : BitVec 64)
    (M : Mem) (hc : CodeAt M mpInitSizeBase mpInitSizeCode) (hra : ra.toNat % 4 = 0) (hs : SFacts sp)
    (h24 : bytesT8 M (sp - 32 + 24) = ra) (h16 : bytesT8 M (sp - 32 + 16) = s0)
    (h8 : bytesT8 M (sp - 32 + 8) = s1) :
    Triple (At 0x800014e0#64 (epiL sp pa n r) M v.keepR1 outp)
      (At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (9, s1), (10, r)] (writeLog M [])
        v.keepR1 outp) := by
  mis_ctx
  seg_step misE ra [rd8 M (sp - 32 + 24), rd8 M (sp - 32 + 16), rd8 M (sp - 32 + 8)] [2, 8, 9, 10]
    abiKeysR1 [epiL] [] [h24, h16, h8] hc

/-! ## `mp_init` -/

def initEntry : BitVec 64 := 0x800012fc#64

/-- Registers at the entry: `ra`, `sp`, `s0`, `a0 = a`. -/
def initL (ra s0 : BitVec 64) (sp pa : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 pa)]

/-- At the `calloc(32, 4)` call (`1314`). -/
def icallL (ra : BitVec 64) (sp pa : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 16)), (8, BitVec.ofNat 64 pa), (10, 32#64), (11, 4#64)]

/-- The frame stores: `s0`, `ra`. -/
def iframeLog (ra s0 : BitVec 64) (sp : Nat) : List WEntry := [(sp - 16, 8, s0), (sp - 8, 8, ra)]

/-- The stack frame. -/
structure ISFacts (sp : Nat) : Prop where
  rs : Ram (sp - 16) 16
  sp_al : sp % 16 = 0
  sp_ge : 16 ≤ sp
  code_off : mpInitBase + 80 ≤ sp - 16

/-- The frame; `calloc(32, 4)`. -/
theorem ipro_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa : Nat) (m : Mem)
    (hc : CodeAt m mpInitBase mpInitCode) (hs : ISFacts sp) :
    Triple (At initEntry (initL ra s0 sp pa) m v.keepR outp)
      (At 0x80001314#64 (icallL ra sp pa) (writeLog m (iframeLog ra s0 sp)) v.keepR outp) := by
  mi_ctx
  seg_step minitP 0x80001314#64 ([] : List (List (BitVec 8))) [1, 2, 8, 10] abiKeysR
    [initEntry, initL, iframeLog] [icallL] [] hc

/-- Back from `calloc` (`1318`) with `a0 = q`. -/
def ibackL (sp pa q : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 16)), (8, BitVec.ofNat 64 pa), (10, BitVec.ofNat 64 q)]

/-- At the epilogue (`1334`) with `a0 = r`. -/
def iepiL (sp pa : Nat) (r : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 16)), (8, BitVec.ofNat 64 pa), (10, r)]

/-- The struct stores of the non-null branch: `dp`, `sign`, `used`/`alloc` (`32 << 32`). -/
def iokLog (pa q : Nat) : List WEntry :=
  [(pa + 16, 8, BitVec.ofNat 64 q), (pa + 8, 4, 0#64), (pa, 8, 0x2000000000#64)]

/-- The struct, off the code. -/
structure IStFacts (pa : Nat) : Prop where
  rs : Ram pa 24
  al : pa % 8 = 0
  code_off : pa + 24 ≤ textBase ∨ textBase + textLen ≤ pa

/-- `calloc` gave `q ≠ 0`: `dp := q`, `sign := 0`, `used := 0`, `alloc := 32`, `MP_OKAY`. -/
theorem iok_step (v : Abi) (outp : Array String) (sp pa q : Nat) (M : Mem)
    (hc : CodeAt M mpInitBase mpInitCode) (hp : IStFacts pa)
    (hz : (BitVec.ofNat 64 q == 0#64) = false) :
    Triple (At 0x80001318#64 (ibackL sp pa q) M v.keepR outp)
      (At 0x80001334#64 (iepiL sp pa 0#64) (writeLog M (iokLog pa q)) v.keepR outp) := by
  mi_ctx
  have := hp.code_off; unfold textBase textLen at this
  have h0 := mod64 (x := pa) (by omega)
  have h8 := mod64 (x := pa + 8) (by omega)
  have h16 := mod64 (x := pa + 16) (by omega)
  seg_step minitOK 0x80001334#64 ([] : List (List (BitVec 8))) [2, 8, 10] abiKeysR [ibackL, iokLog]
    [iepiL] [hz, h0, h8, h16] hc

/-- `calloc` gave `NULL`: `dp := NULL`, `MP_MEM`. -/
theorem inull_step (v : Abi) (outp : Array String) (sp pa : Nat) (M : Mem)
    (hc : CodeAt M mpInitBase mpInitCode) (hp : IStFacts pa) :
    Triple (At 0x80001318#64 (ibackL sp pa 0) M v.keepR outp)
      (At 0x80001334#64 (iepiL sp pa 0xfffffffffffffffe#64) (writeLog M [(pa + 16, 8, 0#64)])
        v.keepR outp) := by
  mi_ctx
  have := hp.code_off; unfold textBase textLen at this
  have h16 := mod64 (x := pa + 16) (by omega)
  seg_step minitN 0x80001334#64 ([] : List (List (BitVec 8))) [2, 8, 10] abiKeysR [ibackL]
    [iepiL] [h16] hc

/-- The epilogue: restore `ra`, `s0`, `sp`; return `r`. -/
theorem iepi_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa : Nat) (r : BitVec 64)
    (M : Mem) (hc : CodeAt M mpInitBase mpInitCode) (hra : ra.toNat % 4 = 0) (hs : ISFacts sp)
    (h8 : bytesT8 M (sp - 16 + 8) = ra) (h0 : bytesT8 M (sp - 16) = s0) :
    Triple (At 0x80001334#64 (iepiL sp pa r) M v.keepR outp)
      (At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, r)] (writeLog M [])
        v.keepR outp) := by
  mi_ctx
  seg_step minitE ra [rd8 M (sp - 16 + 8), rd8 M (sp - 16)] [2, 8, 10] abiKeysR [iepiL] [] [h8, h0] hc

/-! ## The struct the stores leave -/

theorem writeLog_out_disj {M : Mem} {log : List WEntry} {lo n x : Nat} (hl : ∀ e ∈ log, lo ≤ e.1 ∧ e.1 + e.2.1 ≤ lo + n)
    (hx : x < lo ∨ lo + n ≤ x) : (writeLog M log)[x]? = M[x]? := by
  apply writeLog_out
  induction log with
  | nil => trivial
  | cons e l ih =>
    have := hl e (List.mem_cons_self ..)
    exact ⟨by omega, ih fun e' he' => hl e' (List.mem_cons_of_mem _ he')⟩

/-- The zero digits of a fresh block, through stores to the struct. -/
theorem digits_zero {M : Mem} {log : List WEntry} {pa q n : Nat}
    (hl : ∀ e ∈ log, pa ≤ e.1 ∧ e.1 + e.2.1 ≤ pa + 24) (hd : Disj q (4 * n) pa 24)
    (hz : ∀ i, i < 4 * n → M[q + i]? = some 0#8) :
    ∀ i, i < n → bytesT4 (writeLog M log) (q + Layout.sizeofDigit * i) = BitVec.ofNat 32 ((MpInt.zeroN n).digit i) := by
  intro i hi
  rw [MpInt.zeroN_digit]
  simp only [Layout.sizeofDigit]
  exact bytesT4_zero fun k hk => by
    rw [writeLog_out_disj hl (by unfold Disj at hd; omega), show q + 4 * i + k = q + (4 * i + k) by omega]
    exact hz _ (by omega)

/-- `mp_init_size`'s non-null stores leave `zeroN n` at `pa` with digits at `q`. -/
theorem ok_at {M : Mem} {pa q n : Nat} (hn : n < 2 ^ 31) (hd : Disj q (4 * n) pa 24)
    (hz : ∀ i, i < 4 * n → M[q + i]? = some 0#8) :
    MpAt (writeLog M (okLog pa q n)) pa q (MpInt.zeroN n) := by
  have e : writeLog M (okLog pa q n) = writeLog (writeLog (writeLog (writeLog M [(pa + 16, 8, BitVec.ofNat 64 q)])
      [(pa, 4, 0#64)]) [(pa + 4, 4, BitVec.ofNat 64 n)]) [(pa + 8, 4, 0#64)] := rfl
  have hdig := digits_zero (log := okLog pa q n)
    (fun e he => by
      simp only [okLog, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> simp only <;> omega) hd hz
  rw [e] at hdig ⊢
  refine { used := ?_, alloc := ?_, sign := ?_, dpv := ?_, digits := hdig }
  · rw [bytesT4_sw_out _ _ _ _ (by simp [Layout.offUsed]), bytesT4_sw_out _ _ _ _ (by simp [Layout.offUsed])]
    simp only [Layout.offUsed, Nat.add_zero]; exact bytesT4_sw_self _ pa 0 (by decide)
  · rw [bytesT4_sw_out _ _ _ _ (by simp [Layout.offAlloc])]
    exact bytesT4_sw_self _ (pa + 4) n (by omega)
  · exact bytesT4_sw_self _ (pa + 8) 0 (by decide)
  · rw [bytesT8_sw_out _ _ _ _ (by simp [Layout.offDp]), bytesT8_sw_out _ _ _ _ (by simp [Layout.offDp]),
      bytesT8_sw_out _ _ _ _ (by simp [Layout.offDp])]
    exact bytesT8_sd_self _ _ _

/-- The bytes `32 << 32` puts at `a`, `a + 4`. -/
theorem sd_prec (X : Mem) (a : Nat) :
    bytesT4 (writeLog X [(a, 8, 0x2000000000#64)]) a = 0#32 ∧
      bytesT4 (writeLog X [(a, 8, 0x2000000000#64)]) (a + 4) = 32#32 := by
  have hb : ∀ k, k < 8 → (writeLog X [(a, 8, 0x2000000000#64)])[a + k]? =
      some ((0x2000000000#64 : BitVec 64).extractLsb' (8 * k) 8) := fun k hk => by
    rw [writeLog_single, getElem?_applyW_sd_in _ a (a + k) _ (by omega) (by omega), Nat.add_sub_cancel_left,
      sdData_val_id]
  have h0 := hb 0 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [bytesT4]
  rw [h0, hb 1 (by decide), hb 2 (by decide), hb 3 (by decide), show a + 4 + 1 = a + 5 by omega,
    show a + 4 + 2 = a + 6 by omega, show a + 4 + 3 = a + 7 by omega, hb 4 (by decide), hb 5 (by decide),
    hb 6 (by decide), hb 7 (by decide)]
  exact ⟨by decide, by decide⟩

/-- `mp_init`'s non-null stores leave `zeroN 32` at `pa` with digits at `q`. -/
theorem iok_at {M : Mem} {pa q : Nat} (hd : Disj q (4 * 32) pa 24)
    (hz : ∀ i, i < 4 * 32 → M[q + i]? = some 0#8) :
    MpAt (writeLog M (iokLog pa q)) pa q (MpInt.zeroN 32) := by
  have e : writeLog M (iokLog pa q) = writeLog (writeLog (writeLog M [(pa + 16, 8, BitVec.ofNat 64 q)])
      [(pa + 8, 4, 0#64)]) [(pa, 8, 0x2000000000#64)] := by
    rw [show iokLog pa q = [(pa + 16, 8, BitVec.ofNat 64 q)] ++ [(pa + 8, 4, 0#64)] ++ [(pa, 8, 0x2000000000#64)]
      from rfl, writeLog_append, writeLog_append]
  have out8 : ∀ (X : Mem) (x : Nat), x < pa ∨ pa + 8 ≤ x → (writeLog X [(pa, 8, 0x2000000000#64)])[x]? = X[x]? :=
    fun X x hx => writeLog_out _ _ _ ⟨hx, trivial⟩
  have hdig := digits_zero (log := iokLog pa q)
    (fun e he => by
      simp only [iokLog, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> simp only <;> omega) hd hz
  rw [e] at hdig ⊢
  refine { used := ?_, alloc := ?_, sign := ?_, dpv := ?_, digits := hdig }
  · simp only [Layout.offUsed, Nat.add_zero]; exact (sd_prec _ pa).1
  · simp only [Layout.offAlloc]; exact (sd_prec _ pa).2
  · rw [bytesT4_congr fun x h1 h2 => out8 _ x (by simp only [Layout.offSign] at *; omega)]
    exact bytesT4_sw_self _ (pa + 8) 0 (by decide)
  · rw [bytesT8_congr fun x h1 h2 => out8 _ x (by simp only [Layout.offDp] at *; omega),
      bytesT8_sw_out _ _ _ _ (by simp [Layout.offDp])]
    exact bytesT8_sd_self _ _ _

/-- The null branch's store: `dp = 0`. -/
theorem null_dp (M : Mem) (pa : Nat) : bytesT8 (writeLog M [(pa + 16, 8, 0#64)]) (pa + 16) = 0#64 :=
  bytesT8_sd_self _ _ _

end Tom.Machine.Fn.MpInit
