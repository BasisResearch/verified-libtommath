import Tom.Machine.Seg.MpGrowR
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Jal
import Tom.Machine.Kit.Frame
import Tom.Spec.Init

/-!
# `mp_grow` on the machine: the segments

`mp_grow(a, size)` at `0x80001270` (35 instructions). `size < 0`: `MP_VAL`
(`mgrowV`); `size ≤ a->alloc`: `MP_OKAY` (`mgrowK`), as `Fn/MpGrow.lean`. Otherwise (`mgrowP`) save `ra`, `a`, `size` in a 32-byte
frame and call `realloc(a->dp, 4 * size)` at `12a4`. Null: `MP_MEM`
(`mgrowN`). Otherwise reload `a` and `size` (`mgrowR1`), store `dp`, `alloc`,
and call `memset(dp + 4 * alloc, 0, 4 * (size - alloc))` at `12d8`
(`mgrowR2`); then `MP_OKAY` (`mgrowE`). `s0` is not touched; it and `sp`
travel in the pin list (`Abi.keepR`).
-/


namespace Tom.Machine.Fn.MpGrowR

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mgrow_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpGrowBase = 0x80001270 := rfl
   have : mpGrowCode.length = 35 := rfl))

def entry : BitVec 64 := 0x80001270#64

/-- Registers at the entry: `ra`, `sp`, `s0`, `a0 = a`, `a1 = size`. -/
def entryL (ra s0 : BitVec 64) (sp p : Nat) (size : BitVec 64) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, BitVec.ofNat 64 p), (11, size)]

/-- At a return with `a0 = r`. -/
def retL (ra s0 : BitVec 64) (sp : Nat) (r : BitVec 64) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, r)]

/-- `size < 0`: `MP_VAL`. -/
theorem val_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp p : Nat) (size : BitVec 64) (m : Mem)
    (hc : CodeAt m mpGrowBase mpGrowCode) (hra : ra.toNat % 4 = 0) (hs : zopz0zI_s size 0#64 = true) :
    Triple (At entry (entryL ra s0 sp p size) m v.keepR outp)
      (At ra (retL ra s0 sp 0xfffffffffffffffd#64) (writeLog m []) v.keepR outp) := by
  mgrow_ctx
  seg_step mgrowV ra ([] : List (List (BitVec 8))) [1, 2, 8, 10, 11] abiKeysR [entry, entryL] [retL] [hs] hc

/-- `0 ≤ size ≤ a->alloc`: `MP_OKAY`, nothing written. -/
theorem keep_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp p al size : Nat) (m : Mem)
    (hc : CodeAt m mpGrowBase mpGrowCode) (hra : ra.toNat % 4 = 0) (hp : Ram p 24)
    (hal : bytesT4 m (p + 4) = BitVec.ofNat 32 al) (hal' : al < 2 ^ 31) (hs : size ≤ al) :
    Triple (At entry (entryL ra s0 sp p (BitVec.ofNat 64 size)) m v.keepR outp)
      (At ra (retL ra s0 sp 0#64) (writeLog m []) v.keepR outp) := by
  mgrow_ctx
  have hsx : BitVec.signExtend 64 (bytesT4 m (p + 4)) = BitVec.ofNat 64 al := by
    rw [hal, signExtend_ofNat32 _ hal']
  seg_step mgrowK ra [rd4 m (p + 4)] [1, 2, 8, 10, 11] abiKeysR [entry, entryL] [retL] [hsx] hc

/-- At the `realloc` call (`12a4`): `a0 = dp`, `a1 = 4 * size`. -/
def callL (ra s0 : BitVec 64) (sp p dp size : Nat) : GRegs :=
  [(1, ra), (2, BitVec.ofNat 64 (sp - 32)), (8, s0), (10, BitVec.ofNat 64 dp),
   (11, BitVec.ofNat 64 (size * 4))]

/-- The frame stores: `ra`, `a`, `size`. -/
def frameLog (ra : BitVec 64) (sp p size : Nat) : List WEntry :=
  [(sp - 8, 8, ra), (sp - 24, 8, BitVec.ofNat 64 p), (sp - 32, 8, BitVec.ofNat 64 size)]

/-- The stack frame. -/
structure SFacts (sp : Nat) : Prop where
  rs : Ram (sp - 32) 32
  sp_al : sp % 16 = 0
  sp_ge : 32 ≤ sp
  code_off : mpGrowBase + 140 ≤ sp - 32

/-- `a->alloc < size`: the frame, `realloc(dp, 4 * size)`. -/
theorem pro_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp p al dp size : Nat) (m : Mem)
    (hc : CodeAt m mpGrowBase mpGrowCode) (hp : Ram p 24) (hs : SFacts sp)
    (hal : bytesT4 m (p + 4) = BitVec.ofNat 32 al) (hal' : al < 2 ^ 31) (hlt : al < size) (h31 : size < 2 ^ 31)
    (hdp : bytesT8 m (p + 16) = BitVec.ofNat 64 dp) :
    Triple (At entry (entryL ra s0 sp p (BitVec.ofNat 64 size)) m v.keepR outp)
      (At 0x800012a4#64 (callL ra s0 sp p dp size) (writeLog m (frameLog ra sp p size)) v.keepR outp) := by
  mgrow_ctx
  have hsx : BitVec.signExtend 64 (bytesT4 m (p + 4)) = BitVec.ofNat 64 al := by
    rw [hal, signExtend_ofNat32 _ hal']
  seg_step mgrowP 0x800012a4#64 [rd4 m (p + 4), rd8 m (p + 16)] [1, 2, 8, 10, 11] abiKeysR
    [entry, entryL, frameLog] [callL] [hsx, hdp] hc

/-- Back from `realloc` (`12a8`) with `a0 = q`. -/
def backL (s0 : BitVec 64) (sp q : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (8, s0), (10, BitVec.ofNat 64 q)]

/-- `realloc` gave `NULL`: `MP_MEM`. -/
theorem null_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M mpGrowBase mpGrowCode) (hra : ra.toNat % 4 = 0) (hs : SFacts sp)
    (h24 : bytesT8 M (sp - 32 + 24) = ra) :
    Triple (At 0x800012a8#64 (backL s0 sp 0) M v.keepR outp)
      (At ra (retL ra s0 sp 0xfffffffffffffffe#64) (writeLog M []) v.keepR outp) := by
  mgrow_ctx
  seg_step mgrowN ra [rd8 M (sp - 32 + 24)] [2, 8, 10] abiKeysR [backL] [retL] [h24] hc

/-- `a` and `size` reloaded (`12b4`). -/
def reL (s0 : BitVec 64) (sp p q size : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (8, s0), (10, BitVec.ofNat 64 q), (12, BitVec.ofNat 64 size),
   (15, BitVec.ofNat 64 p)]

/-- `realloc` gave `q ≠ 0`: reload `a` and `size`. -/
theorem re_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (sp p q size : Nat) (M : Mem)
    (hc : CodeAt M mpGrowBase mpGrowCode) (hs : SFacts sp)
    (hz : (BitVec.ofNat 64 q == 0#64) = false)
    (h8 : bytesT8 M (sp - 32 + 8) = BitVec.ofNat 64 p) (h0 : bytesT8 M (sp - 32) = BitVec.ofNat 64 size) :
    Triple (At 0x800012a8#64 (backL s0 sp q) M v.keepR outp)
      (At 0x800012b4#64 (reL s0 sp p q size) (writeLog M []) v.keepR outp) := by
  mgrow_ctx
  seg_step mgrowR1 0x800012b4#64 [rd8 M (sp - 32 + 8), rd8 M (sp - 32)] [2, 8, 10] abiKeysR [backL]
    [reL] [hz, h8, h0] hc

/-- At the `memset` call (`12d8`): `a0 = q + 4 alloc`, `a1 = 0`, `a2 = 4 (size - alloc)`. -/
def setL (s0 : BitVec 64) (sp q al size : Nat) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 32)), (8, s0), (10, BitVec.ofNat 64 (q + al * 4)), (11, 0#64),
   (12, BitVec.ofNat 64 ((size - al) * 4))]

/-- The struct stores: `dp := q`, `alloc := size`. -/
def stLog (p q size : Nat) : List WEntry := [(p + 16, 8, BitVec.ofNat 64 q), (p + 4, 4, BitVec.ofNat 64 size)]

/-- The struct, off the code. -/
structure StFacts (p : Nat) : Prop where
  rs : Ram p 24
  al : p % 8 = 0
  code_off : p + 24 ≤ textBase ∨ textBase + textLen ≤ p

theorem mod64 {x : Nat} (h : x < 2 ^ 64) : x % 18446744073709551616 = x := Nat.mod_eq_of_lt h

/-- Store `dp` and `alloc`; set up `memset`. -/
theorem st_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (sp p q al size : Nat) (M : Mem)
    (hc : CodeAt M mpGrowBase mpGrowCode) (hp : StFacts p) (hq : q + 4 * size < 2 ^ 32)
    (hal : bytesT4 M (p + 4) = BitVec.ofNat 32 al) (hlt : al < size) (h31 : size < 2 ^ 31) :
    Triple (At 0x800012b4#64 (reL s0 sp p q size) M v.keepR outp)
      (At 0x800012d8#64 (setL s0 sp q al size) (writeLog M (stLog p q size)) v.keepR outp) := by
  mgrow_ctx
  have := hp.code_off; unfold textBase textLen at this
  have h4 := mod64 (x := p + 4) (by omega)
  have h16 := mod64 (x := p + 16) (by omega)
  have hsub : (size - al) % 4294967296 = size - al := Nat.mod_eq_of_lt (by omega)
  seg_step mgrowR2 0x800012d8#64 [rd4 M (p + 4)] [2, 8, 10, 12, 15] abiKeysR [reL, stLog]
    [setL] [hal, h4, h16, hsub] hc

/-- After `memset` (`12dc`): `MP_OKAY`. -/
theorem end_step (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp : Nat) (M : Mem)
    (hc : CodeAt M mpGrowBase mpGrowCode) (hra : ra.toNat % 4 = 0) (hs : SFacts sp)
    (h24 : bytesT8 M (sp - 32 + 24) = ra) :
    Triple (At 0x800012dc#64 [(2, BitVec.ofNat 64 (sp - 32)), (8, s0)] M v.keepR outp)
      (At ra (retL ra s0 sp 0#64) (writeLog M []) v.keepR outp) := by
  mgrow_ctx
  seg_step mgrowE ra [rd8 M (sp - 32 + 24)] [2, 8] abiKeysR [] [retL] [h24] hc

/-! ## The grown `mp_int` -/

/-- `a` grown to `size` digits: the old digits, zeros above. -/
def grown (a : MpInt) (size : Nat) : MpInt :=
  { a with alloc := size, digits := a.digits ++ List.replicate (size - a.alloc) 0 }

theorem grown_post {a : MpInt} {size : Nat} (ha : a.Shape) (hlt : a.alloc < size) : GrowPost a size (grown a size) :=
  { used := rfl, sign := rfl, alloc := rfl
    len := by simp only [grown, List.length_append, List.length_replicate, ha.len]; omega
    low := fun i hi => by
      simp only [grown, MpInt.digit, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [ha.len]; exact hi)]
    high := fun i hi => by
      simp only [grown, MpInt.digit, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by rw [ha.len]; exact hi), List.getElem?_replicate]
      split <;> rfl }

/-- The struct and digits after the `dp`/`alloc` stores and `memset`. -/
theorem grown_at {M2 M4 : Mem} {p q size : Nat} {a : MpInt} (ha : a.Shape) (hlt : a.alloc < size)
    (h31 : size < 2 ^ 31)
    (hs : ∀ x, p ≤ x → x < p + 24 → M4[x]? = (writeLog M2 (stLog p q size))[x]?)
    (hu : bytesT4 M2 p = BitVec.ofNat 32 a.used) (hsg : bytesT4 M2 (p + 8) = BitVec.ofNat 32 a.sign)
    (hlo : ∀ i, i < a.alloc → bytesT4 M4 (q + 4 * i) = BitVec.ofNat 32 (a.digit i))
    (hhi : ∀ i, a.alloc ≤ i → i < size → bytesT4 M4 (q + 4 * i) = 0#32) :
    MpAt M4 p q (grown a size) := by
  have h4 : ∀ o, o + 4 ≤ 24 → bytesT4 M4 (p + o) = bytesT4 (writeLog M2 (stLog p q size)) (p + o) :=
    fun _ ho => bytesT4_congr fun x h1 h2 => hs x (by omega) (by omega)
  have e : writeLog M2 (stLog p q size) =
      writeLog (writeLog M2 [(p + 16, 8, BitVec.ofNat 64 q)]) [(p + 4, 4, BitVec.ofNat 64 size)] := rfl
  have gp := grown_post ha hlt
  refine { used := ?_, alloc := ?_, sign := ?_, dpv := ?_, digits := ?_ }
  · simp only [Layout.offUsed]
    rw [h4 0 (by decide), e, bytesT4_sw_out _ _ _ _ (by omega),
      bytesT4_congr fun x h1 h2 => writeLog_out _ [(p + 16, 8, BitVec.ofNat 64 q)] x ⟨.inl (by simp only; omega), trivial⟩]
    exact hu
  · simp only [Layout.offAlloc]
    rw [h4 4 (by decide), e]; exact bytesT4_sw_self _ _ _ (by omega)
  · simp only [Layout.offSign]
    rw [h4 8 (by decide), e, bytesT4_sw_out _ _ _ _ (by omega),
      bytesT4_congr fun x h1 h2 => writeLog_out _ [(p + 16, 8, BitVec.ofNat 64 q)] x ⟨.inl (by simp only; omega), trivial⟩]
    exact hsg
  · simp only [Layout.offDp]
    rw [bytesT8_congr fun x h1 h2 => hs x (by omega) (by omega), e, bytesT8_sw_out _ _ _ _ (by omega)]
    exact bytesT8_sd_self _ _ _
  · intro i hi
    simp only [Layout.sizeofDigit]
    by_cases hl : i < a.alloc
    · rw [hlo i hl, gp.low i hl]
    · rw [hhi i (by omega) hi, gp.high i (by omega)]

end Tom.Machine.Fn.MpGrowR
