import Tom.Machine.Api.StdHeap
import Tom.Machine.Api.MpInit
import Tom.Machine.Api.MpClear
import Tom.Machine.Fn.MpInitMain
import Tom.Machine.Fn.MpClearMain
import Tom.Machine.Api.MpGrow
import Tom.Machine.Fn.MpGrowMain
import Tom.Machine.Api.MpInitCopy
import Tom.Machine.Fn.MpInitCopyMain

/-!
# The allocating functions as `HContract` records

`mp_init_size(a, size)` and `mp_clear(a)`, their `Api/MpInit.lean`/`Api/MpClear.lean`
statements (`Fn.MpInit.size_correct`, `Fn.MpClear.correct`) re-read over
`Kit/MeetHeap.lean`: the Pre's `ACtx` from the stack residue, `Heap` and
`_impure_ptr` from `AHeap`, the struct and digits from the bundle; the Post's
`Fresh`/`MpLive`/`HFrm` as the site's placement, the new kinds and the frame.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- An off-heap range misses `_impure_ptr`. -/
theorem offHeap_imp {a n x : Nat} (h : OffHeap a n) (h1 : a ≤ x) (h2 : x < a + n) : ¬ ImpI x := by
  have eL : allocLo = 0x800188a0 := rfl; have eE : heapEnd = 0x87800000 := rfl
  unfold OffHeap at h; unfold ImpI impurePtr; omega

/-- The stack of a `StkRes` is off-heap. -/
theorem StkRes.off {sp F : Nat} (h : StkRes sp F) : OffHeap (sp - F) F := by have := h.lo; unfold OffHeap; omega

/-- A struct's and a fresh block's geometry. -/
theorem geom_fresh {H : List (Nat × Nat)} {p q n : Nat} (hs : Ram p 24) (hal : p % 8 = 0) (ho : OffHeap p 24)
    (hf : Fresh H q (4 * n)) (hn : 0 < n) : MpGeom p q n :=
  { st := by simpa [Layout.sizeofMpInt] using hs, st_al := hal
    ds := by simpa [Layout.sizeofDigit] using (Place.fresh (I := Iv.nil) hf (by omega)).ram Ram.nil
    ds_al := by have := hf.al; omega
    disj := by have := hf.off_heap ho; unfold Disj at this; simp only [Layout.sizeofMpInt, Layout.sizeofDigit]; omega }

/-! ## `mp_init_size(a, size)` -/

inductive Is | stk | aS | site | code
  deriving DecidableEq

structure IsP where
  sp : Nat
  pa : Nat
  size : Nat
  H : List (Nat × Nat)

def IsP.n (p : IsP) : Nat := initPrec p.size

def Is.lay (p : IsP) : Is → Iv
  | .stk => ⟨p.sp - MpInit.Fsize, MpInit.Fsize⟩
  | .aS => ⟨p.pa, 24⟩
  | .site => Iv.nil
  | .code => textIv

def Is.out (p : IsP) : Option Nat → Is → Kind
  | some q, .aS => .mpS p.pa q (MpInt.zeroN p.n)
  | some q, .site => .mpD q p.n (MpInt.zeroN p.n).digit
  | _, .code => .code
  | _, _ => .ram

structure IsRes (p : IsP) : Prop where
  stk : StkRes p.sp MpInit.Fsize
  size_lt : p.size < 2 ^ 31
  pa_al : p.pa % 8 = 0
  soff : OffHeap p.pa 24

def Is.σ : MpInit.R → Is
  | .stk => .stk
  | .aS => .aS
  | .code => .code

def mpInitSize : HContract where
  P := IsP
  X := Option Nat
  R := Is
  all := [.stk, .aS, .site, .code]
  hall r := by cases r <;> simp
  entry := Fn.MpInit.sizeEntry
  args p := [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.size)]
  rets _ x ra := [(1, ra), (10, match x with | none => MpInit.memBV | some _ => 0#64)]
  lay := Is.lay
  kind _ := fun | .code => .code | _ => .ram
  out := Is.out
  isW := fun | .code => false | _ => true
  ws := [.stk, .aS, .site]
  site := .site
  site' p x := Ca.siteI p.n x
  hin p := p.H
  hout p x := Ca.hout p.n p.H x
  Res := IsRes
  Q p x := Ca.Q p.n p.H x
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by cases x <;> cases r <;> simp_all [Is.out, Kind.isRam, Kind.indep]
  pos p _ r := by
    cases r with
    | stk => exact .inl (show 0 < MpInit.Fsize by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | site => exact .inr (.inl (show 0x80000000 < heapStart by decide))
    | code => exact .inl (show 0 < textLen by decide)
  spec := by
    intro p m v outp ra hra hres hS hB hH _ c hc
    obtain ⟨sp, pa, size, H⟩ := p
    obtain ⟨hst, hsz, hpa, hso⟩ := hres
    have hctx := hst.ctx hc rfl rfl (hB .code).2 hH.imp hra
    have hsub : ∀ r, (MpInit.lay MpInit.Fsize sp pa r).Sub (Is.lay ⟨sp, pa, size, H⟩ (Is.σ r)) := by
      intro r; cases r <;> exact Iv.sub_self _
    have hpre : MpInit.Pre m v H sp pa MpInit.Fsize ra :=
      { heap := hH.heap, st := (hB .aS).2, st_al := hpa, soff := hso
        ctx := ⟨hctx.img, hctx.impure, hctx.gp, hctx.sp_v, hctx.sp_al, hctx.sp_lo, hctx.sp_hi⟩
        ra_al := hra, lay := hS.pull Is.σ [.stk, .aS, .code] MpInit.all hsub (by decide) }
    obtain ⟨c', hs, r, M, hat, hpost⟩ := Fn.MpInit.size_correct hpre hsz c (hc.subL rfl)
    have hW : ∀ a, InAny (MpInit.lay MpInit.Fsize sp pa) MpInit.ws a → InAny (Is.lay ⟨sp, pa, size, H⟩)
        [Is.stk, .aS, .site] a := fun a ha => by
      rcases ha with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact h.elim
    have himp : ∀ (M : Mem), HFrm (MpInit.lay MpInit.Fsize sp pa) MpInit.ws H m M → ImpureAt M := fun M hf =>
      ImpureAt.of_keep hf (fun a h1 h2 hw => hw.elim (fun hw => by
          rcases hw with h | h | h
          · exact offHeap_imp hst.off h.1 h.2 ⟨h1, h2⟩
          · exact offHeap_imp hso h.1 h.2 ⟨h1, h2⟩
          · exact h.elim) (impure_off_foot h1 h2)) hH.imp
    cases hpost with
    | @ok q hf heap live frame =>
      have hn : 0 < initPrec size := by unfold initPrec minPrec; simp only [Layout.digitBits]; omega
      have g := geom_fresh (hB .aS).2 hpa hso hf hn
      refine ⟨c', hs, some q, M, hat, hf, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | aS => exact ⟨Iv.sub_self _, Hdr.of_mpAt live.repr g⟩
                | site => exact absurd rfl hrs
                | code => simp at hr
              wsite := ⟨Iv.sub_self _, Dig.of_mpAt live.repr g⟩
              place := .fresh hf (show 0 < 4 * initPrec size by omega)
              frame := Keep.mono frame fun a h => h.imp_left (hW a)
              heap := ⟨heap, himp M frame⟩
              foot := fun a ha => .inl (Foot.of_cons ha), off := off_blk hf (show 0 < 4 * initPrec size by omega) }
    | mem heap dp frame =>
      refine ⟨c', hs, none, M, hat, trivial, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | aS => exact ⟨trivial, (hB .aS).2⟩
                | site => exact absurd rfl hrs
                | code => simp at hr
              wsite := ⟨trivial, Ram.nil⟩, place := .keep
              frame := Keep.mono frame fun a h => h.imp_left (hW a)
              heap := ⟨heap, himp M frame⟩, foot := fun a ha => .inl ha, off := Off.nil H }

/-! ## `mp_init(a)` -/

structure InP where
  sp : Nat
  pa : Nat
  H : List (Nat × Nat)

def InP.n (_ : InP) : Nat := defPrec

def In.lay (p : InP) : Is → Iv
  | .stk => ⟨p.sp - MpInit.Finit, MpInit.Finit⟩
  | .aS => ⟨p.pa, 24⟩
  | .site => Iv.nil
  | .code => textIv

def In.out (p : InP) : Option Nat → Is → Kind
  | some q, .aS => .mpS p.pa q (MpInt.zeroN p.n)
  | some q, .site => .mpD q p.n (MpInt.zeroN p.n).digit
  | _, .code => .code
  | _, _ => .ram

structure InRes (p : InP) : Prop where
  stk : StkRes p.sp MpInit.Finit
  pa_al : p.pa % 8 = 0
  soff : OffHeap p.pa 24


def mpInit : HContract where
  P := InP
  X := Option Nat
  R := Is
  all := [.stk, .aS, .site, .code]
  hall r := by cases r <;> simp
  entry := Fn.MpInit.initEntry
  args p := [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa)]
  rets _ x ra := [(1, ra), (10, match x with | none => MpInit.memBV | some _ => 0#64)]
  lay := In.lay
  kind _ := fun | .code => .code | _ => .ram
  out := In.out
  isW := fun | .code => false | _ => true
  ws := [.stk, .aS, .site]
  site := .site
  site' p x := Ca.siteI p.n x
  hin p := p.H
  hout p x := Ca.hout p.n p.H x
  Res := InRes
  Q p x := Ca.Q p.n p.H x
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by cases x <;> cases r <;> simp_all [In.out, Kind.isRam, Kind.indep]
  pos p _ r := by
    cases r with
    | stk => exact .inl (show 0 < MpInit.Finit by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | site => exact .inr (.inl (show 0x80000000 < heapStart by decide))
    | code => exact .inl (show 0 < textLen by decide)
  spec := by
    intro p m v outp ra hra hres hS hB hH _ c hc
    obtain ⟨sp, pa, H⟩ := p
    obtain ⟨hst, hpa, hso⟩ := hres
    have hctx := hst.ctx hc rfl rfl (hB .code).2 hH.imp hra
    have hsub : ∀ r, (MpInit.lay MpInit.Finit sp pa r).Sub (In.lay ⟨sp, pa, H⟩ (Is.σ r)) := by
      intro r; cases r <;> exact Iv.sub_self _
    have hpre : MpInit.Pre m v H sp pa MpInit.Finit ra :=
      { heap := hH.heap, st := (hB .aS).2, st_al := hpa, soff := hso
        ctx := ⟨hctx.img, hctx.impure, hctx.gp, hctx.sp_v, hctx.sp_al, hctx.sp_lo, hctx.sp_hi⟩
        ra_al := hra, lay := hS.pull Is.σ [.stk, .aS, .code] MpInit.all hsub (by decide) }
    obtain ⟨c', hs, r, M, hat, hpost⟩ := Fn.MpInit.init_correct hpre c (hc.subL rfl)
    have hW : ∀ a, InAny (MpInit.lay MpInit.Finit sp pa) MpInit.ws a → InAny (In.lay ⟨sp, pa, H⟩)
        [Is.stk, .aS, .site] a := fun a ha => by
      rcases ha with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact h.elim
    have himp : ∀ (M : Mem), HFrm (MpInit.lay MpInit.Finit sp pa) MpInit.ws H m M → ImpureAt M := fun M hf =>
      ImpureAt.of_keep hf (fun a h1 h2 hw => hw.elim (fun hw => by
          rcases hw with h | h | h
          · exact offHeap_imp hst.off h.1 h.2 ⟨h1, h2⟩
          · exact offHeap_imp hso h.1 h.2 ⟨h1, h2⟩
          · exact h.elim) (impure_off_foot h1 h2)) hH.imp
    cases hpost with
    | @ok q hf heap live frame =>
      have hn : 0 < defPrec := by decide
      have g := geom_fresh (hB .aS).2 hpa hso hf hn
      refine ⟨c', hs, some q, M, hat, hf, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | aS => exact ⟨Iv.sub_self _, Hdr.of_mpAt live.repr g⟩
                | site => exact absurd rfl hrs
                | code => simp at hr
              wsite := ⟨Iv.sub_self _, Dig.of_mpAt live.repr g⟩
              place := .fresh hf (show 0 < 4 * defPrec by decide)
              frame := Keep.mono frame fun a h => h.imp_left (hW a)
              heap := ⟨heap, himp M frame⟩
              foot := fun a ha => .inl (Foot.of_cons ha), off := off_blk hf (show 0 < 4 * defPrec by decide) }
    | mem heap dp frame =>
      refine ⟨c', hs, none, M, hat, trivial, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | aS => exact ⟨trivial, (hB .aS).2⟩
                | site => exact absurd rfl hrs
                | code => simp at hr
              wsite := ⟨trivial, Ram.nil⟩, place := .keep
              frame := Keep.mono frame fun a h => h.imp_left (hW a)
              heap := ⟨heap, himp M frame⟩, foot := fun a ha => .inl ha, off := Off.nil H }

/-! ## `mp_init_copy(a, b)` -/

inductive Ic | stk | aS | bS | bD | site | code
  deriving DecidableEq

structure IcP where
  sp : Nat
  pa : Nat
  pb : Nat
  bdp : Nat
  b : MpInt
  H : List (Nat × Nat)

def IcP.n (p : IcP) : Nat := initPrec p.b.used

def Ic.lay (p : IcP) : Ic → Iv
  | .stk => ⟨p.sp - MpInitCopy.F, MpInitCopy.F⟩
  | .aS => ⟨p.pa, 24⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .site => Iv.nil
  | .code => textIv

def Ic.kind (p : IcP) : Ic → Kind
  | .bS => .mpS p.pb p.bdp p.b
  | .bD => .mpD p.bdp p.b.alloc p.b.digit
  | .code => .code
  | _ => .ram

def Ic.out (p : IcP) : Option (Nat × MpInt) → Ic → Kind
  | some (q, a'), .aS => .mpS p.pa q a'
  | some (q, a'), .site => .mpD q a'.alloc a'.digit
  | _, r => Ic.kind p r

def Ic.site' (p : IcP) : Option (Nat × MpInt) → Iv
  | none => Iv.nil
  | some (q, a') => ⟨q, 4 * a'.alloc⟩

def Ic.hout (p : IcP) : Option (Nat × MpInt) → List (Nat × Nat)
  | none => p.H
  | some (q, a') => (q, 4 * a'.alloc) :: p.H

def Ic.Q (p : IcP) : Option (Nat × MpInt) → Prop
  | none => True
  | some (q, a') => Fresh p.H q (4 * p.n) ∧ CopyPost p.b (MpInt.zeroN p.n) a'

structure IcRes (p : IcP) : Prop where
  stk : StkRes p.sp MpInitCopy.F
  pa_al : p.pa % 8 = 0
  soff : OffHeap p.pa 24
  boff : OffHeap p.pb 24
  blk : digBlk p.bdp p.b ∈ p.H
  vb : p.b.Valid
  bpos : 0 < p.b.alloc

def Ic.σ : MpInitCopy.R → Ic
  | .stk => .stk
  | .aS => .aS
  | .bS => .bS
  | .bD => .bD
  | .code => .code

def mpInitCopy : HContract where
  P := IcP
  X := Option (Nat × MpInt)
  R := Ic
  all := [.stk, .aS, .bS, .bD, .site, .code]
  hall r := by cases r <;> simp
  entry := Fn.MpInitCopy.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]
  rets _ x ra := [(1, ra), (10, match x with | none => MpInit.memBV | some _ => 0#64)]
  lay := Ic.lay
  kind := Ic.kind
  out := Ic.out
  isW := fun | .stk | .aS | .site => true | _ => false
  ws := [.stk, .aS, .site]
  site := .site
  site' := Ic.site'
  hin p := p.H
  hout := Ic.hout
  Res := IcRes
  Q := Ic.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by cases x <;> cases r <;> simp_all [Ic.out, Ic.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    cases r with
    | stk => exact .inl (show 0 < MpInitCopy.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | bS => exact .inl (show 0 < 24 by decide)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by have := h.bpos; omega)
    | site => exact .inr (.inl (show 0x80000000 < heapStart by decide))
    | code => exact .inl (show 0 < textLen by decide)
  spec := by
    intro p m v outp ra hra hres hS hB hH _ c hc
    obtain ⟨sp, pa, pb, bdp, b, H⟩ := p
    have hst : StkRes sp MpInitCopy.F := hres.stk
    have hpa : pa % 8 = 0 := hres.pa_al
    have hso : OffHeap pa 24 := hres.soff
    have hbo : OffHeap pb 24 := hres.boff
    have hctx := hst.ctx hc rfl rfl (hB .code).2 hH.imp hra
    have hsub : ∀ r, (MpInitCopy.lay MpInitCopy.F sp pa pb bdp b r).Sub (Ic.lay ⟨sp, pa, pb, bdp, b, H⟩ (Ic.σ r)) := by
      intro r; cases r <;> exact Iv.sub_self _
    have gb := Hdr.geom (show Hdr m pb bdp b from (hB .bS).2)
    have hpre : MpInitCopy.Pre m v H sp pa pb bdp b ra :=
      { heap := hH.heap, st := (hB .aS).2, st_al := hpa, soff := hso
        live := ⟨Hdr.mpAt (hB .bS).2 (hB .bD).2, hres.blk, hbo⟩, vb := hres.vb, apos := hres.bpos, gb := gb
        ctx := ⟨hctx.img, hctx.impure, hctx.gp, hctx.sp_v, hctx.sp_al, hctx.sp_lo, hctx.sp_hi⟩
        ra_al := hra, lay := hS.pull Ic.σ [.stk, .aS, .bS, .bD, .code] MpInitCopy.all hsub (by decide) }
    obtain ⟨c', hs, r, M, hat, hpost⟩ := Fn.MpInitCopy.correct hpre c (hc.subL rfl)
    have hW : ∀ a, InAny (MpInitCopy.lay MpInitCopy.F sp pa pb bdp b) MpInitCopy.ws a →
        InAny (Ic.lay ⟨sp, pa, pb, bdp, b, H⟩) [Ic.stk, .aS, .site] a := fun a ha => by
      rcases ha with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact h.elim
    have himp : ∀ (M : Mem), HFrm (MpInitCopy.lay MpInitCopy.F sp pa pb bdp b) MpInitCopy.ws H m M →
        ImpureAt M := fun M hf =>
      ImpureAt.of_keep hf (fun a h1 h2 hw => hw.elim (fun hw => by
          rcases hw with h | h | h
          · exact offHeap_imp hst.off h.1 h.2 ⟨h1, h2⟩
          · exact offHeap_imp hso h.1 h.2 ⟨h1, h2⟩
          · exact h.elim) (impure_off_foot h1 h2)) hH.imp
    have hn : 0 < initPrec b.used := by unfold initPrec minPrec; simp only [Layout.digitBits]; omega
    cases hpost with
    | @ok q a' hf heap live copy frame =>
      have hal : a'.alloc = initPrec b.used := copy.alloc
      have hf' : Fresh H q (4 * a'.alloc) := by rw [hal]; exact hf
      have g := geom_fresh (show Ram pa 24 from (hB .aS).2) hpa hso hf' (by rw [hal]; exact hn)
      refine ⟨c', hs, some (q, a'), M, hat, ⟨hf, copy⟩, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | aS => exact ⟨Iv.sub_self _, Hdr.of_mpAt live.repr g⟩
                | site => exact absurd rfl hrs
                | _ => simp at hr
              wsite := ⟨Iv.sub_self _, Dig.of_mpAt live.repr g⟩
              place := .fresh hf' (by rw [hal]; omega)
              frame := Keep.mono frame fun a h => h.imp_left (hW a)
              heap := ⟨by show Heap M ((q, 4 * a'.alloc) :: H); rw [hal]; exact heap, himp M frame⟩
              foot := fun a ha => .inl (Foot.of_cons ha), off := off_blk hf' (by rw [hal]; omega) }
    | mem heap dp frame =>
      refine ⟨c', hs, none, M, hat, trivial, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | aS => exact ⟨trivial, (hB .aS).2⟩
                | site => exact absurd rfl hrs
                | _ => simp at hr
              wsite := ⟨trivial, Ram.nil⟩, place := .keep
              frame := Keep.mono frame fun a h => h.imp_left (hW a)
              heap := ⟨heap, himp M frame⟩, foot := fun a ha => .inl ha, off := Off.nil H }

/-! ## `mp_clear(a)` of a live `a` -/

structure ClP where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt
  H : List (Nat × Nat)

structure ClRes (p : ClP) : Prop where
  stk : StkRes p.sp MpClear.F
  soff : OffHeap p.pa 24
  apos : 0 < p.a.alloc

def mpClear : HContract where
  P := ClP
  X := Unit
  R := Un.R
  all := [.stk, .aS, .aD, .code]
  hall := Un.all
  entry := Fn.MpClear.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa)]
  rets _ _ ra := [(1, ra)]
  lay p := Un.lay MpClear.F p.sp p.pa p.adp p.a
  kind p := Tom.Machine.Un.kind p.pa p.adp p.a
  out _ _ := fun | .code => .code | _ => .ram
  isW := Un.isW
  ws := Un.ws
  site := .aD
  site' _ _ := Iv.nil
  hin p := digBlk p.adp p.a :: p.H
  hout p _ := p.H
  Res := ClRes
  Q _ _ := True
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by cases r <;> simp_all [Kind.isRam, Kind.indep]
  pos p h r := by
    cases r with
    | stk => exact .inl (show 0 < MpClear.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by have := h.apos; omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := by
    intro p m v outp ra hra hres hS hB hH _ c hc
    obtain ⟨sp, pa, adp, a, H⟩ := p
    obtain ⟨hst, hso, hap⟩ := hres
    have hctx := hst.ctx hc rfl rfl (hB .code).2 hH.imp hra
    have g := Hdr.geom (hB .aS).2
    have hpre : MpClear.Pre m v H sp pa adp a ra :=
      { repr := Hdr.mpAt (hB .aS).2 (hB .aD).2, heap := hH.heap
        st := by simpa [Layout.sizeofMpInt] using g.st, st_al := g.st_al, soff := hso
        ctx := ⟨hctx.img, hctx.impure, hctx.gp, hctx.sp_v, hctx.sp_al, hctx.sp_lo, hctx.sp_hi⟩
        ra_al := hra, lay := hS }
    obtain ⟨c', hs, M, hat, hpost⟩ := Fn.MpClear.correct hpre c (hc.subL rfl)
    have hb := Fn.Alloc.Heap.blk hH.heap (List.mem_cons_self ..)
    refine ⟨c', hs, (), M, hat, trivial, ?_⟩
    exact { wit := fun r hr hrs => by
              cases r with
              | stk => exact ⟨trivial, (hB .stk).2⟩
              | aS => exact ⟨trivial, show Ram pa 24 by simpa [Layout.sizeofMpInt] using g.st⟩
              | aD => exact absurd rfl hrs
              | code => simp [Un.ws] at hr
            wsite := ⟨trivial, Ram.nil⟩, place := .nil
            frame := Keep.mono hpost.frame fun x h => h.elim .inl fun hf =>
              (foot_uncons (e := digBlk adp a) hf).elim .inr fun hb' => .inl (.inr (.inr (.inl hb')))
            heap := ⟨hpost.heap, ImpureAt.of_keep hpost.frame (fun x h1 h2 hw => hw.elim (fun hw => by
                rcases hw with h | h | h | h
                · exact offHeap_imp hst.off h.1 h.2 ⟨h1, h2⟩
                · exact offHeap_imp hso h.1 h.2 ⟨h1, h2⟩
                · have e : heapStart = 0x80019d10 := rfl
                  have hb1 : heapStart + 16 ≤ adp := hb.1
                  have := h.1; simp only [Un.lay] at this; unfold impurePtr at h2; omega
                · exact h.elim) (impure_off_foot h1 h2)) hH.imp⟩
            foot := fun a ha => foot_uncons ha, off := Off.nil H }

/-! ## `mp_grow(a, size)` (with `realloc`) of a live `a` -/

structure GrP where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt
  size : Nat
  H : List (Nat × Nat)

structure GrRes (p : GrP) : Prop where
  stk : StkRes p.sp MpGrow.F
  soff : OffHeap p.pa 24
  shape : p.a.Shape
  apos : 0 < p.a.alloc
  size_lt : p.size < 2 ^ 31

/-- `none`: room, nothing done; `some none`: `realloc` failed; `some (some (q, a'))`: grown at `q`. -/
abbrev GrX := Option (Option (Nat × MpInt))

def Gr.out (p : GrP) : GrX → Un.R → Kind
  | some (some (q, a')), .aS => .mpS p.pa q a'
  | some (some (q, a')), .aD => .mpD q a'.alloc a'.digit
  | _, r => Tom.Machine.Un.kind p.pa p.adp p.a r

def Gr.site' (p : GrP) : GrX → Iv
  | some (some (q, a')) => ⟨q, 4 * a'.alloc⟩
  | _ => ⟨p.adp, 4 * p.a.alloc⟩

def Gr.hout (p : GrP) : GrX → List (Nat × Nat)
  | some (some (q, a')) => (q, 4 * a'.alloc) :: p.H
  | _ => digBlk p.adp p.a :: p.H

def Gr.Q (p : GrP) : GrX → Prop
  | none => p.size ≤ p.a.alloc
  | some none => p.a.alloc < p.size
  | some (some (_, a')) => p.a.alloc < p.size ∧ GrowPost p.a p.size a'

def mpGrowH : HContract where
  P := GrP
  X := GrX
  R := Un.R
  all := [.stk, .aS, .aD, .code]
  hall := Un.all
  entry := Fn.MpGrowR.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.size)]
  rets _ x ra := [(1, ra), (10, match x with | some none => MpGrow.memBV | _ => 0#64)]
  lay p := Un.lay MpGrow.F p.sp p.pa p.adp p.a
  kind p := Tom.Machine.Un.kind p.pa p.adp p.a
  out := Gr.out
  isW := Un.isW
  ws := Un.ws
  site := .aD
  site' := Gr.site'
  hin p := digBlk p.adp p.a :: p.H
  hout := Gr.hout
  Res := GrRes
  Q := Gr.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | _ | ⟨q, a'⟩ <;> cases r <;> simp_all [Gr.out, Tom.Machine.Un.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    cases r with
    | stk => exact .inl (show 0 < MpGrow.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by have := h.apos; omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := by
    intro p m v outp ra hra hres hS hB hH hoff c hc
    obtain ⟨sp, pa, adp, a, size, H⟩ := p
    obtain ⟨hst, hso, hsh, hap, hsz⟩ := hres
    have hctx := hst.ctx hc rfl rfl (hB .code).2 hH.imp hra
    have g := Hdr.geom (hB .aS).2
    have hpre : MpGrow.Pre m v H sp pa adp a size ra :=
      { repr := Hdr.mpAt (hB .aS).2 (hB .aD).2, shape := hsh, heap := hH.heap
        st := by simpa [Layout.sizeofMpInt] using g.st, st_al := g.st_al, soff := hso, size_lt := hsz
        ctx := ⟨hctx.img, hctx.impure, hctx.gp, hctx.sp_v, hctx.sp_al, hctx.sp_lo, hctx.sp_hi⟩
        ra_al := hra, lay := hS }
    obtain ⟨c', hs, r, M, hat, hpost⟩ := Fn.MpGrowR.correct hpre c (hc.subL rfl)
    have hb := Fn.Alloc.Heap.blk hH.heap (List.mem_cons_self ..)
    have hstr : Ram pa 24 := by simpa [Layout.sizeofMpInt] using g.st
    have himp : ∀ (M : Mem), HFrm (MpGrow.lay sp pa adp a) Un.ws H m M → ImpureAt M := fun M hf =>
      ImpureAt.of_keep hf (fun x h1 h2 hw => hw.elim (fun hw => by
          rcases hw with h | h | h | h
          · exact offHeap_imp hst.off h.1 h.2 ⟨h1, h2⟩
          · exact offHeap_imp hso h.1 h.2 ⟨h1, h2⟩
          · have e : heapStart = 0x80019d10 := rfl
            have hb1 : heapStart + 16 ≤ adp := hb.1
            have := h.1; simp only [Un.lay] at this; unfold impurePtr at h2; omega
          · exact h.elim) (impure_off_foot h1 h2)) hH.imp
    have hfr : ∀ (M : Mem), HFrm (MpGrow.lay sp pa adp a) Un.ws H m M →
        HFrm (Un.lay MpGrow.F sp pa adp a) Un.ws (digBlk adp a :: H) m M := fun M hf =>
      Keep.mono hf fun x h => h.elim .inl fun hf =>
        (foot_uncons (e := digBlk adp a) hf).elim .inr fun hb' => .inl (.inr (.inr (.inl hb')))
    cases hpost with
    | keep hle same =>
      rw [same] at hat
      refine ⟨c', hs, none, m, hat, hle, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | aS => exact hB .aS
                | aD => exact absurd rfl hrs
                | code => simp [Un.ws] at hr
              wsite := hB .aD, place := .keep, frame := fun _ _ => rfl, heap := hH
              foot := fun a ha => .inl ha, off := hoff .aD }
    | @ok q a' hlt hf heap repr grow frame =>
      have hn : 0 < size := by omega
      have g' := geom_fresh hstr g.st_al hso (grow.alloc ▸ hf) (by rw [grow.alloc]; exact hn)
      refine ⟨c', hs, some (some (q, a')), M, hat, ⟨hlt, grow⟩, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | aS => exact ⟨Iv.sub_self _, Hdr.of_mpAt repr g'⟩
                | aD => exact absurd rfl hrs
                | code => simp [Un.ws] at hr
              wsite := ⟨Iv.sub_self _, Dig.of_mpAt repr g'⟩
              place := .regrow (grow.alloc ▸ hf) (by rw [grow.alloc]; omega) rfl
              frame := hfr M frame, heap := ⟨by rw [Gr.hout, grow.alloc]; exact heap, himp M frame⟩
              foot := fun x hx => foot_uncons (e := digBlk adp a) (Foot.of_cons hx)
              off := by show Off ⟨q, 4 * a'.alloc⟩ ((q, 4 * a'.alloc) :: H); exact off_blk (grow.alloc ▸ hf) (by rw [grow.alloc]; omega) }
    | mem hlt heap repr frame =>
      refine ⟨c', hs, some none, M, hat, hlt, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | aS => exact ⟨Iv.sub_self _, Hdr.of_mpAt repr g⟩
                | aD => exact absurd rfl hrs
                | code => simp [Un.ws] at hr
              wsite := ⟨Iv.sub_self _, Dig.of_mpAt repr g⟩, place := .keep
              frame := hfr M frame, heap := ⟨heap, himp M frame⟩
              foot := fun x hx => .inl hx, off := hoff .aD }

end Tom.Machine.Std
