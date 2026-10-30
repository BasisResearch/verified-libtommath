import Tom.Machine.Kit.Meet
import Tom.Machine.Api.MpZero
import Tom.Machine.Api.Libgcc
import Tom.Machine.Fn.MpZeroMain
import Tom.Machine.Fn.LibgccSigned
import Tom.Machine.Fn.Clamp
import Tom.Machine.Fn.MpGrow
import Tom.Machine.Fn.MemcpyMain
import Tom.Machine.Kit.MulCall
import Tom.Machine.Kit.Bytes
import Tom.Machine.Fn.CmpMag
import Tom.Machine.Kit.BitW
import Tom.Spec.DigitShift

/-!
# Standard contracts as `Contract` records: the leaf library (the adapters)

`mp_zero`, `mp_clamp`, `mp_grow` (with room), `memset(d, 0, n)` over a digit
array (`memsetD`: the `MP_ZERO_DIGITS` calls), `__divdi3`, `__moddi3`,
`__muldi3`, `memcpy` from one digit array into another (`memcpyD`), `mp_cmp_mag`. Each is
its existing statement, re-read: the Pre from the region bundle and a scalar
residue, the Post as the written regions' new witnesses. `Api/Std.lean` adds
the contracts of functions proved over `Kit/Meet.lean` (`mp_copy`, `mp_lshd`).
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api

theorem At.sp_eq {pc : BitVec 64} {L : GRegs} {m : Mem} {v : Abi} {outp : Array String} {c : Vsa.Machine.Config}
    (h : At pc L m v.keep outp c) {x : BitVec 64} (hx : lookupG 2 L = some x) : v.sp = x := by
  have h1 := gholds_lookup L h.regs hx
  have h2 := gholds_lookup (n := 2) (v := v.sp) v.keep h.keep rfl
  rw [h1] at h2; exact (Option.some.inj h2).symm

theorem witS {M : Mem} {p dp : Nat} {a a' : MpInt} (hM : MpAt M p dp a') (g : MpGeom p dp a.alloc)
    (hal : a'.alloc = a.alloc) {I : Iv} (hI : Iv.Sub ⟨p, 24⟩ I) :
    (Kind.mpS p dp a').Fits I ∧ (Kind.mpS p dp a').Wit I M := ⟨hI, Hdr.of_mpAt hM (hal ▸ g)⟩

theorem witD {M : Mem} {p dp : Nat} {a a' : MpInt} (hM : MpAt M p dp a') (g : MpGeom p dp a.alloc)
    (hal : a'.alloc = a.alloc) {I : Iv} (hI : Iv.Sub ⟨dp, 4 * a.alloc⟩ I) :
    (Kind.mpD dp a'.alloc a'.digit).Fits I ∧ (Kind.mpD dp a'.alloc a'.digit).Wit I M :=
  ⟨by show Iv.Sub ⟨dp, 4 * a'.alloc⟩ I; rw [hal]; exact hI, Dig.of_mpAt hM (hal ▸ g)⟩

theorem _root_.Tom.CopyPost.shape {a b b' : MpInt} (h : CopyPost a b b') (ha : a.Shape) (hb : b.Shape)
    (hroom : a.used ≤ b.alloc) : b'.Shape :=
  { len := by rw [h.len, h.alloc]
    used_le := by rw [h.used, h.alloc]; exact hroom
    alloc_lt := by rw [h.alloc]; exact hb.alloc_lt
    digit_lt := fun i => by
      rw [h.digit]; split
      · exact ha.digit_lt _
      · split
        · exact radix_pos
        · exact hb.digit_lt _
    high_zero := fun i hi => by
      rw [h.used] at hi; rw [h.digit, if_neg (by omega)]; split
      · rfl
      · exact hb.high_zero i (by omega) }

theorem _root_.Tom.ZeroPost.shape {a a' : MpInt} (h : ZeroPost a a') (ha : a.Shape) : a'.Shape :=
  { len := by rw [h.len, h.alloc], used_le := by rw [h.used]; exact Nat.zero_le _
    alloc_lt := by rw [h.alloc]; exact ha.alloc_lt
    digit_lt := fun i => by rw [h.digit]; exact radix_pos
    high_zero := fun i _ => h.digit i }

theorem _root_.Tom.LshdPost.alloc' {a a' : MpInt} {k : Nat} (h : LshdPost a k a') : a'.alloc = a.alloc := by
  by_cases h0 : k = 0 ∨ a.used = 0
  · rw [h.noop h0]
  · exact (h.shift (by omega) (by omega)).alloc

/-! ## One operand, no stack: `mp_zero(a)`, `mp_clamp(a)` -/

inductive Ob | S | D | code
  deriving DecidableEq

def Ob.lay (p dp n : Nat) : Ob → Iv
  | .S => ⟨p, 24⟩
  | .D => ⟨dp, 4 * n⟩
  | .code => textIv

def Ob.kind (p dp : Nat) (a : MpInt) : Ob → Kind
  | .S => .mpS p dp a
  | .D => .mpD dp a.alloc a.digit
  | .code => .code

def Ob.isW : Ob → Bool
  | .code => false
  | _ => true

def Ob.isWS : Ob → Bool
  | .S => true
  | _ => false

structure ObP where
  p : Nat
  dp : Nat
  a : MpInt

theorem Ob.all (r : Ob) : r ∈ [Ob.S, .D, .code] := by cases r <;> simp

def mpZero : Contract where
  P := ObP
  X := MpInt
  R := Ob
  all := [.S, .D, .code]
  hall := Ob.all
  entry := MpZero.entry
  args p := [(10, BitVec.ofNat 64 p.p)]
  rets _ ra := [(1, ra)]
  lay p := Ob.lay p.p p.dp p.a.alloc
  kind := fun ⟨p, dp, a⟩ => Ob.kind p dp a
  out := fun ⟨p, dp, _⟩ x => Ob.kind p dp x
  isW := Ob.isW
  ws := [.S, .D]
  Res p := p.a.Shape
  Q p x := ZeroPost p.a x ∧ x.Shape
  fits p r := by cases p; cases r <;> exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> simp [Ob.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Ob.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB
    obtain ⟨qp, qdp, qa⟩ := p
    have e1 := hS .S .D (by decide); have e2 := hS .S .code (by decide); have e3 := hS .D .code (by decide)
    have hU : Sound (Un.lay 0 0 qp qdp qa) Un.isW := fun r s h => by
      cases r <;> cases s <;> simp_all [Sep, Un.isW, Un.lay, Ob.lay, Iv.Disj, Disj] <;> omega
    have hpre : MpZero.Pre m 0 qp qdp qa ra :=
      { ra_ := Hdr.mpAt (hB .S).2 (hB .D).2, sa := hres, ga := Hdr.geom (hB .S).2, ra_al := hra
        img := (hB .code).2, lay := hU }
    refine Triple.rmap (fun cf ⟨a', M, hat, hpost⟩ => ?_) (Fn.MpZero.correct (v := v) (outp := outp) hpre)
    have hF : Frm (Ob.lay qp qdp qa.alloc) [Ob.S, Ob.D] m M := fun x hx => hpost.frame x fun h' => by
      rcases h' with h' | h' | h' | h'
      · simp [Un.lay, Iv.In] at h'
      · exact hx (Or.inl h')
      · exact hx (Or.inr (Or.inl h'))
      · exact h'.elim
    have hal := hpost.zero.alloc
    refine ⟨a', M, hat.sub rfl rfl, ⟨hpost.zero, hpost.zero.shape hres⟩, ?_, hF⟩
    intro r; cases r
    · exact witS hpost.repr (Hdr.geom (hB .S).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .S).2) hal (Iv.sub_self _)
    · exact hB.keep hS hF Ob.code

def clamp : Contract where
  P := ObP
  X := MpInt
  R := Ob
  all := [.S, .D, .code]
  hall := Ob.all
  entry := Fn.Clamp.entry
  args p := [(10, BitVec.ofNat 64 p.p)]
  rets p ra := [(1, ra), (10, BitVec.ofNat 64 p.p)]
  lay p := Ob.lay p.p p.dp p.a.alloc
  kind := fun ⟨p, dp, a⟩ => Ob.kind p dp a
  out := fun ⟨p, dp, a⟩ x r => if r = .S then .mpS p dp x else Ob.kind p dp a r
  isW := Ob.isWS
  ws := [.S]
  Res p := p.a.Shape
  Q p x := ClampPost p.a x
  fits p r := by cases p; cases r <;> exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> simp [Ob.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Ob.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB
    obtain ⟨qp, qdp, qa⟩ := p
    have hco := hS.sub (r := Ob.S) (s := Ob.code) (Iv.sub_self _)
      (show Iv.Sub ⟨mpClampBase, 64⟩ textIv from ⟨by decide, by decide⟩) (by decide)
    have hpre : Fn.Clamp.Pre m qp qdp qa :=
      { repr := Hdr.mpAt (hB .S).2 (hB .D).2, shape := hres, geom := Hdr.geom (hB .S).2
        code := Img.mpClamp (hB .code).2, code_off := hco }
    refine Triple.rmap (fun cf ⟨a', M, hat, hpost⟩ => ?_) (Fn.Clamp.correct ra v outp qp qdp qa m hra hpre)
    have hF : Frm (Ob.lay qp qdp qa.alloc) [Ob.S] m M :=
      Frm.call (w := Ob.S) hpost.frame (by simp only [Iv.Sub, Ob.lay]; omega)
    refine ⟨a', M, hat.sub rfl rfl, hpost.clamp, ?_, hF⟩
    intro r; cases r
    · exact witS hpost.repr (Hdr.geom (hB .S).2) hpost.clamp.alloc (Iv.sub_self _)
    · exact hB.keep hS hF Ob.D
    · exact hB.keep hS hF Ob.code

/-! ## `memset(dp + 4 i, 0, 4 (k - i))` over a digit array -/

/-- Digits `[i, k)` zeroed. -/
def zfill (f : Nat → Nat) (i k : Nat) : Nat → Nat := fun j => if i ≤ j ∧ j < k then 0 else f j

inductive Dz | D | code
  deriving DecidableEq

structure ZP where
  dp : Nat
  n : Nat
  f : Nat → Nat
  i : Nat
  k : Nat
  /-- The word count `k - i`. -/
  w : Nat

def memsetD : Contract where
  P := ZP
  X := Unit
  R := Dz
  all := [.D, .code]
  hall r := by cases r <;> simp
  entry := Fn.Memset.entry
  args p := [(10, BitVec.ofNat 64 (p.dp + 4 * p.i)), (11, 0#64), (12, BitVec.ofNat 64 (4 * p.w))]
  rets _ ra := [(1, ra)]
  lay p := fun | .D => ⟨p.dp, 4 * p.n⟩ | .code => textIv
  kind := fun ⟨dp, n, f, _, _, _⟩ r => match r with | .D => .mpD dp n f | .code => .code
  out := fun ⟨dp, n, f, i, k, _⟩ _ r => match r with | .D => .mpD dp n (zfill f i k) | .code => .code
  isW := fun | .D => true | .code => false
  ws := [.D]
  Res p := p.i ≤ p.k ∧ p.k ≤ p.n ∧ p.w = p.k - p.i
  Q _ _ := True
  fits p r := by cases p; cases r <;> exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> simp [Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB
    obtain ⟨qdp, qn, qf, qi, qk, qw⟩ := p
    obtain ⟨hik, hkn, hw⟩ : qi ≤ qk ∧ qk ≤ qn ∧ qw = qk - qi := hres
    subst hw
    have hd : Dig m qdp qn qf := (hB .D).2
    have hpre : Fn.Memset.Pre m (qdp + 4 * qi) 0 (4 * (qk - qi)) :=
      memset_pre hS (r := Dz.D) (c := Dz.code) (hB .code).2 (Iv.sub_self _)
        (by show Iv.Sub _ ⟨qdp, 4 * qn⟩; simp only [Iv.Sub]; omega)
        (Ram.sub hd.ram (by omega) (by omega))
    refine Triple.rmap (fun cf ⟨M, hat, hpost⟩ => ?_)
      (Fn.Memset.correct_zero ra v outp m (qdp + 4 * qi) (4 * (qk - qi)) hra hpre)
    have hF : Frm (fun | .D => (⟨qdp, 4 * qn⟩ : Iv) | .code => textIv) [Dz.D] m M :=
      Frm.call (w := Dz.D) hpost.frame (by show Iv.Sub _ ⟨qdp, 4 * qn⟩; simp only [Iv.Sub]; omega)
    refine ⟨(), M, hat.sub rfl rfl, trivial, ?_, hF⟩
    intro r; cases r
    · refine ⟨Iv.sub_self _, ?_⟩
      show Dig M qdp qn (zfill qf qi qk)
      refine { ram := hd.ram, al := hd.al, arr := fun j hj => ?_ }
      by_cases hin : qi ≤ j ∧ j < qk
      · rw [bytesT4_zero fun t ht => by
          have := hpost.fill (4 * (j - qi) + t) (by omega)
          rwa [show qdp + 4 * qi + (4 * (j - qi) + t) = qdp + 4 * j + t by omega] at this]
        simp [zfill, hin]
      · rw [bytesT4_congr fun y h1 h2 => hpost.frame y (by omega), hd.arr j hj]
        simp [zfill, hin]
    · exact hB.keep hS hF Dz.code

/-! ## libgcc: `__divdi3`, `__moddi3` on non-negative operands -/

inductive Cd | code
  deriving DecidableEq

structure DivP where
  n : Nat
  d : Nat

structure DivRes (p : DivP) : Prop where
  n_lt : p.n < 2 ^ 63
  d_pos : 0 < p.d
  d_lt : p.d < 2 ^ 63

theorem DivRes.of {n d : Nat} (hn : n < 2 ^ 63) (hd : 0 < d) (hd' : d < 2 ^ 63) : DivRes ⟨n, d⟩ :=
  ⟨hn, hd, hd'⟩

theorem ofNat_ne_zero {d : Nat} (h1 : 0 < d) (h2 : d < 2 ^ 63) : BitVec.ofNat 64 d ≠ 0#64 := fun h => by
  have := congrArg BitVec.toNat h; simp at this; omega

def divdi3 : Contract where
  P := DivP
  X := Unit
  R := Cd
  all := [.code]
  hall r := by cases r; simp
  entry := Libgcc.divdi3Entry
  args p := [(10, BitVec.ofNat 64 p.n), (11, BitVec.ofNat 64 p.d)]
  rets p _ := [(10, BitVec.ofNat 64 (p.n / p.d))]
  lay _ _ := textIv
  kind _ _ := .code
  out _ _ _ := .code
  isW _ := false
  ws := []
  Res := DivRes
  Q _ _ := True
  fits _ _ := Iv.sub_self _
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB
    have h := Fn.Libgcc.Divdi3.correct (v := v) (outp := outp) (n := BitVec.ofNat 64 p.n)
      (d := BitVec.ofNat 64 p.d) (hB .code).2 hra (ofNat_ne_zero hres.d_pos hres.d_lt)
    rw [BitW.sdiv_ofNat _ _ hres.n_lt hres.d_lt] at h
    exact Triple.rmap (fun cf hc => ⟨(), m, hc, trivial, hB, Frm.refl _ _⟩) h

def moddi3 : Contract where
  P := DivP
  X := Unit
  R := Cd
  all := [.code]
  hall r := by cases r; simp
  entry := Libgcc.moddi3Entry
  args p := [(10, BitVec.ofNat 64 p.n), (11, BitVec.ofNat 64 p.d)]
  rets p _ := [(10, BitVec.ofNat 64 (p.n % p.d))]
  lay _ _ := textIv
  kind _ _ := .code
  out _ _ _ := .code
  isW _ := false
  ws := []
  Res := DivRes
  Q _ _ := True
  fits _ _ := Iv.sub_self _
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB
    have h := Fn.Libgcc.Moddi3.correct (v := v) (outp := outp) (n := BitVec.ofNat 64 p.n)
      (d := BitVec.ofNat 64 p.d) (hB .code).2 hra (ofNat_ne_zero hres.d_pos hres.d_lt)
    rw [BitW.srem_ofNat _ _ hres.n_lt hres.d_lt] at h
    exact Triple.rmap (fun cf hc => ⟨(), m, hc, trivial, hB, Frm.refl _ _⟩) h

/-! ## `mp_grow(a, size)` with room (no `realloc`, D5) -/

structure GrowP where
  p : Nat
  dp : Nat
  a : MpInt
  size : Nat

def mpGrow : Contract where
  P := GrowP
  X := Unit
  R := Ob
  all := [.S, .D, .code]
  hall := Ob.all
  entry := Fn.MpGrow.entry
  args p := [(10, BitVec.ofNat 64 p.p), (11, BitVec.ofNat 64 p.size)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Ob.lay p.p p.dp p.a.alloc
  kind := fun ⟨p, dp, a, _⟩ => Ob.kind p dp a
  out := fun ⟨p, dp, a, _⟩ _ => Ob.kind p dp a
  isW _ := false
  ws := []
  Res p := p.a.Shape ∧ p.size ≤ p.a.alloc
  Q _ _ := True
  fits p r := by cases p; cases r <;> exact Iv.sub_self _
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB
    obtain ⟨qp, qdp, qa, qs⟩ := p
    have h := Fn.MpGrow.correct_ok (v := v) (outp := outp)
      { repr := Hdr.mpAt (hB .S).2 (hB .D).2, shape := hres.1, geom := Hdr.geom (hB .S).2, room := hres.2
        ra_al := hra, img := (hB .code).2 : Fn.MpGrow.PreOK m qp qdp qa qs ra }
    exact Triple.rmap (fun cf hc => ⟨(), m, hc.sub rfl rfl, trivial, hB, Frm.refl _ _⟩) h

/-! ## `__muldi3` -/

structure MulP where
  x : Nat
  y : Nat

def muldi3 : Contract where
  P := MulP
  X := Unit
  R := Cd
  all := [.code]
  hall r := by cases r; simp
  entry := Libgcc.muldi3Entry
  args p := [(10, BitVec.ofNat 64 p.x), (11, BitVec.ofNat 64 p.y)]
  rets p ra := [(1, ra), (10, BitVec.ofNat 64 (p.x * p.y))]
  lay _ _ := textIv
  kind _ _ := .code
  out _ _ _ := .code
  isW _ := false
  ws := []
  Res _ := True
  Q _ _ := True
  fits _ _ := Iv.sub_self _
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB
    have h := Fn.Libgcc.Muldi3.correct (v := v) (outp := outp) (x := BitVec.ofNat 64 p.x)
      (y := BitVec.ofNat 64 p.y) (hB .code).2 hra
    rw [ofNat_mul_ofNat] at h
    exact Triple.rmap (fun cf hc => ⟨(), m, hc, trivial, hB, Frm.refl _ _⟩) h

/-! ## `memcpy(d + 4 i, s + 4 j, 4 k)` from one digit array into another -/

/-- Digits `[i, i + k)` of `f` replaced by `g`'s from `j`. -/
def cpy (f g : Nat → Nat) (i j k : Nat) : Nat → Nat := fun t => if i ≤ t ∧ t < i + k then g (j + (t - i)) else f t

inductive Dc | D | S | code
  deriving DecidableEq

structure CpP where
  ddp : Nat
  dn : Nat
  df : Nat → Nat
  di : Nat
  sdp : Nat
  sn : Nat
  sf : Nat → Nat
  sj : Nat
  k : Nat

def Dc.lay (p : CpP) : Dc → Iv
  | .D => ⟨p.ddp, 4 * p.dn⟩
  | .S => ⟨p.sdp, 4 * p.sn⟩
  | .code => textIv

theorem memcpy_sub : Iv.Sub ⟨memcpyBase, 4 * memcpyCode.length⟩ textIv := ⟨by decide, by decide⟩

def memcpyD : Contract where
  P := CpP
  X := Unit
  R := Dc
  all := [.D, .S, .code]
  hall r := by cases r <;> simp
  entry := Fn.Memcpy.entry
  args p := [(10, BitVec.ofNat 64 (p.ddp + 4 * p.di)), (11, BitVec.ofNat 64 (p.sdp + 4 * p.sj)),
    (12, BitVec.ofNat 64 (4 * p.k))]
  rets p ra := [(1, ra), (10, BitVec.ofNat 64 (p.ddp + 4 * p.di))]
  lay := Dc.lay
  kind p r := match r with | .D => .mpD p.ddp p.dn p.df | .S => .mpD p.sdp p.sn p.sf | .code => .code
  out p _ r := match r with
    | .D => .mpD p.ddp p.dn (cpy p.df p.sf p.di p.sj p.k) | .S => .mpD p.sdp p.sn p.sf | .code => .code
  isW := fun | .D => true | _ => false
  ws := [.D]
  Res p := p.di + p.k ≤ p.dn ∧ p.sj + p.k ≤ p.sn
  Q _ _ := True
  fits p r := by cases r <;> exact Iv.sub_self _
  out_ram p x r _ h := by cases r <;> simp [Kind.isRam] at h
  out_ind p x r _ h := by cases r <;> first | rfl | simp [Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB
    obtain ⟨qd, qn, qf, qi, qs, qsn, qg, qj, qk⟩ := p
    obtain ⟨hik, hjk⟩ : qi + qk ≤ qn ∧ qj + qk ≤ qsn := hres
    have hd : Dig m qd qn qf := (hB .D).2
    have hs : Dig m qs qsn qg := (hB .S).2
    have hI : Iv.Sub ⟨qd + 4 * qi, 4 * qk⟩ ⟨qd, 4 * qn⟩ := by simp only [Iv.Sub]; omega
    have hJ : Iv.Sub ⟨qs + 4 * qj, 4 * qk⟩ ⟨qs, 4 * qsn⟩ := by simp only [Iv.Sub]; omega
    have hpre : Fn.Memcpy.Pre m (qd + 4 * qi) (qs + 4 * qj) (4 * qk) :=
      { img := (hB .code).2, rd := Ram.sub hd.ram (by omega) (by omega), rs := Ram.sub hs.ram (by omega) (by omega)
        disj := hS.sub (r := Dc.D) (s := Dc.S) hI hJ (by decide)
        code_off := hS.sub (r := Dc.D) (s := Dc.code) hI memcpy_sub (by decide) }
    refine Triple.rmap (fun cf ⟨M, hat, hpost⟩ => ?_)
      (Fn.Memcpy.correct ra v outp m (qd + 4 * qi) (qs + 4 * qj) (4 * qk) hra hpre)
    have hF : Frm (Dc.lay ⟨qd, qn, qf, qi, qs, qsn, qg, qj, qk⟩) [Dc.D] m M :=
      Frm.call (w := Dc.D) hpost.frame (by show Iv.Sub _ ⟨qd, 4 * qn⟩; exact hI)
    refine ⟨(), M, hat.sub rfl rfl, trivial, ?_, hF⟩
    intro r; cases r
    · refine ⟨Iv.sub_self _, ?_⟩
      show Dig M qd qn (cpy qf qg qi qj qk)
      refine { ram := hd.ram, al := hd.al, arr := fun t ht => ?_ }
      by_cases hin : qi ≤ t ∧ t < qi + qk
      · have e : bytesT4 M (qd + 4 * t) = bytesT4 m (qs + 4 * (qj + (t - qi))) := bytesT4_congrD fun j hj => by
          have := hpost.copy (4 * (t - qi) + j) (by omega)
          rw [show qd + 4 * qi + (4 * (t - qi) + j) = qd + 4 * t + j by omega,
            show qs + 4 * qj + (4 * (t - qi) + j) = qs + 4 * (qj + (t - qi)) + j by omega] at this
          rw [this]; rfl
        rw [e, hs.arr _ (by omega)]
        simp [cpy, hin]
      · rw [bytesT4_congr fun y h1 h2 => hpost.frame y (by omega), hd.arr t ht]
        simp [cpy, hin]
    · exact hB.keep hS hF Dc.S
    · exact hB.keep hS hF Dc.code

/-! ## `mp_cmp_mag(a, b)` -/

inductive Cm | aS | aD | bS | bD | code
  deriving DecidableEq

structure CmP where
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt

def Cm.lay (p : CmP) : Cm → Iv
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .bS => ⟨p.pb, 24⟩
  | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
  | .code => textIv

def Cm.kind (p : CmP) : Cm → Kind
  | .aS => .mpS p.pa p.adp p.a
  | .aD => .mpD p.adp p.a.alloc p.a.digit
  | .bS => .mpS p.pb p.bdp p.b
  | .bD => .mpD p.bdp p.b.alloc p.b.digit
  | .code => .code

def cmpMag : Contract where
  P := CmP
  X := Unit
  R := Cm
  all := [.aS, .aD, .bS, .bD, .code]
  hall r := by cases r <;> simp
  entry := Fn.CmpMag.entry
  args p := [(10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]
  rets p ra := [(1, ra), (10, BitVec.ofInt 64 (ordCode (compare p.a.mag p.b.mag)))]
  lay := Cm.lay
  kind := Cm.kind
  out p _ := Cm.kind p
  isW _ := false
  ws := []
  Res p := p.a.Valid ∧ p.b.Valid
  Q _ _ := True
  fits p r := by cases r <;> exact Iv.sub_self _
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB
    obtain ⟨qa, qadp, qb, qbdp, a, b⟩ := p
    have hpre : Fn.CmpMag.Pre m qa qadp qb qbdp a b :=
      { ra := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2, va := hres.1, vb := hres.2
        ga := Hdr.geom (hB .aS).2, gb := Hdr.geom (hB .bS).2, code := (hB .code).2.mpCmpMag }
    exact Triple.rmap (fun cf hc => ⟨(), m, hc, trivial, hB, Frm.refl _ _⟩)
      (Fn.CmpMag.correct ra v outp qa qadp qb qbdp a b m hra hpre)

end Tom.Machine.Std
