import Tom.Machine.Kit.Frame
import Tom.Machine.Code

/-!
# Destination kernels: one assembly for distinct and aliased operands

`s_mp_add(a, b, c)` and `s_mp_sub(a, b, c)` write only their stack frame and
`c` (its struct, then its digits in place, then `mp_clamp` on its struct).
libtommath calls them with `c` distinct from both operands and with `c = a`
or `c = b` (`s_mp_sub(x, n, x)`, `s_mp_add(a, &q, a)`, …). The machine code
is the same; only what the loops read differs. The assembly is proved once
over the **kernel** regions `K` (the stack frame, `c`'s struct and digits,
the code of the routine, `memset` and `mp_clamp`), and each operand is a
`Src`:

* `Src.own`: its own `mp_int`, which stays in memory while only the
  kernel's written regions change (the caller proves this in its own names:
  `Frm.push` the kernel frame, then `Frm.keep`), with its struct off the
  stack frame and off `c`'s struct;
* `Src.self`: `c` itself. Its digit `j` is read at a join point whose digit
  array holds `ovl g c.digit i` (`Kit/Frame.lean`): the loops read index `i`
  before they write it, so for `j ≥ i` the array still holds `c.digit j`.

`Src.read` gives the loops' reads (`SrcAt`: the digit pointer and the digits
from the loop index on) in both cases; `Src.mp1` the operand before any
write to `c`; `Src.off_fr`/`Src.off_used` the two disjointness facts the
prologue segments need.
-/

namespace Tom.Machine.Dst

open Vsa.Sim Tom.Machine.Code

/-- The kernel regions. -/
inductive K | fr | cS | cD | code | ms | cl
  deriving DecidableEq

def isW : K → Bool
  | .fr | .cS | .cD => true
  | _ => false

/-- The placement: a stack frame of `F` bytes below `sp`, `c`, the routine's code. -/
def lay (F sp pc cdp : Nat) (c : MpInt) (code : Iv) : K → Iv
  | .fr => ⟨sp - F, F⟩
  | .cS => ⟨pc, 24⟩
  | .cD => ⟨cdp, 4 * c.alloc⟩
  | .code => code
  | .ms => ⟨memsetBase, 220⟩
  | .cl => ⟨mpClampBase, 64⟩

/-- The written names. -/
def ws : List K := [.fr, .cS, .cD]

theorem all (k : K) : k ∈ [K.fr, .cS, .cD, .code, .ms, .cl] := by cases k <;> simp

/-- An operand `x` (struct `p`, digits `dp`) of a routine whose destination is
`c` (struct `pc`, digits `cdp`): its own `mp_int`, or `c`. -/
inductive Src (ρ : K → Iv) (m : Mem) (pc cdp : Nat) (c : MpInt) : Nat → Nat → MpInt → Prop
  | own {p dp : Nat} {x : MpInt} (keep : ∀ M, Frm ρ ws m M → MpAt M p dp x)
      (fr : Iv.Disj ⟨p, 24⟩ (ρ .fr)) (cs : Iv.Disj ⟨p, 24⟩ (ρ .cS)) : Src ρ m pc cdp c p dp x
  | self : Src ρ m pc cdp c pc cdp c

/-- What a loop reads of an operand at index `i`: its digit pointer, and its
digits from `i` on. -/
structure SrcAt (M : Mem) (p dp : Nat) (x : MpInt) (i : Nat) : Prop where
  dpv : bytesT8 M (p + 16) = BitVec.ofNat 64 dp
  dig : ∀ j, i ≤ j → j < x.alloc → bytesT4 M (dp + 4 * j) = BitVec.ofNat 32 (x.digit j)

theorem SrcAt.of_mp {M : Mem} {p dp : Nat} {x : MpInt} (h : MpAt M p dp x) (i : Nat) : SrcAt M p dp x i :=
  { dpv := by simpa [Layout.offDp] using h.dpv
    dig := fun j _ hj => by simpa [Layout.sizeofDigit] using h.digits j hj }

section
variable {F sp pc cdp : Nat} {c : MpInt} {code : Iv} {m : Mem} {p dp : Nat} {x : MpInt}

local notation "ρ" => lay F sp pc cdp c code

/-- The operand before any write to `c` (only the stack frame changed). -/
theorem Src.mp1 (h : Src ρ m pc cdp c p dp x) (hS : Sound ρ isW) (hc : MpAt m pc cdp c) {M : Mem}
    (hF : Frm ρ [.fr] m M) : MpAt M p dp x := by
  cases h with
  | own keep _ _ => exact keep M hF.mono
  | self => exact hF.keep hS (MpAt.reads (rs := K.cS) (rd := K.cD) (Iv.sub_self _) (Iv.sub_self _)) hc

/-- **The loops' reads**, at a join point after the prologue `m2` (which
changed only the frame and `c`'s struct, and left `c`'s digit pointer):
the array holds the results below `i` and `c`'s old digits from `i` on. -/
theorem Src.read (h : Src ρ m pc cdp c p dp x) (hS : Sound ρ isW) {m2 M : Mem} {g : Nat → Nat} {i : Nat}
    (hF2 : Frm ρ [.fr, .cS] m m2) (hdp : bytesT8 m2 (pc + 16) = BitVec.ofNat 64 cdp)
    (hI : ArrFrm ρ .cD m2 M cdp c.alloc (ovl g c.digit i)) : SrcAt M p dp x i := by
  cases h with
  | own keep _ _ => exact SrcAt.of_mp (keep M (hF2.trans hI.fr).mono) i
  | self =>
    exact { dpv := hI.fr.keep hS (Reads.w8 (r := K.cS) ⟨by simp [lay], by simp only [lay]; omega⟩) hdp
            dig := fun j hj hjn => by
              have := hI.arr j hjn
              simp only [ovl, if_neg (show ¬ j < i by omega)] at this
              exact this }

/-- The operand's struct is off the stack frame. -/
theorem Src.off_fr (h : Src ρ m pc cdp c p dp x) (hS : Sound ρ isW) : Disj p 24 (sp - F) F := by
  cases h with
  | own _ hfr _ => exact hfr
  | self => exact hS.disj (r := K.cS) (s := K.fr)

/-- `c->used` is off the operand's digit pointer. -/
theorem Src.off_used (h : Src ρ m pc cdp c p dp x) : pc + 4 ≤ p + 16 ∨ p + 24 ≤ pc := by
  cases h with
  | own _ _ hcs => simp only [Iv.Disj, Disj, lay] at hcs; omega
  | self => omega

end

end Tom.Machine.Dst
