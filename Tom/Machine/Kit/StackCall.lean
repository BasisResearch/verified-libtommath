import Tom.Machine.Api.Two
import Tom.Machine.Kit.Refine
import Tom.Spec.Signed

/-!
# A call on a stack copy of the first operand

`mp_add_d(a, b, c)` and `mp_sub_d(a, b, c)` call each other with a copy
`a_` of `a` at `sp - 40` in their 64-byte frame. The callee's regions (its
stack of depth 64 below the frame, `a_`, `a`'s digits, `c`) sit in the
caller's by `calleeR` (`a_` in the caller's stack, `callee_sub`); the
callee's layout is sound by refinement (`callee_sound`: its stack and `a_`
are apart). After the call, the caller reads its own frame (saved registers, spill)
through the callee's frame clause in the pieces (`K`, `klay`).
-/

namespace Tom.Machine.Api.Two

open Vsa.Sim Tom.Machine Tom.Machine.Code

/-- The callee's names in the caller's. -/
def calleeR : R → R
  | .aS => .stk
  | r => r

theorem callee_sub {F sp pa adp pc cdp : Nat} {a c : MpInt} (hF : 128 ≤ F) (hsp : F ≤ sp) :
    ∀ k, (lay 64 (sp - 64) (sp - 40) adp pc cdp (a.withSign 0) c k).Sub
      (lay F sp pa adp pc cdp a c (calleeR k)) := by
  intro k; cases k <;> (simp only [Iv.Sub, lay, calleeR, MpInt.withSign]; omega)

/-- **The callee's layout is sound.** -/
theorem callee_sound {F sp pa adp pc cdp : Nat} {a c : MpInt} (hS : Sound (lay F sp pa adp pc cdp a c) isW)
    (hF : 128 ≤ F) (hsp : F ≤ sp) :
    Sound (lay 64 (sp - 64) (sp - 40) adp pc cdp (a.withSign 0) c) isW := by
  refine Sound.refine calleeR hS (callee_sub hF hsp) ?_
  intro k l h hs'
  cases k <;> cases l <;> first
    | exact absurd h (by decide)
    | exact absurd hs' (by decide)
    | (simp only [Iv.Disj, Disj, lay]; omega)

/-! ## The caller's frame in pieces

The caller's own names for its stack: the callee's stack and below (`lo`,
`[sp - F, sp - 64)`), the spill slot (`sl`, `[sp - 64, sp - 56)`), the slot of
the copy (`cp`, `[sp - 56, sp - 16)`), the saved registers (`sv`,
`[sp - 16, sp)`). `ksound`: this finer layout is sound when `Two`'s is
(`Sound.refine`); the callee's regions sit in it by `calleeK`, so the
callee's layout is sound by plain renaming (`callee_soundK`) and its frame
is one in the pieces (`Frm.push calleeK`). -/

inductive K | lo | sl | cp | sv | aS | aD | bS | bD | code
  deriving DecidableEq

def kW : K → Bool
  | .aS | .aD | .code => false
  | _ => true

def klay (F sp pa adp pc cdp : Nat) (a c : MpInt) : K → Iv
  | .lo => ⟨sp - F, F - 64⟩
  | .sl => ⟨sp - 64, 8⟩
  | .cp => ⟨sp - 56, 40⟩
  | .sv => ⟨sp - 16, 16⟩
  | .aS => ⟨pa, 24⟩
  | .aD => ⟨adp, 4 * a.alloc⟩
  | .bS => ⟨pc, 24⟩
  | .bD => ⟨cdp, 4 * c.alloc⟩
  | .code => textIv

/-- The pieces in `Two`'s names. -/
def kg : K → R
  | .lo | .sl | .cp | .sv => .stk
  | .aS => .aS | .aD => .aD | .bS => .bS | .bD => .bD | .code => .code

theorem kall (k : K) : k ∈ [K.lo, .sl, .cp, .sv, .aS, .aD, .bS, .bD, .code] := by cases k <;> simp

theorem ksub {F sp pa adp pc cdp : Nat} {a c : MpInt} (hF : 64 ≤ F) (hsp : F ≤ sp) :
    ∀ k, (klay F sp pa adp pc cdp a c k).Sub (lay F sp pa adp pc cdp a c (kg k)) := by
  intro k; cases k <;> (simp only [Iv.Sub, klay, lay, kg]; omega)

theorem ksound {F sp pa adp pc cdp : Nat} {a c : MpInt} (hS : Sound (lay F sp pa adp pc cdp a c) isW)
    (hF : 64 ≤ F) (hsp : F ≤ sp) : Sound (klay F sp pa adp pc cdp a c) kW := by
  refine Sound.refine kg hS (ksub hF hsp) ?_
  intro k l h hs'
  cases k <;> cases l <;> first
    | exact absurd h (by decide)
    | exact absurd hs' (by decide)
    | (simp only [Iv.Disj, Disj, klay]; omega)

/-- The callee's names in the caller's pieces. -/
def calleeK : R → K
  | .stk => .lo | .aS => .cp | .aD => .aD | .bS => .bS | .bD => .bD | .code => .code

theorem callee_subK {F sp pa adp pc cdp : Nat} {a c : MpInt} (hF : 128 ≤ F) (hsp : F ≤ sp) :
    ∀ k, (lay 64 (sp - 64) (sp - 40) adp pc cdp (a.withSign 0) c k).Sub
      (klay F sp pa adp pc cdp a c (calleeK k)) := by
  intro k; cases k <;> (simp only [Iv.Sub, lay, klay, calleeK, MpInt.withSign]; omega)

/-- **The callee's layout is sound** (by renaming into the pieces). -/
theorem callee_soundK {F sp pa adp pc cdp : Nat} {a c : MpInt} (hK : Sound (klay F sp pa adp pc cdp a c) kW)
    (hF : 128 ≤ F) (hsp : F ≤ sp) : Sound (lay 64 (sp - 64) (sp - 40) adp pc cdp (a.withSign 0) c) isW :=
  hK.pull calleeK _ all (callee_subK hF hsp)

/-- `bytesT8` past a write log that misses it. -/
theorem bytesT8_log_out (M : Mem) (log : List WEntry) (x : Nat) (h : OutLRange log x 8) :
    bytesT8 (writeLog M log) x = bytesT8 M x :=
  bytesT8_congr fun y h1 h2 => writeLog_out M log y (outL_of_range h h1 h2)

end Tom.Machine.Api.Two
