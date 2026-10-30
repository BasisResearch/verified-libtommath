import Tom.Machine.Api.Reduce2kSetup
import Tom.Machine.Api.Expt2G

/-!
# `mp_reduce_2k_setup(a, &d)` growing `tmp`: the contract

`Api/Reduce2kSetup.lean` asks for room (`mp_count_bits(a) / MP_DIGIT_BIT + 1 ≤ MP_PREC`, D5: `tmp`'s
`mp_init` block holds `2^p`). Here `mp_2expt(&tmp, p)` grows `tmp` (`Std.mp2exptG`; its `MP_MEM`
frees `tmp` and returns it), then `s_mp_sub(&tmp, a, &tmp)` in `tmp`'s block and `*d = tmp.dp[0]`,
`mp_clear(&tmp)`. Regions, parameters, outcome and post are `Api/Reduce2kSetup.lean`'s; the stack is
the 80-byte frame and `mp_2expt`'s 592 (`mp_init` 560, `mp_clear` 544, `s_mp_sub` 48).
-/

namespace Tom.Machine.Api.Reduce2kSetupGr

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.Reduce2kSetup (R P)

abbrev entry := Reduce2kSetup.entry
abbrev kind := Reduce2kSetup.kind
abbrev out := Reduce2kSetup.out
abbrev isW := Reduce2kSetup.isW
abbrev ws := Reduce2kSetup.ws
abbrev hin := Reduce2kSetup.hin
abbrev args := Reduce2kSetup.args
abbrev rets := Reduce2kSetup.rets
abbrev Q := Reduce2kSetup.Q

/-- The stack depth: the 80-byte frame and `mp_2expt`'s (growing `tmp`). -/
abbrev F : Nat := 80 + Expt2G.F

def lay (p : P) : R → Iv
  | .stk => ⟨p.sp - F, F⟩
  | .aS => ⟨p.pa, 24⟩
  | .aD => ⟨p.adp, 4 * p.a.alloc⟩
  | .dD => ⟨p.pd, 4 * p.d.alloc⟩
  | .code => textIv

/-- What `mp_reduce_2k_setup(a, &d)` needs: `Reduce2kSetup.Res` without the room. -/
structure Res (p : P) : Prop where
  stk : StkRes p.sp F
  va : p.a.Valid
  /-- `mp_count_bits`'s `int` result. -/
  bits : Layout.digitBits * p.a.used < 2 ^ 31
  apos : 0 < p.a.alloc

/-- **`mp_reduce_2k_setup(a, &d)` on the machine, `tmp` growing.** -/
def Statement : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws .dD (out p x) (lay p .dD) (hin p) (hin p) m M)

end Tom.Machine.Api.Reduce2kSetupGr
