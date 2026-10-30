import Tom.Machine.Api.MpReduce2k

/-! `mp_reduce_2k`'s per-function helper: `n`'s digit block nonempty (the entry's
`Off` positivity, from the contract's `npos`). `mp_cmp_mag`'s result word: `cmp_lt`/`cmp_ge`,
Kit/Run.lean. -/

namespace Tom.Machine.Fn.MpReduce2kG5

open Tom

theorem nalloc_pos {p : Api.MpReduce2k.P} (h : Api.MpReduce2k.Res p) : 0 < p.n.alloc := by
  have hu : 0 < p.n.used := by
    rcases Nat.eq_zero_or_pos p.n.used with h0 | h0
    · have := h.npos; simp [MpInt.mag, h0, natUpTo] at this
    · exact h0
  exact Nat.lt_of_lt_of_le hu h.vn.used_le

end Tom.Machine.Fn.MpReduce2kG5
