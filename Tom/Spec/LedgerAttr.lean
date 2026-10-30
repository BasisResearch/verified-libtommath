import Lean

/-! `ledger_nf`: the Ledger's unit normal form (`Tom/Spec/Ledger.lean`): the machine's literal
`268435456` (`MP_MASK + 1`) read as `radix`. Its own file because an attribute is usable only
in the modules after the one that registers it. -/

register_simp_attr ledger_nf
