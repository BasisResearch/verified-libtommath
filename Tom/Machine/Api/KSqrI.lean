import Tom.Machine.Api.KSqr
import Tom.Machine.Api.MpAddH
import Tom.Machine.Api.MpLshdH

/-!
# What karatsuba's generated assembly proves

`s_mp_karatsuba_sqr`'s contract (`Api.KSqr.Statement`, with the induction hypothesis in its
residue) from the growing `mp_add` and `mp_lshd` (named premises, `Api/MpAddH.lean`,
`Api/MpLshdH.lean`).
-/

namespace Tom.Machine.Api.KSqrI

def Statement : Prop := MpAddH.Statement → MpLshdH.Statement → KSqr.Statement

end Tom.Machine.Api.KSqrI

namespace Tom.Machine.Api.KSqrAI

def Statement : Prop := MpAddH.Statement → MpLshdH.Statement → KSqr.StatementA

end Tom.Machine.Api.KSqrAI
