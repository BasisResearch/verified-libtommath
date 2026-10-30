import VsaIris.Vsa.Malloc

/-!
# `realloc`'s entry

ship-your-interpreter's `VsaIris/Vsa/MallocConsumer.lean` defines
`reallocEntryBV` from `Vsa.Sim.reallocEntry`, which lives in its WHILE
interpreter's `Vsa/Sim/EnvDefSpec2.lean`; the relocated allocator files import
this module instead (`experiments/port/alloc/modules.json`). The value is this
image's `realloc` wrapper (`nm`: `realloc` at `0x8000823c`).
-/

def Vsa.Sim.reallocEntry : Nat := 0x8000823c

namespace VsaIris.VsaHeap

def reallocEntryBV : BitVec 64 := BitVec.ofNat 64 Vsa.Sim.reallocEntry

end VsaIris.VsaHeap
