import Tom.Machine.Conventions
import Tom.Machine.Fn.MpReduceMainG

set_option autoImplicit false

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}

/-! # `mp_reduce`: the concise specification (SPECS.lean), from `Fn.MpReduceG5.correct` -/

namespace Tom.Machine.Api.MpReduce
open Tom.Reduce
open Tom.Machine.Api.MpSqr (X)

/-- **`mp_reduce(x, n, mu)`** (Barrett): `x ← x mod n`, for `0 ≤ x < radix^(2k)`, `k = n.used`,
`mu = ⌊radix^(2k) / n⌋` (`hmu`, `hx`: for the meaning only). -/
theorem _root_.Specs.mp_reduce {p : P} (cv : Conv m ra p.sp F (hin p)) (sound : Sound (lay p) isW)
    (x : MpOut m p.px p.xdp p.x) (vx : p.x.Valid) (n : MpOwn m p.H p.pn p.ndp p.n)
    (mu : MpOwn m p.H p.pu p.udp p.mu) (fx : Fits p.x) (xz : p.x.sign = Layout.mpZpos)
    (nz : p.n.sign = Layout.mpZpos) (muz : p.mu.sign = Layout.mpZpos) (k1 : 0 < p.n.used)
    (fn : Layout.digitBits * (p.n.used + 1) < 2 ^ 31) (xu : p.x.used ≤ 2 * p.n.used)
    (mul : p.n.used ≤ p.mu.used) (muh : p.mu.used ≤ p.n.used + 2)
    (hmu : p.mu.mag = radix ^ (2 * p.n.used) / p.n.mag) (hx : p.x.mag < radix ^ (2 * p.n.used)) :
    ApiTriple m v outp ra entry p.sp [p.px, p.pn, p.pu] okRet fun o M =>
      OkRes o (fun x' => x'.Valid ∧ x'.val = (p.x.mag % p.n.mag : Nat)) ∧
      HPost (lay p) ws .xD (out p o) (site' p o) (hin p) (hout p o) m M :=
  ApiTriple.of (Reg.call (Fn.MpReduceG5.correct cv.ra_al ⟨cv.stk, vx, xz, n.valid, nz, mu.valid,
    muz, k1, fn, fx, xu, mul, muh, x.pos, n.pos, mu.pos, x.off, n.off, mu.off⟩ sound) cv.heap
    (by mp_regions)) fun _ hq h =>
      let s := ReducePost.spec vx.toShape n.valid mu.valid.toShape k1 hmu hx (hq.post h); ⟨s.1, s.2.2⟩

end Tom.Machine.Api.MpReduce
