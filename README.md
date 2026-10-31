# verified-libtommath

Lean 4 proofs that [libtommath](https://github.com/libtom/libtommath) v1.3.0, compiled for bare-metal
RV64I (`c/tommath-arith.elf`: xPack GCC 15.2.0, `-O2`, 28-bit digits), is correct: all 100 functions of
the image (76 libtommath functions and the 24 newlib/libgcc routines they call: the allocator,
`memset`/`memcpy`/`memmove`, 64-bit multiply and divide) meet specifications over Lean's `Int`/`Nat`,
as total-correctness triples on the Sail RISC-V model. `SPECS.lean` states the main contract of each
public function (declared in `tommath.h`) over `Int`/`Nat` in the conventions of
`Tom/Machine/Conventions.lean`, each proved from the machine contract; `SPECS_UNFOLDED.lean` states the
same contracts unfolded down to the triple; `SPECS_INTERNAL.lean` the
other forms, the `s_mp_*` helpers and the newlib/libgcc routines. Licensed under Apache-2.0 (`LICENSE`); third-party material and its
licenses: `NOTICE`, `licenses/`.

Toolchain: Lean 4.34.0 via elan (`lean-toolchain`); to rebuild the image and the generated files,
xPack `riscv-none-elf-gcc` 15.2.0 under `~/toolchains`.

    scripts/build.sh    # lake build of Vsa, VsaIris, TomSpec, Tom (about 55 min cold with LEAN_NUM_THREADS=3, under 12 GB)
    scripts/check.sh    # image, forbidden tokens, generated files, build, axioms, coverage

## Bugs found in libtommath v1.3.0

1. `mp_exptmod(2, 30, 3·2^28)` returns 0: `mp_reduce_2k_setup` loses `2^p − n` when it equals the radix (excluded by the spec's exact-`2^k` premise, `Exptmod.Lossy2k`).
2. `mp_invmod(-3, 7)` returns −2, not an inverse: `s_mp_invmod_fast` copies `a`'s sign (stated exactly, `InvmodPost.spec_neg_odd`).
3. `mp_exptmod(G, 0, 1)` returns 1, not 0 (the specs assume `P > 1`).
4. `mp_read_radix` reads one byte past `s_mp_rmap_reverse` for the input byte 0x80 (modelled, `Radix.charVal`).
5. Internal only: `s_mp_invmod_slow` loops forever for odd `b` with `a ≡ 0 mod b`; `s_mp_mul_high_digs` reads `b->dp` out of bounds when `a->used > digs + 1`; `mp_dr_reduce` with `dp[0] = 0` stores a non-digit carry (excluded by the internal preconditions).
6. `mp_gcd` leaks a digit block when the second `mp_init_copy` fails: the cleanup labels are swapped (stated exactly).
7. `s_mp_balance_mul` leaves stale digits above `used` in its slice (benign: `mp_mul` is proved for such operands).

Reproducers (1, 2, 3, 5) in `tests/bugs/`, against the vendored sources:
`for f in tests/bugs/*.c; do gcc -w -DMP_32BIT -Ivendor/libtommath -o /tmp/t "$f" vendor/libtommath/bn_*.c && /tmp/t; done`
