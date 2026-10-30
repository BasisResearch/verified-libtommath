# verified-libtommath

Lean 4 proofs that [libtommath](https://github.com/libtom/libtommath) v1.3.0, compiled for bare-metal
RV64I (`c/tommath-arith.elf`: xPack GCC 15.2.0, `-O2`, 28-bit digits), is correct: all 100 functions of
the image (76 libtommath functions and the 24 newlib/libgcc routines they call: the allocator,
`memset`/`memcpy`/`memmove`, 64-bit multiply and divide) meet specifications over Lean's `Int`/`Nat`,
as total-correctness triples on the Sail RISC-V model. `SPECS.lean` collects every function's
specification for review. Licensed under Apache-2.0 (`LICENSE`); third-party material and its
licenses: `NOTICE`, `licenses/`.

Toolchain: Lean 4.34.0 via elan (`lean-toolchain`); to rebuild the image and the generated files,
xPack `riscv-none-elf-gcc` 15.2.0 under `~/toolchains`.

    scripts/build.sh    # lake build of Vsa, VsaIris, TomSpec, Tom (about 55 min cold with LEAN_NUM_THREADS=3, under 12 GB)
    scripts/check.sh    # image, forbidden tokens, generated files, build, axioms, coverage
