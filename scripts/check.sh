#!/usr/bin/env bash
# Build and check the proofs.   scripts/check.sh [--no-build]
#  (1) the proof image c/tommath-arith.elf is RV64I only and a fresh build of it is byte-identical;
#  (2) no sorry, axiom, native_decide, bv_decide, ofReduceBool or trustCompiler outside comments;
#  (3) every generated file is what its generator writes (scripts/regen.sh, in a scratch copy);
#  (4) lake build of the default targets (scripts/build.sh);
#  (5) #print axioms of scripts/axioms.lean and of every theorem of SPECS.lean is within
#      {propext, Classical.choice, Quot.sound};
#  (6) every function of the image has a proved contract (scripts/coverage.py).
set -u
cd "$(dirname "$0")/.."
fail() { echo "check: FAIL: $*"; exit 1; }
BUILD=1; [ "${1:-}" = --no-build ] && BUILD=0
w=$(mktemp -d); trap 'rm -rf "$w"' EXIT

scripts/check_isa.sh c/tommath-arith.elf || fail "instructions outside RV64I"
make -s -C c build/MP_32BIT/arith.elf >/dev/null 2>&1 || fail "build of the proof image"
cmp -s c/build/MP_32BIT/arith.elf c/tommath-arith.elf || fail "c/tommath-arith.elf differs from a fresh build"
echo "check: (1) image OK"

bad=$(find Tom Vsa VsaIris scripts SPECS.lean -name '*.lean' -print0 | xargs -0 python3 -I -c '
import re, sys
toks = re.compile(r"\b(sorry|native_decide|bv_decide|ofReduceBool|trustCompiler)\b|^\s*(private\s+)?axiom\b")
for p in sys.argv[1:]:
    s = open(p, encoding="utf-8").read()
    s = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), s, flags=re.S)
    for i, line in enumerate(s.splitlines(), 1):
        line = re.sub(r"--.*", "", line)
        if toks.search(line): print(f"{p}:{i}: {line.strip()}")
')
[ -z "$bad" ] || { echo "$bad"; fail "forbidden token"; }
echo "check: (2) tokens OK"

git ls-files -z | (tar --null -cf - -T -) | (mkdir -p "$w/r" && cd "$w/r" && tar xf -)
cp -a c/tommath-arith.elf "$w/r/c/"
(cd "$w/r" && git init -q && git add -A && git -c user.email=x -c user.name=x commit -qm base) >/dev/null
bash "$w/r/scripts/regen.sh" || fail "a generator failed"
changed=$(cd "$w/r" && git status --short)
[ -z "$changed" ] || { echo "$changed" | head; fail "generated files differ from what their generators write"; }
echo "check: (3) generated files OK"

if [ $BUILD = 1 ]; then scripts/build.sh >/dev/null || fail "lake build"; echo "check: (4) build OK"; fi

STD='\[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$'
{ cat SPECS.lean; echo; grep -oE '^theorem (_root_\.)?Specs\.[A-Za-z0-9_]+' SPECS.lean |
    sed -E 's/^theorem (_root_\.)?/#print axioms /'; } > "$w/specs_axioms.lean"
for f in scripts/axioms.lean "$w/specs_axioms.lean"; do
  out=$(lake env lean "$f" 2>&1)
  n=$(echo "$out" | grep -c "depends on axioms")
  [ "$n" -gt 0 ] && ! echo "$out" | grep -q "error" || { echo "$out" | head; fail "$f does not elaborate"; }
  if echo "$out" | grep "depends on axioms" | grep -vqE "$STD"; then
    echo "$out" | grep "depends on axioms" | grep -vE "$STD"; fail "nonstandard axioms in $f"
  fi
  echo "check: (5) $(basename "$f"): $n theorems, standard axioms only"
done

python3 scripts/coverage.py | head -1 | grep -q "^100 of 100 functions proved" || fail "coverage"
echo "check: (6) coverage: $(python3 scripts/coverage.py | head -1)"
echo "check: all OK"
