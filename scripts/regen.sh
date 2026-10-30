#!/usr/bin/env bash
# Regenerate every generated file in place from its sources: Tom/Layout.lean (gen_layout.sh),
# Tom/Machine/{Code,Img}.lean (gen_code.py), Tom/Machine/Seg/*.lean (gen_segs.py, experiments/segs/
# modules.tsv), the segment lemmas (gen_rows.py, experiments/segs/*.rows.json), the function
# assemblies (gen_asm.py, experiments/asm/*.asm.json), the allocator's step tables
# (gen_alloc_steps.py) and SPECS.lean (gen_specs.py).
set -u
cd "$(dirname "$0")/.."
fail=0
scripts/gen_layout.sh >/dev/null || { echo "FAIL gen_layout.sh"; fail=1; }
python3 scripts/gen_code.py >/dev/null || { echo "FAIL gen_code.py"; fail=1; }
while IFS=$'\t' read -r src mod; do
  python3 scripts/gen_segs.py "$src" "$mod" >/dev/null || { echo "FAIL gen_segs.py $src"; fail=1; }
done < experiments/segs/modules.tsv
for f in experiments/segs/*.rows.json; do
  python3 scripts/gen_rows.py "$f" >/dev/null || { echo "FAIL gen_rows.py $f"; fail=1; }
done
for f in experiments/asm/*.asm.json; do
  grep -q '"abstract": true' "$f" && continue
  python3 scripts/gen_asm.py "$f" >/dev/null 2>&1 || { echo "FAIL gen_asm.py $f"; fail=1; }
done
python3 scripts/gen_alloc_steps.py >/dev/null || { echo "FAIL gen_alloc_steps.py"; fail=1; }
python3 scripts/gen_specs.py >/dev/null || { echo "FAIL gen_specs.py"; fail=1; }
exit $fail
