#!/bin/bash
# Fail if an ELF contains an instruction outside RV64I (+ Zicsr/fence): no M,
# A, F, D, Q or C.
set -u
TC=$(ls -d "$HOME"/toolchains/xpack-riscv-none-elf-gcc-15.2.0-*/bin | head -1)
rc=0
for elf in "$@"; do
  bad=$("$TC/riscv-none-elf-objdump" -d -M no-aliases "$elf" | awk -F'\t' 'NF>=3{print $2"\t"$3}' |
    awk -F'\t' '{w=$1; gsub(/ /,"",w); if (length(w)!=8) {print "C:" $0; next}
      op=$2; sub(/ .*/,"",op);
      if (op ~ /^(mul|mulh|mulhsu|mulhu|div|divu|rem|remu|mulw|divw|divuw|remw|remuw)$/ ||
          op ~ /^(lr|sc|amo)/ || op ~ /^f/ && op != "fence" && op != "fence.i" && op != "fence.tso") print "X:" $0}' | head -5)
  if [ -n "$bad" ]; then echo "check_isa: $elf:"; echo "$bad"; rc=1; fi
done
exit $rc
