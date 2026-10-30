#!/usr/bin/env bash
# Build the default targets (Vsa, VsaIris, TomSpec, Tom). LEAN_NUM_THREADS bounds
# Lake's task pool and each Lean process's threads (default 3).
set -eu
cd "$(dirname "$0")/.."
LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-3} lake build "$@"
