#!/bin/bash
# run_baseline_all.sh - re-measures every PRE-EXISTING repo litmus file on this host.
# Group 1: litmus/rvwmo-suite/*.toml            (36 files, all tests)
# Group 2: litmus/trap-scoping/*.toml MINUS the 5 riscv64_g2_*.toml CONFIG files (13 tests)
set -u
A=${ARTIFACT_ROOT:?export ARTIFACT_ROOT=<path of this artifact>}
R="$A/litmus/frozen-suite/run_repo_baseline.sh"
OUT=${OUT_DIR:-.}
rm -f "$OUT/baseline_rvwmo.txt" "$OUT/baseline_trap.txt"

ls "$A"/litmus/trap-scoping/*.toml \
  | grep -v '/riscv64_g2_' \
  | xargs -n 1 -P 5 -I{} bash "$R" trap {}
echo TRAP_GROUP_DONE

ls "$A"/litmus/rvwmo-suite/*.toml \
  | xargs -n 1 -P 8 -I{} bash "$R" rvwmo {}
echo RVWMO_GROUP_DONE
