#!/bin/bash
# run_repo_baseline.sh - re-measures the PRE-EXISTING repo litmus files on THIS host, so that the
# repo-wide "runnable test" count in RESULTS.md is measured rather than cited.
#
# Each pre-existing test is run with the recipe it was developed with, not with a
# single uniform recipe: these files were developed against different configs and cats, and running
# a file under a config it was never designed for produces a meaningless `error` (in an earlier
# measurement, not part of this release, the stock config turned an `allowed (7 of 7) 446ms` into
# an `error (0 of 1) 99004ms`).
#
#   litmus/rvwmo-suite/*        rv64d.ir      configs/riscv64_g2.toml              riscv.cat
#                               (litmus/rvwmo-suite/REFERENCE.md)
#   S1_mp, S1_control_fence     rv64d.ir      configs/riscv64_g2.toml              riscv_s1_nodrain.cat
#   S1v2_*                      rv64d_g58.ir  riscv64_g2_trap_umode_ipo.toml       riscv_s1v2_nodrain.cat
#                               (litmus/trap-scoping/DRAIN_RESULTS.md)
#   trap_ecall*, faultA         rv64d.ir      riscv64_g2_trap.toml                 riscv.cat
#   faultB1, diag_umode_exit    rv64d.ir      riscv64_g2_trap_umode.toml           riscv.cat
#   faultB1_defaults,           rv64d.ir      riscv64_g2_trap_umode_defaults.toml  riscv.cat
#   faultB2_replay,
#   diag_umode_exit_fixed
#
# -s 300 throughout (this host is ~5x slower than the one the originals were measured on).
set -u
ISLA=${ISLA:-${ISLA_ROOT}/target/release/isla-axiomatic}
REPO=${ARTIFACT_ROOT:?export ARTIFACT_ROOT=<path of this artifact>}
TS=$REPO/litmus/trap-scoping
IR_OLD=${ISLA_IR_OLD:-${ISLA_SNAPSHOTS}/rv64d.ir}     # patch 1 only (model/REBUILD.md)
IR_G58=${ISLA_IR:-${ISLA_SNAPSHOTS}/rv64d_g58.ir}     # all three patches (model/REBUILD.md)
OUT=${OUT_DIR:-.}
CAT_STOCK=${ISLA_ROOT}/web/client/dist/riscv.cat
CFG_STOCK=${ISLA_ROOT}/configs/riscv64_g2.toml

run_one () {   # $1 outfile  $2 IR  $3 config  $4 cat  $5 test
  B=$(basename "$5" .toml)
  LOG=$(mktemp)
  timeout 2400 "$ISLA" -A "$2" -C "$3" --footprint-config "$3" -m "$4" -s 300 -T 4 "$5" > "$LOG" 2>&1
  RC=$?
  LINE=$(grep -aE "^[A-Za-z0-9_.+-]+ (allowed|forbidden|error|timeout) " "$LOG" | tail -1 \
         | sed -e 's/\x1b\[[0-9;]*m//g' -e 's/ \.\{2,\}.*$//' -e 's/[[:space:]]*$//')
  if [ -z "$LINE" ]; then
    LINE="NO-SUMMARY-LINE rc=$RC last: $(grep -av 'No primop' "$LOG" | tail -2 | tr '\n' ' ')"
  fi
  printf '%s\t%s\n' "$B" "$LINE" >> "$1"
  rm -f "$LOG"
}

case "$1" in
  # NOTE (measured 2026-07-30): the rvwmo suite is run here on rv64d_g58.ir, NOT on the rv64d.ir
  # used by an earlier run. On rv64d.ir all 36 now come back
  # `error (0 of 1)` in 5-19s with
  #     error: Symbolic (bit)vector length in subrange_internal
  #     Backtrace: zisla_footprint / zisla_footprint_no_init / zexecute / zvmem_write
  # i.e. the split_misaligned symbolic-width crash that model/split_misaligned_footprint_fix.patch
  # exists to fix. rv64d_g58.ir carries that fix and returns verdicts. See RESULTS.md sec 4.
  rvwmo)
    run_one "$OUT/baseline_rvwmo.txt" "$IR_G58" "$CFG_STOCK" "$CAT_STOCK" "$2" ;;
  rvwmo_oldir)
    run_one "$OUT/baseline_rvwmo_OLD_IR.txt" "$IR_OLD" "$CFG_STOCK" "$CAT_STOCK" "$2" ;;
  trap)
    B=$(basename "$2" .toml)
    case "$B" in
      S1_mp|S1_control_fence)
        run_one "$OUT/baseline_trap.txt" "$IR_OLD" "$CFG_STOCK" \
                "$REPO/litmus/cat/riscv_s1_nodrain.cat" "$2" ;;
      S1v2_*)
        run_one "$OUT/baseline_trap.txt" "$IR_G58" "$TS/riscv64_g2_trap_umode_ipo.toml" \
                "$REPO/litmus/cat/riscv_s1v2_nodrain.cat" "$2" ;;
      trap_ecall|trap_ecall_working|trap_store_faultA)
        run_one "$OUT/baseline_trap.txt" "$IR_OLD" "$TS/riscv64_g2_trap.toml" "$CAT_STOCK" "$2" ;;
      trap_store_faultB1|diag_umode_exit)
        run_one "$OUT/baseline_trap.txt" "$IR_OLD" "$TS/riscv64_g2_trap_umode.toml" "$CAT_STOCK" "$2" ;;
      trap_store_faultB1_defaults|trap_store_faultB2_replay|diag_umode_exit_fixed)
        run_one "$OUT/baseline_trap.txt" "$IR_OLD" "$TS/riscv64_g2_trap_umode_defaults.toml" \
                "$CAT_STOCK" "$2" ;;
      *) printf '%s\tSKIPPED-NOT-A-TEST\n' "$B" >> "$OUT/baseline_trap.txt" ;;
    esac ;;
esac
