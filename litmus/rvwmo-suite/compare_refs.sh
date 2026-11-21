#!/bin/bash
# compare_refs.sh - compare Isla verdicts of the RVWMO calibration suite with the herd reference results.
# usage: bash compare_refs.sh [results-file]
#   results-file: one line per test, "<test><TAB><verbatim isla-axiomatic summary line>", as written by
#   `litmus/frozen-suite/run_repo_baseline.sh rvwmo <test>.toml` (baseline_rvwmo.txt); default: the
#   recorded results measured_isla.txt (copied from litmus/frozen-suite/RESULTS.md, Section 3.2).
# A herd observation "Never" means forbidden; "Sometimes" or "Always" means allowed.
D=$(cd "$(dirname "$0")" && pwd)
RES=${1:-$D/measured_isla.txt}
awk -F'\t' '
  FNR == NR { if ($0 ~ /^Observation /) { split($0, w, " "); ref[w[2]] = (w[3] == "Never") ? "forbidden" : "allowed" } next }
  { line = (NF > 1) ? $2 : $1; split(line, w, " "); t = w[1]; v = w[2]
    if (!(t in ref)) { printf "%-24s no reference\n", t; next }
    n++; ok = (v == ref[t]); a += ok
    printf "%-24s expected %-9s measured %-9s %s\n", t, ref[t], v, ok ? "agrees" : "DISAGREES" }
  END { printf "%d of %d agree\n", a, n }
' "$D/refs_herd.txt" "$RES"
