#!/bin/bash
# z3_variants.sh - re-solve the one BF candidate z3 left `unknown` under other z3 settings (inside chroot)
# Isla writes every candidate execution it sends to z3 as
#   isla_candidate_<test>_<uid>_<pid>_<n>.smt2
# in its cache directory (option --cache, default the system temporary directory). The run
# recorded in BF_c10_variants.txt used candidate 10 of EW_BF_r575 (pid 752836); pass the
# corresponding file of your own run.
F=${1:?usage: z3_variants.sh <candidate.smt2>}
run () { S=$(date +%s); R=$(timeout 1800 z3 "$@" $F 2>&1 | head -1); echo "$* -> $R $(( $(date +%s)-S ))s"; }
run smt.random_seed=1 &
run smt.random_seed=2 &
run smt.random_seed=3 &
run smt.mbqi.max_iterations=100000 &
run smt.relevancy=0 &
run smt.ematching=false &
run smt.macro_finder=true &
run model.compact=false &
wait
