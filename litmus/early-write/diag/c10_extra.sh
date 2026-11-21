# check that the option works when placed where isla puts --extra-smt (after the assertions, before check-sat)
# Isla writes every candidate execution it sends to z3 as
#   isla_candidate_<test>_<uid>_<pid>_<n>.smt2
# in its cache directory (option --cache, default the system temporary directory). The run
# recorded in BF_c10_variants.txt used candidate 10 of EW_BF_r575 (pid 752836); pass the
# corresponding file of your own run.
F=${1:?usage: c10_extra.sh <candidate.smt2>}
G=/tmp/c10_extra.smt2
awk 'BEGIN{d=0} /^\(check-sat\)/ && !d {print "(set-option :smt.macro_finder true)"; d=1} {print}' $F > $G
S=$(date +%s); timeout 600 z3 -T:2400 $G 2>&1 | head -2 | cut -c1-200; echo "$(( $(date +%s)-S ))s"
