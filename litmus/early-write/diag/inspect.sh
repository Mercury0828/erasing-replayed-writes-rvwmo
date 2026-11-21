# Isla writes every candidate execution it sends to z3 as
#   isla_candidate_<test>_<uid>_<pid>_<n>.smt2
# in its cache directory (option --cache, default the system temporary directory). The run
# recorded in BF_c10_variants.txt used candidate 10 of EW_BF_r575 (pid 752836); pass the
# corresponding file of your own run.
# usage: bash inspect.sh <candidate_10.smt2> <candidate_9.smt2>
F=${1:?usage: inspect.sh <candidate_10.smt2> <candidate_9.smt2>}
F9=${2:?usage: inspect.sh <candidate_10.smt2> <candidate_9.smt2>}
tail -c 1200 $F; echo
echo "forall: $(grep -c forall $F)  exists: $(grep -c exists $F)"
grep -n "set-option\|check-sat\|set-logic" $F | head
diff <(sed 's/[0-9]\+//g' $F) <(sed 's/[0-9]\+//g' "$F9") | wc -l
