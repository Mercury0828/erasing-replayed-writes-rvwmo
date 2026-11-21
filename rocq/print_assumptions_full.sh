#!/usr/bin/env bash
# print_assumptions_full.sh — run after verify.sh (needs the compiled .vo files).
# Prints the COMPLETE, unabridged `Print Assumptions` output for every headline theorem listed in
# verify.sh's HEADLINE table, one theorem at a time, fully qualified (RestartV.<File>.<thm>).
set -u
cd "$(dirname "$0")"
eval "$(sed -n '/^declare -A HEADLINE=(/,/^)/p' verify.sh)"
echo "== coqc --version =="; coqc --version
echo "== theorems: ${#HEADLINE[@]} =="
# Print a header line per theorem, then coqc's full output for that theorem.
for thm in $(printf '%s\n' "${!HEADLINE[@]}" | sort); do
  f="${HEADLINE[$thm]}"
  one="$(mktemp /tmp/pa1_XXXX.v)"
  printf 'Require RestartV.%s.\nPrint Assumptions RestartV.%s.%s.\n' "$f" "$f" "$thm" > "$one"
  echo "---- RestartV.$f.$thm"
  coqc -Q . RestartV "$one" 2>&1
  rm -f "$one"
done
