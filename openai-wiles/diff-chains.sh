#!/usr/bin/env bash
# Diff the right/wrong chains of the openai-wiles formalization.
#
# The two chains differ in exactly ONE mathematical input: the reverse stabilization-trace
# sign. `traces-right.b4m` carries [6]'s value (+1, as arXiv:1303.0588v2 Lemma 3.4's proof
# states it); `traces-wrong.b4m` carries the value OpenAI's withdrawal notice says is correct
# in the manuscript's convention (-1). Every other file in each chain is a copy, duplicated
# only because `import` names a fixed path and a shared file cannot choose its dependency.
#
# Usage:  ./diff-chains.sh          # substantive diffs only (comments stripped)
#         ./diff-chains.sh --full   # everything, comments included
set -uo pipefail
cd "$(dirname "$0")"

FULL=0
[ "${1:-}" = "--full" ] && FULL=1

PAIRS=(
  "legendrian/traces-right.b4m|legendrian/traces-wrong.b4m"
  "legendrian/stabilization-traces-right.md|legendrian/stabilization-traces-wrong.md"
  "construction/marked-class-right.md|construction/marked-class-wrong.md"
  "construction/chern-constancy-right.md|construction/chern-constancy-wrong.md"
  "eigenvalues/independence-right.md|eigenvalues/independence-wrong.md"
  "architecture-right.md|architecture-wrong.md"
)

# strip comment-only lines and blank lines, so the report shows MATH differences
strip() { grep -v '^[[:space:]]*//' "$1" | grep -v '^[[:space:]]*$'; }

rc=0
for pair in "${PAIRS[@]}"; do
  R="${pair%%|*}"; W="${pair##*|}"
  if [ "$FULL" = 1 ]; then
    out=$(diff -u "$R" "$W" || true)
  else
    out=$(diff -u <(strip "$R") <(strip "$W") || true)
  fi
  if [ -z "$out" ]; then
    printf '  IDENTICAL   %s\n' "$R"
  else
    n=$(printf '%s\n' "$out" | grep -c '^[+-][^+-]' || true)
    printf '  DIFFERS(%s)  %s\n' "$n" "$R"
    printf '%s\n' "$out" | sed 's/^/      /'
    rc=1
  fi
done

echo
if [ "$rc" = 0 ]; then
  echo "No substantive differences — which would mean the sign is NOT load-bearing."
  echo "(That was a real bug once: insertedTotal(n) = n hard-coded +1 into a DEFINITION,"
  echo " so swapping the sign module changed nothing and both chains passed.)"
else
  echo "Verify the split is real:"
  echo "  2b4m check openai-wiles/architecture-right.md theWeilPlaneIsSpannedByAlgebraicClasses  # PASSES"
  echo "  2b4m check openai-wiles/architecture-wrong.md theWeilPlaneIsSpannedByAlgebraicClasses  # FAILS at Lemma 3.6"
fi
