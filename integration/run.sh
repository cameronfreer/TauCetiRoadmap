#!/bin/bash
# Supplier-substitution integration check for the five InfinitaryLogic successor roadmaps.
# Usage, from the repository root on this branch:
#   lake build Completed.InfinitaryLogic.Suggested   # once: the parent prototype's olean
#   integration/run.sh [S]
# S defaults to TauCetiRoadmap/ (holding <Dir>/Suggested.lean). Outputs go to integration/_build/.
set -u
AU="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$AU/.." && pwd)"
# LAKE_ROOT: a checkout whose .lake holds the built dependencies and the parent prototype's olean
# (defaults to this one).
LAKE_ROOT="${LAKE_ROOT:-$REPO}"
S="${1:-$REPO/TauCetiRoadmap}"
B="$AU/_build"
python3 -I "$AU/substitute.py" "$S" "$B" || exit 1
mkdir -p "$B/olean/TauCetiRoadmap" "$B/src/TauCetiRoadmap/Integration" "$B/diffs" "$B/logs"
cp "$AU/Integration.lean" "$AU/Adapters.lean" "$B/src/TauCetiRoadmap/Integration/"
# The parent prototype is `Completed.InfinitaryLogic.Suggested`; Lean resolves `Completed.*` in the
# lake build directory, since our olean root holds no `Completed/` dir.
for d in CountableStructureSpaces CountableModelCounting HanfNumbers; do
  diff -u "$B/orig/$d.lean" "$B/src/TauCetiRoadmap/$d/Suggested.lean" > "$B/diffs/$d.diff"
done
fail=0
for m in InfinitaryModelExistence BorelEquivalenceRelations CountableStructureSpaces \
         CountableModelCounting HanfNumbers Adapters Integration; do
  "$AU/compile1.sh" "$m" || fail=1
done
[ $fail = 0 ] && echo "ALL COMPILED" || echo "SOME FILE FAILED (see integration/_build/logs/)"
exit $fail
