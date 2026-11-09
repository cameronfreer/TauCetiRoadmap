#!/bin/bash
# Supplier-substitution integration check for the InfinitaryLogic successor roadmaps.
# Usage, from the repository root on this branch, after building the Tau Ceti modules the drafts
# import (see README.md):
#   integration/run.sh [S]
# S defaults to TauCetiRoadmap/ (holding <Dir>/Suggested.lean). Outputs go to integration/_build/.
# LAKE_ROOT=<checkout> reuses another checkout's built .lake (same lake-manifest.json).
set -u
AU="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$AU/.." && pwd)"
LAKE_ROOT="${LAKE_ROOT:-$REPO}"
S="${1:-$REPO/TauCetiRoadmap}"
B="$AU/_build"
rm -rf "$B"
python3 -I "$AU/substitute.py" "$S" "$B" || { echo "SUBSTITUTION FAILED"; exit 1; }
mkdir -p "$B/olean" "$B/src/TauCetiRoadmap/Integration" "$B/diffs" "$B/logs"
cp "$AU/Integration.lean" "$B/src/TauCetiRoadmap/Integration/"
for d in InfinitaryModelExistence BorelEquivalenceRelations CountableStructureSpaces \
         CountableModelCounting HanfNumbers RandomGraphs; do
  diff -u "$B/orig/$d.lean" "$B/src/TauCetiRoadmap/$d/Suggested.lean" > "$B/diffs/$d.diff"
done
LAKE_LEAN_PATH=$(cd "$LAKE_ROOT" && lake env printenv LEAN_PATH) || exit 1
LAKE_LEAN=$(cd "$LAKE_ROOT" && lake env which lean) || exit 1
export LAKE_ROOT LAKE_LEAN_PATH LAKE_LEAN
fail=0
# Dependency order: B' imports A; Integration imports A, B', D, E.
for m in InfinitaryModelExistence BorelEquivalenceRelations CountableStructureSpaces \
         CountableModelCounting HanfNumbers RandomGraphs Integration; do
  "$AU/compile1.sh" "$m" || fail=1
done
if [ $fail = 0 ] && grep -q "declaration uses .sorry." "$B/logs/Integration.out"; then
  echo "Integration.lean uses sorry"; fail=1
fi
# Known interface collision (README, "What is not checked"): C's prototype declares root names
# that Tau Ceti's modules imported by B and D also declare, so C cannot be imported with them.
# This probe reports whether that is still so; it does not affect the result.
printf 'import TauCetiRoadmap.BorelEquivalenceRelations.Suggested\nimport TauCetiRoadmap.CountableModelCounting.Suggested\n' \
  > "$B/src/TauCetiRoadmap/Integration/CoImportC.lean"
if (cd "$LAKE_ROOT" && LEAN_PATH=$B/olean:$LAKE_LEAN_PATH "$LAKE_LEAN" \
      "$B/src/TauCetiRoadmap/Integration/CoImportC.lean" > "$B/logs/CoImportC.out" 2>&1); then
  echo "NOTE: C now imports together with D; Integration.lean can import C again"
else
  echo "NOTE: C still cannot be imported together with D: $(grep -o "environment already contains '[^']*'" "$B/logs/CoImportC.out" | head -1)"
fi
[ $fail = 0 ] && echo "ALL COMPILED" || echo "SOME FILE FAILED (see integration/_build/logs/)"
exit $fail
