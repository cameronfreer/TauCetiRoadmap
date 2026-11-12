#!/bin/bash
# Supplier integration check for the InfinitaryLogic successor roadmaps.
# Usage, from the repository root on this branch, after building the Tau Ceti modules the drafts,
# the checks and Integration.lean import (see README.md):
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
python3 -I "$AU/prepare.py" "$S" "$AU" "$B" || { echo "PREPARATION FAILED"; exit 1; }
mkdir -p "$B/olean" "$B/logs"
LAKE_LEAN_PATH=$(cd "$LAKE_ROOT" && lake env printenv LEAN_PATH) || exit 1
LAKE_LEAN=$(cd "$LAKE_ROOT" && lake env which lean) || exit 1
export LAKE_ROOT LAKE_LEAN_PATH LAKE_LEAN
DIRS="InfinitaryModelExistence BorelEquivalenceRelations CountableStructureSpaces \
CountableModelCounting HanfNumbers RandomGraphs"
fail=0
# The drafts (each imports only Mathlib and Tau Ceti), then the boundary checks moved out of them
# (each imports its own draft), then Integration.lean (imports A, B, C, D, E and the checks it
# uses).
for m in $DIRS; do "$AU/compile1.sh" "$m" || fail=1; done
for m in $DIRS; do "$AU/compile1.sh" "Checks/$m" || fail=1; done
"$AU/compile1.sh" Integration || fail=1
# Neither the checks nor the integration file may use `sorry`.
for m in $DIRS; do
  if grep -q "declaration uses .sorry." "$B/logs/Checks.$m.out"; then
    echo "Checks/$m.lean uses sorry"; fail=1
  fi
done
if grep -q "declaration uses .sorry." "$B/logs/Integration.out"; then
  echo "Integration.lean uses sorry"; fail=1
fi
# The five drafts must import together. C's prototype once declared root names that Tau Ceti's
# modules imported by B and D also declare (fixed in #1616 at 6908d404); this check names the
# clashing declaration if that returns.
printf 'import TauCetiRoadmap.%s.Suggested\n' InfinitaryModelExistence BorelEquivalenceRelations \
    CountableStructureSpaces CountableModelCounting HanfNumbers \
  > "$B/src/TauCetiRoadmap/Integration/CoImport.lean"
if (cd "$LAKE_ROOT" && LEAN_PATH=$B/olean:$LAKE_LEAN_PATH "$LAKE_LEAN" \
      "$B/src/TauCetiRoadmap/Integration/CoImport.lean" > "$B/logs/CoImport.out" 2>&1); then
  echo "=== CoImport: A, B, C, D and E import together"
else
  clash=$(grep -o "environment already contains '[^']*'" "$B/logs/CoImport.out" | head -1)
  echo "=== CoImport FAILED: ${clash:-see logs/CoImport.out}"
  fail=1
fi
[ $fail = 0 ] && echo "ALL COMPILED" || echo "SOME FILE FAILED (see integration/_build/logs/)"
exit $fail
