#!/bin/bash
# compile1.sh <name>: compile one file of integration/_build/src against integration/_build/olean.
#   compile1.sh InfinitaryModelExistence   (src/TauCetiRoadmap/<Dir>/Suggested.lean)
#   compile1.sh Adapters                   (src/TauCetiRoadmap/Integration/<Name>.lean)
# Runs the pinned `lean` directly with LEAN_PATH=olean:<lake LEAN_PATH>; `lake env lean` would
# reset LEAN_PATH.
set -u
AU="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$AU/.." && pwd)"
LAKE_ROOT="${LAKE_ROOT:-$REPO}"
B="$AU/_build"
LP=$(cd "$LAKE_ROOT" && lake env printenv LEAN_PATH)
LEAN=$(cd "$LAKE_ROOT" && lake env which lean)
name=$1
if [ -f "$B/src/TauCetiRoadmap/$name/Suggested.lean" ]; then
  src=$B/src/TauCetiRoadmap/$name/Suggested.lean; out=$B/olean/TauCetiRoadmap/$name/Suggested.olean
else
  src=$B/src/TauCetiRoadmap/Integration/$name.lean; out=$B/olean/TauCetiRoadmap/Integration/$name.olean
fi
mkdir -p "$(dirname "$out")" "$B/logs"
cd "$LAKE_ROOT"
LEAN_PATH=$B/olean:$LP $LEAN -R "$B/src" -o "$out" "$src" > "$B/logs/$name.out" 2>&1
rc=$?
nsorry=$(grep -c "declaration uses .sorry." "$B/logs/$name.out")
nerr=$(grep -c ": error" "$B/logs/$name.out")
echo "=== $name exit=$rc sorry-warnings=$nsorry error-lines=$nerr"
grep -v "declaration uses .sorry." "$B/logs/$name.out" | head -${HEADN:-40}
exit $rc
