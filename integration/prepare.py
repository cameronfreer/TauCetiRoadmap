#!/usr/bin/env python3
"""Copy the six Suggested.lean drafts and the moved boundary checks into the build tree.

usage: prepare.py <S> <AU> <OUT>
  S   = directory holding <Dir>/Suggested.lean for the drafts (read only)
  AU  = the integration folder (holding checks/<Dir>.lean and Integration.lean)
  OUT = output directory; writes OUT/src/TauCetiRoadmap/<Dir>/Suggested.lean (the drafts, verbatim),
        OUT/src/TauCetiRoadmap/Integration/Checks/<Dir>.lean (the moved checks, verbatim) and
        OUT/src/TauCetiRoadmap/Integration/Integration.lean

Nothing is substituted: since the 12 November conformance pass no draft carries a cross-roadmap
stand-in, and the integration file imports InfinitaryModelExistence for `pcSeparation` directly.
Before copying, this script asserts that this is still so:

1. no draft carries a stand-in marker other than the ones listed in `EXPECTED`;
2. no draft but InfinitaryModelExistence declares `pcSeparation` (CountableStructureSpaces carried
   a stand-in copy until the pass);
3. no draft imports another roadmap.
"""
import os
import re
import shutil
import sys

S, AU, OUT = sys.argv[1], sys.argv[2], sys.argv[3]
A, C, B, D, E, RG = ("InfinitaryModelExistence", "BorelEquivalenceRelations",
                     "CountableStructureSpaces", "CountableModelCounting", "HanfNumbers",
                     "RandomGraphs")
DIRS = [A, C, B, D, E, RG]
# Roadmaps a stand-in could be owed to: the five successors, RandomGraphs and the parent.
ROADMAPS = [A, C, B, D, E, RG, "InfinitaryLogic"]


def read(d):
    with open(os.path.join(S, d, "Suggested.lean")) as f:
        return f.read()


snap = {d: read(d) for d in DIRS}

# --- 1. No stand-in. ----------------------------------------------------------------------------
# Every line carrying a stand-in marker is listed here, keyed by (draft, line). A new marker
# anywhere fails; a marker naming only Tau Ceti or Mathlib as its owner would be allowed (a marked
# stand-in for a declaration absent at the pin) but is reported.
MARKER = re.compile(r"stand-?ins?\b|^Owner:|checked against revision", re.IGNORECASE)
EXPECTED = {
    (E, "(`FirstOrder.Language.infinitaryType`, `realizedTypes`). There are no stand-ins. Skolem "
        "towers"): "module docstring: says there are none",
}


def comment_block(lines, k):
    i = k
    while i > 0 and "/-" not in lines[i]:
        i -= 1
    j = k
    while j < len(lines) - 1 and "-/" not in lines[j]:
        j += 1
    return "\n".join(lines[i:j + 1])


seen, report, bad = set(), [], []
for d in DIRS:
    lines = snap[d].split("\n")
    for k, l in enumerate(lines):
        if not MARKER.search(l):
            continue
        key = (d, l)
        if key in EXPECTED:
            seen.add(key)
            report.append(f"  {d}:{k + 1}: expected ({EXPECTED[key]})")
            continue
        block = comment_block(lines, k)
        owners = [r for r in ROADMAPS if r in block]
        if not owners and re.search(r"Tau Ceti|Mathlib", block):
            report.append(f"  {d}:{k + 1}: allowed, Tau Ceti/Mathlib stand-in: {l.strip()}")
        else:
            bad.append(f"  {d}:{k + 1}: {l.strip()}  (roadmaps named: {owners or 'none'})")
missing = set(EXPECTED) - seen
assert not missing, "expected stand-in markers not found (draft changed?):\n" + \
    "\n".join(f"  {d}: {l}" for d, l in sorted(missing))
assert not bad, "unexpected stand-in markers:\n" + "\n".join(bad)

# --- 2. `pcSeparation` is declared by its owner only. --------------------------------------------
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*"
                  r"(?:theorem|lemma|def|abbrev|axiom|opaque|instance)\s+(?:\S*\.)?pcSeparation\b",
                  re.MULTILINE)
owners = [d for d in DIRS if DECL.search(snap[d])]
assert owners == [A], f"pcSeparation declared by {owners}, expected only {A}"

# --- 3. No draft imports another roadmap. -------------------------------------------------------
IMP = re.compile(r"^(?:public )?import (TauCetiRoadmap\.\S+)", re.MULTILINE)
cross = [(d, m) for d in DIRS for m in IMP.findall(snap[d])]
assert not cross, "drafts import roadmap modules: " + ", ".join(f"{d} -> {m}" for d, m in cross)

# --- Copies. ------------------------------------------------------------------------------------
for d in DIRS:
    p = os.path.join(OUT, "src", "TauCetiRoadmap", d)
    os.makedirs(p, exist_ok=True)
    with open(os.path.join(p, "Suggested.lean"), "w") as f:
        f.write(snap[d])
chk = os.path.join(OUT, "src", "TauCetiRoadmap", "Integration", "Checks")
os.makedirs(chk, exist_ok=True)
for d in DIRS:
    shutil.copyfile(os.path.join(AU, "checks", d + ".lean"), os.path.join(chk, d + ".lean"))
shutil.copyfile(os.path.join(AU, "Integration.lean"),
                os.path.join(OUT, "src", "TauCetiRoadmap", "Integration", "Integration.lean"))

print(f"prepare.py: no draft declares pcSeparation except {A}; no draft imports another roadmap")
print("prepare.py: stand-in markers found (none unexpected):")
print("\n".join(report))
