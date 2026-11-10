#!/usr/bin/env python3
"""Build the supplier-substituted copies of the six Suggested.lean drafts.

usage: substitute.py <S> <OUT>
  S   = directory holding <Dir>/Suggested.lean for the drafts (read only)
  OUT = output directory; writes OUT/orig/<Dir>.lean (verbatim snapshot) and
        OUT/src/TauCetiRoadmap/<Dir>/Suggested.lean (copy to compile)

After the migration to native Tau Ceti imports, the only cross-roadmap stand-in left is
CountableStructureSpaces' copy of InfinitaryModelExistence's `pcSeparation`. This script

1. asserts that the copy's statement is textually identical to the owner's;
2. asserts that no draft carries any other stand-in marker than the ones listed in `EXPECTED`;
3. deletes the copy (with its stand-in section header) from B' and resolves the name to the
   owner's declaration by importing A and a selective `open`.

Every edit is anchored on exact text and asserts that the anchor occurs exactly once, so a change
in a draft makes this script fail loudly instead of silently producing a different check.
"""
import os
import re
import sys

S, OUT = sys.argv[1], sys.argv[2]
A, C, B, D, E, RG = ("InfinitaryModelExistence", "BorelEquivalenceRelations",
                     "CountableStructureSpaces", "CountableModelCounting", "HanfNumbers",
                     "RandomGraphs")
DIRS = [A, C, B, D, E, RG]
# Roadmaps a stand-in could be owed to: the five successors, RandomGraphs and the parent.
ROADMAPS = [A, C, B, D, E, RG, "InfinitaryLogic"]


def read(d):
    with open(os.path.join(S, d, "Suggested.lean")) as f:
        return f.read()


def write(d, text):
    p = os.path.join(OUT, "src", "TauCetiRoadmap", d)
    os.makedirs(p, exist_ok=True)
    with open(os.path.join(p, "Suggested.lean"), "w") as f:
        f.write(text)


def replace1(s, old, new):
    assert s.count(old) == 1, f"anchor not unique/absent ({s.count(old)} hits): {old[:80]!r}"
    return s.replace(old, new)


def line_index(lines, pred, what):
    idx = [i for i, l in enumerate(lines) if pred(l)]
    assert len(idx) == 1, f"anchor {what}: {len(idx)} hits"
    return idx[0]


def statement(text, name):
    """The lines from `theorem <name>` through the first line ending in `:= by`, i.e. the full
    statement up to the proof."""
    lines = text.split("\n")
    pat = r"^theorem " + re.escape(name) + r"(?=[\s{(\[:]|$)"
    i = line_index(lines, lambda l: re.match(pat, l), f"theorem {name}")
    j = next(k for k in range(i, len(lines)) if lines[k].rstrip().endswith(":= by"))
    return "\n".join(lines[i:j + 1])


snap = {d: read(d) for d in DIRS}
os.makedirs(os.path.join(OUT, "orig"), exist_ok=True)
for d in DIRS:
    with open(os.path.join(OUT, "orig", d + ".lean"), "w") as f:
        f.write(snap[d])

# --- 1. B's stand-in must be the owner's statement, verbatim. -----------------------------------
sa, sb = statement(snap[A], "pcSeparation"), statement(snap[B], "pcSeparation")
if sa != sb:
    import difflib
    sys.stderr.write("\n".join(difflib.unified_diff(sa.split("\n"), sb.split("\n"),
                                                    f"{A}/pcSeparation", f"{B}/pcSeparation",
                                                    lineterm="")) + "\n")
    raise AssertionError(f"{B}'s pcSeparation stand-in differs from {A}'s statement")

# --- 2. No other stand-in. ----------------------------------------------------------------------
# Every comment block containing a stand-in marker is listed here, keyed by (draft, first line of
# the marker). A new marker anywhere fails; a marker naming only Tau Ceti or Mathlib as its owner
# would be allowed (a marked stand-in for a declaration absent at the pin) but is reported.
MARKER = re.compile(r"stand-?ins?\b|^Owner:|checked against revision", re.IGNORECASE)
EXPECTED = {
    (B, "form and proved by the library's theorem. One declaration below, `pcSeparation`, is a "
        "stand-in for"): "module docstring: announces the pcSeparation stand-in",
    (B, "/-! ### Stand-in owned by InfinitaryModelExistence"): "pcSeparation stand-in header",
    (B, "Owner: the InfinitaryModelExistence roadmap, Layer 7. Declaration: `pcSeparation`, over "
        "the pinned"): "pcSeparation stand-in header",
    (B, "infinitary syntax. Checked against revision 786457c7 of that roadmap (follow-up "
        "TauCetiRoadmap #1615). The"): "pcSeparation stand-in header, owner revision",
    (B, "/-- **Stand-in for `pcSeparation` of the InfinitaryModelExistence roadmap** (its Craig"):
        "pcSeparation stand-in docstring",
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

# --- 3. Copies. ---------------------------------------------------------------------------------
for d in (A, C, D, E, RG):
    write(d, snap[d])

s = snap[B]
s = replace1(s, "public import TauCeti.Topology.Algebra.Group.Perm\n",
             "public import TauCeti.Topology.Algebra.Group.Perm\n"
             "public import TauCetiRoadmap.InfinitaryModelExistence.Suggested\n")
s = replace1(s, "open scoped Pointwise\n",
             "open scoped Pointwise\n"
             "-- [integration] the owner's declaration replaces the stand-in\n"
             "open TauCetiRoadmap.InfinitaryModelExistence (pcSeparation)\n")
lines = s.split("\n")
i = line_index(lines, lambda l: l == "/-! ### Stand-in owned by InfinitaryModelExistence",
               "stand-in section header")
t = line_index(lines, lambda l: l.startswith("theorem pcSeparation "), "theorem pcSeparation")
assert i < t
j = next(k for k in range(t, len(lines)) if lines[k] == "  sorry")
assert all(not l.startswith(("theorem ", "def ", "lemma ", "instance ", "noncomputable ",
                             "inductive ", "structure ", "abbrev "))
           for l in lines[i:t]), "something other than comments between header and stand-in"
if j + 1 < len(lines) and lines[j + 1] == "":
    j += 1
lines[i:j + 1] = [
    "-- [integration] stand-in `pcSeparation` (and its stand-in section header) deleted; the name",
    "-- resolves to TauCetiRoadmap.InfinitaryModelExistence.pcSeparation by the selective `open`",
    "-- above.",
    "",
]
write(B, "\n".join(lines))

print("substitute.py: B's pcSeparation stand-in is textually identical to "
      "InfinitaryModelExistence's statement; deleted in B'")
print("substitute.py: stand-in markers found (none unexpected):")
print("\n".join(report))
