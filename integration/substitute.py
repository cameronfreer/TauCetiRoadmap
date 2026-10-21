#!/usr/bin/env python3
"""Build the supplier-substituted copies of the five Suggested.lean drafts.

usage: substitute.py <S> <OUT>
  S   = directory holding <Dir>/Suggested.lean for the five drafts (read only)
  OUT = output directory; writes OUT/orig/<Dir>.lean (verbatim snapshot) and
        OUT/src/TauCetiRoadmap/<Dir>/Suggested.lean (substituted copy)

Every edit is anchored on exact text and asserts that the anchor occurs exactly once, so a change
in a draft makes this script fail loudly instead of silently producing a different check.
"""
import os
import sys

S, AU = sys.argv[1], sys.argv[2]
DIRS = ["InfinitaryModelExistence", "BorelEquivalenceRelations", "CountableStructureSpaces",
        "CountableModelCounting", "HanfNumbers"]


def read(d):
    return open(os.path.join(S, d, "Suggested.lean")).read()


def write(d, text):
    p = os.path.join(AU, "src", "TauCetiRoadmap", d)
    os.makedirs(p, exist_ok=True)
    open(os.path.join(p, "Suggested.lean"), "w").write(text)


def replace1(s, old, new):
    assert s.count(old) == 1, f"anchor not unique/absent: {old[:80]!r}"
    return s.replace(old, new)


def cut(s, start, end, note):
    """Delete from the line starting with `start` through the first later line equal to `end`
    (plus one following blank line) and put `note` in its place."""
    lines = s.split("\n")
    idx = [i for i, l in enumerate(lines) if l.startswith(start)]
    assert len(idx) == 1, f"start anchor {start!r}: {len(idx)} hits"
    i = idx[0]
    j = next(k for k in range(i, len(lines)) if lines[k] == end)
    if j + 1 < len(lines) and lines[j + 1] == "":
        j += 1
    return "\n".join(lines[:i] + note + [""] + lines[j + 1:])


os.makedirs(os.path.join(AU, "orig"), exist_ok=True)
for d in DIRS:
    open(os.path.join(AU, "orig", d + ".lean"), "w").write(read(d))

# A and C: unchanged.
write("InfinitaryModelExistence", read("InfinitaryModelExistence"))
write("BorelEquivalenceRelations", read("BorelEquivalenceRelations"))

# B': drop the PCMem / pcSeparation stand-ins, import A, resolve selectively.
s = read("CountableStructureSpaces")
s = replace1(s, "import TauCetiRoadmap.InfinitaryLogic.Suggested\n",
             "import TauCetiRoadmap.InfinitaryLogic.Suggested\n"
             "import TauCetiRoadmap.InfinitaryModelExistence.Suggested\n")
s = replace1(s, "open scoped Pointwise\n",
             "open scoped Pointwise\n"
             "-- [integration] the owner's declarations replace the stand-ins\n"
             "open TauCetiRoadmap.InfinitaryModelExistence (PCMem pcSeparation)\n")
s = cut(s, "/-- **Stand-in for `PCMem`", "  sorry",
        ["-- [integration] stand-ins `PCMem` and `pcSeparation` deleted; resolved to",
         "-- TauCetiRoadmap.InfinitaryModelExistence.{PCMem, pcSeparation} by the selective `open` above."])
write("CountableStructureSpaces", s)

# D': drop the B stand-ins, the A stand-ins and the `exs` stand-in; import A, B', C; replace the
# inline perfect-set forms by C's named definitions.
s = read("CountableModelCounting")
s = replace1(s, "import TauCetiRoadmap.InfinitaryLogic.Suggested\n",
             "import TauCetiRoadmap.InfinitaryLogic.Suggested\n"
             "import TauCetiRoadmap.InfinitaryModelExistence.Suggested\n"
             "import TauCetiRoadmap.CountableStructureSpaces.Suggested\n"
             "import TauCetiRoadmap.BorelEquivalenceRelations.Suggested\n")
s = replace1(s, "open TauCetiRoadmap.InfinitaryLogic\n",
             "open TauCetiRoadmap.InfinitaryLogic\n"
             "-- [integration] owners' declarations replace the stand-ins\n"
             "open TauCetiRoadmap.CountableStructureSpaces\n"
             "open TauCetiRoadmap.InfinitaryModelExistence (onBoundedFormulaInf realize_onBoundedFormulaInf exs\n"
             "  morleyize lhomMorleyize morleyExpansion countable_relations_morleyize nonempty_morleyEquiv_iff)\n"
             "open TauCetiRoadmap.BorelEquivalenceRelations (HasPerfectAntichainOn HasCantorAntichainOn IsThinOn)\n")
s = cut(s, "/-! ## Stand-ins for the CountableStructureSpaces", "end StandIns",
        ["-- [integration] StandIns section (CountableStructureSpaces stand-ins) deleted; names resolve to",
         "-- TauCetiRoadmap.CountableStructureSpaces via the namespace `open` above."])
s = cut(s, "/-- Existential closure over all bound positions.", "  | _ + 1, φ => exs φ.ex",
        ["-- [integration] `exs` stand-in deleted; A's own `exs` stand-in (identical text) is used instead."])
s = cut(s, "section LanguageMaps", "end LanguageMaps",
        ["-- [integration] LanguageMaps stand-ins deleted; resolved to InfinitaryModelExistence's",
         "-- `onBoundedFormulaInf` / `realize_onBoundedFormulaInf`."])
s = cut(s, "section MorleyStandIns", "end MorleyStandIns",
        ["-- [integration] Morleyization stand-ins deleted; resolved to InfinitaryModelExistence's",
         "-- `morleyize`, `lhomMorleyize`, `morleyExpansion`, `morleyize_isRelational`,",
         "-- `countable_relations_morleyize`, `nonempty_morleyEquiv_iff`."])
C_SUBST = [
    ("""def HasPerfectSetOfNonisoModelsOn (α : Type) (φ : Sentenceω L) : Prop :=
  ∃ P : Set (StructureSpaceOn L α), Perfect P ∧ P.Nonempty ∧ P ⊆ modelsOf φ ∧
    ∀ c ∈ P, ∀ d ∈ P, structureIsoSetoidOn L α c d → c = d""",
     """def HasPerfectSetOfNonisoModelsOn (α : Type) (φ : Sentenceω L) : Prop :=
  -- [integration] C-substituted
  HasPerfectAntichainOn (structureIsoSetoidOn L α) (modelsOf φ : Set (StructureSpaceOn L α))"""),
    ("""def IsThinOnNatModels (φ : Sentenceω L) : Prop :=
  ¬ HasPerfectSetOfNonisoModelsOn ℕ φ""",
     """def IsThinOnNatModels (φ : Sentenceω L) : Prop :=
  -- [integration] C-substituted
  IsThinOn (structureIsoSetoid L) (modelsOf φ : Set (StructureSpace L))"""),
    ("""    ¬ ∃ f : (ℕ → Bool) → StructureSpace L, Continuous f ∧ (∀ x, f x ∈ K) ∧
        ∀ x y, x ≠ y → ¬ structureIsoSetoid L (f x) (f y) := by""",
     """    ¬ HasCantorAntichainOn (structureIsoSetoid L) K := by -- [integration] C-substituted"""),
    ("""    (¬ ∃ P : Set (StructureSpace L), Perfect P ∧ P.Nonempty ∧ P ⊆ C ∧
        ∀ c ∈ P, ∀ d ∈ P, structureIsoSetoid L c d → c = d) ↔""",
     """    IsThinOn (structureIsoSetoid L) C ↔ -- [integration] C-substituted"""),
    ("""    (∃ f : (ℕ → Bool) → StructureSpace (morleyize L Φ), Continuous f ∧
        (∀ x, f x ∈ morleyCode Φ '' K) ∧
        ∀ x y, x ≠ y → ¬ structureIsoSetoid (morleyize L Φ) (f x) (f y)) ↔
      ∃ f : (ℕ → Bool) → StructureSpace L, Continuous f ∧ (∀ x, f x ∈ K) ∧
        ∀ x y, x ≠ y → ¬ structureIsoSetoid L (f x) (f y) := by""",
     """    HasCantorAntichainOn (structureIsoSetoid (morleyize L Φ)) (morleyCode Φ '' K) ↔
      HasCantorAntichainOn (structureIsoSetoid L) K := by -- [integration] C-substituted"""),
    ("""      ∃ P : Set (StructureSpace L), Perfect P ∧ P.Nonempty ∧ P ⊆ modelsOfTheory T ∧
        ∀ c ∈ P, ∀ d ∈ P, structureIsoSetoid L c d → c = d""",
     """      HasPerfectAntichainOn (structureIsoSetoid L) (modelsOfTheory T) -- [integration] C-substituted"""),
]
for old, new in C_SUBST:
    s = replace1(s, old, new)
write("CountableModelCounting", s)

# E': drop the three A stand-ins, import A, resolve selectively.
s = read("HanfNumbers")
s = replace1(s, "import TauCetiRoadmap.InfinitaryLogic.Suggested\n",
             "import TauCetiRoadmap.InfinitaryLogic.Suggested\n"
             "import TauCetiRoadmap.InfinitaryModelExistence.Suggested\n")
s = replace1(s, "open TauCetiRoadmap.InfinitaryLogic\n",
             "open TauCetiRoadmap.InfinitaryLogic\n"
             "-- [integration] owner's declarations replace the stand-ins\n"
             "open TauCetiRoadmap.InfinitaryModelExistence (onBoundedFormulaInf infinitaryType realizedTypes)\n")
s = cut(s, "section LanguageMaps", "end LanguageMaps",
        ["-- [integration] `onBoundedFormulaInf` stand-in deleted; resolved to InfinitaryModelExistence's."])
s = cut(s, "/-- Stand-in for `infinitaryType`", "  Set.range (infinitaryType M (n := n))",
        ["-- [integration] `infinitaryType` / `realizedTypes` stand-ins deleted; resolved to",
         "-- InfinitaryModelExistence's."])
write("HanfNumbers", s)


# The `exs` swap in D' is justified only if A's and D's stand-ins are textually identical.
def block(text, start, end):
    lines = text.split("\n")
    i = next(k for k, l in enumerate(lines) if l.startswith(start))
    j = next(k for k in range(i, len(lines)) if lines[k] == end)
    return "\n".join(lines[i:j + 1])


ea = block(read("InfinitaryModelExistence"), "/-- Existential closure over all bound positions.",
           "  | _ + 1, φ => exs φ.ex")
ed = block(read("CountableModelCounting"), "/-- Existential closure over all bound positions.",
           "  | _ + 1, φ => exs φ.ex")
assert ea == ed, "A's and D's `exs` stand-ins differ"
print("substitute.py: wrote substituted copies; A/D `exs` stand-ins textually identical")
