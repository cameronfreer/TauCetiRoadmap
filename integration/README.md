# Supplier-substitution integration check

This folder is evidence for the InfinitaryLogic successor roadmaps after their migration to
native Tau Ceti imports. It is not meant to be merged. It checks that the prototypes compile
together, that the one cross-roadmap stand-in left still matches its owner, and that each
cross-roadmap use fits: the supplier's theorem, applied to the consumer's own objects, gives what
the consumer's README needs.

## Revisions

The tree is TauCetiRoadmap `main` at 35884a8c, octopus-merged (bd424796) with the six heads
below, so `TauCetiRoadmap/<Dir>/` here is what was checked.

| roadmap | pull request | head checked |
|---|---|---|
| InfinitaryModelExistence (A) | follow-up [#1615](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1615) to [#1315](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1315) | 786457c7 |
| BorelEquivalenceRelations (C) | follow-up [#1616](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1616) to [#1317](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1317) | 5ae57b57 |
| CountableStructureSpaces (B) | [#1316](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1316) | 7cb889e0 |
| CountableModelCounting (D) | follow-up [#2012](https://github.com/TauCetiProject/TauCetiRoadmap/pull/2012) to [#1318](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1318) | e2b39535 |
| HanfNumbers (E) | [#1319](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1319) | c716a691 |
| RandomGraphs | [#1223](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1223) | 1752d9dd |

RandomGraphs is compiled with the others but takes no part in the substitution check.

Pins (those of `main` at 35884a8c): Lean `v4.36.0-rc2`, Mathlib 1b1ccf4b0, Tau Ceti 2fd255d99.

Earlier runs of this check, at the old pins (Lean `v4.35.0-rc3`, Tau Ceti 358314d) and against the
pre-migration prototypes, are preserved on fork branches at 8a0783a8 (first run) and 19849b3d
(5 November rerun). They are not results at the current pins.

## What is checked

1. **The remaining stand-in.** After the migration, every prototype imports Tau Ceti modules
   instead of the parent prototype, and the only cross-roadmap stand-in left is B's copy of A's
   `pcSeparation`. `substitute.py` asserts that the copy's statement, from `theorem pcSeparation`
   through `:= by`, is textually identical to A's; then it deletes the copy and its stand-in
   section header from B's copy B', adds `public import TauCetiRoadmap.InfinitaryModelExistence.Suggested`
   and resolves the name with `open TauCetiRoadmap.InfinitaryModelExistence (pcSeparation)`.
   Every edit is anchored on exact draft text and asserted unique, so a changed draft makes the
   script fail instead of quietly checking something else.
2. **No other stand-in.** `substitute.py` scans the six drafts for stand-in markers (`stand-in`,
   `Owner:`, `checked against revision`) and fails on any marker it does not expect. A marker
   naming only Tau Ceti or Mathlib as owner (a marked stand-in for a declaration absent at the pin)
   would be allowed and reported. At these heads the only markers are B's `pcSeparation` block
   and E's module docstring sentence "There are no stand-ins."
3. **Compilation.** A, C, D, E and RandomGraphs compile unchanged and B' compiles with A's
   `pcSeparation`, each with the pinned `lean`, in dependency order, into `_build/olean`.
4. **`Integration.lean`** imports A, B', D and E and has three parts:
   * name-resolution guards: `#assert_absent` fails if B's `pcSeparation` (or any stand-in removed
     before or during the migration) is still declared, and `#assert_uses` fails unless a consumer
     declaration's type or proof term mentions the owner's constant, for instance D's
     `HasPerfectSetOfNonisoModelsOn` and Tau Ceti's `Setoid.HasPerfectAntichainOn` (C's
     interface), D's `isoSetoid_morleyCode_iff` and `nonempty_morleyEquiv_iff` (A's), E's
     `IsLω₁ωSmall` and `realizedTypes` (A's), and `lopezEscobar_steps34` (below) and A's
     `pcSeparation`;
   * one `example` for each cross-roadmap use, sections 1–5: A → B (`pcSeparation` and
     `LHom.PCMem` in López–Escobar), C → B (Gδ subspaces, `AnalyticSet.prod`, invariant
     separation), B, C → D (Silver on model classes, the cardinality form, Scott height,
     Morley-code transport), A → D (language maps, the small presentation, fragments,
     Morleyization), A → E (reducts, isolators, countable `A`-elementary substructures);
   * section 6, universe placement: B's general constant-chain bound gives the countable case D
     consumes, for `M` in any universe; E stretches a source in `Type 1` to a model in `Type`; and
     E's Morley–Hanf route (E's source, E's exact-cardinality stretching, A's reduct lemma)
     assembles into the statement of `exists_model_card_eq_of_forall_beth`.

   Section 1 also has the theorem `lopezEscobar_steps34`, the remaining PC-separation boundary:
   B 5.3 steps 3–4, with A's `pcSeparation` applied to the PC sentences of B's
   `exists_pcSentence`, turn tree representations of `B` and of its complement into a sentence
   `θ` with `B = modelsOf θ`, the conclusion of B's `lopez_escobar`. Its hypotheses are B's own
   earlier steps (the tree representations of Layer 3 and the disjointness of step 2, which uses
   invariance), not supplier lemmas.

   Most suppliers are now Tau Ceti declarations that owner and consumer both use. An example is
   kept when it still checks a fit: a native theorem applied to the consumer's own setoids, model
   classes or codes. The integration files contain no `sorry`, and no hypothesis stands in for a
   missing supplier lemma.

## What is not checked

* The prototypes' own `sorry`s. The build shows that the interfaces fit together as stated, not
  that the stated theorems are proved.
* **C's prototype against its consumers.** C's `Suggested.lean` declares, at the root,
  `MeasureTheory.AnalyticSet.inter`, `.offDiag`, `.prod` and
  `MeasurableSet.exists_nat_bool_injection_of_not_countable`. Tau Ceti's
  `MeasureTheory/Constructions/Polish/Analytic.lean` and `Polish/Perfect.lean`, which B's and
  D's Tau Ceti imports bring in (B the first, D both), declare the same names, so importing C together with B or
  D fails ("environment already contains 'MeasureTheory.AnalyticSet.inter'"). `Integration.lean`
  therefore does not import C: the C → B and C → D examples check Tau Ceti's implementation of
  C's interface, which is what B's and D's READMEs cite, and C's own statements (for example its
  `TauCetiRoadmap.BorelEquivalenceRelations.HasCantorAntichainOn`) are not connected to the
  consumers. `run.sh` probes this on every run and prints a `NOTE` saying whether it is still so.

## Examples dropped in the port

The pre-migration `Integration.lean` had 26 examples in sections 1–6; 22 are ported, 4 dropped,
and 1 (`lopezEscobar_steps34`) added.

| old example | reason |
|---|---|
| D's `hasCantorAntichainOn_image_morleyCode_iff` "is exactly the conclusion above" (section 3) | Only restated one D declaration; before the migration it checked that substitution had not changed D's statement, and nothing is substituted in D now. The transport itself is still checked from its parts. |
| D's `toStructure_morleyCode` stated against A's `morleyExpansion` (section 3) | Restated one D declaration, whose type now names Tau Ceti's `morleyExpansion` directly. Covered by `#assert_uses` (`morleyCode` mentions `morleyExpansion`) and used in the section 4 canonical-expansion example. |
| A's `countable_relations_morleyize` supplies the Morleyized instance (section 3) | Restated one A declaration. It is used inside the Morley-code transport example. |
| E's `IsEMSource` closure fields are A's `Fragment` fields (section 5) | E now takes `Γ : L.Fragment`, Tau Ceti's type, so there is nothing left to match. Covered by `#assert_uses` (`IsEMSource` mentions `Fragment`). |

The glue instance `countable_functions_of_isRelational` is gone too: instance search finds it at
the pin. Two examples changed shape: the canonical-expansion example of section 4 is now stated on
D's codes (`morleyCode Φ c` is a code of the image of `φ` along `lhomMorleyize Φ` exactly when `c`
is a code of `φ`), and the invariant-separation example of section 2 adds the step from disjoint
sets with a saturated `B` to disjoint saturations, which Tau Ceti's
`Setoid.exists_invariant_measurableSet_separating` takes.

## Rerun

From the repository root on this branch, with a `.lake` at the pinned manifest:

```
lake exe cache get
grep -h '^\(public \)\?import TauCeti\.' integration/Integration.lean \
    TauCetiRoadmap/{InfinitaryModelExistence,BorelEquivalenceRelations,CountableStructureSpaces,CountableModelCounting,HanfNumbers,RandomGraphs}/Suggested.lean \
  | awk '{print $NF}' | sort -u | xargs lake build
integration/run.sh
```

The second step builds (or downloads) the Tau Ceti modules the files import; no roadmap target is
built by `lake`. `run.sh` then runs `substitute.py` and compiles, in order, A, C, B', D, E,
RandomGraphs and `Integration.lean`, each with the pinned `lean` and
`LEAN_PATH=_build/olean:<lake LEAN_PATH>`. Files with a `module` header need no extra flag:
`lean -o X.olean` also writes the `X.olean.server` and `X.olean.private` parts that their importers
read. It prints one line per file with its exit code and number of `sorry` warnings, followed by
any other compiler output, and ends with `ALL COMPILED` or `SOME FILE FAILED`. Outputs go to
`integration/_build/`:

* `orig/`, the draft snapshot;
* `src/`, the copies compiled (B' substituted, the others verbatim);
* `diffs/`, each draft against its copy (only B's is nonempty);
* `logs/`, one compiler log per file.

`LAKE_ROOT=<checkout> integration/run.sh` reuses another checkout's built `.lake`, provided it has
the same `lake-manifest.json`.

The result at these heads:

| file | exit | `sorry` warnings |
|---|---|---|
| InfinitaryModelExistence | 0 | 9 |
| BorelEquivalenceRelations | 0 | 59 |
| CountableStructureSpaces (B') | 0 | 43 (the draft has 44; the deleted stand-in was one) |
| CountableModelCounting | 0 | 35 |
| HanfNumbers | 0 | 32 |
| RandomGraphs | 0 | 60 |
| Integration | 0 | 0 |

Perturbing A's `pcSeparation` statement in a scratch copy (adding `[Infinite M]` to the
disjointness hypothesis) makes `substitute.py` fail with the diff of the two statements, before
anything is compiled.

When a draft changes, merge the heads onto `main` here again and rerun. The stand-in block in B
records the owner revision it was checked against; keep it in step.
