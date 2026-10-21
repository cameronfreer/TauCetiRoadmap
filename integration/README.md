# Supplier-substitution integration check

This branch is evidence for the five InfinitaryLogic successor roadmaps. It is not meant to be
merged. It checks that their prototypes compile against each other's actual declarations instead
of the marked stand-ins each consumer carries:

| roadmap | PR | revision checked |
|---|---|---|
| InfinitaryModelExistence (A) | [#1315](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1315) | 6da153fb |
| BorelEquivalenceRelations (C) | [#1317](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1317) | 34b35e1d |
| CountableStructureSpaces (B) | [#1316](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1316) | c49a0b43 |
| CountableModelCounting (D) | [#1318](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1318) | ebe7b370 |
| HanfNumbers (E) | [#1319](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1319) | 9d85e0c1 |

All five branch from `main` at 098fab01. The pins are those of that `main`: Lean
`v4.35.0-rc3`, Mathlib 6b7abb3c and TauCeti a91d3aaf. The merge commit on this branch contains
exactly those five revisions, so `TauCetiRoadmap/<Dir>/` here is what was checked.

## What is checked

1. `substitute.py` deletes each consumer's stand-ins and resolves their names to the owners'
   declarations:
   * B' uses A's `PCMem` and `pcSeparation`;
   * D' uses B's coding space, model classes, isomorphism, back-and-forth and Scott-height
     declarations; A's language maps and Morleyization (`morleyize`, `lhomMorleyize`,
     `morleyExpansion`, `morleyize_isRelational`, `countable_relations_morleyize`,
     `nonempty_morleyEquiv_iff`); A's copy of `exs`; and C's `HasPerfectAntichainOn`,
     `HasCantorAntichainOn` and `IsThinOn` in place of D's six inline perfect-set forms;
   * E' uses A's `onBoundedFormulaInf`, `infinitaryType` and `realizedTypes`.

   Every edit is anchored on exact draft text and asserted unique. If a draft changes, the script
   fails instead of quietly checking something else. It also asserts that A's and D's `exs`
   stand-ins are textually identical.
2. `Adapters.lean` restates D's original inline forms and proves by `Iff.rfl` that they are C's
   named definitions. It then checks that the D' theorems prove the original statements.
3. `Integration.lean` has two parts:
   * name-resolution guards: `#assert_absent` fails if a stand-in survived, and `#assert_uses`
     fails unless a consumer declaration mentions the owner's constant;
   * one `example` for each cross-roadmap use, applying the supplier's theorem to the consumer's
     objects to produce the conclusion the consumer's README needs.

   The integration files contain no `sorry`, and no hypothesis stands in for a missing supplier
   lemma. This includes Morleyization transport: C's `hasCantorAntichainOn_image_iff` is applied to
   D's `morleyCode` through D's `measurableEmbedding_morleyCode` and
   `structureIsoSetoid_morleyCode_iff`, over A's Morleyization.

What is not checked: the prototypes' own `sorry`s. The build shows that the interfaces fit
together as stated, not that the stated theorems are proved.

## Rerun

From the repository root on this branch:

```
lake exe cache get
lake build TauCetiRoadmap.InfinitaryLogic.Suggested
integration/run.sh
```

The steps build the parent prototype's olean once, then compile, in order:

1. A and C, unchanged;
2. B', D' and E', the substituted copies;
3. `Adapters.lean`;
4. `Integration.lean`.

Each file is compiled with the pinned `lean` and `LEAN_PATH=_build/olean:<lake LEAN_PATH>`. The
outputs go to `integration/_build/`:

* `orig/`, the draft snapshot;
* `src/`, the substituted copies;
* `diffs/`, each draft against its substituted copy;
* `logs/`, one compiler log per file.

The expected final line is `ALL COMPILED`, with no `sorry` warning in `Adapters` or `Integration`.

`LAKE_ROOT=<checkout> integration/run.sh` reuses another checkout's built `.lake`, provided it has
the same manifest and the same parent prototype.

When a draft changes, update the five branches and merge them here again. The stand-in blocks in
each consumer record the owner revision they were checked against; keep those in step.
