# Supplier-substitution integration check

This branch is evidence for the five InfinitaryLogic successor roadmaps. It is not meant to be
merged. It checks that their prototypes compile against each other's actual declarations instead
of the marked stand-ins each consumer carries:

| roadmap | state | revision checked |
|---|---|---|
| InfinitaryModelExistence (A) | merged ([#1315](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1315)); follow-up [#1615](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1615) open | bf6203dd |
| BorelEquivalenceRelations (C) | merged ([#1317](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1317)); follow-up [#1616](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1616) open | a614e6e8 |
| CountableStructureSpaces (B) | [#1316](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1316) open | 113f1716 |
| CountableModelCounting (D) | merged ([#1318](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1318)); stand-in record follow-up on branch `doc/countable-model-counting-bfequiv-standin` | ba98be7d |
| HanfNumbers (E) | [#1319](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1319) open | d590c4e4 |

The tree is `main` at d0bb87a6 merged with the four open heads and the follow-up commit ba98be7d
(which is on `main` at 3b51055b; nothing in the five directories or the pins changed between those
two `main` revisions), so `TauCetiRoadmap/<Dir>/` here is what was checked. The pins are those of
that `main`: Lean `v4.35.0-rc3`, Mathlib f6090c7 and
TauCeti 358314d. The parent prototype is `Completed/InfinitaryLogic/Suggested.lean`.

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
   stand-ins are textually identical, and that every stand-in D and E mark as verbatim still matches
   its owner's declaration, attributes included: in D, B's coding space with its topology and
   σ-algebra instances, decoding, encoding, isomorphism relations, model classes and Scott height,
   and A's language maps and Morleyization including `morleyExpansion`; in E, A's three
   stand-ins. D's `bfEquivSetoid` is compared on its signature and relation only: D
   admits the equivalence laws inline, while B assembles them from stand-ins for the parent's
   `BFEquiv.refl`, `BFEquiv.symm` and `BFEquiv.trans`.
2. `Adapters.lean` restates D's original inline forms and proves by `Iff.rfl` that they are C's
   named definitions. It then checks that the D' theorems prove the original statements.
3. `Integration.lean` has three parts:
   * name-resolution guards: `#assert_absent` fails if a stand-in survived, and `#assert_uses`
     fails unless a consumer declaration mentions the owner's constant;
   * one `example` for each cross-roadmap use, applying the supplier's theorem to the consumer's
     objects to produce the conclusion the consumer's README needs;
   * universe placement of the revised statements: B's general constant-chain bound gives the
     countable case D consumes for `M` in any universe; E stretches a source in `Type 1` to a
     model in `Type`; and E's Morley–Hanf route (E's source, E's exact-cardinality stretching,
     A's reduct) assembles into the statement of `exists_model_card_eq_of_forall_beth`.

   The integration files contain no `sorry`, and no hypothesis stands in for a missing supplier
   lemma. This includes Morleyization transport: C's `hasCantorAntichainOn_image_iff` is applied to
   D's `morleyCode` through D's `measurableEmbedding_morleyCode` and
   `structureIsoSetoid_morleyCode_iff`, over A's Morleyization.

What is not checked: the prototypes' own `sorry`s, and the stand-ins for Tau Ceti declarations
(B's `BFEquiv.refl`, `BFEquiv.symm`, `BFEquiv.trans`; A's and D's `exs`), whose owners are later
than the pinned Tau Ceti. The build shows that the interfaces fit
together as stated, not that the stated theorems are proved.

## Rerun

From the repository root on this branch:

```
lake exe cache get
lake build Completed.InfinitaryLogic.Suggested
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

When a draft changes, merge the open heads and follow-ups onto `main` here again. The stand-in blocks in
each consumer record the owner revision they were checked against; keep those in step.
