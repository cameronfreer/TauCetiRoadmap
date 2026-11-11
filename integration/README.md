# Supplier-substitution integration check

This folder is evidence for the InfinitaryLogic successor roadmaps after their migration to
native Tau Ceti imports. It is not meant to be merged. It checks that the prototypes compile
together, that the one cross-roadmap stand-in left still matches its owner, and that each
cross-roadmap use fits: the supplier's theorem, applied to the consumer's own objects, gives what
the consumer's README needs.

## Revisions

The tree is TauCetiRoadmap `main` at 35884a8c, octopus-merged (540f108f) with the six heads as
revised after the second round of reviews, then merged (c9c13c3b) with A, C, B and D as revised
after the 10 November reviews, so `TauCetiRoadmap/<Dir>/` here is what was checked.

| roadmap | pull request | head checked |
|---|---|---|
| InfinitaryModelExistence (A) | follow-up [#1615](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1615) to [#1315](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1315) | 6601a3b5 |
| BorelEquivalenceRelations (C) | follow-up [#1616](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1616) to [#1317](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1317) | e4077268 |
| CountableStructureSpaces (B) | [#1316](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1316) | eb1eee58 |
| CountableModelCounting (D) | follow-up [#2012](https://github.com/TauCetiProject/TauCetiRoadmap/pull/2012) to [#1318](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1318) | a25a711d |
| HanfNumbers (E) | [#1319](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1319) | 2dc7d398 |
| RandomGraphs | [#1223](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1223) | d6486263 |

RandomGraphs is compiled with the others but takes no part in the substitution check.

Pins (those of `main` at 35884a8c): Lean `v4.36.0-rc2`, Mathlib 1b1ccf4b0, Tau Ceti 2fd255d99.

Runs against earlier heads at the same pins: 7d5a38c9 (A 786457c7, C 6908d404, B 7cb889e0,
D e2b39535, E c716a691, RandomGraphs 1752d9dd) and 43633a12 (A 35db8dff, C 68c5f0bf, B 31039c31,
D 8584c5d3, E and RandomGraphs as here). The changes since are listed under
[Changes for the revised heads](#changes-for-the-revised-heads).

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
   (which records A's revision 35db8dff; A's statement is unchanged at 6601a3b5, as the
   identity check confirms) and E's module docstring sentence "There are no stand-ins."
3. **Compilation.** A, C, D, E and RandomGraphs compile unchanged and B' compiles with A's
   `pcSeparation`, each with the pinned `lean`, in dependency order, into `_build/olean`. A file
   importing A, B', C, D and E together must compile too (`CoImport` in the output). C's
   prototype once redeclared root names that Tau Ceti declares (fixed in #1616 at 6908d404); since
   e4077268 it states only the two targets Tau Ceti lacks (`isSmooth_of_isClosed` and the
   analytic perfect set theorem) and imports Tau Ceti for the rest. The run fails, naming the
   declaration, if a clash returns.
4. **`Integration.lean`** imports A, B', C, D and E and has three parts:
   * name-resolution guards: `#assert_absent` fails if B's `pcSeparation` (or any stand-in removed
     before or during the migration) is still declared, and `#assert_uses` fails unless a consumer
     declaration's type or proof term mentions the owner's constant, for instance D's
     `HasPerfectSetOfNonisoModelsOn` and Tau Ceti's `Setoid.HasPerfectAntichainOn` (C's
     interface, which C now cites as Tau Ceti's), D's `isoSetoid_morleyCode_iff` and `nonempty_morleyEquiv_iff` (A's), E's
     `IsLω₁ωSmall` and `realizedTypes` (A's), and `lopezEscobar_steps34` (below) and A's
     `pcSeparation`;
   * one `example` for each cross-roadmap use, sections 1–5: A → B (`pcSeparation` and
     `LHom.PCMem` in López–Escobar), C → B (Gδ subspaces, `AnalyticSet.prod`, invariant
     separation), B, C → D (Silver on model classes, the cardinality form, Scott height,
     Morley-code transport), A → D (language maps, the small presentation, fragments,
     Morleyization), A → E (reducts, isolators, countable `A`-elementary substructures, and the
     graph translation of A's Layer 6 in E 5.6);
   * section 6, universe placement: B's general constant-chain bound gives the countable case D
     consumes, for `M` in any universe; E stretches a source in `Type 1` to a model in `Type`; and
     E's Morley–Hanf route (E's source, E's exact-cardinality stretching, A's reduct lemma)
     assembles into the statement of `exists_model_card_eq_of_forall_beth`.

   Section 1 also has the theorem `lopezEscobar_steps34`, the remaining PC-separation boundary:
   B 5.3 steps 3–4, with A's `pcSeparation` applied to the PC sentences of B's
   `exists_pcSentence`, turn tree representations of `B` and of its complement into a sentence
   `θ` with `B = modelsOf θ`, the conclusion of B's `lopez_escobar`. Its hypotheses are B's own
   earlier steps (the tree representations of Layer 3 and the disjointness of step 2, which uses
   invariance), not supplier lemmas. Like B's steps 1–4 it assumes countably many relation
   symbols; B's `lopez_escobar` now holds for every relational language, by B's step 0, which
   reduces to the countable sublanguage of the atoms a Borel set depends on.

   Most suppliers are now Tau Ceti declarations that owner and consumer both use. Where a
   consumer's draft cites a Tau Ceti or Mathlib declaration directly, the example uses that
   declaration; an example is kept when it still checks a fit, a native theorem applied to the
   consumer's own setoids, model classes or codes. Every use where C supplies B or D is of this
   kind: C, B and D all cite the same Tau Ceti declarations, and C states none of them. The
   integration file contains no `sorry`, and no hypothesis stands in for a missing supplier lemma.

## What is not checked

* The prototypes' own `sorry`s. The build shows that the interfaces fit together as stated, not
  that the stated theorems are proved.

## Examples dropped in the port

The pre-migration `Integration.lean` had 26 examples in sections 1–6; 22 are ported, 4 dropped,
and 2 added (`lopezEscobar_steps34` and the E 5.6 graph-translation step), 24 in all. The checks
of C's own statements added in the meantime are gone again (see below).

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

## Changes for the revised heads

### 10 November reviews (this run)

* **C** deletes every definition and theorem Tau Ceti already has (18 definitions, 42 theorems)
  and cites Tau Ceti's instead; it states only `isSmooth_of_isClosed` and the analytic perfect
  set theorem. So `Adapters.lean` (C's antichain vocabulary against Tau Ceti's) is deleted, and so
  are the six examples that repeated a C-supplied use with C's own statement: invariant
  separation on B's coding space, relative Silver at one level and on `Fin n`, the
  Cantor-to-perfect, subtype and continuum lemmas, the cardinality form, and the Morley-code
  transport. Each had a Tau Ceti twin just before it, which remains. The table comparing C's
  hypotheses with Tau Ceti's is moot and removed.
* **B** states López–Escobar for every relational language; `lopezEscobar_steps34` needed no
  change (its docstring now says how the countable case it checks relates to the general one).
* **D** drops a countability hypothesis from `hasVaughtDichotomy_and_infiniteSentence_iff`, which
  no example uses.

### Second-round reviews (43633a12)

The revised heads delete the prototypes' verbatim wrappers of Tau Ceti declarations and rename a
few declarations. The examples follow the drafts: they now use the Tau Ceti or Mathlib declaration
the consumer cites, and no wrapper is reintroduced here.

* **B**: `ActionInvariant` is Mathlib's `MulAction.IsFixedBlock (Equiv.Perm ℕ)`, with B's
  `saturated_iff_isFixedBlock`; the Polish structure of `Equiv.Perm ℕ` is found by instance
  search; `measurableSet_modelsOf`, `measurableSet_setOf_bfEquivSetoid`,
  `isoSetoid_le_bfEquivSetoid` and the `standardBorelSpace_modelsOf` instance are
  `TauCeti.RelationalConfiguration`'s and `nonempty_equiv_of_bfEquiv_of_scottHeight_le` is
  `TauCeti`'s. B's `exists_pcSentence` and `measurableSet_iso_inter_of_scottHeight_le` now use `@`
  forms; the examples using them compile unchanged.
* **A**: `countable_relations_morleyize`, `realize_smallPresentation`,
  `Fragment.generated_countable`, `exists_isolatingFormula` and
  `exists_countable_aElementary_substructure` are `FirstOrder.Language`'s,
  `realize_onBoundedFormulaInf` is `LHom.realize_onBoundedFormulaInf`, and
  `isExpansionOn_morleyExpansion` is an instance. `pcSeparation` and `fragmentType` are still A's.
* **D**: the transport of the count is Tau Ceti's
  `LEquiv.lift_countableModelCount_onBoundedFormulaInf`.
* **C**: the two examples applying C's own `IsGδ.standardBorelSpace` and `AnalyticSet.prod` are
  dropped, since C no longer states them (its README cites Tau Ceti's). The Tau Ceti examples
  remain.
* **E**: one example added for the new Layer 5.6: E's relational
  `isLω₁ωSmall_iff_exists_isCompleteSentence` applied to the graph language and graph expansion,
  with Tau Ceti's `BoundedFormulaInf.backTranslate` and `realize_backTranslate` (A's Layer 6),
  gives the sentence `σ` of E's README 5.6 and its two properties.
* **Guards**: `#assert_uses` for D's `isIsolatingRank_scottHeight` (mentions `scottHeight`) and
  D's `lift_countableModelCount_onBoundedFormulaInf` (mentions `LHom.onBoundedFormulaInf`) are
  dropped: both declarations are deleted, D cites `TauCeti.isIsolatingRank_scottHeight` and
  `LEquiv.lift_countableModelCount_onBoundedFormulaInf` directly, and no remaining D statement
  mentions those constants. The uses themselves are checked by the section 3 `isolates` example
  and the section 4 transport example.

No example needed a change to a draft.

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
any other compiler output, then the result of the co-import check, and ends with `ALL COMPILED`
or `SOME FILE FAILED`. Outputs go to `integration/_build/`:

* `orig/`, the draft snapshot;
* `src/`, the copies compiled (B' substituted, the others verbatim);
* `diffs/`, each draft against its copy (only B's is nonempty);
* `logs/`, one compiler log per file.

`LAKE_ROOT=<checkout> integration/run.sh` reuses another checkout's built `.lake`, provided it has
the same `lake-manifest.json`.

The result at these heads:

| file | exit | `sorry` warnings |
|---|---|---|
| InfinitaryModelExistence | 0 | 8 |
| BorelEquivalenceRelations | 0 | 2 |
| CountableStructureSpaces (B') | 0 | 38 (the draft has 39; the deleted stand-in was one) |
| CountableModelCounting | 0 | 36 |
| HanfNumbers | 0 | 28 |
| RandomGraphs | 0 | 62 |
| Integration | 0 | 0 |

Perturbing A's `pcSeparation` statement in a scratch copy (adding `[Infinite M]` to the
disjointness hypothesis) makes `substitute.py` fail with the diff of the two statements, before
anything is compiled.

When a draft changes, merge the heads onto `main` here again and rerun. The stand-in block in B
records the owner revision it was checked against; keep it in step.
