# Supplier integration check

This folder is evidence for the InfinitaryLogic successor roadmaps after their migration to
native Tau Ceti imports. It is not meant to be merged. It checks that the prototypes compile
together, that none of them carries a cross-roadmap stand-in, that the boundary checks moved out
of the prototypes still compile against them, and that each cross-roadmap use fits: the
supplier's theorem, applied to the consumer's own objects, gives what the consumer's README needs.
(Until the 12 November conformance pass the harness also substituted B's stand-in copy of A's
`pcSeparation`; B has since removed it, so nothing is substituted any more.)

## Revisions

The tree is TauCetiRoadmap `main` at 35884a8c, octopus-merged (540f108f) with the six heads as
revised after the second round of reviews, then merged (c9c13c3b) with A, C, B and D as revised
after the 10 November reviews, (b3b9502b) with the B and C follow-ups, and (73e23254) with the
six heads as revised in the 12 November conformance pass, so `TauCetiRoadmap/<Dir>/` here is what
was checked.

| roadmap | pull request | head checked |
|---|---|---|
| InfinitaryModelExistence (A) | follow-up [#1615](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1615) to [#1315](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1315) | bb883e0b |
| BorelEquivalenceRelations (C) | follow-up [#1616](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1616) to [#1317](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1317) | 6ca8a4f0 |
| CountableStructureSpaces (B) | [#1316](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1316) | 65a7a7ea |
| CountableModelCounting (D) | follow-up [#2012](https://github.com/TauCetiProject/TauCetiRoadmap/pull/2012) to [#1318](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1318) | 1c8987f5 |
| HanfNumbers (E) | [#1319](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1319) | c61d6445 |
| RandomGraphs | [#1223](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1223) | 2210a669 |

RandomGraphs is compiled with the others, with its moved checks, but supplies and consumes no
cross-roadmap use.

Pins (those of `main` at 35884a8c): Lean `v4.36.0-rc2`, Mathlib 1b1ccf4b0, Tau Ceti 2fd255d99.

Runs against earlier heads at the same pins: 7d5a38c9 (A 786457c7, C 6908d404, B 7cb889e0,
D e2b39535, E c716a691, RandomGraphs 1752d9dd), 43633a12 (A 35db8dff, C 68c5f0bf, B 31039c31,
D 8584c5d3, E 2dc7d398, RandomGraphs d6486263) and ec503a21 (A 6601a3b5, C 81fe877e, B cf843fd3,
D a25a711d, E 2dc7d398, RandomGraphs d6486263; with the substitution of B's stand-in). The
changes since are listed under [Changes for the revised heads](#changes-for-the-revised-heads).

Earlier runs of this check, at the old pins (Lean `v4.35.0-rc3`, Tau Ceti 358314d) and against the
pre-migration prototypes, are preserved on fork branches at 8a0783a8 (first run) and 19849b3d
(5 November rerun). They are not results at the current pins.

## What is checked

1. **No stand-in.** Every prototype imports Mathlib and Tau Ceti only, never another roadmap,
   and none carries a cross-roadmap stand-in. `prepare.py` asserts this before anything is
   compiled: it scans the six drafts for stand-in markers (`stand-in`, `Owner:`,
   `checked against revision`) and fails on any marker it does not expect (a marker naming only
   Tau Ceti or Mathlib as owner, a marked stand-in for a declaration absent at the pin, would be
   allowed and reported); it fails if any draft but A declares `pcSeparation`, or if any draft
   imports a `TauCetiRoadmap` module. At these heads the only marker is E's module docstring
   sentence "There are no stand-ins." B's draft mentions A's `pcSeparation` only in prose (its
   README quotes the supplier contract). Nothing is substituted: `prepare.py` copies the drafts
   verbatim.
2. **The moved boundary checks.** The 12 November conformance pass moved proved boundary checks
   (conventions, indexing adapters, generality and definition-fit checks against Tau Ceti and
   Mathlib) out of the drafts; each README keeps the statements. They are kept here, with their
   comments, as `checks/<Dir>.lean`, one per roadmap, each importing its own draft and using its
   roadmap's namespace under unchanged names. Each must compile with no `sorry` warning (some use
   a draft theorem that is itself admitted, for instance RandomGraphs' `exists_isQF_equivalent`,
   which applies the draft's `exists_computable_quantifierElimination`).

   | file | from | contents |
   |---|---|---|
   | `checks/InfinitaryModelExistence.lean` | A at 6601a3b5 | `model_existence_omitting` (set-of-types indexing over Tau Ceti's indexed family), `AElementary.fragmentType_comp` |
   | `checks/BorelEquivalenceRelations.lean` | C at 81fe877e | two examples: the Polish and perfect instances of Cantor and Baire space found with Tau Ceti imported; Alexandrov's theorem for `T6` spaces from Tau Ceti's form |
   | `checks/CountableStructureSpaces.lean` | B at cf843fd3 | nine theorems, among them `continuousSMul_relationalConfiguration`, `analyticSet_orbitRel_graph`, `saturated_iff_isFixedBlock` and `bfEquiv_of_selfStabilizesCompletely`, which `Integration.lean` uses |
   | `checks/CountableModelCounting.lean` | D at a25a711d | `measurableSet_isoSetoid_fin`, `encodeVia_mem_modelsOf`, the image forms of three Tau Ceti counting results, six Morley-code lemmas (among them `toStructure_morleyCode` and `isoSetoid_morleyCode_iff`, which `Integration.lean` uses) and `VaughtConjecture.cardinal` |
   | `checks/HanfNumbers.lean` | E at 2dc7d398 | six examples against E's definitions (`iteratedTwoPow`, `IsIndiscernibleOn`, `templateOf`, `morleySeed`, `hanfNumber`, `IsLω₁ωSmall`) |
   | `checks/RandomGraphs.lean` | RandomGraphs at d6486263 | six theorems (strong amalgamation, extension-budget boundary and direction, the QE adapter, the Scott-sentence boundary, `cardEq`) |

   `productGraphon_isolated_expectation`, an admitted computed value, stays in the RandomGraphs
   draft as a target; every declaration in `checks/RandomGraphs.lean` is proved.
3. **Compilation.** The six drafts compile unchanged, each with the pinned `lean`, into
   `_build/olean`; then the six check files; then `Integration.lean`. A file importing A, B, C, D
   and E together must compile too (`CoImport` in the output). C's prototype once redeclared root
   names that Tau Ceti declares (fixed in #1616 at 6908d404); since e4077268 it states only the
   two targets Tau Ceti lacks (`isSmooth_of_isClosed` and the analytic perfect set theorem) and
   imports Tau Ceti for the rest. The run fails, naming the declaration, if a clash returns.
4. **`Integration.lean`** imports A, B, C, D and E, the moved checks of B and D that it uses
   (`checks/CountableStructureSpaces.lean`, `checks/CountableModelCounting.lean`) and the Tau Ceti
   modules its examples cite, and has three parts:
   * name-resolution guards: `#assert_absent` fails if B declares `pcSeparation` (or if any
     stand-in removed before or during the migration is still declared),
     `#assert_only_declaration pcSeparation TauCetiRoadmap.InfinitaryModelExistence.pcSeparation`
     fails if any other declaration in the environment has that last name component, and
     `#assert_uses` fails unless a consumer declaration's type or proof term mentions the owner's
     constant, for instance D's `HasPerfectSetOfNonisoModelsOn` and Tau Ceti's
     `Setoid.HasPerfectAntichainOn` (C's interface, which C now cites as Tau Ceti's), D's
     `isoSetoid_morleyCode_iff` (a moved check) and `nonempty_morleyEquiv_iff` (A's), E's
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

   Section 1 also has the theorem `lopezEscobar_steps34`, the PC-separation boundary: B 5.3
   steps 3–4, with A's `pcSeparation` (imported from A directly) applied to the PC sentences of B's
   `exists_pcSentence`, turn tree representations of `B` and of its complement into a sentence
   `θ` with `B = modelsOf θ`, the conclusion of B's `lopez_escobar`. Its hypotheses are B's own
   earlier steps (the tree representations of Layer 3 and the disjointness of step 2, which uses
   invariance), not supplier lemmas. Like B's steps 1–4 it assumes countably many relation
   symbols; B's `lopez_escobar` now holds for every relational language, by B's step 0, which
   reduces to the countable sublanguage of the atoms a Borel set depends on.

   Step 0 itself is checked after section 1: `preimage_reductConfiguration_eq_modelsOf` shows,
   for relational `L₀`, `L` and `g : L₀ →ᴸ L` with no countability assumed, that the preimage of
   `B₀ = modelsOf φ₀` under Tau Ceti's `LHom.reductConfiguration` is
   `modelsOf (g.onBoundedFormulaInf φ₀)`, by Tau Ceti's `realize_sentenceInf_reductConfiguration`
   (a guard checks that it uses that lemma); and an example applies B's `lopezEscobar_iff` at an
   arbitrary relational `L`, with no countability instance in scope, to that preimage.

   Most suppliers are now Tau Ceti declarations that owner and consumer both use. Where a
   consumer's draft cites a Tau Ceti or Mathlib declaration directly, the example uses that
   declaration; an example is kept when it still checks a fit, a native theorem applied to the
   consumer's own setoids, model classes or codes. Every use where C supplies B or D is of this
   kind: C, B and D all cite the same Tau Ceti declarations, and C states none of them. The
   integration file contains no `sorry`, and no hypothesis stands in for a missing supplier lemma.

   Where an example uses a check that moved out of a draft (B's
   `continuousSMul_relationalConfiguration`, `analyticSet_orbitRel_graph`,
   `saturated_iff_isFixedBlock` and `bfEquiv_of_selfStabilizesCompletely` in sections 2 and 6; D's
   `measurableSet_isoSetoid_fin`, `isoSetoid_morleyCode_iff` and `toStructure_morleyCode` in
   sections 3 and 4 and in the guard on `isoSetoid_morleyCode_iff`), the name resolves to the
   declaration in `checks/<Dir>.lean`.

## What is not checked

* The prototypes' own `sorry`s. The build shows that the interfaces fit together as stated, not
  that the stated theorems are proved.

## Examples dropped in the port

The pre-migration `Integration.lean` had 26 examples in sections 1–6; 22 are ported, 4 dropped,
and 4 added (`lopezEscobar_steps34`, the two step-0 checks of B's general López–Escobar and the
E 5.6 graph-translation step), 26 in all. The checks
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

### 12 November conformance pass (this run)

Each draft keeps its targets and moves its proved boundary checks into a check file (see "What is
checked"); no statement that `Integration.lean` uses changed.

* **B** removes its `pcSeparation` stand-in (unused in the draft; its README keeps the supplier
  contract). So `substitute.py`, which asserted that the copy's statement was A's verbatim and
  deleted it from B', is replaced by `prepare.py`, which substitutes nothing and fails if any
  draft but A declares `pcSeparation`; B's draft is compiled as it is, and `Integration.lean`
  imports A for `pcSeparation` (as it already did). `#assert_only_declaration` is added beside the
  `#assert_absent` guard. `lopezEscobar_steps34` and the two step-0 checks compile unchanged. B
  also moves nine proved checks out (to `checks/CountableStructureSpaces.lean`), four of which
  the examples of sections 2 and 6 use.
* **D** moves `measurableSet_isoSetoid_fin`, `toStructure_morleyCode`, `isoSetoid_morleyCode_iff`
  and the rest of its proved checks out (to `checks/CountableModelCounting.lean`), deletes
  `countable_quotient_isoSetoidOn_iff` (no example used it) and drops its unused import of
  `TauCeti.ModelTheory.Counting.LanguageEquiv`. The two section 4 examples applying
  `LEquiv.lift_countableModelCount_onBoundedFormulaInf` and `L.smallPresentation`, which D's README
  still cites as Tau Ceti's, failed only for want of that import; `Integration.lean` now imports it
  directly. The examples are unchanged.
* **A**, **C**, **E** and **RandomGraphs** move their proved boundary checks out (two, two, six
  and six), none of which `Integration.lean` uses; RandomGraphs restores
  `productGraphon_isolated_expectation` to its draft as an admitted target. A's `pcSeparation` is
  unchanged.

No example was dropped or changed, and none needed a change to a draft. The examples' count is
unchanged (26, with `lopezEscobar_steps34` and `preimage_reductConfiguration_eq_modelsOf`).

### 10 November reviews (ec503a21)

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
* **B** follow-up cf843fd3 (docstrings and README: the general López–Escobar theorem is for the
  product σ-algebra) and **C** follow-up 81fe877e (README only) change no statement. Two checks of
  B's step 0 are added (see "What is checked").

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
grep -h '^\(public \)\?import TauCeti\.' integration/Integration.lean integration/checks/*.lean \
    TauCetiRoadmap/{InfinitaryModelExistence,BorelEquivalenceRelations,CountableStructureSpaces,CountableModelCounting,HanfNumbers,RandomGraphs}/Suggested.lean \
  | awk '{print $NF}' | sort -u | xargs lake build
integration/run.sh
```

The second step builds (or downloads) the Tau Ceti modules the files import; no roadmap target is
built by `lake`. `run.sh` then runs `prepare.py` and compiles, in order, A, C, B, D, E,
RandomGraphs, the six files `checks/<Dir>.lean` (as
`TauCetiRoadmap.Integration.Checks.<Dir>`) and `Integration.lean`, each with the pinned `lean` and
`LEAN_PATH=_build/olean:<lake LEAN_PATH>`. Files with a `module` header need no extra flag:
`lean -o X.olean` also writes the `X.olean.server` and `X.olean.private` parts that their importers
read. It prints one line per file with its exit code and number of `sorry` warnings, followed by
any other compiler output, then the result of the co-import check, and ends with `ALL COMPILED`
or `SOME FILE FAILED`; a `sorry` warning in a check file or in `Integration.lean` fails the run.
Outputs go to `integration/_build/`:

* `src/`, the copies compiled (all verbatim);
* `olean/`, the compiled files;
* `logs/`, one compiler log per file (`Checks.<Dir>.out` for the check files).

`LAKE_ROOT=<checkout> integration/run.sh` reuses another checkout's built `.lake`, provided it has
the same `lake-manifest.json`.

The result at these heads:

| file | exit | `sorry` warnings |
|---|---|---|
| InfinitaryModelExistence | 0 | 7 |
| BorelEquivalenceRelations | 0 | 2 |
| CountableStructureSpaces | 0 | 38 |
| CountableModelCounting | 0 | 36 |
| HanfNumbers | 0 | 29 |
| RandomGraphs | 0 | 74 |
| checks/InfinitaryModelExistence | 0 | 0 |
| checks/BorelEquivalenceRelations | 0 | 0 |
| checks/CountableStructureSpaces | 0 | 0 |
| checks/CountableModelCounting | 0 | 0 |
| checks/HanfNumbers | 0 | 0 |
| checks/RandomGraphs | 0 | 0 |
| Integration | 0 | 0 |

The co-import check passes. Declaring a `pcSeparation` in B's namespace in a scratch file that
imports `Integration.lean` makes both `#assert_absent` and `#assert_only_declaration` fail, and
adding `theorem pcSeparation` to a scratch copy of B's draft makes `prepare.py` fail before
anything is compiled.

When a draft changes, merge the heads onto `main` here again and rerun. A check that a draft
moves out goes to `checks/<Dir>.lean`, and `Integration.lean` imports it if an example uses it.
