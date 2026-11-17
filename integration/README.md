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
six heads as revised in the 12 November conformance pass, (da6e0abc) with the heads corrected
for the 13 November reviews, (3d833598) with the heads revised in the 14 November fix round, and
(903386e6) with the heads revised for the 14 November evening reviews, (3cd62208) with B's 6.1
strengthening, (ed6085b4) with the heads revised for the 16 November reviews, and (ceb4b1b4) with
RandomGraphs as revised for the 17 November review, so
`TauCetiRoadmap/<Dir>/` here is what was checked.

| roadmap | pull request | head checked |
|---|---|---|
| InfinitaryModelExistence (A) | follow-up [#1615](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1615) to [#1315](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1315) | 8c93fecf |
| BorelEquivalenceRelations (C) | follow-up [#1616](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1616) to [#1317](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1317) | b4d6f21d (unchanged since the 13 November round) |
| CountableStructureSpaces (B) | [#1316](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1316) | 60f81ce3 |
| CountableModelCounting (D) | follow-up [#2012](https://github.com/TauCetiProject/TauCetiRoadmap/pull/2012) to [#1318](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1318) | b79bc76c |
| HanfNumbers (E) | [#1319](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1319) | 84bb2ec3 |
| RandomGraphs | [#1223](https://github.com/TauCetiProject/TauCetiRoadmap/pull/1223) | 74db85ee |

RandomGraphs is compiled with the others, with its moved checks. It supplies no cross-roadmap use
and, since the 14 November fix round, consumes one: B's fixed-assignment graph events (B's
Layer 2, built on B's decoding identity `toStructure_toRelationalConfiguration`; section 7 of
`Integration.lean`).

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
   | `checks/CountableStructureSpaces.lean` | B at cf843fd3 and 27e4b31f | nine theorems, among them `continuousSMul_relationalConfiguration`, `analyticSet_orbitRel_graph`, `saturated_iff_isFixedBlock` and `bfEquiv_of_selfStabilizesCompletely`, which `Integration.lean` uses; and, from the 14 November fix round, three corollaries proved in one term from B's targets and Tau Ceti (`internalScottRank_le_succ_scottHeight`, `orbitRank_le_scottHeight`, `exists_uniform_bfSeparation_prod`) |
   | `checks/CountableModelCounting.lean` | D at a25a711d | `measurableSet_isoSetoid_fin`, `encodeVia_mem_modelsOf`, the image forms of three Tau Ceti counting results, six Morley-code lemmas (among them `toStructure_morleyCode` and `isoSetoid_morleyCode_iff`, which `Integration.lean` uses) and `VaughtConjecture.cardinal` |
   | `checks/HanfNumbers.lean` | E at 2dc7d398 | six examples against E's definitions (`iteratedTwoPow`, `IsIndiscernibleOn`, `templateOf`, `morleySeed`, `hanfNumber`, `IsLω₁ωSmall`) |
   | `checks/RandomGraphs.lean` | RandomGraphs at 0a7e6ae5 | its own spelling of `StrongAmalgamation` (the draft no longer declares it) and eight theorems (strong amalgamation, extension-budget boundary and direction, the QE adapter, the Scott-sentence boundary, `cardEq`, isomorphism invariance of satisfaction, the graphon-mixture integral), and four examples instantiating the general formula-coding theorems (the graph language; a language with a unary function symbol, with a round trip) |

   Every declaration in `checks/RandomGraphs.lean` is proved (`exists_isQF_equivalent` through
   the draft's admitted `exists_computable_quantifierElimination`); its README keeps the isolated-
   vertex expectation, which the draft no longer states.
3. **Compilation.** The six drafts compile unchanged, each with the pinned `lean`, into
   `_build/olean`; then the six check files; then `Integration.lean`. A file importing A, B, C, D
   and E together must compile too (`CoImport` in the output). C's prototype once redeclared root
   names that Tau Ceti declares (fixed in #1616 at 6908d404); since e4077268 it states only the
   two targets Tau Ceti lacks (`isSmooth_of_isClosed` and the analytic perfect set theorem) and
   imports Tau Ceti for the rest. The run fails, naming the declaration, if a clash returns.
4. **`Integration.lean`** imports A, B, C, D, E and RandomGraphs, the moved checks of B and D that it uses
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
     `IsLω₁ωSmall` and `realizedTypes` (A's), `lopezEscobar_steps34` (below) and A's
     `pcSeparation`, and `invariant_analytic_separation_of_sublanguage` (below) and B's
     `exists_countable_sublanguage_separating`;
   * one `example` for each cross-roadmap use, sections 1–5: A → B (`pcSeparation` and
     `LHom.PCMem` in López–Escobar), C → B (Gδ subspaces, `AnalyticSet.prod`, invariant
     separation), B, C → D (Silver on model classes, the cardinality form, Scott height,
     Morley-code transport), A → D (language maps, the small presentation, fragments,
     Morleyization), A → E (reducts, isolators, countable `A`-elementary substructures, and the
     graph translation of A's Layer 6 in E 5.6);
   * section 7, B → RandomGraphs: the fixed-assignment graph event RandomGraphs consumes from B's
     Layer 2 (a first-order graph formula on any countable carrier, at fixed assignments) follows,
     by the route B's README gives, from B's `toStructure_toRelationalConfiguration` and Tau
     Ceti's `RelationalConfiguration.measurableSet_setOf_realize`,
     `SimpleGraph.measurable_toRelationalConfiguration` and `BoundedFormula.realize_toInf`;
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

   Section 2 checks B 6.1 in two steps. `invariant_analytic_separation_of_countable` is the
   countable case, from Tau Ceti's `Setoid.exists_invariant_measurableSet_separating` for the orbit
   relation with B's `analyticSet_orbitRel_graph` and `saturated_iff_isFixedBlock`.
   `invariant_analytic_separation_of_sublanguage` derives B's `invariant_analytic_separation` for
   an arbitrary `L`, with no countability instance in scope: B's admitted
   `exists_countable_sublanguage_separating` gives a countable `R` whose sublanguage
   `symbSublang ∅ R` separates the reducts of `A` and `B`, the countable case separates them there
   (with `countable_relations_symbSublang`), and Tau Ceti's `LHom.continuous_reductConfiguration`,
   `measurable_reductConfiguration` and `reductConfiguration_perm_smul` carry analyticity,
   measurability and invariance across the reduct. A guard checks that it uses B's lemma.

   Most suppliers are now Tau Ceti declarations that owner and consumer both use. Where a
   consumer's draft cites a Tau Ceti or Mathlib declaration directly, the example uses that
   declaration; an example is kept when it still checks a fit, a native theorem applied to the
   consumer's own setoids, model classes or codes. Every use where C supplies B or D is of this
   kind: C, B and D all cite the same Tau Ceti declarations, and C states none of them. The
   integration file contains no `sorry`, and no hypothesis stands in for a missing supplier lemma.
   One hypothesis is a consumer's own requirement: the E 5.6 example takes E's relational 5.4
   equivalence (small structures and complete sentences), which E's README states and E's draft
   no longer declares, as the hypothesis `h54` at the graph language, with 5.4's relational and
   countability hypotheses as instance binders that Tau Ceti's instances discharge.

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
and 5 added (`lopezEscobar_steps34`, the two step-0 checks of B's general López–Escobar, the
E 5.6 graph-translation step and, in the 14 November fix round, the B → RandomGraphs graph-event
check of section 7), 27 in all. The checks
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

### 17 November review of RandomGraphs (this run)

* **RandomGraphs** names its construction targets `radoQE` and `decideRado` in the README and rewrites two docstrings and its module docstring (4798017b, 74db85ee); no declaration changed. The results are those of the previous run.

### 16 November reviews

* **A** adds a `#check` of Tau Ceti's `Fragment.generated_countable` to its draft (8c93fecf); B, D and RandomGraphs change README prose only; C and E are unchanged. No example or check changed, and the results are those of the previous run.

### 14 November evening reviews

* **RandomGraphs** removes its `measurableSet_setOf_realize_graph` (417aecc9) and consumes the
  fixed-assignment graph events from B's Layer 2. Section 7 no longer takes its statement from
  RandomGraphs' draft by `type_of%`: it states the event as RandomGraphs uses it (a first-order
  graph formula on any countable carrier) and proves it by B's route, with the same proof. The
  check `bind_infiniteSampleLawOnSpace_satisfies` in `checks/RandomGraphs.lean` now takes the
  measurability of `{G | Satisfies G φ}` from the section of RandomGraphs' joint target
  `measurableSet_realize_jointly` at the empty assignments. RandomGraphs adds the admitted
  target `eventually_exists_finite_model`, which no example uses.
* **A**, **B** (apart from its 6.1 change below), **D** and **E** change only README prose,
  docstrings and one instance docstring (D); no declaration any example uses changed. **C** is
  unchanged.
* **B** (e1083ae7–f17c9478, merged at 3cd62208) states `invariant_analytic_separation` and
  `exists_sentence_separating` without `[∀ n, Countable (L.Relations n)]`, through the new
  admitted target `exists_countable_sublanguage_separating` (disjoint analytic classes have
  disjoint reducts to the sublanguage of a countable set of relation symbols); its README adds
  two Layer 4 negative controls for uncountably many symbols and the finite and empty carriers of
  the fixed-assignment graph events. In section 2 the countable-case example becomes the theorem
  `invariant_analytic_separation_of_countable`, and the new theorem
  `invariant_analytic_separation_of_sublanguage` derives B's statement for every language from
  it, B's new lemma and Tau Ceti's reduct API, with a guard on B's lemma. B has 36 `sorry`
  warnings (35 before).

Sections 2 and 7 and the one RandomGraphs check changed as above; no example was dropped.

### 14 November fix round

* **E** removes its relational `isLω₁ωSmall_iff_exists_isCompleteSentence` from the draft
  (8e3245ab; it stays a README requirement, 5.4). The E 5.6 example applied it to the graph
  language; it now takes that equivalence as the hypothesis `h54`, named and documented as E's
  README 5.4 requirement (the relational statement with its hypotheses as instance binders, at
  `L.graphLanguage`), and still checks that Tau Ceti's instances meet 5.4's hypotheses on the
  graph language and that `backTranslate` and `realize_backTranslate` carry the complete `θ` to
  the sentence `σ` of E 5.6 in the original language.
* **B** moves `internalScottRank_le_succ_scottHeight`, `orbitRank_le_scottHeight` and
  `exists_uniform_bfSeparation_prod` out of its draft (27ba43a7, 067dda28); they are appended,
  proved, to `checks/CountableStructureSpaces.lean`. B adds the Layer 0 target
  `toStructure_toRelationalConfiguration` and restores `measurableSet_setOf_realize_graph` (an
  Lω₁ω sentence event on `SimpleGraph ℕ`) as a Layer 2 target proved from it (52c32254).
* **RandomGraphs** consumes B's `toStructure_toRelationalConfiguration` for its own
  fixed-assignment graph events; section 7 is added to check that use, and `Integration.lean` now
  imports RandomGraphs' draft (it compiles together with A–E). RandomGraphs drops
  `StrongAmalgamation`, `satisfies_iso` and other unused declarations from its draft and renames
  `GraphAlphabet` to `FormulaAlphabet`; `checks/RandomGraphs.lean` is replaced by its new set of
  checks, which spells `StrongAmalgamation` itself.
* **A**, **D** and **E** otherwise change their drafts only by removing or adding targets no
  example uses (A declares `Fragment.slice`; D removes its admitted acceptance block). **C** is
  unchanged.

The E 5.6 example changed as above and one example was added (section 7); none was dropped, and
none needed a change to a draft.

### 12 November conformance pass

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
| CountableStructureSpaces | 0 | 36 |
| CountableModelCounting | 0 | 33 |
| HanfNumbers | 0 | 24 |
| RandomGraphs | 0 | 75 |
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
