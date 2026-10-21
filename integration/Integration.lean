import TauCetiRoadmap.InfinitaryModelExistence.Suggested
import TauCetiRoadmap.BorelEquivalenceRelations.Suggested
import TauCetiRoadmap.CountableStructureSpaces.Suggested
import TauCetiRoadmap.CountableModelCounting.Suggested
import TauCetiRoadmap.HanfNumbers.Suggested

/-!
# Supplier-substitution integration check

All five prototypes are imported in their substituted form (consumers' stand-ins deleted, names
resolved to the owners' declarations). For each cross-roadmap edge, an `example` applies the
supplier's actual theorem to the consumer's actual objects and produces the conclusion the
consumer's README says it needs. Proof terms are supplier applications plus small glue; nothing
here is `sorry`, and no hypothesis stands in for a missing supplier lemma: every cross-roadmap
use is discharged by a declaration of one of the five prototypes.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u v w

open FirstOrder FirstOrder.Language MeasureTheory Cardinal Set Descriptive
open scoped Pointwise

/-! ## 0. Name-resolution guards

`#assert_absent n` fails if `n` is still declared (a stand-in survived); `#assert_uses d c` fails
unless the type or value of `d` mentions the constant `c` (the consumer really elaborates against
the owner's declaration, not against a copy). -/

section Guards
open Lean Elab Command

elab "#assert_absent " id:ident : command => do
  if (← getEnv).contains id.getId then
    throwError "stand-in {id.getId} is still declared"

elab "#assert_uses " d:ident c:ident : command => do
  let some ci := (← getEnv).find? d.getId | throwError "unknown declaration {d.getId}"
  let inTy := ci.type.getUsedConstants.contains c.getId
  let inVal := (ci.value?.map fun e => e.getUsedConstants.contains c.getId).getD false
  unless inTy || inVal do throwError "{d.getId} does not mention {c.getId}"

end Guards

-- B: stand-ins gone, `analyticSet_iff_exists_pc` is stated with A's `PCMem`.
#assert_absent TauCetiRoadmap.CountableStructureSpaces.PCMem
#assert_absent TauCetiRoadmap.CountableStructureSpaces.pcSeparation
#assert_uses TauCetiRoadmap.CountableStructureSpaces.analyticSet_iff_exists_pc
  TauCetiRoadmap.InfinitaryModelExistence.PCMem

-- D: every B, A and Tau Ceti stand-in gone.
#assert_absent TauCetiRoadmap.CountableModelCounting.RelQueryOn
#assert_absent TauCetiRoadmap.CountableModelCounting.StructureSpaceOn
#assert_absent TauCetiRoadmap.CountableModelCounting.StructureSpace
#assert_absent TauCetiRoadmap.CountableModelCounting.StructureSpaceOn.toStructure
#assert_absent TauCetiRoadmap.CountableModelCounting.StructureSpaceOn.ofStructure
#assert_absent TauCetiRoadmap.CountableModelCounting.StructureSpaceOn.encodeVia
#assert_absent TauCetiRoadmap.CountableModelCounting.structureIsoSetoidOn
#assert_absent TauCetiRoadmap.CountableModelCounting.structureIsoSetoid
#assert_absent TauCetiRoadmap.CountableModelCounting.modelsOf
#assert_absent TauCetiRoadmap.CountableModelCounting.bfEquivSetoid
#assert_absent TauCetiRoadmap.CountableModelCounting.StabilizesCompletely
#assert_absent TauCetiRoadmap.CountableModelCounting.scottHeight
#assert_absent TauCetiRoadmap.CountableModelCounting.exs
#assert_absent TauCetiRoadmap.CountableModelCounting.onBoundedFormulaInf
#assert_absent TauCetiRoadmap.CountableModelCounting.realize_onBoundedFormulaInf
#assert_absent TauCetiRoadmap.CountableModelCounting.morleyize
#assert_absent TauCetiRoadmap.CountableModelCounting.lhomMorleyize
#assert_absent TauCetiRoadmap.CountableModelCounting.morleyExpansion
#assert_absent TauCetiRoadmap.CountableModelCounting.morleyize_isRelational
#assert_absent TauCetiRoadmap.CountableModelCounting.countable_relations_morleyize
#assert_absent TauCetiRoadmap.CountableModelCounting.nonempty_morleyEquiv_iff
#assert_uses TauCetiRoadmap.CountableModelCounting.morleyCode
  TauCetiRoadmap.InfinitaryModelExistence.morleyize
#assert_uses TauCetiRoadmap.CountableModelCounting.toStructure_morleyCode
  TauCetiRoadmap.InfinitaryModelExistence.morleyExpansion
-- D elaborates against B's, A's and C's declarations.
#assert_uses TauCetiRoadmap.CountableModelCounting.isoSetoidOn
  TauCetiRoadmap.CountableStructureSpaces.structureIsoSetoidOn
#assert_uses TauCetiRoadmap.CountableModelCounting.classOf
  TauCetiRoadmap.CountableStructureSpaces.StructureSpaceOn.encodeVia
#assert_uses TauCetiRoadmap.CountableModelCounting.bfEquivSetoidOn
  TauCetiRoadmap.CountableStructureSpaces.bfEquivSetoid
#assert_uses TauCetiRoadmap.CountableModelCounting.isIsolatingRank_scottHeight
  TauCetiRoadmap.CountableStructureSpaces.scottHeight
#assert_uses TauCetiRoadmap.CountableModelCounting.infiniteSentence
  TauCetiRoadmap.InfinitaryModelExistence.exs
#assert_uses TauCetiRoadmap.CountableModelCounting.lift_countableModelCount_onBoundedFormulaInf
  TauCetiRoadmap.InfinitaryModelExistence.onBoundedFormulaInf
#assert_uses TauCetiRoadmap.CountableModelCounting.HasPerfectSetOfNonisoModelsOn
  TauCetiRoadmap.BorelEquivalenceRelations.HasPerfectAntichainOn
#assert_uses TauCetiRoadmap.CountableModelCounting.IsThinOnNatModels
  TauCetiRoadmap.BorelEquivalenceRelations.IsThinOn
#assert_uses TauCetiRoadmap.CountableModelCounting.not_hasCantorAntichainOn_of_bfScattered
  TauCetiRoadmap.BorelEquivalenceRelations.HasCantorAntichainOn

-- E: stand-ins gone, statements use A's declarations.
#assert_absent TauCetiRoadmap.HanfNumbers.onBoundedFormulaInf
#assert_absent TauCetiRoadmap.HanfNumbers.infinitaryType
#assert_absent TauCetiRoadmap.HanfNumbers.realizedTypes
#assert_uses TauCetiRoadmap.HanfNumbers.exists_emSource_of_forall_beth
  TauCetiRoadmap.InfinitaryModelExistence.onBoundedFormulaInf
#assert_uses TauCetiRoadmap.HanfNumbers.IsLω₁ωSmall
  TauCetiRoadmap.InfinitaryModelExistence.realizedTypes

namespace TauCetiRoadmap.Integration

open TauCetiRoadmap.InfinitaryLogic

/-! ## 1. A → B: `PCMem`, `pcSeparation` in the López–Escobar hard direction (B 5.3) -/

section AtoB

open TauCetiRoadmap.CountableStructureSpaces
open TauCetiRoadmap.InfinitaryModelExistence (PCMem pcSeparation)

variable {L : FirstOrder.Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- **B 5.3 step 3**, with A's `pcSeparation` at `L₁ = L₂ = pcWitnessLanguage` (in
`Language.{0, 0}`) and `L` in arbitrary universes, models in `Type` (`w = 0`): the disjointness
of the two projective classes on countable nonempty structures gives one `θ` whose model class
contains every code in the first class and no code in the second. -/
example (ψ₀ ψ₁ : Sentenceω (L.sum pcWitnessLanguage))
    (hdisj : ∀ (M : Type) [L.Structure M] [Nonempty M] [Countable M],
      PCMem LHom.sumInl ψ₀ M → ¬ PCMem LHom.sumInl ψ₁ M) :
    ∃ θ : Sentenceω L,
      (∀ c : StructureSpace L, (letI : L.Structure ℕ := c.toStructure; PCMem LHom.sumInl ψ₀ ℕ) →
        c ∈ (modelsOf θ : Set (StructureSpace L))) ∧
      (∀ c : StructureSpace L, (letI : L.Structure ℕ := c.toStructure; PCMem LHom.sumInl ψ₁ ℕ) →
        c ∉ (modelsOf θ : Set (StructureSpace L))) := by
  obtain ⟨θ, h₀, h₁⟩ := pcSeparation.{u, v, 0, 0, 0, 0, 0} ψ₀ ψ₁ hdisj
  exact ⟨θ, fun c hc => @h₀ ℕ c.toStructure _ hc, fun c hc => @h₁ ℕ c.toStructure _ hc⟩

/-- **B 5.3 step 4**: B's `exists_pcSentence` (completeness clause, standard witness on `ℕ`)
puts every code with a branch into A's `PCMem` for the PC sentence, through Mathlib's
sum structure, so step 3's `θ` holds at every code of `B`. -/
example (T : tree (Bool × ℕ)) (ψ : Sentenceω (L.sum pcWitnessLanguage))
    (hψ : ∀ (c : StructureSpace L) (g : ℕ → ℕ), (fun n => (queryCode c n, g n)) ∈ body T →
        letI : L.Structure ℕ := c.toStructure
        letI : pcWitnessLanguage.Structure ℕ := standardWitness g
        ψ.Realize ℕ)
    (c : StructureSpace L) (g : ℕ → ℕ) (hc : (fun n => (queryCode c n, g n)) ∈ body T) :
    letI : L.Structure ℕ := c.toStructure; PCMem LHom.sumInl ψ ℕ := by
  letI : L.Structure ℕ := c.toStructure
  letI : pcWitnessLanguage.Structure ℕ := standardWitness g
  exact ⟨Language.sumStructure L pcWitnessLanguage ℕ, inferInstance, hψ c g hc⟩

end AtoB

/-! ## 2. C → B: Gδ subspaces, `AnalyticSet.prod`, invariant separation -/

section CtoB

open TauCetiRoadmap.CountableStructureSpaces
open TauCetiRoadmap.BorelEquivalenceRelations (exists_invariant_measurableSet_separating)

variable {L : FirstOrder.Language.{u, v}}

/-- **B Layer 2, Gδ model classes** (B's README target `polishSpace_modelsOf_of_isGδ` and its
standard-Borel form): C's `IsGδ.polishSpace` and `IsGδ.standardBorelSpace` applied to B's
`isGδ_modelsOf_toInf_alls`, with B's own Polish/Borel instances on `StructureSpace L`. -/
example [L.IsRelational] [Countable (Σ l, L.Relations l)] {n : ℕ}
    (ψ : L.BoundedFormula Empty n) (hψ : ψ.IsExistential) :
    PolishSpace (modelsOf (toInf (ι := ℕ) ψ.alls) : Set (StructureSpace L)) ∧
      StandardBorelSpace (modelsOf (toInf (ι := ℕ) ψ.alls) : Set (StructureSpace L)) :=
  ⟨(isGδ_modelsOf_toInf_alls ψ hψ).polishSpace,
    (isGδ_modelsOf_toInf_alls ψ hψ).standardBorelSpace⟩

/-- **B Layer 1, `analyticSet_iUnion_smul`**, re-derived as B's README says: the saturation is the
image of `univ ×ˢ A` under the continuous action, analytic by C's `AnalyticSet.prod`
(with B's `polishSpace_perm`, `continuousSMul_structureSpaceOn`). -/
example [Countable (Σ l, L.Relations l)] {A : Set (StructureSpace L)} (hA : AnalyticSet A) :
    AnalyticSet (⋃ σ : Equiv.Perm ℕ, σ • A) := by
  haveI : PolishSpace (Equiv.Perm ℕ) := polishSpace_perm
  haveI : ContinuousSMul (Equiv.Perm ℕ) (StructureSpace L) := continuousSMul_structureSpaceOn
  have h := (((isClosed_univ (X := Equiv.Perm ℕ)).analyticSet).prod hA).image_of_continuous
    (continuous_smul (M := Equiv.Perm ℕ) (X := StructureSpace L))
  convert h using 1
  ext c
  simp only [mem_iUnion, mem_image, mem_prod, mem_univ, true_and, Prod.exists, Set.mem_smul_set]

/-- **B 6.1, `invariant_analytic_separation`**, obtained from C's
`exists_invariant_measurableSet_separating` on B's `StructureSpace L` (Polish and Borel by B's
instances under `[Countable (Σ l, L.Relations l)]`) with `E` the orbit relation. -/
example [Countable (Σ l, L.Relations l)] {A B : Set (StructureSpace L)} (hA : AnalyticSet A)
    (hB : AnalyticSet B) (hinv : ActionInvariant B) (hd : Disjoint A B) :
    ∃ C, A ⊆ C ∧ Disjoint B C ∧ MeasurableSet C ∧ ActionInvariant C := by
  obtain ⟨C, hCm, hCsat, hAC, hCB⟩ := exists_invariant_measurableSet_separating
    (MulAction.orbitRel (Equiv.Perm ℕ) (StructureSpace L)) analyticSet_orbitRel_graph hA hB
    (saturated_iff_actionInvariant.mpr hinv) hd
  exact ⟨C, hAC, hCB.symm, hCm, saturated_iff_actionInvariant.mp hCsat⟩

end CtoB

/-! ## 3. B, C → D: Silver on model classes, cardinality form, Morley-code transport -/

section BCtoD

open TauCetiRoadmap.CountableStructureSpaces TauCetiRoadmap.CountableModelCounting
open TauCetiRoadmap.BorelEquivalenceRelations (countable_or_hasCantorAntichainOn_of_measurableSet
  hasCantorAntichainOn_iff_hasPerfectAntichainOn mk_quotient_le_aleph0_or_eq_continuum
  hasCantorAntichainOn_image_iff HasCantorAntichainOn)

variable {L : FirstOrder.Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- **D Layer 3, one level** (`countable_bfClasses_or_hasPerfectSet`): C's
`countable_or_hasCantorAntichainOn_of_measurableSet` with `X = StructureSpace L`,
`A = modelsOf φ` (B's `measurableSet_modelsOf`), `R = structureIsoSetoid L`,
`F = bfEquivSetoidOn φ β` (Borel by B's `measurableSet_bfEquivSetoid`, refined by `R` by B's
`structureIsoSetoid_le_bfEquivSetoid`), then C's Cantor-to-perfect passage. -/
example (φ : Sentenceω L) {β : Ordinal.{0}} (hβ : β < Ordinal.omega 1) :
    Countable (Quotient (bfEquivSetoidOn φ β)) ∨ HasPerfectSetOfNonisoModelsOn ℕ φ := by
  have hF : MeasurableSet {p : ↥(modelsOf φ : Set (StructureSpace L)) ×
      ↥(modelsOf φ : Set (StructureSpace L)) | bfEquivSetoidOn φ β p.1 p.2} :=
    (measurableSet_bfEquivSetoid hβ).preimage
      (measurable_subtype_coe.prodMap measurable_subtype_coe)
  rcases countable_or_hasCantorAntichainOn_of_measurableSet (measurableSet_modelsOf (α := ℕ) φ)
      (structureIsoSetoid L) (bfEquivSetoidOn φ β)
      (fun _ _ h => structureIsoSetoid_le_bfEquivSetoid β h) hF with h | h
  · exact Or.inl h
  · exact Or.inr (hasCantorAntichainOn_iff_hasPerfectAntichainOn.mp h)

/-- **D Layer 0, `HasPerfectlyManyCountableModels.countableModelCount_eq`, one tier**: "with
(E0), a perfect set gives `𝔠 ≤ #(Quotient (isoSetoidOn α φ))`". C's
`hasCantorAntichainOn_iff_hasPerfectAntichainOn` (Polish by B's instances) turns D's perfect set
into a Cantor antichain in the ambient space; C's `HasCantorAntichainOn.continuum_le_mk_quotient`
then needs it on the subtype `modelsOf φ` for the restricted relation `isoSetoidOn α φ`, which is
C's `hasCantorAntichainOn_subtype_iff`. -/
example {α : Type} [Countable α] (φ : Sentenceω L) (h : HasPerfectSetOfNonisoModelsOn α φ) :
    𝔠 ≤ #(Quotient (isoSetoidOn α φ)) := by
  exact (TauCetiRoadmap.BorelEquivalenceRelations.hasCantorAntichainOn_subtype_iff.mpr
    (hasCantorAntichainOn_iff_hasPerfectAntichainOn.mpr h)).continuum_le_mk_quotient

/-- **D Layer 0, finite tiers** (`countable_or_hasPerfectSetOfNonisoModelsOn_fin`): the same C
theorem on `StructureSpaceOn L (Fin n)` (Polish by B's instances) with `R = F` = isomorphism,
Borel by D's `measurableSet_structureIsoSetoidOn_fin`. -/
example (φ : Sentenceω L) (n : ℕ) :
    Countable (Quotient (isoSetoidOn (Fin n) φ)) ∨ HasPerfectSetOfNonisoModelsOn (Fin n) φ := by
  have hF : MeasurableSet {p : ↥(modelsOf φ : Set (StructureSpaceOn L (Fin n))) ×
      ↥(modelsOf φ : Set (StructureSpaceOn L (Fin n))) | isoSetoidOn (Fin n) φ p.1 p.2} :=
    (measurableSet_structureIsoSetoidOn_fin n).preimage
      (measurable_subtype_coe.prodMap measurable_subtype_coe)
  rcases countable_or_hasCantorAntichainOn_of_measurableSet
      (measurableSet_modelsOf (α := Fin n) φ) (structureIsoSetoidOn L (Fin n))
      (isoSetoidOn (Fin n) φ) (fun _ _ h => h) hF with h | h
  · exact Or.inl h
  · exact Or.inr (hasCantorAntichainOn_iff_hasPerfectAntichainOn.mp h)

/-- **D Layer 2, `..._of_bounded'`** (the cardinality form (E2)): C's
`mk_quotient_le_aleph0_or_eq_continuum` on the standard Borel space `modelsOf φ` (B's
`standardBorelSpace_modelsOf`), for isomorphism, Borel under bounded Scott height by B's
`measurableSet_iso_inter_of_scottHeight_le`. -/
example {φ : Sentenceω L} {β : Ordinal.{0}} (hβ : β < Ordinal.omega 1)
    (hbound : ∀ c ∈ (modelsOf φ : Set (StructureSpace L)),
      (letI : L.Structure ℕ := c.toStructure; scottHeight (L := L) ℕ) ≤ β) :
    #(Quotient (isoSetoidOn ℕ φ)) ≤ ℵ₀ ∨ #(Quotient (isoSetoidOn ℕ φ)) = 𝔠 := by
  haveI := standardBorelSpace_modelsOf (L := L) φ
  have hE : MeasurableSet {p : ↥(modelsOf φ : Set (StructureSpace L)) ×
      ↥(modelsOf φ : Set (StructureSpace L)) | isoSetoidOn ℕ φ p.1 p.2} := by
    have hm := measurable_subtype_coe (p := (· ∈ (modelsOf φ : Set (StructureSpace L))))
    have := (measurableSet_iso_inter_of_scottHeight_le hβ hbound).preimage (hm.prodMap hm)
    convert this using 1
    ext ⟨c, d⟩
    simp only [mem_ofPred_eq, mem_preimage, Prod.map, mem_inter_iff, mem_prod, c.2, d.2, and_true]
    rfl
  exact mk_quotient_le_aleph0_or_eq_continuum _ hE

/-- **D Layer 1, `isIsolatingRank_scottHeight`, the `isolates` field**: B's
`nonempty_equiv_of_bfEquiv_of_scottHeight_le` at `M = N = ℕ` with the two decoded structures,
`β = scottHeight` of the first (in `Ordinal.{0}`, matching B's `bfEquivSetoid`). -/
example (c d : StructureSpace L)
    (h : bfEquivSetoid (letI : L.Structure ℕ := c.toStructure; scottHeight (L := L) ℕ) c d) :
    structureIsoSetoid L c d :=
  @nonempty_equiv_of_bfEquiv_of_scottHeight_le L _ ℕ ℕ c.toStructure d.toStructure _ _ _ le_rfl h

/-- **D 4g, Morleyization transport**: C's `hasCantorAntichainOn_image_iff` with
`X = StructureSpace L`, `Y = StructureSpace (morleyize L Φ)` (A's Morleyization), applied to D's
actual `morleyCode` with D's `measurableEmbedding_morleyCode` and
`structureIsoSetoid_morleyCode_iff`; the instance on the Morleyized relation symbols is A's
`countable_relations_morleyize`. No hypothesis stands in for any part of the interface. -/
example (Φ : Set (Σ n, BoundedFormulaω L Empty n)) (hΦ : Φ.Countable)
    (K : Set (StructureSpace L)) :
    HasCantorAntichainOn (structureIsoSetoid (InfinitaryModelExistence.morleyize L Φ))
        (morleyCode Φ '' K) ↔ HasCantorAntichainOn (structureIsoSetoid L) K := by
  haveI := InfinitaryModelExistence.countable_relations_morleyize (L := L) hΦ
  exact hasCantorAntichainOn_image_iff (measurableEmbedding_morleyCode Φ hΦ)
    (structureIsoSetoid_morleyCode_iff Φ) K

/-- D's own transport theorem is, after substitution, exactly the conclusion above. -/
example (Φ : Set (Σ n, BoundedFormulaω L Empty n)) (hΦ : Φ.Countable)
    (K : Set (StructureSpace L)) :
    HasCantorAntichainOn (structureIsoSetoid (InfinitaryModelExistence.morleyize L Φ))
        (morleyCode Φ '' K) ↔ HasCantorAntichainOn (structureIsoSetoid L) K :=
  hasCantorAntichainOn_image_morleyCode_iff Φ hΦ K

/-- D's decoding agreement is stated against A's canonical expansion. -/
example (Φ : Set (Σ n, BoundedFormulaω L Empty n)) (c : StructureSpace L) :
    (morleyCode Φ c).toStructure =
      @InfinitaryModelExistence.morleyExpansion L Φ ℕ c.toStructure :=
  toStructure_morleyCode Φ c

/-- A's `countable_relations_morleyize` supplies the instance the previous example assumes. -/
example (Φ : Set (Σ n, BoundedFormulaω L Empty n)) (hΦ : Φ.Countable) :
    Countable (Σ l, (InfinitaryModelExistence.morleyize L Φ).Relations l) :=
  InfinitaryModelExistence.countable_relations_morleyize hΦ

end BCtoD

/-! ## 4. A → D: language maps, small presentation, fragments, Morleyization -/

section AtoD

open TauCetiRoadmap.CountableStructureSpaces TauCetiRoadmap.CountableModelCounting
open TauCetiRoadmap.InfinitaryModelExistence (onBoundedFormulaInf realize_onBoundedFormulaInf
  smallPresentation smallPresentationEquiv realize_smallPresentation Fragment GeneratedFrom
  fragmentType morleyize lhomMorleyize morleyExpansion)

variable {L : FirstOrder.Language.{u, v}}

/-- Glue: a relational language has countably many function symbols (none). Needed to form A's
`smallPresentation L`, which demands `[Countable (Σ n, L.Functions n)]`. -/
instance countable_functions_of_isRelational [L.IsRelational] : Countable (Σ n, L.Functions n) :=
  inferInstance

/-- **D Layer 0 transport (M0, M4)**: D's `lift_countableModelCount_onBoundedFormulaInf`
instantiated at A's `smallPresentationEquiv L`, moving the count to `Language.{0, 0}`. -/
example [L.IsRelational] [Countable (Σ l, L.Relations l)] (φ : Sentenceω L) :
    Cardinal.lift.{0} (countableModelCount φ) =
      Cardinal.lift.{v} (countableModelCount
        (onBoundedFormulaInf (smallPresentationEquiv L).toLHom φ)) :=
  lift_countableModelCount_onBoundedFormulaInf (smallPresentationEquiv L) φ

/-- **D Layer 0 transport**, the realization step on codes, by A's `realize_smallPresentation`:
`c ∈ modelsOf φ` iff the reinterpreted structure realizes the transported sentence. -/
example [L.IsRelational] [Countable (Σ l, L.Relations l)] (φ : Sentenceω L)
    (c : StructureSpace L) :
    c ∈ (modelsOf φ : Set (StructureSpace L)) ↔
      letI : L.Structure ℕ := c.toStructure
      @SentenceInf.Realize (smallPresentation L) ℕ
        (onBoundedFormulaInf (smallPresentationEquiv L).toLHom φ) ℕ
        ((smallPresentationEquiv L).invLHom.reduct ℕ) := by
  letI : L.Structure ℕ := c.toStructure
  exact (realize_smallPresentation φ Empty.elim Fin.elim0).symm

/-- **D Layer 5, universes** (`vaughtConjecture_iff_forall_universe`): D's `VaughtConjecture`,
quantified over `Language.{0, 0}`, applies to A's `smallPresentation L` of a countable relational
`L` in any universe, through A's instances `smallPresentation_isRelational` and
`countable_relations_smallPresentation`. -/
example [L.IsRelational] [Countable (Σ l, L.Relations l)] (h : VaughtConjecture)
    (φ : Sentenceω L) :
    HasVaughtDichotomy (onBoundedFormulaInf (smallPresentationEquiv L).toLHom φ) :=
  h (smallPresentation L) _

/-- **D 4f, fragment spectra**: A's `Fragment.generated_countable` on the range of a list of
sentences. -/
example (θ : ℕ → Sentenceω L) :
    (InfinitaryModelExistence.Fragment.generated
      (range fun k => (⟨0, θ k⟩ : Σ n, BoundedFormulaω L Empty n))).toSet.Countable :=
  InfinitaryModelExistence.Fragment.generated_countable (countable_range _)

/-- **D 4f**: "the arity-0 spectrum of `Fragment.generated` of the range of a list `θ` determines
its truth sequences", with A's `fragmentType` read in decoded codes and D's `sentenceTheory`. -/
example [L.IsRelational] (θ : ℕ → Sentenceω L) (c d : StructureSpace L)
    (h : @fragmentType L (InfinitaryModelExistence.Fragment.generated
        (range fun k => (⟨0, θ k⟩ : Σ n, BoundedFormulaω L Empty n))) ℕ c.toStructure 0
          Fin.elim0 =
      @fragmentType L (InfinitaryModelExistence.Fragment.generated
        (range fun k => (⟨0, θ k⟩ : Σ n, BoundedFormulaω L Empty n))) ℕ d.toStructure 0
          Fin.elim0) :
    sentenceTheory θ c = sentenceTheory θ d := by
  funext k
  have hmem : (⟨0, θ k⟩ : Σ n, BoundedFormulaω L Empty n) ∈
      (InfinitaryModelExistence.Fragment.generated
        (range fun k => (⟨0, θ k⟩ : Σ n, BoundedFormulaω L Empty n))).toSet :=
    GeneratedFrom.base ⟨k, rfl⟩
  have hk := Set.ext_iff.mp h (θ k)
  have hcd : c ∈ (modelsOf (θ k) : Set (StructureSpace L)) ↔
      d ∈ (modelsOf (θ k) : Set (StructureSpace L)) :=
    ⟨fun hc => (hk.mp ⟨hmem, hc⟩).2, fun hd => (hk.mpr ⟨hmem, hd⟩).2⟩
  by_cases hc : c ∈ (modelsOf (θ k) : Set (StructureSpace L))
  · simp [sentenceTheory, hc, hcd.mp hc]
  · simp [sentenceTheory, hc, mt hcd.mpr hc]

/-- **D 4g, canonical expansion**: A's `realize_onBoundedFormulaInf` along A's
`lhomMorleyize Φ` in A's `morleyExpansion Φ M`. The expansion instance is glue: A's prototype
does not declare `(lhomMorleyize Φ).IsExpansionOn M` for `morleyExpansion`, but it holds by
`rfl`. -/
example (Φ : Set (Σ n, BoundedFormulaω L Empty n)) (M : Type w) [L.Structure M]
    (φ : Sentenceω L) :
    @SentenceInf.Realize (morleyize L Φ) ℕ (onBoundedFormulaInf (lhomMorleyize Φ) φ) M
        (morleyExpansion Φ M) ↔ SentenceInf.Realize φ M := by
  letI := morleyExpansion Φ M
  haveI := InfinitaryModelExistence.isExpansionOn_morleyExpansion Φ M
  exact realize_onBoundedFormulaInf (lhomMorleyize Φ) φ _ _

end AtoD

/-! ## 5. A → E: reducts, isolators, countable `A`-elementary substructures, fragments -/

section AtoE

open TauCetiRoadmap.HanfNumbers
open TauCetiRoadmap.InfinitaryModelExistence (Fragment GeneratedFrom AElementary
  exists_countable_aElementary_substructure exists_isolatingFormula infinitaryType realizedTypes
  onBoundedFormulaInf realize_onBoundedFormulaInf)

variable {L : FirstOrder.Language.{u, v}}

/-- **E 3.4, the reduct step** of `exists_model_card_eq_of_forall_beth`: the EM model realizes the
image `onBoundedFormulaInf g φ` (E's `exists_emSource_of_forall_beth`, with `L'` in
`Language.{0, 0}`); its reduct along `g` realizes `φ` by A's `realize_onBoundedFormulaInf`. -/
example {L' : FirstOrder.Language.{0, 0}} (g : L →ᴸ L') (φ : Sentenceω L) (E : Type w)
    [L'.Structure E] (hE : SentenceInf.Realize (onBoundedFormulaInf g φ) E) :
    @SentenceInf.Realize L ℕ φ E (g.reduct E) := by
  letI := g.reduct E
  exact (realize_onBoundedFormulaInf g φ _ _).mp hE

/-- **E 2.1**: E's `IsEMSource` closure fields are exactly A's `Fragment` closure fields, so `Γ`
is the underlying set of an A-`Fragment` (as E's docstring claims). -/
example {Γ : Set (Σ n, BoundedFormulaω L Empty n)} {N : Type w} [L.Structure N] {a : ℕ → N}
    (h : IsEMSource Γ N a) : ∃ F : Fragment L, F.toSet = Γ :=
  ⟨{ toSet := Γ
     imp_left_mem := fun hm => (h.imp_mem _ _ hm).1
     imp_right_mem := fun hm => (h.imp_mem _ _ hm).2
     all_mem := fun hm => h.all_mem _ hm
     iInf_mem := fun hm k => h.iInf_mem _ k hm
     iSup_mem := fun hm k => h.iSup_mem _ k hm }, rfl⟩

/-- **E 5.4, countable companion seed**: for E's `IsLω₁ωSmall M` (stated with A's
`realizedTypes`), A's `exists_isolatingFormula` gives an isolator for each realized type, A's
`Fragment.generated_countable` a countable fragment containing them, and A's
`exists_countable_aElementary_substructure` with `X = ∅` a countable `A`-elementary substructure
(function symbols: none, `L` relational). -/
example [L.IsRelational] [Countable (Σ l, L.Relations l)] (M : Type w) [L.Structure M]
    (hM : IsLω₁ωSmall (L := L) M) :
    ∃ (F : Fragment L) (N : L.Substructure M), F.toSet.Countable ∧
      (∀ (n : ℕ) (a : Fin n → M), ∃ χ : BoundedFormulaω L Empty n,
        (⟨n, χ⟩ : Σ n, BoundedFormulaω L Empty n) ∈ F.toSet ∧
        ∀ b : Fin n → M, χ.Realize Empty.elim b ↔
          infinitaryType (L := L) M b = infinitaryType M a) ∧
      AElementary F N.subtype ∧ Countable N := by
  have hiso : ∀ (n : ℕ) (p : realizedTypes (L := L) M n), ∃ χ : BoundedFormulaω L Empty n,
      ∀ b : Fin n → M, χ.Realize Empty.elim b ↔ infinitaryType (L := L) M b = p.1 := by
    rintro n ⟨p, a, rfl⟩
    exact exists_isolatingFormula (hM n) a
  choose χ hχ using hiso
  let S : Set (Σ n, BoundedFormulaω L Empty n) :=
    ⋃ n, range fun p : realizedTypes (L := L) M n => (⟨n, χ n p⟩ : Σ n, BoundedFormulaω L Empty n)
  have hS : S.Countable :=
    countable_iUnion fun n => by haveI := (hM n).to_subtype; exact countable_range _
  have hF := InfinitaryModelExistence.Fragment.generated_countable hS
  obtain ⟨N, -, hN, hNc⟩ := exists_countable_aElementary_substructure
    (InfinitaryModelExistence.Fragment.generated S) hF (X := (∅ : Set M)) countable_empty
  exact ⟨_, N, hF, fun n a => ⟨χ n ⟨infinitaryType M a, a, rfl⟩,
    GeneratedFrom.base (mem_iUnion.2 ⟨n, _, rfl⟩), hχ n _⟩, hN, hNc⟩

end AtoE

end TauCetiRoadmap.Integration
