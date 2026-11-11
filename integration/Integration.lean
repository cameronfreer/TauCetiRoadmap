import TauCetiRoadmap.InfinitaryModelExistence.Suggested
import TauCetiRoadmap.BorelEquivalenceRelations.Suggested
import TauCetiRoadmap.CountableStructureSpaces.Suggested
import TauCetiRoadmap.CountableModelCounting.Suggested
import TauCetiRoadmap.HanfNumbers.Suggested
import TauCeti.MeasureTheory.Constructions.Polish.GDelta
import TauCeti.SetTheory.Descriptive.Silver
import TauCeti.SetTheory.Descriptive.InvariantSeparation
import TauCeti.ModelTheory.Infinitary.GraphTranslation.BackTranslate

/-!
# Supplier-substitution integration check

The prototypes of InfinitaryModelExistence (A), BorelEquivalenceRelations (C),
CountableStructureSpaces (B, in its substituted form B'), CountableModelCounting (D) and
HanfNumbers (E) are imported together. In B' the one
remaining cross-roadmap stand-in, `pcSeparation`, is deleted and the name resolves to A's
declaration. For each cross-roadmap use, an `example` (or a named theorem, where a guard needs a
name) applies the supplier's theorem to the consumer's own objects and produces the conclusion
the consumer's README needs.

After the migration to native imports most suppliers are Tau Ceti declarations at the pin, which
both the owner and the consumer use; such a use is kept when it checks that the supplier's
statement fits the consumer's objects, and dropped (see `README.md`) when it would only restate
one declaration.

C now states only the two targets Tau Ceti lacks (`isSmooth_of_isClosed` and the analytic perfect
set theorem), neither of which B or D consumes, and cites Tau Ceti for everything else. Where C
supplies B or D, the uses are therefore checked against Tau Ceti's declarations, which C, B and D
all cite. C is imported so that a clash between its declarations and the others' would fail
here.

Nothing here is `sorry`, and no hypothesis stands in for a missing supplier lemma. Hypotheses
that are a consumer's own earlier step (the disjointness step 2 of B 5.3, the tree
representations of B Layer 3) are named as such.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
-- Theorems are elaborated synchronously so that `#assert_uses` sees their proof terms.
set_option Elab.async false

universe u v w u' v'

open FirstOrder FirstOrder.Language MeasureTheory Cardinal Set Descriptive
open TauCeti
open TauCeti.RelationalConfiguration (modelsOf isoSetoid isoSetoidOn bfEquivSetoid bfEquivSetoidOn)
open scoped Pointwise

/-! ## 0. Name-resolution guards

`#assert_absent n` fails if `n` is still declared (a stand-in survived); `#assert_uses d c` fails
unless the type or value (for a theorem, its proof term) of `d` mentions the constant `c`: the
consumer really elaborates against the owner's declaration, not against a copy. -/

section Guards
open Lean Elab Command

elab "#assert_absent " id:ident : command => do
  if (← getEnv).contains id.getId then
    throwError "stand-in {id.getId} is still declared"

elab "#assert_uses " d:ident c:ident : command => do
  let env ← getEnv
  unless env.contains c.getId do throwError "unknown owner constant {c.getId}"
  let some ci := env.find? d.getId | throwError "unknown declaration {d.getId}"
  let inTy := ci.type.getUsedConstants.contains c.getId
  let inVal := ((ci.value? (allowOpaque := true)).map fun e =>
    e.getUsedConstants.contains c.getId).getD false
  unless inTy || inVal do throwError "{d.getId} does not mention {c.getId}"

end Guards

-- B': the `pcSeparation` stand-in is gone; projective classes are A's interface `LHom.PCMem`
-- (implemented in Tau Ceti), and the López–Escobar check below uses A's `pcSeparation`
-- (`#assert_uses` after `lopezEscobar_steps34`).
#assert_absent TauCetiRoadmap.CountableStructureSpaces.pcSeparation
#assert_absent TauCetiRoadmap.CountableStructureSpaces.PCMem
#assert_uses TauCetiRoadmap.CountableStructureSpaces.analyticSet_iff_exists_pc
  FirstOrder.Language.LHom.PCMem

-- D: the stand-ins of the earlier, pre-migration runs stay gone.
#assert_absent TauCetiRoadmap.CountableModelCounting.RelQueryOn
#assert_absent TauCetiRoadmap.CountableModelCounting.StructureSpaceOn
#assert_absent TauCetiRoadmap.CountableModelCounting.StructureSpace
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
#assert_absent TauCetiRoadmap.CountableModelCounting.HasPerfectAntichainOn
#assert_absent TauCetiRoadmap.CountableModelCounting.HasCantorAntichainOn
#assert_absent TauCetiRoadmap.CountableModelCounting.IsThinOn
-- D elaborates against the interfaces B, C and A own, as Tau Ceti implements them at the pin.
#assert_uses TauCetiRoadmap.CountableModelCounting.HasPerfectSetOfNonisoModelsOn
  Setoid.HasPerfectAntichainOn
#assert_uses TauCetiRoadmap.CountableModelCounting.IsThinOnNatModels Setoid.IsThinOn
#assert_uses TauCetiRoadmap.CountableModelCounting.not_hasCantorAntichainOn_of_bfScattered
  Setoid.HasCantorAntichainOn
#assert_uses TauCetiRoadmap.CountableModelCounting.HasPerfectSetOfNonisoModelsOn
  TauCeti.RelationalConfiguration.modelsOf
#assert_uses TauCetiRoadmap.CountableModelCounting.countable_bfClasses_or_hasPerfectSet
  TauCeti.RelationalConfiguration.bfEquivSetoidOn
#assert_uses TauCetiRoadmap.CountableModelCounting.morleyCode FirstOrder.Language.morleyExpansion
#assert_uses TauCetiRoadmap.CountableModelCounting.isoSetoid_morleyCode_iff
  FirstOrder.Language.nonempty_morleyEquiv_iff

-- E: the stand-ins of the earlier runs stay gone; statements use A's interfaces.
#assert_absent TauCetiRoadmap.HanfNumbers.onBoundedFormulaInf
#assert_absent TauCetiRoadmap.HanfNumbers.infinitaryType
#assert_absent TauCetiRoadmap.HanfNumbers.realizedTypes
#assert_uses TauCetiRoadmap.HanfNumbers.exists_emSource_of_forall_beth
  FirstOrder.Language.LHom.onBoundedFormulaInf
#assert_uses TauCetiRoadmap.HanfNumbers.IsEMSource FirstOrder.Language.Fragment
#assert_uses TauCetiRoadmap.HanfNumbers.IsLω₁ωSmall FirstOrder.Language.realizedTypes

namespace TauCetiRoadmap.Integration

/-! ## 1. A → B: `pcSeparation` in the López–Escobar hard direction (B 5.3) -/

section AtoB

open TauCetiRoadmap.CountableStructureSpaces (pcWitnessLanguage standardWitness queryCode body
  exists_pcSentence)

variable {L : FirstOrder.Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]

/-- **B 5.3 step 3**, with A's `pcSeparation` at `L₁ = L₂ = pcWitnessLanguage` (in
`Language.{0, 0}`), `L` in arbitrary universes and models in `Type` (`w = 0`): disjointness of the
two projective classes on countable nonempty structures gives one `θ` whose model class contains
every code in the first class and no code in the second. -/
example (ψ₀ ψ₁ : (L.sum pcWitnessLanguage).Sentenceω)
    (hdisj : ∀ (M : Type) [L.Structure M] [Nonempty M] [Countable M],
      LHom.PCMem LHom.sumInl ψ₀ M → ¬ LHom.PCMem LHom.sumInl ψ₁ M) :
    ∃ θ : L.Sentenceω,
      (∀ c : RelationalConfiguration L ℕ,
        (letI : L.Structure ℕ := c.toStructure; LHom.PCMem LHom.sumInl ψ₀ ℕ) →
          c ∈ (modelsOf θ : Set (RelationalConfiguration L ℕ))) ∧
      (∀ c : RelationalConfiguration L ℕ,
        (letI : L.Structure ℕ := c.toStructure; LHom.PCMem LHom.sumInl ψ₁ ℕ) →
          c ∉ (modelsOf θ : Set (RelationalConfiguration L ℕ))) := by
  obtain ⟨θ, h₀, h₁⟩ := InfinitaryModelExistence.pcSeparation.{u, v, 0, 0, 0, 0, 0} ψ₀ ψ₁ hdisj
  exact ⟨θ, fun c hc => RelationalConfiguration.mem_modelsOf.2 (@h₀ ℕ c.toStructure _ hc),
    fun c hc hm => @h₁ ℕ c.toStructure _ hc (RelationalConfiguration.mem_modelsOf.1 hm)⟩

/-- **B 5.3 step 4**: B's `exists_pcSentence` (completeness clause, standard witness on `ℕ`) puts
every code with a branch into the projective class `LHom.PCMem` of the PC sentence, through
Mathlib's sum structure. -/
example (T : tree (Bool × ℕ)) (ψ : (L.sum pcWitnessLanguage).Sentenceω)
    (hψ : ∀ (c : RelationalConfiguration L ℕ) (g : ℕ → ℕ),
      (fun n => (queryCode c n, g n)) ∈ body T →
        letI : L.Structure ℕ := c.toStructure
        letI : pcWitnessLanguage.Structure ℕ := standardWitness g
        SentenceInf.Realize ψ ℕ)
    (c : RelationalConfiguration L ℕ) (g : ℕ → ℕ) (hc : (fun n => (queryCode c n, g n)) ∈ body T) :
    letI : L.Structure ℕ := c.toStructure; LHom.PCMem LHom.sumInl ψ ℕ := by
  letI : L.Structure ℕ := c.toStructure
  letI : pcWitnessLanguage.Structure ℕ := standardWitness g
  exact LHom.pcMem_of_isExpansionOn (hψ c g hc)

/-- **B 5.3 steps 3–4 together: the PC-separation boundary.** Given tree representations `T₀` of
`B` and `T₁` of its complement (B Layer 3) and the disjointness of the projective classes of their
PC sentences (B 5.3 step 2, B's own proof obligation, which uses invariance), A's `pcSeparation`
applied to the PC sentences of B's `exists_pcSentence` yields a sentence whose model class is
`B`: the conclusion of B's `lopez_escobar`. Steps 1–4 assume countably many relation symbols, as
here; B's `lopez_escobar` holds for every relational language, by B's step 0, which reduces to the
countable sublanguage of the atoms a Borel set depends on. -/
theorem lopezEscobar_steps34 (B : Set (RelationalConfiguration L ℕ)) (T₀ T₁ : tree (Bool × ℕ))
    (hT₀ : ∀ c, c ∈ B ↔ ∃ g : ℕ → ℕ, (fun n => (queryCode c n, g n)) ∈ body T₀)
    (hT₁ : ∀ c, c ∉ B ↔ ∃ g : ℕ → ℕ, (fun n => (queryCode c n, g n)) ∈ body T₁)
    (hdisj : ∀ ψ₀ ψ₁ : (L.sum pcWitnessLanguage).Sentenceω,
      (∀ (M : Type) [L.Structure M] [pcWitnessLanguage.Structure M], SentenceInf.Realize ψ₀ M →
        ∃ e : M ≃ ℕ, ∃ g : ℕ → ℕ, (fun n => (queryCode (e.encodeVia (L := L)) n, g n)) ∈ body T₀) →
      (∀ (M : Type) [L.Structure M] [pcWitnessLanguage.Structure M], SentenceInf.Realize ψ₁ M →
        ∃ e : M ≃ ℕ, ∃ g : ℕ → ℕ, (fun n => (queryCode (e.encodeVia (L := L)) n, g n)) ∈ body T₁) →
      ∀ (M : Type) [L.Structure M] [Nonempty M] [Countable M],
        LHom.PCMem LHom.sumInl ψ₀ M → ¬ LHom.PCMem LHom.sumInl ψ₁ M) :
    ∃ θ : L.Sentenceω, B = modelsOf θ := by
  obtain ⟨ψ₀, hc₀, hs₀⟩ := exists_pcSentence.{u, v, 0} (L := L) T₀
  obtain ⟨ψ₁, hc₁, hs₁⟩ := exists_pcSentence.{u, v, 0} (L := L) T₁
  obtain ⟨θ, h₀, h₁⟩ :=
    InfinitaryModelExistence.pcSeparation.{u, v, 0, 0, 0, 0, 0} ψ₀ ψ₁
      (hdisj ψ₀ ψ₁ (fun M _ _ => hs₀ M) (fun M _ _ => hs₁ M))
  refine ⟨θ, Set.ext fun c => ?_⟩
  letI : L.Structure ℕ := c.toStructure
  rw [RelationalConfiguration.mem_modelsOf]
  constructor
  · intro hc
    obtain ⟨g, hg⟩ := (hT₀ c).1 hc
    letI : pcWitnessLanguage.Structure ℕ := standardWitness g
    exact h₀ ℕ (LHom.pcMem_of_isExpansionOn (hc₀ c g hg))
  · intro hθ
    by_contra hc
    obtain ⟨g, hg⟩ := (hT₁ c).1 hc
    letI : pcWitnessLanguage.Structure ℕ := standardWitness g
    exact h₁ ℕ (LHom.pcMem_of_isExpansionOn (hc₁ c g hg)) hθ

end AtoB

/-! ### B 5.3 step 0: López–Escobar for every relational language

B states López–Escobar (`lopez_escobar`, `lopezEscobar_iff`, ...) for every relational `L`, with no
countability hypothesis. Its step 0 reduces to the countable sublanguage `L₀` of the atoms a set
measurable for the product σ-algebra depends on: with `g : L₀ →ᴸ L` the inclusion, `B` is the
preimage of an `L₀`-class `B₀` under Tau Ceti's `LHom.reductConfiguration`, and
`realize_sentenceInf_reductConfiguration` carries a sentence for `B₀` to one for `B`. -/

section StepZero

variable {L₀ : FirstOrder.Language.{u', v'}} {L : FirstOrder.Language.{u, v}}
  [L₀.IsRelational] [L.IsRelational]

/-- **B 5.3 step 0, the transfer.** If `B₀ = modelsOf φ₀` for codes of the sublanguage `L₀`, then
the preimage of `B₀` under the reduct along `g : L₀ →ᴸ L` is the model class of the image of `φ₀`
along `g`, by Tau Ceti's `LHom.realize_sentenceInf_reductConfiguration`. No countability of
either language is used. -/
theorem preimage_reductConfiguration_eq_modelsOf (g : L₀ →ᴸ L)
    {B₀ : Set (RelationalConfiguration L₀ ℕ)} {φ₀ : L₀.Sentenceω} (hB₀ : B₀ = modelsOf φ₀) :
    g.reductConfiguration ⁻¹' B₀ =
      (modelsOf (g.onBoundedFormulaInf φ₀) : Set (RelationalConfiguration L ℕ)) := by
  subst hB₀
  ext c
  rw [Set.mem_preimage, RelationalConfiguration.mem_modelsOf,
    RelationalConfiguration.mem_modelsOf]
  exact (g.realize_sentenceInf_reductConfiguration c φ₀).symm

/-- **B's `lopezEscobar_iff` at an arbitrary relational language.** With only `[L.IsRelational]`
in scope (no countability instance for `L` or `L₀`), B's headline applies to the class obtained
by step 0, whose sentence the transfer above supplies: the preimage of a model class of `L₀` is
Borel and isomorphism invariant. -/
example (g : L₀ →ᴸ L) (φ₀ : L₀.Sentenceω) :
    MeasurableSet (g.reductConfiguration ⁻¹' (modelsOf φ₀ : Set (RelationalConfiguration L₀ ℕ))) ∧
      RelationalConfiguration.IsomorphismInvariant
        (g.reductConfiguration ⁻¹' (modelsOf φ₀ : Set (RelationalConfiguration L₀ ℕ))) :=
  CountableStructureSpaces.lopezEscobar_iff.mpr
    ⟨_, preimage_reductConfiguration_eq_modelsOf g rfl⟩

end StepZero

/-! ## 2. C → B: Gδ subspaces, `AnalyticSet.prod`, invariant separation

B's README names these as BorelEquivalenceRelations results "as implemented at the pin":
Mathlib's `IsGδ.polishSpace`, Tau Ceti's `IsGδ.standardBorelSpace`, `AnalyticSet.prod` and
`Setoid.exists_invariant_measurableSet_separating`, which C's README also cites as Tau Ceti's. -/

section CtoB

open TauCetiRoadmap.CountableStructureSpaces (isGδ_modelsOf_toInf_alls
  continuousSMul_relationalConfiguration analyticSet_orbitRel_graph saturated_iff_isFixedBlock)

variable {L : FirstOrder.Language.{u, v}}

/-- **B Layer 2, Gδ model classes**: `IsGδ.polishSpace` and `IsGδ.standardBorelSpace` applied to
B's `isGδ_modelsOf_toInf_alls`, with the Polish and Borel structure of the coding space. -/
example [L.IsRelational] [∀ n, Countable (L.Relations n)] {n : ℕ}
    (ψ : L.BoundedFormula Empty n) (hψ : ψ.IsExistential) :
    PolishSpace (modelsOf (ψ.alls.toInf (ι := ℕ)) : Set (RelationalConfiguration L ℕ)) ∧
      StandardBorelSpace
        (modelsOf (ψ.alls.toInf (ι := ℕ)) : Set (RelationalConfiguration L ℕ)) :=
  ⟨(isGδ_modelsOf_toInf_alls ψ hψ).polishSpace,
    (isGδ_modelsOf_toInf_alls ψ hψ).standardBorelSpace⟩

/-- **B Layer 1, `analyticSet_iUnion_smul`**, derived as B's README says: the saturation is the
image of `univ ×ˢ A` under the continuous action, analytic by `AnalyticSet.prod` (with the
Polish group `Equiv.Perm ℕ` and B's `continuousSMul_relationalConfiguration`). -/
example [∀ n, Countable (L.Relations n)] {A : Set (RelationalConfiguration L ℕ)}
    (hA : AnalyticSet A) : AnalyticSet (⋃ σ : Equiv.Perm ℕ, σ • A) := by
  haveI : ContinuousSMul (Equiv.Perm ℕ) (RelationalConfiguration L ℕ) :=
    continuousSMul_relationalConfiguration
  have h := (((isClosed_univ (X := Equiv.Perm ℕ)).analyticSet).prod hA).image_of_continuous
    (continuous_smul (M := Equiv.Perm ℕ) (X := RelationalConfiguration L ℕ))
  convert h using 1
  ext c
  simp only [mem_iUnion, mem_image, mem_prod, mem_univ, true_and, Prod.exists, Set.mem_smul_set]

/-- **B 6.1, `invariant_analytic_separation`**, from
`Setoid.exists_invariant_measurableSet_separating` on B's coding space with `E` the orbit relation
(analytic by B's `analyticSet_orbitRel_graph`) and B's `saturated_iff_isFixedBlock`. -/
example [∀ n, Countable (L.Relations n)] {A B : Set (RelationalConfiguration L ℕ)}
    (hA : AnalyticSet A) (hB : AnalyticSet B) (hinv : MulAction.IsFixedBlock (Equiv.Perm ℕ) B)
    (hd : Disjoint A B) :
    ∃ C, A ⊆ C ∧ Disjoint B C ∧ MeasurableSet C ∧ MulAction.IsFixedBlock (Equiv.Perm ℕ) C := by
  set E := MulAction.orbitRel (Equiv.Perm ℕ) (RelationalConfiguration L ℕ)
  have hsat : Quotient.mk E ⁻¹' (Quotient.mk E '' B) = B := saturated_iff_isFixedBlock.mpr hinv
  have hd' : Disjoint (Quotient.mk E '' A) (Quotient.mk E '' B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hb
    exact Set.disjoint_left.mp hd ha (hsat ▸ hb)
  obtain ⟨C, hCm, hCsat, hAC, hCB⟩ :=
    Setoid.exists_invariant_measurableSet_separating E analyticSet_orbitRel_graph hA hB hd'
  exact ⟨C, hAC, hCB.symm, hCm, saturated_iff_isFixedBlock.mp hCsat⟩

end CtoB

/-! ## 3. B, C → D: Silver on model classes, the cardinality form, Morley-code transport

D consumes C's perfect-set vocabulary (E0), Silver relative to a Borel subset (E1) and its
cardinality form (E2) as Tau Ceti implements them, and B's Borelness, refinement and Scott-height
results; the examples apply them to D's own setoids and model classes. C's README cites the same
Tau Ceti declarations. -/

section BCtoD

open TauCetiRoadmap.CountableModelCounting (HasPerfectSetOfNonisoModelsOn
  measurableSet_isoSetoid_fin morleyCode measurableEmbedding_morleyCode isoSetoid_morleyCode_iff)

variable {L : FirstOrder.Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]

/-- **D Layer 3, one level** (`countable_bfClasses_or_hasPerfectSet`): Silver relative to the
Borel set `modelsOf φ` (`RelationalConfiguration.measurableSet_modelsOf`) for
`R = isoSetoid L ℕ` and `F = bfEquivSetoidOn ℕ φ β` (Borel by
`measurableSet_setOf_bfEquivSetoid`, refined by `R` by `isoSetoid_le_bfEquivSetoid`: B's
interface (S2), (S4), which B and D both cite as Tau Ceti's), then the Cantor-to-perfect
passage into D's `HasPerfectSetOfNonisoModelsOn`. -/
example (φ : L.Sentenceω) {β : Ordinal.{0}} (hβ : β < Ordinal.omega 1) :
    Countable (Quotient (bfEquivSetoidOn ℕ φ β)) ∨ HasPerfectSetOfNonisoModelsOn ℕ φ := by
  have hF : MeasurableSet {p : ↥(modelsOf φ : Set (RelationalConfiguration L ℕ)) ×
      ↥(modelsOf φ : Set (RelationalConfiguration L ℕ)) | bfEquivSetoidOn ℕ φ β p.1 p.2} :=
    (RelationalConfiguration.measurableSet_setOf_bfEquivSetoid hβ).preimage
      (measurable_subtype_coe.prodMap measurable_subtype_coe)
  rcases Setoid.countable_or_hasCantorAntichainOn_of_measurableSet
      (RelationalConfiguration.measurableSet_modelsOf (V := ℕ) φ) (isoSetoid L ℕ)
      (bfEquivSetoidOn ℕ φ β)
      (fun _ _ h => RelationalConfiguration.isoSetoid_le_bfEquivSetoid β h) hF with h | h
  · exact Or.inl h
  · exact Or.inr (Setoid.hasCantorAntichainOn_iff_hasPerfectAntichainOn.mp h)

/-- **D Layer 0, `HasPerfectlyManyCountableModels.countableModelCount_eq`, one tier**: a perfect
set gives `𝔠 ≤ #(Quotient (isoSetoidOn α φ))`. The perfect set of D's definition becomes a Cantor
antichain in the coding space, then one on the subtype `modelsOf φ` for the restricted relation
`isoSetoidOn α φ`, whose quotient has at least continuum many classes. -/
example {α : Type} [Countable α] (φ : L.Sentenceω) (h : HasPerfectSetOfNonisoModelsOn α φ) :
    𝔠 ≤ #(Quotient (isoSetoidOn α φ)) :=
  (Setoid.hasCantorAntichainOn_subtype_iff.mpr
    (Setoid.hasCantorAntichainOn_iff_hasPerfectAntichainOn.mpr h)).continuum_le_mk_quotient

/-- **D Layer 0, finite tiers** (`countable_or_hasPerfectSetOfNonisoModelsOn_fin`): the same
Silver theorem on the coding space on `Fin n` with `R = F` = isomorphism, Borel by D's
`measurableSet_isoSetoid_fin`. -/
example (φ : L.Sentenceω) (n : ℕ) :
    Countable (Quotient (isoSetoidOn (Fin n) φ)) ∨ HasPerfectSetOfNonisoModelsOn (Fin n) φ := by
  have hF : MeasurableSet {p : ↥(modelsOf φ : Set (RelationalConfiguration L (Fin n))) ×
      ↥(modelsOf φ : Set (RelationalConfiguration L (Fin n))) | isoSetoidOn (Fin n) φ p.1 p.2} :=
    (measurableSet_isoSetoid_fin n).preimage
      (measurable_subtype_coe.prodMap measurable_subtype_coe)
  rcases Setoid.countable_or_hasCantorAntichainOn_of_measurableSet
      (RelationalConfiguration.measurableSet_modelsOf (V := Fin n) φ) (isoSetoid L (Fin n))
      (isoSetoidOn (Fin n) φ) (fun _ _ h => h) hF with h | h
  · exact Or.inl h
  · exact Or.inr (Setoid.hasCantorAntichainOn_iff_hasPerfectAntichainOn.mp h)

/-- Glue for (E2): B's `measurableSet_iso_inter_of_scottHeight_le`, restricted to the subtype
`modelsOf φ`, is the Borelness of D's `isoSetoidOn ℕ φ`. -/
private theorem measurableSet_isoSetoidOn_of_scottHeight_le {φ : L.Sentenceω} {β : Ordinal.{0}}
    (hβ : β < Ordinal.omega 1)
    (hbound : ∀ c ∈ (modelsOf φ : Set (RelationalConfiguration L ℕ)),
      (letI : L.Structure ℕ := c.toStructure; scottHeight (L := L) ℕ) ≤ β) :
    MeasurableSet {p : ↥(modelsOf φ : Set (RelationalConfiguration L ℕ)) ×
      ↥(modelsOf φ : Set (RelationalConfiguration L ℕ)) | isoSetoidOn ℕ φ p.1 p.2} := by
  have hm := measurable_subtype_coe (p := (· ∈ (modelsOf φ : Set (RelationalConfiguration L ℕ))))
  have := (CountableStructureSpaces.measurableSet_iso_inter_of_scottHeight_le hβ hbound).preimage
    (hm.prodMap hm)
  convert this using 1
  ext ⟨c, d⟩
  simp only [mem_ofPred_eq, mem_preimage, Prod.map, mem_inter_iff, mem_prod, c.2, d.2, and_true]
  rfl

/-- **D Layer 2, the cardinality form (E2)** under bounded Scott height: the cardinality form of
Silver's theorem on the standard Borel space `modelsOf φ` (Tau Ceti's `standardBorelSpace_modelsOf`
instance), for isomorphism, Borel there by B's `measurableSet_iso_inter_of_scottHeight_le`. -/
example {φ : L.Sentenceω} {β : Ordinal.{0}} (hβ : β < Ordinal.omega 1)
    (hbound : ∀ c ∈ (modelsOf φ : Set (RelationalConfiguration L ℕ)),
      (letI : L.Structure ℕ := c.toStructure; scottHeight (L := L) ℕ) ≤ β) :
    #(Quotient (isoSetoidOn ℕ φ)) ≤ ℵ₀ ∨ #(Quotient (isoSetoidOn ℕ φ)) = 𝔠 := by
  exact Setoid.mk_quotient_le_aleph0_or_eq_continuum _
    (measurableSet_isoSetoidOn_of_scottHeight_le hβ hbound)

/-- **D Layer 1, the `isolates` field of `TauCeti.isIsolatingRank_scottHeight`** (which D now
cites directly): `TauCeti.nonempty_equiv_of_bfEquiv_of_scottHeight_le` (B's interface (S5)) at
`M = N = ℕ` with the two decoded structures and `β` the Scott height of the first (in
`Ordinal.{0}`, the level type of D's `bfEquivSetoid`). -/
example (c d : RelationalConfiguration L ℕ)
    (h : bfEquivSetoid L ℕ (letI : L.Structure ℕ := c.toStructure; scottHeight (L := L) ℕ) c d) :
    isoSetoid L ℕ c d :=
  RelationalConfiguration.isoSetoid_apply.mpr
    (@TauCeti.nonempty_equiv_of_bfEquiv_of_scottHeight_le L _ ℕ c.toStructure _ ℕ d.toStructure _
      _ le_rfl (RelationalConfiguration.bfEquivSetoid_apply.mp h))

/-- **D 4g, Morleyization transport**: `Setoid.hasCantorAntichainOn_image_iff` between the coding
spaces of `L` and of the Morleyization (A's interface, Tau Ceti's `morleyize`), applied to D's
`morleyCode` with D's `measurableEmbedding_morleyCode` and `isoSetoid_morleyCode_iff`; the
countability of the Morleyized relation symbols is Tau Ceti's `countable_relations_morleyize`
(A's interface). This is
the proof D's `hasCantorAntichainOn_image_morleyCode_iff` names, with nothing assumed. -/
example (Φ : Set (Σ n, L.BoundedFormulaω Empty n)) (hΦ : Φ.Countable)
    (K : Set (RelationalConfiguration L ℕ)) :
    (isoSetoid (L.morleyize Φ) ℕ).HasCantorAntichainOn (morleyCode Φ '' K) ↔
      (isoSetoid L ℕ).HasCantorAntichainOn K := by
  haveI := Language.countable_relations_morleyize (L := L) hΦ
  haveI : ∀ n, Countable ((L.morleyize Φ).Relations n) := fun n =>
    (sigma_mk_injective (i := n)).countable
  exact Setoid.hasCantorAntichainOn_image_iff (measurableEmbedding_morleyCode Φ hΦ)
    (isoSetoid_morleyCode_iff Φ) K

end BCtoD

/-! ## 4. A → D: language maps, small presentation, fragments, Morleyization -/

section AtoD

open TauCetiRoadmap.CountableModelCounting (VaughtConjecture HasVaughtDichotomy sentenceTheory
  morleyCode toStructure_morleyCode)

variable {L : FirstOrder.Language.{u, v}}

/-- **D Layer 0 transport (M0, M4)**: Tau Ceti's
`LEquiv.lift_countableModelCount_onBoundedFormulaInf`, which D cites, at the small presentation of
A's Layer 0.3, moving the count to `Language.{0, 0}`. A relational language has countably many
function symbols (none), so the small presentation exists. -/
example [L.IsRelational] [Countable (Σ l, L.Relations l)] (φ : L.Sentenceω) :
    Cardinal.lift.{0} (countableModelCount φ) =
      Cardinal.lift.{v} (countableModelCount
        (L.smallPresentationEquiv.toLHom.onBoundedFormulaInf φ)) :=
  LEquiv.lift_countableModelCount_onBoundedFormulaInf L.smallPresentationEquiv φ

/-- **D Layer 0 transport**, the realization step on codes, by `Language.realize_smallPresentation`
(A's Layer 0.3, as Tau Ceti implements it):
`c ∈ modelsOf φ` iff the reinterpreted structure realizes the transported sentence. -/
example [L.IsRelational] [Countable (Σ l, L.Relations l)] (φ : L.Sentenceω)
    (c : RelationalConfiguration L ℕ) :
    c ∈ (modelsOf φ : Set (RelationalConfiguration L ℕ)) ↔
      letI : L.Structure ℕ := c.toStructure
      @SentenceInf.Realize L.smallPresentation ℕ
        (L.smallPresentationEquiv.toLHom.onBoundedFormulaInf φ) ℕ
        (L.smallPresentationEquiv.invLHom.reduct ℕ) := by
  letI : L.Structure ℕ := c.toStructure
  rw [RelationalConfiguration.mem_modelsOf]
  exact (L.realize_smallPresentation φ Empty.elim Fin.elim0).symm

/-- **D Layer 5, universes** (`vaughtConjecture_iff_forall_universe`): D's `VaughtConjecture`,
quantified over `Language.{0, 0}`, applies to the small presentation of a countable relational
`L` in any universe, through the relational and countability instances A's Layer 0.3 provides. -/
example [L.IsRelational] [Countable (Σ l, L.Relations l)] (h : VaughtConjecture)
    (φ : L.Sentenceω) :
    HasVaughtDichotomy (L.smallPresentationEquiv.toLHom.onBoundedFormulaInf φ) :=
  h L.smallPresentation _

/-- **D 4f, fragment spectra**: `Fragment.generated_countable` (A's Layer 1, in Tau Ceti) on the
range of a list of sentences. -/
example (θ : ℕ → L.Sentenceω) :
    (Fragment.generated
      (range fun k => (⟨0, θ k⟩ : Σ n, L.BoundedFormulaω Empty n))).toSet.Countable :=
  Language.Fragment.generated_countable (countable_range _)

/-- **D 4f**: the arity-0 spectrum of `Fragment.generated` of the range of a list `θ` determines
its truth sequences, with A's `fragmentType` read in decoded codes and D's `sentenceTheory`. -/
example [L.IsRelational] (θ : ℕ → L.Sentenceω) (c d : RelationalConfiguration L ℕ)
    (h : @InfinitaryModelExistence.fragmentType L (Fragment.generated
        (range fun k => (⟨0, θ k⟩ : Σ n, L.BoundedFormulaω Empty n))) ℕ c.toStructure 0
          Fin.elim0 =
      @InfinitaryModelExistence.fragmentType L (Fragment.generated
        (range fun k => (⟨0, θ k⟩ : Σ n, L.BoundedFormulaω Empty n))) ℕ d.toStructure 0
          Fin.elim0) :
    sentenceTheory θ c = sentenceTheory θ d := by
  funext k
  have hmem : (⟨0, θ k⟩ : Σ n, L.BoundedFormulaω Empty n) ∈
      (Fragment.generated (range fun k => (⟨0, θ k⟩ : Σ n, L.BoundedFormulaω Empty n))).toSet :=
    Fragment.mem_toSet.2 (Fragment.subset_generated _ ⟨k, rfl⟩)
  have hk := Set.ext_iff.mp h (θ k)
  have hcd : c ∈ (modelsOf (θ k) : Set (RelationalConfiguration L ℕ)) ↔
      d ∈ (modelsOf (θ k) : Set (RelationalConfiguration L ℕ)) := by
    rw [RelationalConfiguration.mem_modelsOf, RelationalConfiguration.mem_modelsOf]
    exact ⟨fun hc => (hk.mp ⟨hmem, hc⟩).2, fun hd => (hk.mpr ⟨hmem, hd⟩).2⟩
  by_cases hc : c ∈ (modelsOf (θ k) : Set (RelationalConfiguration L ℕ))
  · simp [sentenceTheory, hc, hcd.mp hc]
  · simp [sentenceTheory, hc, mt hcd.mpr hc]

/-- **D 4g, canonical expansion**: the code `morleyCode Φ c` of D's canonical expansion is a code
of the image of `φ` along `lhomMorleyize Φ` exactly when `c` is a code of `φ`: D's
`toStructure_morleyCode` identifies the decoded structure with the canonical expansion, and
`LHom.realize_onBoundedFormulaInf` (A's Layer 0.1, in Tau Ceti; the expansion instance is Tau
Ceti's `isExpansionOn_morleyExpansion`) passes `φ` along the inclusion. -/
example [L.IsRelational] (Φ : Set (Σ n, L.BoundedFormulaω Empty n)) (φ : L.Sentenceω)
    (c : RelationalConfiguration L ℕ) :
    morleyCode Φ c ∈ (modelsOf ((lhomMorleyize Φ).onBoundedFormulaInf φ) :
        Set (RelationalConfiguration (L.morleyize Φ) ℕ)) ↔
      c ∈ (modelsOf φ : Set (RelationalConfiguration L ℕ)) := by
  rw [RelationalConfiguration.mem_modelsOf, RelationalConfiguration.mem_modelsOf,
    toStructure_morleyCode]
  letI : L.Structure ℕ := c.toStructure
  letI := morleyExpansion Φ ℕ
  exact (lhomMorleyize Φ).realize_onBoundedFormulaInf φ _ _

end AtoD

/-! ## 5. A → E: reducts, isolators, countable `A`-elementary substructures, graph translation -/

section AtoE

open TauCetiRoadmap.HanfNumbers (IsLω₁ωSmall)

variable {L : FirstOrder.Language.{u, v}}

/-- **E 3.4, the reduct step** of `exists_model_card_eq_of_forall_beth`: the EM model realizes the
image `g.onBoundedFormulaInf φ` (E's `exists_emSource_of_forall_beth`, with `L'` in
`Language.{0, 0}`); its reduct along `g` realizes `φ` by `LHom.realize_onBoundedFormulaInf` (A's
Layer 0.1). -/
example {L' : FirstOrder.Language.{0, 0}} (g : L →ᴸ L') (φ : L.Sentenceω) (E : Type w)
    [L'.Structure E] (hE : SentenceInf.Realize (g.onBoundedFormulaInf φ) E) :
    @SentenceInf.Realize L ℕ φ E (g.reduct E) := by
  letI := g.reduct E
  exact (g.realize_onBoundedFormulaInf φ _ _).mp hE

/-- **E 5.4, countable companion seed**: for E's `IsLω₁ωSmall M` (stated with A's
`realizedTypes`), `exists_isolatingFormula` gives an isolator for each realized type,
`Fragment.generated_countable` a countable fragment containing them, and
`exists_countable_aElementary_substructure` (A's Layers 4, 1 and 2, all in Tau Ceti) with
`X = ∅` a countable `A`-elementary substructure
(no function symbols: `L` is relational). -/
example [L.IsRelational] [Countable (Σ l, L.Relations l)] (M : Type w) [L.Structure M]
    (hM : IsLω₁ωSmall (L := L) M) :
    ∃ (F : L.Fragment) (N : L.Substructure M), F.toSet.Countable ∧
      (∀ (n : ℕ) (a : Fin n → M), ∃ χ : L.BoundedFormulaω Empty n,
        (⟨n, χ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ F ∧
        ∀ b : Fin n → M, χ.Realize Empty.elim b ↔
          infinitaryType (L := L) M b = infinitaryType M a) ∧
      AElementary F N.subtype ∧ Countable N := by
  have hiso : ∀ (n : ℕ) (p : realizedTypes (L := L) M n), ∃ χ : L.BoundedFormulaω Empty n,
      ∀ b : Fin n → M, χ.Realize Empty.elim b ↔ infinitaryType (L := L) M b = p.1 := by
    rintro n ⟨p, a, rfl⟩
    exact Language.exists_isolatingFormula (hM n) a
  choose χ hχ using hiso
  let S : Set (Σ n, L.BoundedFormulaω Empty n) :=
    ⋃ n, range fun p : realizedTypes (L := L) M n => (⟨n, χ n p⟩ : Σ n, L.BoundedFormulaω Empty n)
  have hS : S.Countable :=
    countable_iUnion fun n => by haveI := (hM n).to_subtype; exact countable_range _
  have hF := Language.Fragment.generated_countable hS
  obtain ⟨N, -, hN, hNc⟩ := Language.exists_countable_aElementary_substructure
    (Fragment.generated S) hF (X := (∅ : Set M)) countable_empty
  exact ⟨_, N, hF, fun n a => ⟨χ n ⟨infinitaryType M a, a, rfl⟩,
    Fragment.subset_generated S (mem_iUnion.2 ⟨n, _, rfl⟩), hχ n _⟩, hN, hNc⟩

open TauCetiRoadmap.HanfNumbers (IsCompleteSentence isLω₁ωSmall_iff_exists_isCompleteSentence) in
/-- **E 5.6, the forward step of `isLω₁ωSmall_iff_exists_isCompleteSentence_of_countable`**: for
`L` with countably many function and relation symbols, E's relational headline
`isLω₁ωSmall_iff_exists_isCompleteSentence`, applied to the graph language of `L` (relational with
countably many relation symbols, by Tau Ceti's instances) and the graph expansion of `M`, gives a
complete `θ`; its back-translation (A's Layer 6, Tau Ceti's `BoundedFormulaInf.backTranslate`
with `realize_backTranslate`) holds in `M` and, in every `L`-structure, exactly when `θ` holds in
the graph expansion. This is the sentence `σ` of E's README 5.6. -/
example [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)] (M : Type w)
    [L.Structure M] (hM : @IsLω₁ωSmall L.graphLanguage M (graphExpansion L M)) :
    ∃ θ : L.graphLanguage.Sentenceω, IsCompleteSentence.{_, _, w} θ ∧
      SentenceInf.Realize θ.backTranslate M ∧
      ∀ (N : Type w) [L.Structure N], SentenceInf.Realize θ.backTranslate N ↔
        @SentenceInf.Realize L.graphLanguage ℕ θ N (graphExpansion L N) := by
  obtain ⟨θ, hθ, hMθ⟩ :=
    (@isLω₁ωSmall_iff_exists_isCompleteSentence L.graphLanguage _ _ M (graphExpansion L M)).1 hM
  exact ⟨θ, hθ, (BoundedFormulaInf.realize_backTranslate θ _ _).2 hMθ,
    fun N _ => BoundedFormulaInf.realize_backTranslate θ _ _⟩

end AtoE

/-! ## 6. Universe placement of the revised statements -/

section Universes

variable {L : FirstOrder.Language.{u, v}}

/-- **B Layer 4, the countable case from the general constant-chain bound.** B's
`bfEquiv_of_selfStabilizesCompletely` (with `N` in its own universe) at a countable `N : Type`
and level `β + ω + 1` gives the external stabilization (`TauCeti.StabilizesCompletely`, testing
countable `N : Type`) that D consumes through `scottHeight`, for `M` in any universe `w`. -/
example [L.IsRelational] {M : Type w} [L.Structure M] {β : Ordinal.{w}}
    (h : SelfStabilizesCompletely (L := L) M β) :
    StabilizesCompletely (L := L) M (β + Ordinal.omega0) :=
  fun _ _ _ _ _ _ hab => CountableStructureSpaces.bfEquiv_of_selfStabilizesCompletely h hab _

open TauCetiRoadmap.HanfNumbers (IsEMSource exists_emModel_card_eq) in
/-- **E 2, the source universe.** E's `exists_emModel_card_eq` stretches a source in `Type 1`
to a model in `Type`. -/
example {L' : FirstOrder.Language.{0, 0}} [Countable (Σ n, L'.Functions n)]
    {Γ : L'.Fragment} {N : Type 1} [L'.Structure N] {a : ℕ → N}
    (h : IsEMSource Γ N a) (ha : Function.Injective a) :
    ∃ (E : Type) (_ : L'.Structure E), #E = ℵ₀ := by
  obtain ⟨E, hE, -, -, -, -, hcard⟩ := exists_emModel_card_eq h ha ℕ
  exact ⟨E, hE, hcard.trans Cardinal.mk_nat⟩

open TauCetiRoadmap.HanfNumbers (exists_emSource_of_forall_beth exists_emModel_card_eq) in
/-- **E 3.4, the Morley–Hanf assembly.** The proof route of E's
`exists_model_card_eq_of_forall_beth`, composed from its parts: E's
`exists_emSource_of_forall_beth` gives a source in `Type` over `L' : Language.{0, 0}`; E's
`exists_emModel_card_eq` stretches it along `κ.ord.ToType` to a model in `Type w` of cardinality
`κ`; `LHom.realize_onBoundedFormulaInf` (A's Layer 0.1) passes `φ` to the reduct along `g`. -/
example (φ : L.Sentenceω)
    (h : ∀ α < Ordinal.omega.{w} 1,
      ∃ (M : Type w) (_ : L.Structure M), SentenceInf.Realize φ M ∧ ℶ_ α ≤ #M)
    {κ : Cardinal.{w}} (hκ : ℵ₀ ≤ κ) :
    ∃ (N : Type w) (_ : L.Structure N), SentenceInf.Realize φ N ∧ #N = κ := by
  obtain ⟨L', _, _, g, Γ, N, _, a, -, hsrc, ha, hmem, hφ⟩ := exists_emSource_of_forall_beth φ h
  haveI : Infinite κ.ord.ToType :=
    Cardinal.infinite_iff.mpr (by rwa [Cardinal.mk_toType, Cardinal.card_ord])
  obtain ⟨E, _, -, hE, -, -, hcard⟩ := exists_emModel_card_eq hsrc ha κ.ord.ToType
  letI := g.reduct E
  refine ⟨E, g.reduct E,
    (g.realize_onBoundedFormulaInf φ _ _).mp ((hE _ hmem).mp hφ), ?_⟩
  rw [hcard, Cardinal.mk_toType, Cardinal.card_ord]

end Universes

end TauCetiRoadmap.Integration

-- The PC-separation boundary check really uses the owner's `pcSeparation`.
#assert_uses TauCetiRoadmap.Integration.lopezEscobar_steps34
  TauCetiRoadmap.InfinitaryModelExistence.pcSeparation
-- B's step 0 transfer uses Tau Ceti's reduct lemma.
#assert_uses TauCetiRoadmap.Integration.preimage_reductConfiguration_eq_modelsOf
  FirstOrder.Language.LHom.realize_sentenceInf_reductConfiguration
