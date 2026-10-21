import TauCetiRoadmap.CountableModelCounting.Suggested

/-!
# Adapters: CountableModelCounting's original inline forms vs BorelEquivalenceRelations' names

In the substituted copy D' of `CountableModelCounting/Suggested.lean`, six places where D wrote
C's perfect-set vocabulary out inline were replaced by C's named definitions. Each `example` below
restates D's *original* inline text (copied verbatim from the draft) and proves by `Iff.rfl` that
it agrees with the C-substituted form, and then that the D' theorem proves the original statement
on the nose.
-/

set_option autoImplicit false

universe u v

namespace TauCetiRoadmap.Integration.Adapters

open FirstOrder FirstOrder.Language Set
open TauCetiRoadmap.InfinitaryLogic TauCetiRoadmap.CountableStructureSpaces
open TauCetiRoadmap.CountableModelCounting
open TauCetiRoadmap.BorelEquivalenceRelations (HasPerfectAntichainOn HasCantorAntichainOn IsThinOn)
open TauCetiRoadmap.InfinitaryModelExistence (morleyize)

variable {L : FirstOrder.Language.{u, v}} [L.IsRelational]

/-- (1) `HasPerfectSetOfNonisoModelsOn`: D's original body (draft line 199-200). -/
example (α : Type) (φ : Sentenceω L) :
    HasPerfectSetOfNonisoModelsOn α φ ↔
      ∃ P : Set (StructureSpaceOn L α), Perfect P ∧ P.Nonempty ∧ P ⊆ modelsOf φ ∧
        ∀ c ∈ P, ∀ d ∈ P, structureIsoSetoidOn L α c d → c = d :=
  Iff.rfl

/-- ... and it is literally C's `HasPerfectAntichainOn`, as D's docstring claims. -/
example (α : Type) (φ : Sentenceω L) :
    HasPerfectSetOfNonisoModelsOn α φ ↔
      HasPerfectAntichainOn (structureIsoSetoidOn L α) (modelsOf φ : Set (StructureSpaceOn L α)) :=
  Iff.rfl

/-- (2) `IsThinOnNatModels`: D's original body was `¬ HasPerfectSetOfNonisoModelsOn ℕ φ`; D'
uses C's `IsThinOn`. -/
example [Countable (Σ l, L.Relations l)] (φ : Sentenceω L) :
    IsThinOnNatModels φ ↔ ¬ HasPerfectSetOfNonisoModelsOn ℕ φ :=
  Iff.rfl

/-- (3) `not_hasCantorAntichainOn_of_bfScattered`: D's original inline conclusion is C's
`¬ HasCantorAntichainOn`, and the D' theorem proves the original statement. -/
example (K : Set (StructureSpace L)) :
    HasCantorAntichainOn (structureIsoSetoid L) K ↔
      ∃ f : (ℕ → Bool) → StructureSpace L, Continuous f ∧ (∀ x, f x ∈ K) ∧
        ∀ x y, x ≠ y → ¬ structureIsoSetoid L (f x) (f y) :=
  Iff.rfl

example {K : Set (StructureSpace L)} (hK : BFScattered K) :
    ¬ ∃ f : (ℕ → Bool) → StructureSpace L, Continuous f ∧ (∀ x, f x ∈ K) ∧
        ∀ x y, x ≠ y → ¬ structureIsoSetoid L (f x) (f y) :=
  not_hasCantorAntichainOn_of_bfScattered hK

/-- (4) `isThin_iff_countable_sentenceSpectra`: original left-hand side vs C's `IsThinOn`. -/
example (C : Set (StructureSpace L)) :
    IsThinOn (structureIsoSetoid L) C ↔
      ¬ ∃ P : Set (StructureSpace L), Perfect P ∧ P.Nonempty ∧ P ⊆ C ∧
        ∀ c ∈ P, ∀ d ∈ P, structureIsoSetoid L c d → c = d :=
  Iff.rfl

example [Countable (Σ l, L.Relations l)] (C : Set (StructureSpace L)) (hC : MeasurableSet C) :
    (¬ ∃ P : Set (StructureSpace L), Perfect P ∧ P.Nonempty ∧ P ⊆ C ∧
        ∀ c ∈ P, ∀ d ∈ P, structureIsoSetoid L c d → c = d) ↔
      ∀ θ : ℕ → Sentenceω L, (sentenceTheory θ '' C).Countable :=
  isThin_iff_countable_sentenceSpectra C hC

/-- (5) `FirstOrderVaughtConjecture`: original perfect-set disjunct vs C's
`HasPerfectAntichainOn`. -/
example (T : L.Theory) :
    HasPerfectAntichainOn (structureIsoSetoid L) (modelsOfTheory T) ↔
      ∃ P : Set (StructureSpace L), Perfect P ∧ P.Nonempty ∧ P ⊆ modelsOfTheory T ∧
        ∀ c ∈ P, ∀ d ∈ P, structureIsoSetoid L c d → c = d :=
  Iff.rfl

/-- (6) `hasCantorAntichainOn_image_morleyCode_iff`: both inline sides are C's
`HasCantorAntichainOn`, and the D' theorem proves the original statement. -/
example [Countable (Σ l, L.Relations l)] (Φ : Set (Σ n, BoundedFormulaω L Empty n))
    (hΦ : Φ.Countable) (K : Set (StructureSpace L)) :
    (∃ f : (ℕ → Bool) → StructureSpace (morleyize L Φ), Continuous f ∧
        (∀ x, f x ∈ morleyCode Φ '' K) ∧
        ∀ x y, x ≠ y → ¬ structureIsoSetoid (morleyize L Φ) (f x) (f y)) ↔
      ∃ f : (ℕ → Bool) → StructureSpace L, Continuous f ∧ (∀ x, f x ∈ K) ∧
        ∀ x y, x ≠ y → ¬ structureIsoSetoid L (f x) (f y) :=
  hasCantorAntichainOn_image_morleyCode_iff Φ hΦ K

end TauCetiRoadmap.Integration.Adapters
