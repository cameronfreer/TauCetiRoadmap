import TauCetiRoadmap.BorelEquivalenceRelations.Suggested
import TauCeti.Topology.MetricSpace.Polish.Pi
import TauCeti.Topology.Perfect
import TauCeti.Topology.MetricSpace.Polish.GDelta

/-!
# BorelEquivalenceRelations (#1616): boundary checks moved out of `Suggested.lean`

Moved from `TauCetiRoadmap/BorelEquivalenceRelations/Suggested.lean` at 81fe877e (lines 62–73) in
the 12 November conformance pass. The README keeps both statements (Layer 0.1 and 0.2, and the
adapter row for `TauCeti.isGδ_of_isCompletelyMetrizableSpace`).
-/

universe u

namespace TauCetiRoadmap.BorelEquivalenceRelations

-- Boundary: instances Mathlib lacks. With Tau Ceti's `TauCeti.polishSpace_pi_of_discreteTopology`
-- and `TauCeti.perfectSpace_pi` imported, instance search finds the Polish and perfect structures
-- of Cantor space (and the perfect structure of Baire space), which it does not find from Mathlib
-- alone (README 0.1 and the list of what Mathlib lacks).
example : PolishSpace (ℕ → Bool) ∧ PerfectSpace (ℕ → Bool) ∧ PerfectSpace (ℕ → ℕ) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

-- Boundary: a different form. Alexandrov's theorem in the README's generality, for `T6` ambient
-- spaces and an explicit complete metrizability hypothesis, from Tau Ceti's form for perfectly
-- normal `T2` spaces with complete metrizability of the subspace as an instance (README 0.2).
example {X : Type u} [TopologicalSpace X] [T6Space X] {s : Set X}
    (hs : TopologicalSpace.IsCompletelyMetrizableSpace s) : IsGδ s :=
  TauCeti.isGδ_of_isCompletelyMetrizableSpace

end TauCetiRoadmap.BorelEquivalenceRelations
