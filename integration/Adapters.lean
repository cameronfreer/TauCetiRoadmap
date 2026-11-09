import TauCetiRoadmap.BorelEquivalenceRelations.Suggested
import TauCeti.SetTheory.Descriptive.Antichain

/-!
# Adapters: BorelEquivalenceRelations' antichain vocabulary vs Tau Ceti's

BorelEquivalenceRelations (C) states its perfect-set vocabulary in its own namespace;
CountableModelCounting (D) states its targets with Tau Ceti's `Setoid.HasPerfectAntichainOn`,
`Setoid.HasCantorAntichainOn` and `Setoid.IsThinOn`, which implement C's interface (D's README,
item (E0)). The three bridges below check that the two vocabularies agree, by the unfolding
lemmas alone (both sides have the same body), so that `Integration.lean` can apply C's own
statements to D's objects.
-/

set_option autoImplicit false

universe u

namespace TauCetiRoadmap.Integration.Adapters

variable {X : Type u} [TopologicalSpace X] (E : Setoid X) (A : Set X)

/-- C's `HasPerfectAntichainOn` is Tau Ceti's. -/
theorem hasPerfectAntichainOn_iff :
    BorelEquivalenceRelations.HasPerfectAntichainOn E A ↔ E.HasPerfectAntichainOn A :=
  Setoid.hasPerfectAntichainOn_iff.symm

/-- C's `HasCantorAntichainOn` is Tau Ceti's. -/
theorem hasCantorAntichainOn_iff :
    BorelEquivalenceRelations.HasCantorAntichainOn E A ↔ E.HasCantorAntichainOn A :=
  Setoid.hasCantorAntichainOn_iff.symm

/-- C's `IsThinOn` is Tau Ceti's. -/
theorem isThinOn_iff : BorelEquivalenceRelations.IsThinOn E A ↔ E.IsThinOn A :=
  (not_congr (hasPerfectAntichainOn_iff E A)).trans Setoid.isThinOn_iff.symm

end TauCetiRoadmap.Integration.Adapters
