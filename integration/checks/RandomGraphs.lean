import TauCetiRoadmap.RandomGraphs.Suggested

/-!
# RandomGraphs (#1223): boundary checks moved out of `Suggested.lean`

Each snippet compiles against `TauCetiRoadmap/RandomGraphs/Suggested.lean` at the head of this
pass. The README keeps every statement below as part of the roadmap; these are checks that the
prototype's definitions meet a convention or a supplier's form, not further targets. All but the
last are proved here (some through admitted prototype theorems); the last is a computed value,
still admitted, recorded so that the boundary case is not lost.
-/

open MeasureTheory FirstOrder FirstOrder.Language CategoryTheory
open scoped unitInterval

namespace TauCetiRoadmap.RandomGraphs

universe u v w

/-- Convention check (Milestone 1): the strong-amalgamation square uses Mathlib's commuting
equation `i.comp f = j.comp g`, so dropping the range condition gives Mathlib's `Amalgamation`. -/
theorem StrongAmalgamation.amalgamation {L : FirstOrder.Language.{u, v}}
    {K : Set (Bundled.{w} L.Structure)} (h : StrongAmalgamation K) : Amalgamation K :=
  fun A B C f g hA hB hC =>
    let ⟨D, i, j, hD, hc, _⟩ := h A B C f g hA hB hC
    ⟨D, i, j, hD, hc⟩

/-- Boundary check (Convention 5): the empty request is included, so budget `0` says exactly that
the carrier is nonempty (false on `Fin 0`). -/
theorem hasExtensionUpTo_zero_iff {V : Type u} (G : SimpleGraph V) :
    HasExtensionUpTo G 0 ↔ Nonempty V := by
  refine ⟨fun h => ?_, fun ⟨x⟩ U Z _ hc => ⟨x, ?_⟩⟩
  · obtain ⟨x, -⟩ := h ∅ ∅ (Finset.disjoint_empty_left _) (by simp)
    exact ⟨x⟩
  · obtain ⟨rfl, rfl⟩ : U = ∅ ∧ Z = ∅ := by
      simp only [Nat.le_zero, Nat.add_eq_zero_iff, Finset.card_eq_zero] at hc
      exact hc
    simp [IsExtensionWitness]

/-- Direction check (Milestone 4.1): a larger budget gives a smaller one (`e ≤ d`). -/
theorem HasExtensionUpTo.mono {V : Type u} {G : SimpleGraph V} {d e : ℕ}
    (h : HasExtensionUpTo G d) (hed : e ≤ d) : HasExtensionUpTo G e :=
  fun U Z hUZ hc => h U Z hUZ (hc.trans hed)

/-- Adapter check (Milestone 5.2): the computable QE contract yields semantic quantifier
elimination modulo `T_R` (for every context `Fin m`, in models of any universe). -/
theorem exists_isQF_equivalent {m : ℕ} (φ : Language.graph.Formula (Fin m)) :
    ∃ ψ : Language.graph.Formula (Fin m), ψ.IsQF ∧
      ∀ (M : Type w) [Language.graph.Structure M], M ⊨ radoAxioms →
        ∀ a : Fin m → M, ψ.Realize a ↔ φ.Realize a :=
  let ⟨_, _, hQ⟩ := exists_computable_quantifierElimination.{w}
  let ⟨ψ, _, hψ⟩ := hQ m φ
  ⟨ψ, hψ⟩

/-- Supplier-boundary check (Milestone 10): Tau Ceti's
`SimpleGraph.HasExtensionProperty.realize_scottSentence_iff` holds in a target graph of any
cardinality, so `Θ_R` and the Scott sentence of `R` agree on graphs in every universe. -/
theorem satisfiesInf_radoSentenceInf_iff_scottSentence {V : Type u} (G : SimpleGraph V) :
    SatisfiesInf G radoSentenceInf ↔
      SatisfiesInf G (@TauCeti.scottSentence Language.graph _ ℕ TauCeti.radoGraph.structure _ _) :=
  (satisfiesInf_radoSentenceInf_iff G).trans
    (TauCeti.hasExtensionProperty_radoGraph.realize_scottSentence_iff G).symm

/-- Boundary check (Milestone 10): `cardEq m` means cardinality exactly `m`, including `m = 0` on
the empty carrier, and fails on infinite carriers. -/
theorem satisfies_cardEq_iff {V : Type u} (G : SimpleGraph V) (m : ℕ) :
    Satisfies G (cardEq m) ↔ Cardinal.mk V = m := by
  let _ := G.structure
  simp only [Satisfies, cardEq, Sentence.realize_inf, Sentence.realize_not,
    Sentence.realize_cardGe, Nat.cast_succ, Cardinal.natCast_add_one_le_iff, not_lt]
  exact and_comm.trans le_antisymm_iff.symm

end TauCetiRoadmap.RandomGraphs
