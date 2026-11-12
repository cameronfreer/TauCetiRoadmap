module

public import TauCetiRoadmap.InfinitaryModelExistence.Suggested
public import TauCeti.ModelTheory.ModelExistence.AElementary
public import TauCeti.ModelTheory.ModelExistence.ModelExistence

/-!
# InfinitaryModelExistence (#1615): boundary tests moved out of `Suggested.lean`

Moved from `TauCetiRoadmap/InfinitaryModelExistence/Suggested.lean` at 6601a3b5. Both were proved
there from Tau Ceti declarations at the pin; they test interfaces, not targets the pin lacks.
-/

@[expose] public section

universe u v w w'

namespace TauCetiRoadmap.InfinitaryModelExistence

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

variable {L : FirstOrder.Language.{u, v}}

-- Indexing adapter: README 3.2's `model_existence_omitting` takes a countable *set* of tagged
-- types (the indexing Layer 4 uses); Tau Ceti's takes a countable indexed family.
theorem model_existence_omitting [Countable (Σ n, L.Functions n)]
    [Countable (Σ n, L.Relations n)] (C : ConsistencyProperty L)
    (P : Set (Σ n, Set (L[[ℕ]].BoundedFormulaω Empty n))) (hP : P.Countable)
    (hPc : ∀ p ∈ P, p.2.Countable)
    (hreq : ∀ p ∈ P, ∀ s ∈ C.sets, ∀ c : Fin p.1 → ℕ, ∃ ψ ∈ p.2,
      insert (BoundedFormulaInf.substBounds (fun i => (L.con (c i)).term) ψ).not s ∈ C.sets)
    {s : L[[ℕ]].Theoryω} (hs : s ∈ C.sets) (hsc : s.Countable) :
    ∃ (M : Type w) (_ : L[[ℕ]].Structure M), Countable M ∧ s.Model M ∧
      (∀ m : M, ∃ c : ℕ, (L.con c : M) = m) ∧ ∀ p ∈ P, OmitsType M p.2 := by
  have := hP.to_subtype
  obtain ⟨M, _, hc, -, hM, hsurj, homit⟩ :=
    C.model_existence_omitting.{u, v, w} (ι := P) (n := fun p => p.1.1) (fun p => p.1.2)
      (fun p => hPc p.1 p.2) (fun p => hreq p.1 p.2) hs hsc
  exact ⟨M, _, hc, hM, hsurj, fun p hp => homit ⟨p, hp⟩⟩

-- Definition fit: the roadmap's `fragmentType` (tagged members `⟨n, φ⟩ ∈ A.toSet`, `Empty.elim`)
-- matches Tau Ceti's `AElementary`, across carriers in different universes (README 4.1).
theorem AElementary.fragmentType_comp {A : L.Fragment} {N : Type w} {M : Type w'}
    [L.Structure N] [L.Structure M] {f : N ↪[L] M} (hf : AElementary A f) {n : ℕ}
    (a : Fin n → N) : fragmentType A M (f ∘ a) = fragmentType A N a :=
  Set.ext fun _ => and_congr_right fun h => hf.realize_iff h a

end TauCetiRoadmap.InfinitaryModelExistence
