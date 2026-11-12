import TauCetiRoadmap.HanfNumbers.Suggested

/-!
# HanfNumbers (PR #1319): interface checks moved out of `Suggested.lean`

Each check was proved in place in `TauCetiRoadmap/HanfNumbers/Suggested.lean` at 2dc7d398. The
README keeps each statement as a target. Here each is an `example` against the roadmap's own
definitions, so that a change of convention in a definition breaks the check.
-/

namespace TauCetiRoadmap.HanfNumbers

open FirstOrder FirstOrder.Language Cardinal

universe u v w u'

-- `iteratedTwoPow_beth`: adapter from the new iterated exponential to Mathlib's `beth`, the index
-- shift `erdos_rado_beth` is derived from (README Convention 4, 0.4).
example (α : Ordinal.{u}) (n : ℕ) : iteratedTwoPow (ℶ_ α) n = ℶ_ (α + n) := by
  induction n <;> simp_all [iteratedTwoPow, ← add_assoc, Cardinal.beth_add_one]

-- `IsIndiscernibleOn.comp`: the direction convention of `Fin n ↪o J`; restriction along `K ↪o J`
-- is composition of order embeddings (README 1.1).
example {L : FirstOrder.Language.{u, v}} {J : Type u'} [LinearOrder J] {K : Type*} [LinearOrder K]
    {M : Type w} [L.Structure M] {a : J → M} {Δ : Set (Σ n, L.BoundedFormulaω Empty n)}
    (h : IsIndiscernibleOn a Δ) (e : K ↪o J) : IsIndiscernibleOn (a ∘ e) Δ :=
  fun p hp s t => h p hp (s.trans e) (t.trans e)

-- `isIndiscernibleOn_iff_realizesOn_templateOf`: `IsIndiscernibleOn`, `templateOf` and
-- `EMTemplate.RealizesOn` fit together over any index order (README 1.2).
example {L : FirstOrder.Language.{u, v}} {J : Type u'} [LinearOrder J] {M : Type w}
    [L.Structure M] (a : J → M) (Δ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    IsIndiscernibleOn a Δ ↔ (templateOf a).RealizesOn a Δ :=
  ⟨fun h p hp t => ⟨fun ht s => (h p hp t s).1 ht, fun hall => hall t⟩,
    fun h p hp s t => ⟨fun hs => (h p hp s).1 hs t, fun ht => (h p hp t).1 ht s⟩⟩

-- `isIndiscernibleOn_morleySeed` (Layer 1 acceptance check): `disEq` is the disequality of the two
-- bound positions, so injectivity of the sequence is what the seed needs (README 1.3).
example {L : FirstOrder.Language.{u, v}} {J : Type u'} [LinearOrder J] {M : Type w}
    [L.Structure M] (φ : L.Sentenceω) {a : J → M} (ha : Function.Injective a) :
    IsIndiscernibleOn a (morleySeed φ) := by
  rintro p (rfl | rfl) s t
  · rw [Subsingleton.elim (a ∘ ⇑s) (a ∘ ⇑t)]
  · simp [disEq, ha.eq_iff, s.injective.eq_iff, t.injective.eq_iff]

-- `hanfNumber_le_beth_omega_one`: `hanfNumber` is the infimum of `IsHanfBound` in the universe of
-- `morley_hanf`, so the headline bounds the Hanf number (README 3.4).
example {L : FirstOrder.Language.{u, v}} (φ : L.Sentenceω) :
    hanfNumber.{u, v, w} φ ≤ ℶ_ (Ordinal.omega.{w} 1) :=
  csInf_le' (morley_hanf φ)

-- `isLω₁ωSmall_of_countable` (Layer 5 acceptance check): `IsLω₁ωSmall` is read through Tau Ceti's
-- `realizedTypes`, with no countability hypothesis on the language (README 5.2).
example {L : FirstOrder.Language.{u, v}} (M : Type w) [L.Structure M] [Countable M] :
    IsLω₁ωSmall (L := L) M :=
  fun _ => (Set.countable_range (infinitaryType M)).mono fun _ hp => mem_realizedTypes.1 hp

end TauCetiRoadmap.HanfNumbers
