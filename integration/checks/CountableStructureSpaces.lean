import TauCetiRoadmap.CountableStructureSpaces.Suggested

/-!
# CountableStructureSpaces (TauCetiRoadmap #1316): boundary checks moved to the integration harness

Each declaration below was proved in place in `Suggested.lean` at cf843fd3 from pinned Tau Ceti and
Mathlib declarations. They test conventions, indexing and generality rather than state new targets,
so they live here; the README keeps every statement and cites the library declarations. Names are
unchanged, so the harness's existing uses (`continuousSMul_relationalConfiguration`,
`analyticSet_orbitRel_graph`, `saturated_iff_isFixedBlock`, `bfEquiv_of_selfStabilizesCompletely`)
resolve once this file is compiled after `Suggested.lean`.
-/

universe u v w w'

namespace TauCetiRoadmap.CountableStructureSpaces

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure MeasureTheory Topology
open TauCeti TauCeti.RelationalConfiguration Descriptive
open scoped Pointwise

variable {L : FirstOrder.Language.{u, v}} {α : Type w}

section PermTopology

variable [TopologicalSpace α] [DiscreteTopology α]

-- Boundary: README 1.1 indexes the neighbourhood basis by `Finset`s; the library's
-- `Equiv.Perm.hasBasis_nhds_one_fixingSubgroup` indexes it by finite `Set`s.
theorem hasBasis_nhds_one_fixingSubgroup :
    (𝓝 (1 : Equiv.Perm α)).HasBasis (fun _ : Finset α => True)
      (fun s => (fixingSubgroup (Equiv.Perm α) (s : Set α) : Set (Equiv.Perm α))) :=
  Equiv.Perm.hasBasis_nhds_one_fixingSubgroup.to_hasBasis
    (fun s hs => ⟨hs.toFinset, trivial, by simp⟩) (fun s _ => ⟨s, s.finite_toSet, subset_rfl⟩)

end PermTopology

-- Convention: README Convention 3 fixes the action direction, `(σ • c)` at `R(x)` is `c` at
-- `R(σ⁻¹ ∘ x)`; this pins Tau Ceti's `eval_perm_smul` to that reading.
theorem eval_smul_atom (σ : Equiv.Perm α) (c : RelationalConfiguration L α) {n : ℕ}
    (R : L.Relations n) (x : Fin n → α) :
    (σ • c).eval (atom R x) = c.eval (atom R (⇑σ⁻¹ ∘ x)) := by
  rw [eval_perm_smul, Atom.map_atom]
  rfl

-- Generality: joint continuity of the logic action for every language (no relational or
-- countability hypothesis), from `continuous_uncurry_restrict` and `continuous_inv_apply`.
theorem continuousSMul_relationalConfiguration [TopologicalSpace α] [DiscreteTopology α] :
    ContinuousSMul (Equiv.Perm α) (RelationalConfiguration L α) := by
  refine ⟨?_⟩
  simp only [perm_smul_def]
  exact (continuous_uncurry_restrict (L := L) (V := α) (W := α)).comp
    ((continuous_pi fun x => (Equiv.Perm.continuous_inv_apply x).comp continuous_fst).prodMk
      continuous_snd)

-- Convention: README Convention 6, Mathlib's two-sided `IsFixedBlock` is Tau Ceti's
-- `IsomorphismInvariant` (through the one-sided `IsInvariantBlock`).
theorem isFixedBlock_iff_isomorphismInvariant [L.IsRelational]
    (B : Set (RelationalConfiguration L α)) :
    MulAction.IsFixedBlock (Equiv.Perm α) B ↔ IsomorphismInvariant B :=
  (isomorphismInvariant_iff_isInvariantBlock.trans
    MulAction.isInvariantBlock_iff_isFixedBlock).symm

-- Convention: README Convention 6, the invariant σ-algebra `⨅ σ, invariants (σ • ·)` is
-- measurability together with action invariance, for every language and carrier.
theorem measurableSet_iInf_invariants_iff (B : Set (RelationalConfiguration L α)) :
    MeasurableSet[⨅ σ : Equiv.Perm α,
        MeasurableSpace.invariants (fun c : RelationalConfiguration L α => σ • c)] B ↔
      MeasurableSet B ∧ MulAction.IsFixedBlock (Equiv.Perm α) B := by
  simp only [MeasurableSpace.measurableSet_iInf, MeasurableSpace.measurableSet_invariants]
  exact ⟨fun h => ⟨(h 1).1, fun σ => by simpa [Set.preimage_smul] using (h σ⁻¹).2⟩,
    fun ⟨hB, hfix⟩ σ => ⟨hB, by rw [Set.preimage_smul, hfix]⟩⟩

open Set in
-- Generality: the orbit relation of the logic action is analytic for every language with
-- countably many relation symbols; the library's `analyticSet_setOf_isoSetoid` is relational.
theorem analyticSet_orbitRel_graph [∀ n, Countable (L.Relations n)] :
    AnalyticSet {p : RelationalConfiguration L ℕ × RelationalConfiguration L ℕ |
      MulAction.orbitRel (Equiv.Perm ℕ) (RelationalConfiguration L ℕ) p.1 p.2} := by
  have : ContinuousSMul (Equiv.Perm ℕ) (RelationalConfiguration L ℕ) :=
    continuousSMul_relationalConfiguration
  have h : Continuous fun q : Equiv.Perm ℕ × RelationalConfiguration L ℕ => (q.1 • q.2, q.2) :=
    continuous_smul.prodMk continuous_snd
  convert analyticSet_range_of_polishSpace h using 1
  ext ⟨c, d⟩
  simp only [mem_ofPred_eq, mem_range, Prod.exists, Prod.mk.injEq, MulAction.orbitRel_apply,
    MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨σ, rfl⟩; exact ⟨σ, d, rfl, rfl⟩
  · rintro ⟨σ, d', h1, rfl⟩; exact ⟨σ, h1⟩

-- Adapter: README 4.1, the isomorphism class of a code as a set is the model class of the Scott
-- sentence of the structure it names (the set form of `realize_scottSentence_iff`).
theorem setOf_iso_eq_modelsOf_scottSentence [L.IsRelational] [∀ n, Countable (L.Relations n)]
    (c : RelationalConfiguration L ℕ) :
    {d | (isoSetoid L ℕ) c d} =
      modelsOf (@scottSentence L _ ℕ c.toStructure _ _) := by
  ext d
  rw [Set.mem_ofPred_eq, isoSetoid_apply, mem_modelsOf]
  exact (@realize_scottSentence_iff L _ _ ℕ c.toStructure _ ℕ d.toStructure _).symm

-- Generality: README 4.2, the constant-chain bound for `N` of any cardinality and in any universe
-- (the library's `stabilizesCompletely_add_omega0` is the countable case).
theorem bfEquiv_of_selfStabilizesCompletely [L.IsRelational] {M : Type w} {N : Type w'}
    [L.Structure M] [L.Structure N] {β : Ordinal.{w}}
    (h : SelfStabilizesCompletely (L := L) M β) {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hab : BFEquiv (L := L) (β + Ordinal.omega0) n a b) (γ : Ordinal.{w}) :
    BFEquiv (L := L) γ n a b := by
  rcases le_total (β + Ordinal.omega0) γ with hγ | hγ
  · refine bfEquiv_of_le_of_forall_add_one (fun n a b => ?_) hγ hab
    exact h.bfEquiv_add_one_of_isSuccLimit (Ordinal.isSuccLimit_add β Ordinal.isSuccLimit_omega0)
      (lt_add_of_pos_right β Ordinal.omega0_pos)
  · exact hab.mono hγ

open Set in
-- Generality: README 6.1, saturation for the orbit relation is action invariance for every
-- language; the library's `isomorphismInvariant_iff_preimage_image_quotientMk` is relational.
theorem saturated_iff_isFixedBlock {B : Set (RelationalConfiguration L ℕ)} :
    Quotient.mk (MulAction.orbitRel (Equiv.Perm ℕ) (RelationalConfiguration L ℕ)) ⁻¹'
        (Quotient.mk (MulAction.orbitRel (Equiv.Perm ℕ) (RelationalConfiguration L ℕ)) '' B) = B ↔
      MulAction.IsFixedBlock (Equiv.Perm ℕ) B := by
  constructor
  · intro h
    refine MulAction.isInvariantBlock_iff_isFixedBlock.1 fun σ => ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [← h]
    exact ⟨x, hx, Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨σ⁻¹, inv_smul_smul σ x⟩)⟩
  · intro h
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hxy)
      rw [← h g⁻¹]
      exact ⟨g • x, hy, inv_smul_smul g x⟩
    · intro hx; exact ⟨x, hx, rfl⟩

end TauCetiRoadmap.CountableStructureSpaces
