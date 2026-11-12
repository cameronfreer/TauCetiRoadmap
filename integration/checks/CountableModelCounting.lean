import TauCetiRoadmap.CountableModelCounting.Suggested

/-!
# CountableModelCounting (#2012): boundary checks moved out of `Suggested.lean`

Moved from `TauCetiRoadmap/CountableModelCounting/Suggested.lean` at a25a711d. Each snippet
compiles against the revised `Suggested.lean` and keeps the roadmap namespace, so the existing
integration references (`measurableSet_isoSetoid_fin`, `isoSetoid_morleyCode_iff`,
`toStructure_morleyCode` in `Integration.lean` §0, §3 and §4) resolve to the declarations here.
The README keeps every statement and cites the library declaration. Nothing here is `sorry`.
-/

universe u v w

namespace TauCetiRoadmap.CountableModelCounting

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Cardinal MeasureTheory Set
open TauCeti
open TauCeti.RelationalConfiguration (atom modelsOf isoSetoid isoSetoidOn bfEquivSetoid
  bfEquivSetoidOn)

variable {L : FirstOrder.Language.{u, v}}

/-! ## Layer 0 -/

-- Boundary: the roadmap's Σ-form countability hypothesis feeds Tau Ceti's per-arity form
-- (Convention 1).
private theorem countable_relations [Countable (Σ l, L.Relations l)] (n : ℕ) :
    Countable (L.Relations n) :=
  (sigma_mk_injective (i := n)).countable

section Layer0

variable [L.IsRelational]

-- Boundary: transport along `Equiv.encodeVia` lands in Tau Ceti's `modelsOf`, for a model in an
-- arbitrary universe `w` (the step behind `classOf`).
theorem encodeVia_mem_modelsOf {α : Type} (φ : L.Sentenceω) {M : Type w} [L.Structure M]
    (e : M ≃ α) (hM : SentenceInf.Realize φ M) :
    e.encodeVia (L := L) ∈ (modelsOf φ : Set (RelationalConfiguration L α)) :=
  RelationalConfiguration.mem_modelsOf.2 ((Equiv.realize_encodeVia e φ).2 hM)

-- Boundary: Tau Ceti's finite-carrier Borel graph `measurableSet_setOf_isoSetoid` under the
-- roadmap's Σ-form hypothesis; consumed by `Integration.lean` §3 (finite tiers).
theorem measurableSet_isoSetoid_fin [Countable (Σ l, L.Relations l)] (n : ℕ) :
    MeasurableSet {p : RelationalConfiguration L (Fin n) × RelationalConfiguration L (Fin n) |
      isoSetoid L (Fin n) p.1 p.2} :=
  haveI := countable_relations (L := L)
  RelationalConfiguration.measurableSet_setOf_isoSetoid

end Layer0

/-! ## Layers 1 and 4b: the image form of Tau Ceti's counting results

Boundary: Tau Ceti states its counting results for the restricted quotient
`Quotient ((isoSetoid L ℕ).comap Subtype.val)`; the README's prose uses the image of `K` in the
quotient by `isoSetoid L ℕ`. These check that the two forms are interchangeable through
`Setoid.comapQuotientEquiv`. -/

section ImageForm

variable [L.IsRelational]

/-- The image of a set `K` of codes in the quotient by isomorphism is the quotient of isomorphism
restricted to `K`. -/
private noncomputable def quotientComapEquivImage (K : Set (RelationalConfiguration L ℕ)) :
    Quotient ((isoSetoid L ℕ).comap (Subtype.val : K → RelationalConfiguration L ℕ)) ≃
      (Quotient.mk (isoSetoid L ℕ) '' K) :=
  (Setoid.comapQuotientEquiv _ _).trans
    (Set.equivOfEq (by rw [Set.range_comp, Subtype.range_coe]))

-- Boundary: `TauCeti.mk_isoClasses_le_aleph_one_of_countable_levels` in image form.
theorem mk_isoClasses_le_aleph_one_of_countable_levels (K : Set (RelationalConfiguration L ℕ))
    (hK : ∀ β < (Ordinal.omega 1 : Ordinal.{0}),
      Countable (Quotient ((bfEquivSetoid L ℕ β).comap
        (Subtype.val : K → RelationalConfiguration L ℕ)))) :
    #(Quotient.mk (isoSetoid L ℕ) '' K) ≤ ℵ₁ :=
  (Cardinal.mk_congr (quotientComapEquivImage K)).symm.trans_le
    (TauCeti.mk_isoClasses_le_aleph_one_of_countable_levels K hK)

-- Boundary: `TauCeti.IsIsolatingRank.countable_isoClasses_iff_bounded` in image form.
theorem IsIsolatingRank.countable_isoClasses_iff_bounded
    {ρ : RelationalConfiguration L ℕ → Ordinal.{0}} (hρ : IsIsolatingRank ρ)
    {K : Set (RelationalConfiguration L ℕ)} (hK : BFScattered K) :
    (Quotient.mk (isoSetoid L ℕ) '' K).Countable ↔
      ∃ β < Ordinal.omega 1, ∀ c ∈ K, ρ c < β := by
  rw [← Set.countable_coe_iff, ← (quotientComapEquivImage K).countable_iff]
  exact hρ.countable_isoClasses_iff_bounded hK

-- Boundary: `TauCeti.IsIsolatingRank.mk_isoClasses_eq_aleph_one` in image form.
theorem IsIsolatingRank.mk_isoClasses_eq_aleph_one
    {ρ : RelationalConfiguration L ℕ → Ordinal.{0}} (hρ : IsIsolatingRank ρ)
    {K : Set (RelationalConfiguration L ℕ)} (hK : BFScattered K)
    (hunc : ¬ (Quotient.mk (isoSetoid L ℕ) '' K).Countable) :
    #(Quotient.mk (isoSetoid L ℕ) '' K) = ℵ₁ := by
  have : Uncountable (Quotient ((isoSetoid L ℕ).comap
      (Subtype.val : K → RelationalConfiguration L ℕ))) := by
    rw [← not_countable_iff, (quotientComapEquivImage K).countable_iff, Set.countable_coe_iff]
    exact hunc
  rw [← Cardinal.mk_congr (quotientComapEquivImage K)]
  exact hρ.mk_isoClasses_eq_aleph_one hK

end ImageForm

/-! ## Layer 4g: the expansion code against Tau Ceti's Morleyization

Boundary: the roadmap's `morleyCode` and `morleyBase` agree with Tau Ceti's `morleyExpansion`,
`lhomMorleyize` and `nonempty_morleyEquiv_iff` (InfinitaryModelExistence's (M3)). These are the
API facts the targets `measurableEmbedding_morleyCode` and
`hasCantorAntichainOn_image_morleyCode_iff` rest on; `Integration.lean` §3 and §4 consume
`isoSetoid_morleyCode_iff` and `toStructure_morleyCode`. -/

section MorleyCode

variable {L : FirstOrder.Language.{u, v}} [L.IsRelational]
  (Φ : Set (Σ n, L.BoundedFormulaω Empty n))

-- Boundary: base bits of the expansion code are copied (`morleyExpansion_relMap_inl`).
theorem morleyCode_inl (c : RelationalConfiguration L ℕ) {l : ℕ} (R : L.Relations l)
    (v : Fin l → ℕ) :
    (morleyCode Φ c).eval (atom (Sum.inl R : (L.morleyize Φ).Relations l) v) =
      c.eval (atom R v) := by
  rw [morleyCode,
    @RelationalConfiguration.eval_ofStructure _ _ (@morleyExpansion L Φ ℕ c.toStructure)]
  simp only [@morleyExpansion_relMap_inl L Φ ℕ c.toStructure,
    RelationalConfiguration.toStructure_relMap, Bool.decide_eq_true]

-- Boundary: the new bit of `φ` at `v` is the truth of `φ` (`morleyExpansion_relMap_morleyRel`).
theorem morleyCode_inr_eq_true_iff (c : RelationalConfiguration L ℕ) {l : ℕ}
    (φ : {φ : L.BoundedFormulaω Empty l // ⟨l, φ⟩ ∈ Φ}) (v : Fin l → ℕ) :
    (morleyCode Φ c).eval (atom (Sum.inr φ : (L.morleyize Φ).Relations l) v) = true ↔
      @BoundedFormulaInf.Realize L ℕ Empty ℕ c.toStructure l φ.1 Empty.elim v := by
  rw [morleyCode,
    @RelationalConfiguration.eval_ofStructure _ _ (@morleyExpansion L Φ ℕ c.toStructure)]
  simp only [decide_eq_true_eq]
  exact @morleyExpansion_relMap_morleyRel L Φ ℕ c.toStructure l φ.1 φ.2 v

-- Boundary: `morleyBase` (the reduct along `lhomMorleyize Φ`) is a left inverse.
theorem morleyBase_morleyCode (c : RelationalConfiguration L ℕ) :
    morleyBase Φ (morleyCode Φ c) = c := by
  ext a
  induction a using RelationalConfiguration.Atom.induction_atom with
  | h R v =>
    rw [morleyBase, LHom.eval_reductConfiguration, LHom.onAtom_atom, lhomMorleyize_onRelation,
      morleyCode_inl]

-- Boundary: injectivity, the input to Lusin–Souslin in `measurableEmbedding_morleyCode`.
theorem morleyCode_injective : Function.Injective (morleyCode Φ) := fun c d h => by
  rw [← morleyBase_morleyCode Φ c, h, morleyBase_morleyCode]

-- Boundary: decoding agreement with Tau Ceti's canonical expansion.
theorem toStructure_morleyCode (c : RelationalConfiguration L ℕ) :
    (morleyCode Φ c).toStructure = @morleyExpansion L Φ ℕ c.toStructure :=
  RelationalConfiguration.toStructure_ofStructure _

-- Boundary: isomorphism of expansion codes is Tau Ceti's `nonempty_morleyEquiv_iff` on codes.
theorem isoSetoid_morleyCode_iff (c d : RelationalConfiguration L ℕ) :
    isoSetoid (L.morleyize Φ) ℕ (morleyCode Φ c) (morleyCode Φ d) ↔ isoSetoid L ℕ c d := by
  rw [RelationalConfiguration.isoSetoid_apply, RelationalConfiguration.isoSetoid_apply,
    toStructure_morleyCode, toStructure_morleyCode]
  exact @nonempty_morleyEquiv_iff L Φ ℕ ℕ c.toStructure d.toStructure

end MorleyCode

/-! ## Layer 5 -/

-- Boundary: the perfect-set form implies the cardinal form through Tau Ceti's
-- `HasPerfectlyManyCountableModels.countableModelCount_eq` (the Layer 5 acceptance check).
theorem VaughtConjecture.cardinal (h : VaughtConjecture) : CardinalVaughtConjecture :=
  fun L _ _ φ => (h L φ).imp_right HasPerfectlyManyCountableModels.countableModelCount_eq

end TauCetiRoadmap.CountableModelCounting
