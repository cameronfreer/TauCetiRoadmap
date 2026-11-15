import TauCetiRoadmap.RandomGraphs.Suggested

/-!
# RandomGraphs: boundary checks moved out of `Suggested.lean`

Each snippet compiles against `TauCetiRoadmap/RandomGraphs/Suggested.lean` at the head of this
pass. The README keeps every statement below as part of the roadmap; these are checks that the
prototype's definitions meet a convention or a supplier's form, or that a general statement
instantiates, not further targets. All are proved here, some through admitted prototype theorems.
-/

open MeasureTheory FirstOrder FirstOrder.Language CategoryTheory TauCeti.DenseGraphLimits
open scoped unitInterval

namespace TauCetiRoadmap.RandomGraphs

universe u v w

/-- The README's strong amalgamation property (Layer 1), spelled here for this check only:
`Suggested.lean` does not declare it. -/
def StrongAmalgamation {L : FirstOrder.Language.{u, v}} (K : Set (Bundled.{w} L.Structure)) :
    Prop :=
  ∀ (A B C : Bundled.{w} L.Structure) (f : A ↪[L] B) (g : A ↪[L] C),
    A ∈ K → B ∈ K → C ∈ K →
      ∃ (D : Bundled.{w} L.Structure) (i : B ↪[L] D) (j : C ↪[L] D),
        D ∈ K ∧ i.comp f = j.comp g ∧
          Set.range i ∩ Set.range j = Set.range (i.comp f)

/-- Convention check (Layer 1): the strong-amalgamation square uses Mathlib's commuting
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

/-- Direction check (Layer 4.1): a larger budget gives a smaller one (`e ≤ d`). -/
theorem HasExtensionUpTo.mono {V : Type u} {G : SimpleGraph V} {d e : ℕ}
    (h : HasExtensionUpTo G d) (hed : e ≤ d) : HasExtensionUpTo G e :=
  fun U Z hUZ hc => h U Z hUZ (hc.trans hed)

/-- Adapter check (Layer 5.2): the computable QE contract yields semantic quantifier
elimination modulo `T_R` (for every context `Fin m`, in models of any universe). -/
theorem exists_isQF_equivalent {m : ℕ} (φ : Language.graph.Formula (Fin m)) :
    ∃ ψ : Language.graph.Formula (Fin m), ψ.IsQF ∧
      ∀ (M : Type w) [Language.graph.Structure M], M ⊨ radoAxioms →
        ∀ a : Fin m → M, ψ.Realize a ↔ φ.Realize a :=
  let ⟨_, _, hQ⟩ := exists_computable_quantifierElimination.{w}
  let ⟨ψ, _, hψ⟩ := hQ m φ
  ⟨ψ, hψ⟩

/-- Supplier-boundary check (Layer 10): Tau Ceti's
`SimpleGraph.HasExtensionProperty.realize_scottSentence_iff` holds in a target graph of any
cardinality, so `Θ_R` and the Scott sentence of `R` agree on graphs in every universe. -/
theorem satisfiesInf_radoSentenceInf_iff_scottSentence {V : Type u} (G : SimpleGraph V) :
    SatisfiesInf G radoSentenceInf ↔
      SatisfiesInf G (@TauCeti.scottSentence Language.graph _ ℕ TauCeti.radoGraph.structure _ _) :=
  (satisfiesInf_radoSentenceInf_iff G).trans
    (TauCeti.hasExtensionProperty_radoGraph.realize_scottSentence_iff G).symm

/-- Boundary check (Layer 10): `cardEq m` means cardinality exactly `m`, including `m = 0` on
the empty carrier, and fails on infinite carriers. -/
theorem satisfies_cardEq_iff {V : Type u} (G : SimpleGraph V) (m : ℕ) :
    Satisfies G (cardEq m) ↔ Cardinal.mk V = m := by
  let _ := G.structure
  simp only [Satisfies, cardEq, Sentence.realize_inf, Sentence.realize_not,
    Sentence.realize_cardGe, Nat.cast_succ, Cardinal.natCast_add_one_le_iff, not_lt]
  exact and_comm.trans le_antisymm_iff.symm

/-- Library check (Layer 0.1): sentence satisfaction is invariant under graph isomorphism, by
Tau Ceti's `SimpleGraph.Iso.toLanguageEquiv` and Mathlib's realization transport. -/
theorem satisfies_iso {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (φ : Language.graph.Sentence) : Satisfies G φ ↔ Satisfies H φ :=
  letI := G.structure
  letI := H.structure
  StrongHomClass.realize_sentence e.toLanguageEquiv φ

/-- Library check (Layer 9.3): under a graphon mixture the probability of a sentence is the
integral of its graphon-sample probabilities, by `Measure.bind_apply`, the section of the joint
event `measurableSet_realize_jointly` at the empty assignments, and Tau Ceti's
`measurable_infiniteSampleLawOnSpace`. -/
theorem bind_infiniteSampleLawOnSpace_satisfies (P : ProbabilityMeasure GraphonSpaceI)
    (φ : Language.graph.Sentence) :
    (P : Measure GraphonSpaceI).bind infiniteSampleLawOnSpace {G | Satisfies G φ} =
      ∫⁻ x, infiniteSampleLawOnSpace x {G | Satisfies G φ} ∂(P : Measure GraphonSpaceI) :=
  Measure.bind_apply
    (by
      have h := (measurableSet_realize_jointly (V := ℕ) φ).preimage
        (measurable_id.prodMk (measurable_const (a := ((default : Empty → ℕ), (default : Fin 0 → ℕ)))))
      convert h using 1
      ext G
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, id, Satisfies, Sentence.Realize,
        Formula.Realize]
      -- the two `default` empty assignments agree (`Empty → ℕ` and `Fin 0 → ℕ` are subsingletons)
      congr! 1)
    measurable_infiniteSampleLawOnSpace.aemeasurable

/-- Instance check (Layer 5.2): the graph language is effectively presented, so the general
coding theorem applies to it; its arities are computable (there are no function symbols, and the
one relation symbol has arity `2`). -/
example :=
  computable_boundedCode (L := Language.graph)
    ((Computable.const 0).of_eq fun s => isEmptyElim s)
    ((Computable.const 2).of_eq (by rintro ⟨_, ⟨⟩⟩; rfl))

/-- A language with one unary function symbol `s` and no relation symbols. -/
inductive UnarySymbol : ℕ → Type
  | s : UnarySymbol 1

/-- The language of one unary function. -/
def unaryLanguage : FirstOrder.Language.{0, 0} := ⟨UnarySymbol, fun _ => Empty⟩

/-- Its one function symbol, numbered through `Unit`. -/
def unarySymbolEquiv : (Σ l, unaryLanguage.Functions l) ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨1, .s⟩
  left_inv := by rintro ⟨_, ⟨⟩⟩; rfl
  right_inv _ := rfl

instance : Primcodable (Σ l, unaryLanguage.Functions l) := Primcodable.ofEquiv Unit unarySymbolEquiv

instance : IsEmpty (Σ l, unaryLanguage.Relations l) := ⟨fun ⟨_, r⟩ => (r : Empty).elim⟩

instance : Primcodable (Σ l, unaryLanguage.Relations l) :=
  Primcodable.ofEquiv Empty (Equiv.equivEmpty _)

/-- Instance check (Layer 5.2): a language with a unary function symbol, whose terms are not
variables alone, instantiates the general term and formula coding theorems. -/
example :=
  computable_termCode (L := unaryLanguage) ((Computable.const 1).of_eq (by rintro ⟨_, ⟨⟩⟩; rfl))

example :=
  computable_boundedCode (L := unaryLanguage)
    ((Computable.const 1).of_eq (by rintro ⟨_, ⟨⟩⟩; rfl))
    ((Computable.const 0).of_eq fun s => isEmptyElim s)

/-- Round-trip check (Layer 5.2): the code of `s(x₀) = x₀` over `Fin 1` decodes to itself. -/
example :
    let t : unaryLanguage.Term (Fin 1 ⊕ Fin 0) := Term.func UnarySymbol.s ![Term.var (Sum.inl 0)]
    boundedDecode unaryLanguage (Fin 1) 0 (boundedCode (t.bdEqual (Term.var (Sum.inl 0)))) =
      some (t.bdEqual (Term.var (Sum.inl 0))) :=
  boundedDecode_boundedCode _

end TauCetiRoadmap.RandomGraphs
