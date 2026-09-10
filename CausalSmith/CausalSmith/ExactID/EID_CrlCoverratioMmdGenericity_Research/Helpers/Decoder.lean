import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Kernel
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Measure.Support
import Causalean.Mathlib.CondIndep

/-!
# Population ratio and conditional-rank decoder

The decoder is a function only of the observed probability laws.  It selects a
topological ordering internally, constructs `[0,1]`-valued conditional ranks,
and prunes to the unique minimal admissible parent sets on the model domain.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @env: S4
variable {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}

/-- A numerical linear extension of a directed relation. Injectivity excludes tied labels. -/
def IsTopologicalOrdering (E : Fin n → Fin n → Prop) (order : Fin n → ℕ) : Prop :=
  Function.Injective order ∧ ∀ ⦃j i⦄, E j i → order j < order i

/-- Labels preceding `i` in the explicitly selected ordering. -/
def predecessorSet (order : Fin n → ℕ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => order j < order i)
  -- @realizes \(B_i\)(labels preceding i in the selected order)

/-- Projection of a coordinate family onto a finite index set. -/
def familyProjection {X Y : Type*} (U : Fin n → X → Y) (S : Finset (Fin n))
    (x : X) : (j : {j // j ∈ S}) → Y := fun j => U j x

/-- A decoder input consists of genuine probability laws in all `n+1` environments. -/
abbrev ObservedProbabilityLawFamily (n : ℕ) :=
  {laws : ObservedLawFamily n // ∀ e, IsProbabilityMeasure (laws e)}

/-- Turn a measure family into a probability-law family when it is one, using a fixed
Dirac probability family only outside that domain.  Model hypotheses prove that this
fallback is never used by the exact-decoder theorem. -/
noncomputable def observedProbabilityLawFamily (laws : ObservedLawFamily n) :
    ObservedProbabilityLawFamily n := by
  classical
  exact if h : ∀ e, IsProbabilityMeasure (laws e) then ⟨laws, h⟩
  else ⟨fun _ => Measure.dirac 0, by intro e; infer_instance⟩

/-- The observable log ratio constructed from the observed Radon--Nikodym ratio. -/
def observedLawLogRatio (laws : ObservedLawFamily n) (i : Fin n) (x : LatentState n) : ℝ :=
  Real.log (observedLawRatio laws i x)

/-- Population MMD computed solely from the observed environment laws. -/
def observedLawDiscrepancy
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : UnitNormFeatureMap H) (laws : ObservedLawFamily n) (j i : Fin n) : ℝ :=
  ‖meanEmbedding U (Measure.map (observedLawRatio laws i) (laws 0)) -
    meanEmbedding U (Measure.map (observedLawRatio laws i) (laws j.succ))‖

/-- The ratio graph constructed solely from observed laws. -/
def observedLawRatioGraph
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : UnitNormFeatureMap H) (laws : ObservedLawFamily n) :
    Fin n → Fin n → Prop :=
  fun j i => j ≠ i ∧ 0 < observedLawDiscrepancy U laws j i
  -- @realizes \(H_D\)(observed-law MMD graph)

/-- The predecessor log-ratio vector used as the conditioning variable. -/
abbrev PredecessorLogRatios (order : Fin n → ℕ) (i : Fin n) :=
  (j : {j // j ∈ predecessorSet order i}) → ℝ

/-- The joint observed log-ratio and predecessor-log-ratio argument. -/
def conditionalRatioArgument (laws : ObservedLawFamily n) (order : Fin n → ℕ)
    (i : Fin n) (x : LatentState n) : ℝ × PredecessorLogRatios order i :=
  (observedLawLogRatio laws i x,
    familyProjection (observedLawLogRatio laws) (predecessorSet order i) x)

/-- The law-derived support on which a conditional-CDF version is required to be continuous. -/
def observedConditionalRatioSupport (laws : ObservedLawFamily n) (order : Fin n → ℕ)
    (i : Fin n) : Set (ℝ × PredecessorLogRatios order i) :=
  Measure.support (Measure.map (conditionalRatioArgument laws order i) (laws i.succ))

/-- The raw regular-conditional-distribution representative, with the original zero fallback
when the supplied environment laws are not finite. -/
def rawObservedConditionalRatioCDF
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n) (t : ℝ)
    (ell : PredecessorLogRatios order i) : ℝ := by
  classical
  exact if hfinite : ∀ e, IsFiniteMeasure (laws.1 e) then
    letI := hfinite i.succ
    (ProbabilityTheory.condDistrib (observedLawLogRatio laws.1 i)
        (familyProjection (observedLawLogRatio laws.1) (predecessorSet order i))
        (laws.1 i.succ) ell (Set.Iic t)).toReal
  else 0

/-- A law-only conditional-CDF version: it agrees almost everywhere with the regular
conditional distribution at every threshold and is continuous on the joint model support. -/
def IsContinuousConditionalRatioCDFVersion
  (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n)
    (C : ℝ → PredecessorLogRatios order i → Set.Icc (0 : ℝ) 1) : Prop :=
  (∀ t, (fun ell => (C t ell : ℝ)) =ᵐ[Measure.map
      (familyProjection (observedLawLogRatio laws.1) (predecessorSet order i)) (laws.1 i.succ)]
      rawObservedConditionalRatioCDF laws order i t) ∧
  ContinuousOn (fun z : ℝ × PredecessorLogRatios order i => (C z.1 z.2 : ℝ))
    (observedConditionalRatioSupport laws.1 order i)

/-- The raw conditional-CDF representative as a unit-interval value, retaining it when it
has the required range and using zero only as the range-check fallback. -/
def rawObservedConditionalRatioCDFUnit
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n) (t : ℝ)
    (ell : PredecessorLogRatios order i) : Set.Icc (0 : ℝ) 1 := by
  classical
  exact if h : rawObservedConditionalRatioCDF laws order i t ell ∈ Set.Icc (0 : ℝ) 1 then
    ⟨rawObservedConditionalRatioCDF laws order i t ell, h⟩
  else ⟨0, by constructor <;> norm_num⟩

/-- The continuous conditional-CDF version selected from the observed laws alone. If no
continuous version exists, this retains the raw `condDistrib`/zero fallback. -/
noncomputable def observedConditionalRatioCDF
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n) :
    ℝ → PredecessorLogRatios order i → Set.Icc (0 : ℝ) 1 := by
  classical
  exact if h : ∃ C, IsContinuousConditionalRatioCDFVersion laws order i C then
    Classical.choose h
  else rawObservedConditionalRatioCDFUnit laws order i
  -- @realizes \(C_i\)(law-selected continuous conditional-CDF version)

/-- The identified rank coordinate, constructed only from observed laws and an explicit ordering. -/
def observedLawRankCoordinate
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n)
    (x : LatentState n) : Set.Icc (0 : ℝ) 1 :=
  observedConditionalRatioCDF laws order i (observedLawLogRatio laws.1 i x)
    (familyProjection (observedLawLogRatio laws.1) (predecessorSet order i) x)
  -- @realizes \(U_i\)(conditional rank computed from observed laws)

/-- Conditional independence of two measurable functions given a third. -/
def CondIndepGiven {Ω A B C : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure Ω) (X : Ω → A) (Y : Ω → B) (Z : Ω → C) : Prop :=
  ∃ hμ : IsFiniteMeasure μ,
    letI := hμ
    ∃ _hX : Measurable X,
      ∃ _hY : Measurable Y,
        ∃ hZ : Measurable Z,
          ProbabilityTheory.CondIndepFun (MeasurableSpace.comap Z inferInstance)
            hZ.comap_le X Y μ

/-- A candidate parent set satisfies the observed-law conditional-independence test. -/
def AdmissibleParentSet (laws : ObservedProbabilityLawFamily n)
    (order : Fin n → ℕ) (i : Fin n) (A : Finset (Fin n)) : Prop :=
  A ⊆ predecessorSet order i ∧
    CondIndepGiven (laws.1 0) (observedLawRankCoordinate laws order i)
      (familyProjection (observedLawRankCoordinate laws order)
        ((predecessorSet order i) \ A))
      (familyProjection (observedLawRankCoordinate laws order) A)

/-- Inclusion-minimal admissibility for parent pruning. -/
def MinimalAdmissibleParentSet (laws : ObservedProbabilityLawFamily n)
    (order : Fin n → ℕ) (i : Fin n) (A : Finset (Fin n)) : Prop :=
  AdmissibleParentSet laws order i A ∧
    ∀ B, AdmissibleParentSet laws order i B → B ⊆ A → A ⊆ B

/-- The uniquely inclusion-minimal admissible set, defined only when it is genuinely unique.
`none` records that the observed laws lie outside the decoder's parent-pruning domain. -/
def selectedParentSet (laws : ObservedProbabilityLawFamily n)
    (order : Fin n → ℕ) (i : Fin n) : Option (Finset (Fin n)) := by
  classical
  exact if h : ∃! A : Finset (Fin n), MinimalAdmissibleParentSet laws order i A then
    some (Classical.choose h.exists)
  else none

/-- The parent relation carried by a successful unique-minimum selection. -/
def selectedParentRelation (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) :
    Fin n → Fin n → Prop :=
  fun j i => ∃ A, selectedParentSet laws order i = some A ∧ j ∈ A

/-- Every selected edge points forward in the supplied ordering. -/
lemma selectedParentSet_precedes
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) {j i : Fin n}
    (hj : selectedParentRelation laws order j i) : order j < order i := by
  rcases hj with ⟨A, hA, hjA⟩
  unfold selectedParentSet at hA
  split at hA
  · rename_i h_unique
    injection hA with hA'
    subst A
    simpa [predecessorSet] using (Classical.choose_spec h_unique.exists).1.1 hjA
  · simp at hA

/-- The selected-parent relation is acyclic because every edge points forward in `order`. -/
lemma selectedParentRelation_acyclic
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n) :
    ¬ Relation.TransGen (selectedParentRelation laws order) i i := by
  intro h
  have path_lt : ∀ {a b : Fin n},
      Relation.TransGen (selectedParentRelation laws order) a b → order a < order b := by
    intro a b hab
    induction hab with
    | single hji => exact selectedParentSet_precedes laws order hji
    | tail hab hbc ih => exact lt_trans ih (selectedParentSet_precedes laws order hbc)
  have hi : order i < order i := path_lt h
  exact (lt_irrefl _ hi)

/-- The acyclic graph induced by all successful unique-minimum parent selections. -/
def selectedParentDAG (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) :
    Causalean.DAG (Fin n) where
  edge := selectedParentRelation laws order
  decEdge := Classical.decRel _
  acyclic := selectedParentRelation_acyclic laws order

/-- Compatibility restricts law-coherence comparisons to representations of the same observed
law family on the same observed support. -/
def CompatibleObservedRepresentation
    {G₁ G₂ : Causalean.DAG (Fin n)} {θ₁ : Mechanism n G₁} {θ₂ : Mechanism n G₂}
    (W₁ : ObservedWorld G₁ θ₁) (W₂ : ObservedWorld G₂ θ₂) : Prop :=
  W₁.law = W₂.law ∧ observedSupport G₁ W₁ = observedSupport G₂ W₂

/-- Coherence uses almost-everywhere Radon--Nikodym representatives, but compares the selected
continuous ranks pointwise on the full common observed support. -/
def ObservedWorldLawCoherent {θ : Mechanism n G} (W : ObservedWorld G θ) : Prop :=
  (∀ i, W.ratio i =ᵐ[W.law 0] observedLawRatio W.law i) ∧
  ∀ (G' : Causalean.DAG (Fin n)) (θ' : Mechanism n G') (W' : ObservedWorld G' θ'),
    CompatibleObservedRepresentation W W' → ∀ order i,
      ∀ x ∈ observedSupport G W,
        observedLawRankCoordinate (observedProbabilityLawFamily W'.law) order i x =
          observedLawRankCoordinate (observedProbabilityLawFamily W.law) order i x

/-- A topological ordering selected from the ratio graph using only the observed laws.  The
numeric label order is a total fallback outside the acyclic model domain. -/
noncomputable def selectedTopologicalOrder
    (laws : ObservedProbabilityLawFamily n) : Fin n → ℕ := by
  classical
  exact if h : ∃ order, IsTopologicalOrdering
      (observedLawRatioGraph gaussianFeatureMap laws.1) order then
    Classical.choose h
  else fun i => i.val

-- @node: def:population-decoder
/-- The law-only population recovery map.  It forms the Gaussian-MMD graph, selects its own
topological ordering, constructs unit-interval ranks, and returns the parent-pruned DAG. -/
def populationDecoder (laws : ObservedProbabilityLawFamily n) :
    (Fin n → Fin n → Prop) ×
      (Fin n → LatentState n → Set.Icc (0 : ℝ) 1) × Causalean.DAG (Fin n) :=
  let order := selectedTopologicalOrder laws
  (observedLawRatioGraph gaussianFeatureMap laws.1,
    observedLawRankCoordinate laws order, selectedParentDAG laws order)
  -- @realizes \(\mathscr D\)(ratio graph, rank coordinates, parent-pruned environment DAG)

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
