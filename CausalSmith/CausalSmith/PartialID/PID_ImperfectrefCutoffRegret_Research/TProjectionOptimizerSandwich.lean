import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TFiniteSampleOptimizerCoverage

set_option linter.style.longLine false

/-! Common-primitive optimizer sandwich, its deterministic comparison with the
coordinatewise screen, and a generic (not data-realization) three-score witness. -/

open MeasureTheory

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

noncomputable section

def ProjectionSandwichEvent {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Set Ω :=
  {sample | projectionInner D G sample hSizes ⊆ optimizerSet M ∧
    optimizerSet M ⊆ projectionOuter D G sample hSizes}

def ProjectionCoverageConclusion {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Prop :=
  μ.real (ProjectionSandwichEvent D G hSizes) ≥
    1 - D.ηs - D.ηα - D.ηβ

def ProjectionOuterEnvelopeConclusion {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Prop :=
  ∀ sample, projectionOuter D G sample hSizes ⊆ optimizerConfSet D G sample hSizes

/-- Algebraic compatibility of a tuple, without asserting that it is a
confidence set from any realized data. -/
def AlgebraicallyCompatible {K : ℕ} (θ : PrimitiveTuple K) : Prop :=
  candidateTotalMass θ = 1 ∧
  θ.alpha = 1 ∧ θ.beta = 1 ∧ candYouden θ = 1 ∧
  0 < θ.pi ∧ θ.pi < 1 ∧
  candYouden θ * θ.pi = candMass θ true + θ.beta - 1 ∧
  θ.a true = θ.alpha * θ.pi ∧
  θ.a false = (1 - θ.alpha) * θ.pi ∧
  ∀ r, 0 ≤ θ.a r ∧ θ.a r ≤ candMass θ r

/-- Signed atom contributions in the generic three-score construction. -/
def genericSignedCell (s : ℝ) (k : Fin 3) : ℝ :=
  let d : ℝ := 2 / 5
  if k = 0 then d * (2 * s - 1)
  else if k = 1 then d * (3 / 5 - s)
  else 2 * d / 5

/-- Common positive filler added to both reference cells of every score atom. -/
def genericCellFiller (s : ℝ) : ℝ :=
  (1 - ∑ k : Fin 3, |genericSignedCell s k|) / 6

def genericObservedCell (s : ℝ) (r : Bool) (k : Fin 3) : ℝ :=
  genericCellFiller s +
    if r then max (genericSignedCell s k) 0
    else max (-genericSignedCell s k) 0

/-- Value of policy `j`, which refers atoms `j,j+1,...,2`. -/
def genericPolicyValue (s : ℝ) (j : Fin 3) : ℝ :=
  ∑ k : Fin 3, if (j : ℕ) ≤ (k : ℕ) then genericSignedCell s k else 0

def genericPolicyRegret (s : ℝ) (j : Fin 3) : ℝ :=
  (Finset.univ.image (fun i : Fin 3 =>
    genericPolicyValue s i - genericPolicyValue s j)).max'
      (by simp)

def genericCoordinateLower (j : Fin 3) : ℝ :=
  sInf {x | ∃ s ∈ Set.Icc (0 : ℝ) 1, x = genericPolicyRegret s j}

def genericCoordinateUpper (j : Fin 3) : ℝ :=
  sSup {x | ∃ s ∈ Set.Icc (0 : ℝ) 1, x = genericPolicyRegret s j}

def genericCoordinateScreen : Set (Fin 3) :=
  {j | genericCoordinateLower j ≤
    (Finset.univ.image genericCoordinateUpper).min' (by simp)}

def genericCommonArgminUnion : Set (Fin 3) :=
  {j | ∃ s ∈ Set.Icc (0 : ℝ) 1,
    ∀ i : Fin 3, genericPolicyRegret s j ≤ genericPolicyRegret s i}

/-- Generic common-primitive counterexample.  This deliberately makes no claim
that the displayed family equals a confidence set for a particular dataset. -/
def GenericThreeScoreCommonPrimitiveWitness : Prop :=
  ∃ θ : ℝ → PrimitiveTuple 2,
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      AlgebraicallyCompatible (θ s) ∧
      (∀ r k, (θ s).omega r k = genericObservedCell s r k) ∧
      (θ s).alpha = 1 ∧ (θ s).beta = 1 ∧
      (θ s).pi = candMass (θ s) true ∧
      (θ s).a true = (θ s).pi ∧ (θ s).a false = 0 ∧
      1 / 30 ≤ genericCellFiller s ∧
      (∀ j : Fin 3, genericPolicyValue s j =
        ∑ k : Fin 3, if (j : ℕ) ≤ (k : ℕ) then
          (θ s).omega true k - (θ s).omega false k else 0)) ∧
    let d : ℝ := 2 / 5
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      genericPolicyValue s 0 = d * s ∧
      genericPolicyValue s 1 = d * (1 - s) ∧
      genericPolicyValue s 2 = d * (2 / 5)) ∧
    genericCoordinateLower 0 = 0 ∧ genericCoordinateUpper 0 = d ∧
    genericCoordinateLower 1 = 0 ∧ genericCoordinateUpper 1 = d ∧
    genericCoordinateLower 2 = d / 10 ∧ genericCoordinateUpper 2 = 3 * d / 5 ∧
    genericCoordinateScreen = Set.univ ∧
    genericCommonArgminUnion = {j | j = 0 ∨ j = 1} ∧
    genericCommonArgminUnion ⊂ genericCoordinateScreen

def ActivationComparisonConclusion {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Prop :=
  ∀ sample, (compatiblePrimitiveSet D G sample hSizes).Nonempty →
    (∅ : Set EReal) ⊆ projectionInner D G sample hSizes ∧
    projectionOuter D G sample hSizes ⊆ M.T ∧
    ((∅ : Set EReal) ⊂ projectionInner D G sample hSizes ↔
      (projectionInner D G sample hSizes).Nonempty) ∧
    (projectionOuter D G sample hSizes ⊂ M.T ↔
      projectionOuter D G sample hSizes ≠ M.T)

theorem projection_sandwich_coverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : ImperfectReferenceModel) (D : EvaluationDesign M μ)
    (G : PolicyGrid M)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M)
    (hEval : IidEvaluation M μ D.Z)
    (hSensitivity : ExternalSensitivitySample M μ D.X₁)
    (hSpecificity : ExternalSpecificitySample M μ D.X₀)
    (hb : PositiveBenefit M) (hc : PositiveCost M)
    (DkwMassartTwoSided_of_gate : DkwMassartTwoSided) :
    ProjectionCoverageConclusion D G hSizes := by sorry

theorem projection_outer_subset_envelope {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : ImperfectReferenceModel) (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀)
    (hb : PositiveBenefit M) (hc : PositiveCost M) :
    ProjectionOuterEnvelopeConclusion D G hSizes := by sorry

theorem coordinatewise_coverage_not_reverse :
    GenericThreeScoreCommonPrimitiveWitness := by sorry

theorem revised_projection_activation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : ImperfectReferenceModel) (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) :
    ActivationComparisonConclusion D G hSizes := by sorry

def ProjectionOptimizerSandwichConclusion {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Prop :=
  ProjectionCoverageConclusion D G hSizes ∧
  ProjectionOuterEnvelopeConclusion D G hSizes ∧
  GenericThreeScoreCommonPrimitiveWitness ∧
  ActivationComparisonConclusion D G hSizes

-- @node: thm:finite-policy-grid-optimizer-sandwich
theorem finite_policy_grid_optimizer_sandwich {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : ImperfectReferenceModel) (D : EvaluationDesign M μ)
    (G : PolicyGrid M)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M)
    (hEval : IidEvaluation M μ D.Z)
    (hSensitivity : ExternalSensitivitySample M μ D.X₁)
    (hSpecificity : ExternalSpecificitySample M μ D.X₀)
    (hb : PositiveBenefit M) (hc : PositiveCost M)
    (DkwMassartTwoSided_of_gate : DkwMassartTwoSided) :
    ProjectionOptimizerSandwichConclusion D G hSizes := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact projection_sandwich_coverage μ M D G hSizes hg hπ hEval hSensitivity
      hSpecificity hb hc DkwMassartTwoSided_of_gate
  · exact projection_outer_subset_envelope μ M D G hSizes hb hc
  · exact coordinatewise_coverage_not_reverse
  · exact revised_projection_activation μ M D G hSizes

end
end CausalSmith.PartialID.ImperfectrefCutoffRegret
