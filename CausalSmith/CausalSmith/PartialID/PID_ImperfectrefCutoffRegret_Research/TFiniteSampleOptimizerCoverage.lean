import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.Projection
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.CitedGates
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TSharpRegretFormula

/-! Simultaneous finite-policy-grid regret and optimizer coverage for arbitrary
Borel score laws within the cutoff-generated atoms. -/

open MeasureTheory

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

noncomputable section

def RegretBandEvent {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Set Ω :=
  {sample | ∀ t, ∀ ht : t ∈ M.T,
    regretLowerEnv D G sample hSizes t ≤ regretAt M ⟨t, ht⟩ ∧
      regretAt M ⟨t, ht⟩ ≤ regretUpperEnv D G sample hSizes t}

/-- The population tuple exactly reproduces every represented regret coordinate;
this is an equality, not an outer approximation. -/
def PopulationGridReduction (M : ImperfectReferenceModel)
    (G : PolicyGrid M) : Prop :=
  ∀ t : Cutoff M,
    candidateRegret M G (populationPrimitive M G) t = regretAt M t

def FinitePolicyGridCoverageConclusion {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ImperfectReferenceModel} (D : EvaluationDesign M μ)
    (G : PolicyGrid M) (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀) : Prop :=
  μ.real (PopulationPrefixBandEvent D G) ≥ 1 - D.ηs - D.ηα - D.ηβ ∧
  PopulationGridReduction M G ∧
  PopulationPrefixBandEvent D G ⊆ RegretBandEvent D G hSizes ∧
  μ.real (RegretBandEvent D G hSizes) ≥ 1 - D.ηs - D.ηα - D.ηβ ∧
  (∀ sample ∈ RegretBandEvent D G hSizes, (optimizerSet M).Nonempty →
    optimizerSet M ⊆ optimizerConfSet D G sample hSizes ∧
    minimaxRegretValue M ∈ Set.Icc
      (sInf (regretLowerEnv D G sample hSizes '' M.T))
      (sInf (regretUpperEnv D G sample hSizes '' M.T)))

theorem finite_grid_prefix_band_coverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : ImperfectReferenceModel) (D : EvaluationDesign M μ)
    (G : PolicyGrid M)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀)
    (hEval : IidEvaluation M μ D.Z)
    (hSensitivity : ExternalSensitivitySample M μ D.X₁)
    (hSpecificity : ExternalSpecificitySample M μ D.X₀)
    (DkwMassartTwoSided_of_gate : DkwMassartTwoSided) :
    μ.real (PopulationPrefixBandEvent D G) ≥
      1 - D.ηs - D.ηα - D.ηβ := by sorry

theorem population_grid_reduction (M : ImperfectReferenceModel)
    (G : PolicyGrid M)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M)
    (hb : PositiveBenefit M) (hc : PositiveCost M) :
    PopulationGridReduction M G := by sorry

theorem finite_grid_envelope_and_optimizer_coverage {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (M : ImperfectReferenceModel)
    (D : EvaluationDesign M μ) (G : PolicyGrid M)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M)
    (hb : PositiveBenefit M) (hc : PositiveCost M) :
    PopulationGridReduction M G →
    PopulationPrefixBandEvent D G ⊆ RegretBandEvent D G hSizes ∧
    (∀ sample ∈ RegretBandEvent D G hSizes, (optimizerSet M).Nonempty →
      optimizerSet M ⊆ optimizerConfSet D G sample hSizes ∧
      minimaxRegretValue M ∈ Set.Icc
        (sInf (regretLowerEnv D G sample hSizes '' M.T))
        (sInf (regretUpperEnv D G sample hSizes '' M.T))) := by sorry

-- @node: thm:finite-policy-grid-optimizer-coverage
theorem finite_policy_grid_optimizer_coverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : ImperfectReferenceModel) (D : EvaluationDesign M μ)
    (G : PolicyGrid M)
    (hSizes : PositiveSampleSizes D.n D.n₁ D.n₀)
    (hEval : IidEvaluation M μ D.Z)
    (hSensitivity : ExternalSensitivitySample M μ D.X₁)
    (hSpecificity : ExternalSpecificitySample M μ D.X₀)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M)
    (hb : PositiveBenefit M) (hc : PositiveCost M)
    (DkwMassartTwoSided_of_gate : DkwMassartTwoSided) :
    FinitePolicyGridCoverageConclusion D G hSizes := by
  let _ : IsProbabilityMeasure μ := D.probability
  have hprefix := finite_grid_prefix_band_coverage μ M D G hSizes hEval hSensitivity
    hSpecificity DkwMassartTwoSided_of_gate
  have hreduce := population_grid_reduction M G hg hπ hb hc
  obtain ⟨hband, hoptimizer⟩ :=
    finite_grid_envelope_and_optimizer_coverage μ M D G hSizes hg hπ hb hc hreduce
  refine ⟨hprefix, hreduce, hband, ?_, hoptimizer⟩
  exact hprefix.trans (measureReal_mono (μ := μ) hband)

end
end CausalSmith.PartialID.ImperfectrefCutoffRegret
