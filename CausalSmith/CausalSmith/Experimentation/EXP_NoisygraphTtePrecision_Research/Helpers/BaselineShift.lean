module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BaselineTranslationAffinity
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BaselineTranslationEnergy

/-!
# Baseline translation and general Hellinger controls

Cold scaffold: definitions are complete; proof obligations are reserved for Stage 3.
-/

public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

/-- [The compact baseline is normalized and has the full square-root translation package;
Hellinger energy controls TV, tensorizes subadditively, and averages over a common marginal.](goal) -/
-- @node: lem:baseline-shift-control
lemma baseline_shift_control :
    ((∀ y, 0 ≤ CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity y) ∧ Integrable CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity ∧ -- @realizes f(nonnegative integrable baseline density)
      (∫ y, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity y) = 1) ∧
    LipschitzWith ((4*Real.pi).toNNReal) (fun y => Real.sqrt (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity y)) ∧
    (∀ a b : ℝ, a ≤ b → Real.sqrt (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity b) - Real.sqrt (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity a) =
      ∫ y in a..b, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.baselineSqrtDerivative y) ∧
    (∫ y, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.baselineSqrtDerivative y ^ 2) = 4 * Real.pi^2 ∧
    (∀ s t : ℝ, (∫ y, (Real.sqrt (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y-s)) -
      Real.sqrt (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity (y-t)))^2) ≤ 4*Real.pi^2*(s-t)^2) ∧
    (∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
      (f g : Ω → ℝ), Measurable f → Measurable g → (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) →
      IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) →
      IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (g x))) →
      Causalean.Stat.tvDist (μ.withDensity (fun x => ENNReal.ofReal (f x)))
        (μ.withDensity (fun x => ENNReal.ofReal (g x))) ≤ Real.sqrt (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.hellingerEnergy μ f g)) ∧
    (∀ (ι : Type*) [Fintype ι] (Ω : ι → Type*) [∀ i, MeasurableSpace (Ω i)]
      (μ : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (μ i)] (f g : ∀ i, Ω i → ℝ),
      (∀ i, Integrable (f i) (μ i)) → (∀ i, Integrable (g i) (μ i)) →
      (∀ i x, 0 ≤ f i x) → (∀ i x, 0 ≤ g i x) →
      (∀ i, (∫ x, f i x ∂μ i) = 1) → (∀ i, (∫ x, g i x ∂μ i) = 1) →
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.hellingerEnergy (Measure.pi μ) (fun x : ∀ i, Ω i => ∏ i, f i (x i))
        (fun x => ∏ i, g i (x i)) ≤ ∑ i, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.hellingerEnergy (μ i) (f i) (g i)) ∧
    (∀ (Ξ Ω : Type) [MeasurableSpace Ξ] [MeasurableSpace Ω]
      (ν : Measure Ξ) [IsProbabilityMeasure ν] (μ : Measure Ω) [SigmaFinite μ]
      (f g : Ξ → Ω → ℝ), Measurable (fun p : Ξ × Ω => f p.1 p.2) →
      Measurable (fun p : Ξ × Ω => g p.1 p.2) →
      (∀ ξ x, 0 ≤ f ξ x) → (∀ ξ x, 0 ≤ g ξ x) →
      (∀ ξ, IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f ξ x)))) →
      (∀ ξ, IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (g ξ x)))) →
      Causalean.Stat.Minimax.hellingerSqMeasure (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.densityJoint ν μ f) (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.densityJoint ν μ g) =
        ∫ ξ, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.hellingerEnergy μ (f ξ) (g ξ) ∂ν) := by
  refine ⟨⟨CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_nonneg,
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.cosSqDensity_integrable_normalized⟩,
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.baseline_sqrt_lipschitz,
    ?_, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.baselineSqrtDerivative_energy,
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.baseline_translation_energy,
    ?_, ?_, ?_⟩
  · intro a b hab
    exact (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.baselineSqrtDerivative_integral
      a b hab).symm
  · intro Ω _ μ _ f g hf hg hf0 hg0 hfp hgp
    letI := hfp
    letI := hgp
    exact CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.density_tv_le_sqrt_hellingerEnergy
      μ f g hf hg hf0 hg0
  · intro ι _ Ω _ μ _ f g hf hg hf0 hg0 hf1 hg1
    have hFp : Integrable (fun x : ∀ i, Ω i => ∏ i, f i (x i)) (Measure.pi μ) :=
      Integrable.fintype_prod_dep hf
    have hGp : Integrable (fun x : ∀ i, Ω i => ∏ i, g i (x i)) (Measure.pi μ) :=
      Integrable.fintype_prod_dep hg
    have hF0 : ∀ x : ∀ i, Ω i, 0 ≤ ∏ i, f i (x i) :=
      fun x => Finset.prod_nonneg (fun i _ => hf0 i (x i))
    have hG0 : ∀ x : ∀ i, Ω i, 0 ≤ ∏ i, g i (x i) :=
      fun x => Finset.prod_nonneg (fun i _ => hg0 i (x i))
    have hF1 : (∫ x : ∀ i, Ω i, ∏ i, f i (x i) ∂Measure.pi μ) = 1 := by
      rw [integral_fintype_prod_eq_prod]; simp [hf1]
    have hG1 : (∫ x : ∀ i, Ω i, ∏ i, g i (x i) ∂Measure.pi μ) = 1 := by
      rw [integral_fintype_prod_eq_prod]; simp [hg1]
    have hE (i : ι) :
        CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.hellingerEnergy (μ i) (f i) (g i) =
          2 * (1 - Causalean.Stat.densityAffinity (μ i) (f i) (g i)) :=
      Causalean.Stat.hellingerSqDensity_eq_two_mul_one_sub_affinity
        (μ i) (f i) (g i) (hf i) (hg i) (hf0 i) (hg0 i) (hf1 i) (hg1 i)
    have ha0 (i : ι) : 0 ≤ Causalean.Stat.densityAffinity (μ i) (f i) (g i) :=
      integral_nonneg (fun _ => Real.sqrt_nonneg _)
    have ha1 (i : ι) : Causalean.Stat.densityAffinity (μ i) (f i) (g i) ≤ 1 := by
      have hn : 0 ≤ CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.hellingerEnergy (μ i) (f i) (g i) :=
        integral_nonneg (fun _ => sq_nonneg _)
      rw [hE i] at hn
      linarith
    change Causalean.Stat.hellingerSqDensity (Measure.pi μ)
      (fun x : ∀ i, Ω i => ∏ i, f i (x i)) (fun x => ∏ i, g i (x i)) ≤ _
    rw [Causalean.Stat.hellingerSqDensity_eq_two_mul_one_sub_affinity
      (Measure.pi μ) _ _ hFp hGp hF0 hG0 hF1 hG1]
    rw [Causalean.Stat.densityAffinity_pi μ f g hf0 hg0]
    simp_rw [hE]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (Causalean.Stat.one_sub_prod_le_sum _ ha0 ha1)
      (by norm_num)
  · intro Ξ Ω _ _ ν _ μ _ f g hf hg hf0 hg0 hfp hgp
    exact (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.common_marginal_hellinger_averaging
      ν μ f g hf hg hf0 hg0 hfp hgp).1

end CausalSmith.Experimentation.NoisygraphTtePrecision
