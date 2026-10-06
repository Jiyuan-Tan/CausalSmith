module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FinitePriorTesting
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_OriginalRecordMixtures

/-! # Hellinger testing reduction for the actual finite priors

The original-sample mixture densities are normalized probability densities.
The library's affinity comparison therefore converts a squared Hellinger
budget of one hundredth into the total variation budget of one tenth,
unchanged by the optional independent seed.
-/
public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The actual finite-prior density integrates to one under the sample reference. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:hU). -/
-- @node: signMixtureCellDensity_integral_one
lemma signMixtureCellDensity_integral_one (n k : ℕ)
    (laws : (Fin (k+1) → Bool) → ObservedLaw)
    (hU : ∀ σ, Measure.map covariate (laws σ).measure = uniformLaw) :
    (∫ o, signMixtureCellDensity n k laws o ∂sampleReference n) = 1 := by
  letI := finiteSignMixture_probability n k laws
  have h := congrArg (fun μ : Measure (Fin n → Record) => μ Set.univ)
    (finiteSignMixture_withDensity n k laws hU)
  rw [measure_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
      (signMixtureCellDensity_integrable n k laws)
      (Filter.Eventually.of_forall (signMixtureCellDensity_nonneg n k laws))] at h
  have hnonneg : 0 ≤ ∫ o, signMixtureCellDensity n k laws o ∂sampleReference n :=
    integral_nonneg (signMixtureCellDensity_nonneg n k laws)
  have ht := congrArg ENNReal.toReal h
  change 0 ≤ ∫ o, signMixtureCellDensity n k laws o
    ∂Measure.pi (fun _ : Fin n => recordReference) at hnonneg
  simpa only [sampleReference, Causalean.Stat.UStatistic.LocalizedVariance.iidLaw,
    ENNReal.toReal_one, ENNReal.toReal_ofReal hnonneg] using ht.symm

/-- The RN formulation of the distance equals the discrepancy of the
literal finite averages of original-record likelihoods. [the documented result](goal) Under [the stated assumptions](hyp:hU₀,hU₁). -/
-- @node: finitePrior_originalRecordHellinger_density
lemma finitePrior_originalRecordHellinger_density (n k₀ k₁ : ℕ)
    (laws₀ : (Fin (k₀+1) → Bool) → ObservedLaw)
    (laws₁ : (Fin (k₁+1) → Bool) → ObservedLaw)
    (hU₀ : ∀ σ, Measure.map covariate (laws₀ σ).measure = uniformLaw)
    (hU₁ : ∀ σ, Measure.map covariate (laws₁ σ).measure = uniformLaw) :
    originalRecordHellinger n (finiteSignMixture n k₀ laws₀)
      (finiteSignMixture n k₁ laws₁) =
      Causalean.Stat.hellingerSqDensity (sampleReference n)
        (signMixtureCellDensity n k₀ laws₀) (signMixtureCellDensity n k₁ laws₁) := by
  have h0 := finiteSignMixture_rnDeriv n k₀ laws₀ hU₀
  have h1 := finiteSignMixture_rnDeriv n k₁ laws₁ hU₁
  unfold originalRecordHellinger Causalean.Stat.hellingerSqDensity
  apply integral_congr_ae
  filter_upwards [h0, h1] with o ho0 ho1
  dsimp only [sampleReference, Causalean.Stat.UStatistic.LocalizedVariance.iidLaw]
  rw [ho0, ho1]

/-- The Cauchy–Schwarz affinity estimate controls the full sample-and-seed
experiment by the square root of its original-record squared Hellinger distance. [the documented result](goal) Under [the stated assumptions](hyp:hU₀,hU₁). -/
-- @node: finitePrior_tv_le_sqrt_hellinger
lemma finitePrior_tv_le_sqrt_hellinger (n k₀ k₁ : ℕ)
    (laws₀ : (Fin (k₀+1) → Bool) → ObservedLaw)
    (laws₁ : (Fin (k₁+1) → Bool) → ObservedLaw)
    (hU₀ : ∀ σ, Measure.map covariate (laws₀ σ).measure = uniformLaw)
    (hU₁ : ∀ σ, Measure.map covariate (laws₁ σ).measure = uniformLaw) :
    Causalean.Stat.tvDist (signPriorExperiment n k₀ laws₀)
      (signPriorExperiment n k₁ laws₁) ≤
      Real.sqrt (originalRecordHellinger n (finiteSignMixture n k₀ laws₀)
        (finiteSignMixture n k₁ laws₁)) := by
  rw [signPriorExperiment_tv, finitePrior_originalRecordHellinger_density
    n k₀ k₁ laws₀ laws₁ hU₀ hU₁]
  have hf := signMixtureCellDensity_integrable n k₀ laws₀
  have hg := signMixtureCellDensity_integrable n k₁ laws₁
  have hf0 := signMixtureCellDensity_nonneg n k₀ laws₀
  have hg0 := signMixtureCellDensity_nonneg n k₁ laws₁
  have hf1 := signMixtureCellDensity_integral_one n k₀ laws₀ hU₀
  have hg1 := signMixtureCellDensity_integral_one n k₁ laws₁ hU₁
  rw [finiteSignMixture_withDensity n k₀ laws₀ hU₀,
    finiteSignMixture_withDensity n k₁ laws₁ hU₁,
    Causalean.Stat.hellingerSqDensity_eq_two_mul_one_sub_affinity
      (sampleReference n) _ _ hf hg hf0 hg0 hf1 hg1]
  exact Causalean.Stat.tvDist_le_sqrt_two_mul_one_sub_affinity
    (sampleReference n) _ _ hf hg hf0 hg0 hf1 hg1

/-- The paper's Hellinger budget yields its seven-tenths testing coefficient. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hI,hP₀,hP₁,hθ₀,hθ₁,hU₀,hU₁,hH) hold, and [the stated conclusion follows](goal). -/
-- @node: finitePrior_hellinger_length_lower
lemma finitePrior_hellinger_length_lower (n k₀ k₁ : ℕ) (α β r a b : ℝ)
    (laws₀ : (Fin (k₀+1) → Bool) → ObservedLaw)
    (laws₁ : (Fin (k₁+1) → Bool) → ObservedLaw)
    (I : Procedure n) (hI : HonestProcedure n α β I)
    (hP₀ : ∀ σ, RadiusModel α β r (laws₀ σ))
    (hP₁ : ∀ σ, Model α β (laws₁ σ))
    (hθ₀ : ∀ σ, effect (laws₀ σ) = a)
    (hθ₁ : ∀ σ, effect (laws₁ σ) = b)
    (hU₀ : ∀ σ, Measure.map covariate (laws₀ σ).measure = uniformLaw)
    (hU₁ : ∀ σ, Measure.map covariate (laws₁ σ).measure = uniformLaw)
    (hH : originalRecordHellinger n (finiteSignMixture n k₀ laws₀)
      (finiteSignMixture n k₁ laws₁) ≤ 1/100) :
    (7/10 : ℝ)*|b-a| ≤ worstLength n α β r I := by
  have htv := (finitePrior_tv_le_sqrt_hellinger n k₀ k₁ laws₀ laws₁ hU₀ hU₁).trans
    (Real.sqrt_le_sqrt hH)
  have hsqrt : Real.sqrt (1/100 : ℝ) ≤ 1/10 := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num
  have h := finitePrior_testing_length_lower n k₀ k₁ α β r a b (1/10)
    laws₀ laws₁ I hI hP₀ hP₁ hθ₀ hθ₁ (htv.trans hsqrt)
  convert h using 1 <;> ring

end CausalSmith.Stat.LogoddsLowsmoothFrontier
