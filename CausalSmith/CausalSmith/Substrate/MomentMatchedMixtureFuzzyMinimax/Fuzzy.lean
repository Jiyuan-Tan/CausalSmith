import CausalSmith.Substrate.MomentMatchedMixtureFuzzyMinimax.Basic
import Causalean.Stat.Minimax.TotalVariation

/-!
# Squared-loss lower bounds from two fuzzy hypotheses

This module converts target concentration under two priors and total-variation closeness of
their predictive mixtures into estimator-wise, worst-case, and minimax squared-risk bounds.
Risks use `ℝ≥0∞` lower integrals, so arbitrary measurable estimators require no artificial
integrability or boundedness assumptions.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Substrate.MomentMatchedMixtureFuzzyMinimax

variable {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]

/-- The squared risk of a real-valued estimator at a parameter is the lower integral of its
squared error under the experiment law. -/
noncomputable def squaredRisk (K : Kernel Θ X) (target : Θ → ℝ) (estimator : X → ℝ)
    (θ : Θ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((estimator x - target θ) ^ 2) ∂K θ

/-- The Bayes squared risk averages the parameterwise squared risks against a prior. -/
noncomputable def bayesSquaredRisk (π : Measure Θ) (K : Kernel Θ X) (target : Θ → ℝ)
    (estimator : X → ℝ) : ℝ≥0∞ :=
  ∫⁻ θ, squaredRisk K target estimator θ ∂π

/-- The worst-case squared risk is the supremum of the parameterwise risks over the parameter
type representing the model class. -/
noncomputable def worstCaseSquaredRisk (K : Kernel Θ X) (target : Θ → ℝ)
    (estimator : X → ℝ) : ℝ≥0∞ :=
  ⨆ θ, squaredRisk K target estimator θ

/-- The measurable-estimator minimax squared risk is the infimum of worst-case risk over all
measurable real-valued estimators. -/
noncomputable def minimaxSquaredRisk (K : Kernel Θ X) (target : Θ → ℝ) : ℝ≥0∞ :=
  ⨅ estimator : {f : X → ℝ // Measurable f}, worstCaseSquaredRisk K target estimator.1

/-- Two fuzzy hypotheses with centers separated by `Delta`, common concentration radius `r`,
prior tail probabilities at most `alpha0,alpha1`, and predictive total variation at most `beta`
force the larger Bayes squared risk of every measurable estimator to be at least
`(Delta/2-r)^2 * (1-beta-alpha0-alpha1) / 2`. -/
theorem twoFuzzyHypotheses_bayesRisk_lower
    (π0 π1 : Measure Θ) (K : Kernel Θ X) (target : Θ → ℝ)
    [IsProbabilityMeasure π0] [IsProbabilityMeasure π1]
    (hK : ∀ θ, IsProbabilityMeasure (K θ))
    (estimator : X → ℝ) (hestimator : Measurable estimator) (htarget : Measurable target)
    (center0 center1 Delta r alpha0 alpha1 beta : ℝ)
    (hDelta : 0 ≤ Delta) (hr : 0 ≤ r) (hrhalf : r < Delta / 2)
    (hsep : Delta ≤ center1 - center0)
    (halpha0 : 0 ≤ alpha0) (halpha1 : 0 ≤ alpha1) (hbeta : 0 ≤ beta)
    (hmass0 : π0.real {θ | r < |target θ - center0|} ≤ alpha0)
    (hmass1 : π1.real {θ | r < |target θ - center1|} ≤ alpha1)
    (htv : Causalean.Stat.tvDist (priorPredictive π0 K) (priorPredictive π1 K) ≤ beta) :
    ENNReal.ofReal (((Delta / 2 - r) ^ 2 * (1 - beta - alpha0 - alpha1)) / 2) ≤
      max (bayesSquaredRisk π0 K target estimator)
        (bayesSquaredRisk π1 K target estimator) := by
  let midpoint := (center0 + center1) / 2
  let A : Set X := {x | midpoint ≤ estimator x}
  let B0 : Set Θ := {θ | r < |target θ - center0|}
  let B1 : Set Θ := {θ | r < |target θ - center1|}
  let c : ℝ≥0∞ := ENNReal.ofReal ((Delta / 2 - r) ^ 2)
  let R0 := bayesSquaredRisk π0 K target estimator
  let R1 := bayesSquaredRisk π1 K target estimator
  have hA : MeasurableSet A := by
    dsimp [A, midpoint]
    exact measurableSet_le measurable_const hestimator
  have hB0 : MeasurableSet B0 := by
    dsimp [B0]
    exact measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (htarget.sub measurable_const))
  have hB1 : MeasurableSet B1 := by
    dsimp [B1]
    exact measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (htarget.sub measurable_const))
  letI : IsProbabilityMeasure (priorPredictive π0 K) :=
    priorPredictive_isProbability π0 K hK
  letI : IsProbabilityMeasure (priorPredictive π1 K) :=
    priorPredictive_isProbability π1 K hK
  have hpoint0 (θ : Θ) :
      c * K θ A ≤ squaredRisk K target estimator θ + B0.indicator (fun _ => c) θ := by
    by_cases hθ : θ ∈ B0
    · rw [Set.indicator_of_mem hθ]
      letI : IsProbabilityMeasure (K θ) := hK θ
      have hKA : K θ A ≤ 1 := by
        calc
          K θ A ≤ K θ Set.univ := measure_mono (Set.subset_univ A)
          _ = 1 := measure_univ
      calc
        c * K θ A ≤ c := by
          simpa only [mul_one] using
            (mul_le_mul (le_refl c) hKA bot_le bot_le)
        _ ≤ squaredRisk K target estimator θ + c := by simp
    · have hgood : |target θ - center0| ≤ r := by
        simpa [B0, not_lt] using hθ
      have hdom : ∀ x ∈ A,
          (Delta / 2 - r) ^ 2 ≤ (estimator x - target θ) ^ 2 := by
        intro x hx
        have hx' : midpoint ≤ estimator x := hx
        have ht : target θ ≤ center0 + r := by
          linarith [(abs_le.mp hgood).2]
        have hd : 0 < Delta / 2 - r := sub_pos.mpr hrhalf
        dsimp [midpoint] at hx'
        nlinarith
      have hnot : θ ∉ B0 := hθ
      simp only [Set.indicator_of_notMem hnot, add_zero]
      unfold squaredRisk
      calc
        c * K θ A = ∫⁻ x, A.indicator (fun _ => c) x ∂K θ := by simp [hA]
        _ ≤ ∫⁻ x, ENNReal.ofReal ((estimator x - target θ) ^ 2) ∂K θ := by
          apply lintegral_mono
          intro x
          by_cases hx : x ∈ A
          · simp only [Set.indicator_of_mem hx]
            exact ENNReal.ofReal_le_ofReal (hdom x hx)
          · simp [Set.indicator_of_notMem hx]
  have hpoint1 (θ : Θ) :
      c * K θ Aᶜ ≤ squaredRisk K target estimator θ + B1.indicator (fun _ => c) θ := by
    by_cases hθ : θ ∈ B1
    · rw [Set.indicator_of_mem hθ]
      letI : IsProbabilityMeasure (K θ) := hK θ
      have hKA : K θ Aᶜ ≤ 1 := by
        calc
          K θ Aᶜ ≤ K θ Set.univ := measure_mono (Set.subset_univ Aᶜ)
          _ = 1 := measure_univ
      calc
        c * K θ Aᶜ ≤ c := by
          simpa only [mul_one] using
            (mul_le_mul (le_refl c) hKA bot_le bot_le)
        _ ≤ squaredRisk K target estimator θ + c := by simp
    · have hgood : |target θ - center1| ≤ r := by
        simpa [B1, not_lt] using hθ
      have hdom : ∀ x ∈ Aᶜ,
          (Delta / 2 - r) ^ 2 ≤ (estimator x - target θ) ^ 2 := by
        intro x hx
        have hx' : estimator x < midpoint := by
          simpa [A] using hx
        have ht : center1 - r ≤ target θ := by
          have := (abs_le.mp hgood).1
          linarith
        have hd : 0 < Delta / 2 - r := sub_pos.mpr hrhalf
        dsimp [midpoint] at hx'
        nlinarith
      have hnot : θ ∉ B1 := hθ
      simp only [Set.indicator_of_notMem hnot, add_zero]
      unfold squaredRisk
      calc
        c * K θ Aᶜ = ∫⁻ x, Aᶜ.indicator (fun _ => c) x ∂K θ := by simp [hA.compl]
        _ ≤ ∫⁻ x, ENNReal.ofReal ((estimator x - target θ) ^ 2) ∂K θ := by
          apply lintegral_mono
          intro x
          by_cases hx : x ∈ Aᶜ
          · simp only [Set.indicator_of_mem hx]
            exact ENNReal.ofReal_le_ofReal (hdom x hx)
          · simp [Set.indicator_of_notMem hx]
  have hmaster0 : c * priorPredictive π0 K A ≤ R0 + c * π0 B0 := by
    calc
      c * priorPredictive π0 K A = ∫⁻ θ, c * K θ A ∂π0 := by
        rw [lintegral_const_mul'' c
          ((Kernel.measurable_coe K hA).aemeasurable)]
        rw [← priorPredictive_apply π0 K hA]
      _ ≤ ∫⁻ θ, (squaredRisk K target estimator θ +
          B0.indicator (fun _ => c) θ) ∂π0 := lintegral_mono hpoint0
      _ = R0 + c * π0 B0 := by
        rw [lintegral_add_right _ (measurable_const.indicator hB0)]
        simp [R0, bayesSquaredRisk, hB0]
  have hmaster1 : c * priorPredictive π1 K Aᶜ ≤ R1 + c * π1 B1 := by
    calc
      c * priorPredictive π1 K Aᶜ = ∫⁻ θ, c * K θ Aᶜ ∂π1 := by
        rw [lintegral_const_mul'' c
          ((Kernel.measurable_coe K hA.compl).aemeasurable)]
        rw [← priorPredictive_apply π1 K hA.compl]
      _ ≤ ∫⁻ θ, (squaredRisk K target estimator θ +
          B1.indicator (fun _ => c) θ) ∂π1 := lintegral_mono hpoint1
      _ = R1 + c * π1 B1 := by
        rw [lintegral_add_right _ (measurable_const.indicator hB1)]
        simp [R1, bayesSquaredRisk, hB1]
  have htest := Causalean.Stat.one_sub_tvDist_le_test
    (μ := priorPredictive π0 K) (ν := priorPredictive π1 K) hA
  have herr : 1 - beta ≤
      (priorPredictive π0 K).real A + (priorPredictive π1 K).real Aᶜ := by
    linarith
  by_cases hR : max R0 R1 = ∞
  · simp [R0, R1, hR]
  have hR0 : R0 ≠ ∞ := fun h => hR (by simp [h])
  have hR1 : R1 ≠ ∞ := fun h => hR (by simp [h])
  have hc : c ≠ ∞ := by simp [c]
  have hcbad0 : c * π0 B0 ≠ ∞ :=
    ENNReal.mul_ne_top hc (measure_ne_top π0 B0)
  have hcbad1 : c * π1 B1 ≠ ∞ :=
    ENNReal.mul_ne_top hc (measure_ne_top π1 B1)
  have hmaster0Real := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hR0, hcbad0⟩) hmaster0
  have hmaster1Real := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hR1, hcbad1⟩) hmaster1
  rw [ENNReal.toReal_mul, ENNReal.toReal_add hR0 hcbad0,
    ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def] at hmaster0Real
  rw [ENNReal.toReal_mul, ENNReal.toReal_add hR1 hcbad1,
    ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def] at hmaster1Real
  have hcReal : c.toReal = (Delta / 2 - r) ^ 2 := by
    simp [c, ENNReal.toReal_ofReal (sq_nonneg _)]
  have hR0max : R0.toReal ≤ (max R0 R1).toReal :=
    ENNReal.toReal_mono hR (le_max_left _ _)
  have hR1max : R1.toReal ≤ (max R0 R1).toReal :=
    ENNReal.toReal_mono hR (le_max_right _ _)
  rw [ENNReal.ofReal_le_iff_le_toReal hR]
  rw [hcReal] at hmaster0Real hmaster1Real
  nlinarith [sq_nonneg (Delta / 2 - r)]

/-- The Bayes squared risk under any probability prior is bounded above by the estimator's
worst-case squared risk over the parameter class. -/
theorem bayesSquaredRisk_le_worstCase
    (π : Measure Θ) (K : Kernel Θ X) (target : Θ → ℝ) (estimator : X → ℝ)
    [IsProbabilityMeasure π] :
    bayesSquaredRisk π K target estimator ≤ worstCaseSquaredRisk K target estimator := by
  unfold bayesSquaredRisk worstCaseSquaredRisk
  apply lintegral_le_const
  filter_upwards with θ
  exact le_iSup (fun θ => squaredRisk K target estimator θ) θ

/-- With radius `Delta/4`, each prior tail at most `1/8`, and predictive total variation at most
`1/16`, every measurable estimator has worst-case squared risk at least
`11 * Delta^2 / 512`. -/
theorem twoFuzzyHypotheses_worstCase_lower_standard
    (π0 π1 : Measure Θ) (K : Kernel Θ X) (target : Θ → ℝ)
    [IsProbabilityMeasure π0] [IsProbabilityMeasure π1]
    (hK : ∀ θ, IsProbabilityMeasure (K θ))
    (estimator : X → ℝ) (hestimator : Measurable estimator) (htarget : Measurable target)
    (center0 center1 Delta : ℝ) (hDelta : 0 < Delta)
    (hsep : Delta ≤ center1 - center0)
    (hmass0 : π0.real {θ | Delta / 4 < |target θ - center0|} ≤ 1 / 8)
    (hmass1 : π1.real {θ | Delta / 4 < |target θ - center1|} ≤ 1 / 8)
    (htv : Causalean.Stat.tvDist (priorPredictive π0 K) (priorPredictive π1 K) ≤ 1 / 16) :
    ENNReal.ofReal (11 * Delta ^ 2 / 512) ≤ worstCaseSquaredRisk K target estimator := by
  have hbayes := twoFuzzyHypotheses_bayesRisk_lower π0 π1 K target hK
    estimator hestimator htarget center0 center1 Delta (Delta / 4) (1 / 8) (1 / 8)
      (1 / 16) (le_of_lt hDelta) (by positivity) (by linarith) hsep
      (by norm_num) (by norm_num) (by norm_num) hmass0 hmass1 htv
  have hconstant :
      (((Delta / 2 - Delta / 4) ^ 2 * (1 - (1 / 16 : ℝ) - 1 / 8 - 1 / 8)) / 2) =
        11 * Delta ^ 2 / 512 := by
    ring
  rw [hconstant] at hbayes
  exact hbayes.trans (max_le
    (bayesSquaredRisk_le_worstCase π0 K target estimator)
    (bayesSquaredRisk_le_worstCase π1 K target estimator))

/-- Under the standard `1/8,1/16,Delta/4` fuzzy-hypothesis constants, the infimum over all
measurable estimators of their supremum squared risk is at least `11 * Delta^2 / 512`. -/
theorem twoFuzzyHypotheses_minimax_lower_standard
    (π0 π1 : Measure Θ) (K : Kernel Θ X) (target : Θ → ℝ)
    [IsProbabilityMeasure π0] [IsProbabilityMeasure π1]
    (hK : ∀ θ, IsProbabilityMeasure (K θ)) (htarget : Measurable target)
    (center0 center1 Delta : ℝ) (hDelta : 0 < Delta)
    (hsep : Delta ≤ center1 - center0)
    (hmass0 : π0.real {θ | Delta / 4 < |target θ - center0|} ≤ 1 / 8)
    (hmass1 : π1.real {θ | Delta / 4 < |target θ - center1|} ≤ 1 / 8)
    (htv : Causalean.Stat.tvDist (priorPredictive π0 K) (priorPredictive π1 K) ≤ 1 / 16) :
    ENNReal.ofReal (11 * Delta ^ 2 / 512) ≤ minimaxSquaredRisk K target := by
  unfold minimaxSquaredRisk
  apply le_iInf
  intro estimator
  exact twoFuzzyHypotheses_worstCase_lower_standard π0 π1 K target hK estimator.1
    estimator.2 htarget center0 center1 Delta hDelta hsep hmass0 hmass1 htv

end CausalSmith.Substrate.MomentMatchedMixtureFuzzyMinimax
