module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerHistogramTransfer

/-! # Integrating the fixed-sample lower comparison

Integrate the parameter-free histogram comparison over the legal packet and
Fejér priors. Both full-count Bayes bounds give fixed-sample minimax lower bounds,
with only the explicit Poisson shortage penalty from roadmap (49).
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Minimax.FuzzyHypotheses
open Causalean.Stat.Minimax.MomentMatchedMixture
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer


-- @node: observedRisk_bddAbove
/-- Finite sample estimators have uniformly bounded observed risk, because the sample alphabet is finite and the observed value lies in the unit interval. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma observedRisk_bddAbove {n d : ℕ} {ε : ℝ} (est : Estimator n d) :
    BddAbove (Set.range (observedRisk n (ε := ε) est)) := by
  obtain ⟨R, hR⟩ := (Set.finite_range (fun o => |est.1 o|)).bddAbove
  refine ⟨(max R 0 + 1) ^ 2, ?_⟩
  rintro _ ⟨P, rfl⟩
  letI : IsProbabilityMeasure (productLaw P.1 n) := by unfold productLaw; infer_instance
  have hpoint (o : Fin n → Obs d) :
      (est.1 o - observedValue P.1) ^ 2 ≤ (max R 0 + 1) ^ 2 := by
    have he : |est.1 o| ≤ max R 0 := (hR (Set.mem_range_self o)).trans (le_max_left _ _)
    have hv := observedValue_mem_unitInterval P.1
    have hb : |est.1 o - observedValue P.1| ≤ max R 0 + 1 := by
      calc
        _ ≤ |est.1 o| + |observedValue P.1| := abs_sub _ _
        _ ≤ _ := add_le_add he (by rw [abs_of_nonneg hv.1]; exact hv.2)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
  unfold observedRisk Causalean.Stat.sqRisk
  exact (integral_mono Integrable.of_finite (integrable_const _) hpoint).trans_eq (by simp)


-- @node: lowerHistogramEstimator_abs_le_one
/-- Averaging a projected prefix leaves the histogram statistic bounded by one. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma lowerHistogramEstimator_abs_le_one {n d : ℕ} (est : Estimator n d)
    (fallback : Fin n → Obs d) (N : Obs d → ℕ) :
    |lowerHistogramEstimator est fallback N| ≤ 1 := by
  apply Causalean.Stat.abs_kernelMean_le _ (by norm_num)
  intro s
  have hp := projectUnit_mem_unitInterval (est.1 (orderedPrefix fallback s))
  exact abs_le.mpr ⟨by dsimp [lowerPrefixEstimator]; linarith [hp.1], hp.2⟩


-- @node: lowerHistogram_squaredRisk_eq
/-- A bounded histogram estimator's nonnegative integral loss agrees exactly with the ENNReal squared risk used by fuzzy testing. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma lowerHistogram_squaredRisk_eq {Θ : Type*} [MeasurableSpace Θ]
    {n d : ℕ} (K : Kernel Θ (Obs d → ℕ)) (θ : Θ)
    [IsProbabilityMeasure (K θ)] (target : Θ → ℝ)
    (est : Estimator n d) (fallback : Fin n → Obs d) :
    squaredRisk K target (lowerHistogramEstimator est fallback) θ =
      ENNReal.ofReal (Causalean.Stat.sqRisk (K θ)
        (lowerHistogramEstimator est fallback) (target θ)) := by
  have hi : Integrable (fun N =>
      (lowerHistogramEstimator est fallback N - target θ) ^ 2) (K θ) := by
    refine (integrable_const ((1 + |target θ|) ^ 2)).mono' (by fun_prop) ?_
    filter_upwards [] with N
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb : |lowerHistogramEstimator est fallback N - target θ| ≤ 1 + |target θ| :=
      (abs_sub _ _).trans (add_le_add (lowerHistogramEstimator_abs_le_one est fallback N) le_rfl)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm

/-- On legal sparse vectors, integrating the fibre transfer costs at most the fixed estimator's worst-case risk plus the uniform shortage penalty. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,hM,hn,hB,hsupp), the [stated conclusion](goal) holds. -/
lemma sparseHistogram_bayesRisk_le_fixedWorstRisk {n d : ℕ} (hd : 2 ≤ d)
    {ε M B : ℝ} (hε : 0 < ε) (hεhi : ε ≤ 1 / 2)
    (hM : 2 ≤ M) (hn : 1 ≤ n) (hB : 2 < B)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsupp : ν (Set.Icc 0 M)ᶜ = 0)
    (est : Estimator n d) (fallback : Fin n → Obs d) :
    bayesSquaredRisk
      (productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) ν))
      (sparseFullObservedPoissonKernel (hMpaper := hM) B n d ε M)
      (fun θ => observedValue (sparseObservedModel hd ε M hε hεhi hM θ).1)
      (lowerHistogramEstimator est fallback) ≤
    ENNReal.ofReal (Causalean.Stat.worstCaseRiskReal (observedRisk n (ε := ε)) est +
      Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B))) := by
  letI : IsProbabilityMeasure (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) ν) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) ν)) := by
    unfold productPrior
    infer_instance
  unfold bayesSquaredRisk
  calc
    _ ≤ ∫⁻ _θ,
        ENNReal.ofReal (Causalean.Stat.worstCaseRiskReal (observedRisk n (ε := ε)) est +
          Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)))
          ∂productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) ν) := by
      apply lintegral_mono_ae
      filter_upwards [sparse_product_prior_ae_legal (hMpaper := hM) ν hsupp] with θ hθ
      letI := sparseFullObservedPoissonKernel_probability (hMpaper := hM) B n d ε M θ
      rw [lowerHistogram_squaredRisk_eq]
      apply ENNReal.ofReal_le_ofReal
      have hclip (x : Fin d) : sparseClippedIntensity (hMpaper := hM) M (θ x) = θ x + sparseReference (_hMpaper := hM) M := by
        simpa only [add_sub_cancel_right] using sparseClippedIntensity_sub_reference (hMpaper := hM) (hθ x)
      have hmodel : (sparseObservedModel hd ε M hε hεhi hM θ).1 =
          sparseLaw (by omega) ε M ⟨hε, hεhi⟩ (fun x => θ x + sparseReference (_hMpaper := hM) M) hθ := by
        unfold sparseObservedModel
        simp_rw [hclip]
      rw [hmodel]
      exact (sparseHistogram_fixedSample_risk_le hd hε hεhi hM hn hB θ hθ est fallback).trans
        (add_le_add (Causalean.Stat.le_worstCaseRisk (observedRisk_bddAbove est) _) le_rfl)
    _ = _ := by simp


-- @node: sparse_fixedSample_minimaxRisk_lower
/-- The packet lower experiment yields a fixed-sample sparse minimax bound. Both prior risks are bounded by the same fixed estimator's worst-case risk; thus only the uniform Poisson shortage term is lost in the comparison. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma sparse_fixedSample_minimaxRisk_lower :
    ∃ (c η C : ℝ) (D : ℕ), 0 < c ∧ 0 < η ∧ 2 ≤ C ∧ 2 ≤ D ∧
      ∀ (n d : ℕ) (ε M B : ℝ),
        1 ≤ n → D ≤ d → 0 < ε → ε ≤ 1 / 2 → 2 ≤ M →
        M ≤ (lowerLogDegree C d : ℝ) ^ 2 → 2 < B →
        M ≤ η * d * lowerLogDegree C d / (B * n * ε) →
        c * M / (lowerLogDegree C d : ℝ) ^ 2 -
          Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) ≤ minimaxRisk n d ε := by
  obtain ⟨c, η, C, A, D, hc, hη, hC, hA, hD, hbound⟩ :=
    sparse_full_observed_logDegree_bayesRisk_lower
  refine ⟨c, η, C, D, hc, hη, hC, hD, ?_⟩
  intro n d ε M B hn hd hε hεhi hM hMhi hB hband
  have hd2 : 2 ≤ d := hD.trans hd
  obtain ⟨P, hdom, hcompletion, hP⟩ :=
    hbound n d ε M B hd2 hε hεhi hM hn hd hMhi hB hband
  letI := P.prob₀
  letI := P.prob₁
  letI : Nonempty (Estimator n d) := ⟨⟨fun _ => 0, measurable_const⟩⟩
  apply Causalean.Stat.le_minimaxValue
  intro est
  let fallback : Fin n → Obs d := fun _ => (⟨0, by omega⟩, false, false)
  have hl := hP (lowerHistogramEstimator est fallback) (by fun_prop)
  have hu := max_le
    (sparseHistogram_bayesRisk_le_fixedWorstRisk hd2 hε hεhi hM hn hB P.ν₀ P.supp₀ est fallback)
    (sparseHistogram_bayesRisk_le_fixedWorstRisk hd2 hε hεhi hM hn hB P.ν₁ P.supp₁ est fallback)
  have hr := ENNReal.ofReal_le_ofReal_iff (p := c * M / (lowerLogDegree C d : ℝ) ^ 2)
    (show 0 ≤ Causalean.Stat.worstCaseRiskReal (observedRisk n (ε := ε)) est +
      Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) from
        add_nonneg (Causalean.Stat.worstCaseRisk_nonneg (observedRisk_nonneg est)) (Real.exp_nonneg _))
  have hreal := hr.mp (hl.trans hu)
  linarith


-- @node: dense_product_prior_ae_legal
/-- Supported scalar dense priors put every product coordinate in the legal parameter interval, so clipping has no effect on the comparison experiment. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hsupp), the [stated conclusion](goal) holds. -/
lemma dense_product_prior_ae_legal {d : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsupp : Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.IsSupportedOnUnitInterval ν) :
    ∀ᵐ θ ∂productPrior d ν, ∀ x, |θ x| ≤ 1 := by
  have hs : ∀ᵐ t ∂ν, |t| ≤ 1 :=
    (mem_ae_iff_prob_eq_one (measurableSet_le (by fun_prop) measurable_const)).2
      (dense_prior_support_radius_one ν hsupp)
  rw [Filter.eventually_all]
  intro x
  exact ((measurePreserving_eval (fun _ : Fin d => ν) x).hasLaw.ae_iff
    (by fun_prop)).2 hs


-- @node: denseHistogram_bayesRisk_le_fixedWorstRisk
/-- The dense full-count prior comparison integrates to the same fixed-sample worst risk and shortage penalty as the sparse comparison. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hεhi,ha,hahi,hn,hB,hsupp), the [stated conclusion](goal) holds. -/
lemma denseHistogram_bayesRisk_le_fixedWorstRisk {n d : ℕ} (hd : 0 < d)
    {ε a B : ℝ} (hε : 0 < ε) (hεhi : ε ≤ 1 / 2)
    (ha : 0 ≤ a) (hahi : a ≤ 1 / 2) (hn : 1 ≤ n) (hB : 2 < B)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsupp : Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.IsSupportedOnUnitInterval ν)
    (est : Estimator n d) (fallback : Fin n → Obs d) :
    bayesSquaredRisk (productPrior d ν)
      (denseFullObservedPoissonKernel d (B * n * ε / d) a (B * n * (1 - ε) / (2 * d)))
      (fun θ => observedValue (denseObservedModel hd ε a hε hεhi ha hahi θ).1)
      (lowerHistogramEstimator est fallback) ≤
    ENNReal.ofReal (Causalean.Stat.worstCaseRiskReal (observedRisk n (ε := ε)) est +
      Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B))) := by
  letI : IsProbabilityMeasure (productPrior d ν) := by unfold productPrior; infer_instance
  unfold bayesSquaredRisk
  calc
    _ ≤ ∫⁻ _θ, ENNReal.ofReal
        (Causalean.Stat.worstCaseRiskReal (observedRisk n (ε := ε)) est +
          Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B))) ∂productPrior d ν := by
      apply lintegral_mono_ae
      filter_upwards [dense_product_prior_ae_legal ν hsupp] with θ hθ
      letI : IsProbabilityMeasure
          (denseFullObservedPoissonKernel d (B * n * ε / d) a
            (B * n * (1 - ε) / (2 * d)) θ) := by
        rw [denseFullObservedPoissonKernel_eq hd ε a B n hε hεhi ha hahi θ hθ]
        infer_instance
      rw [lowerHistogram_squaredRisk_eq]
      apply ENNReal.ofReal_le_ofReal
      have hmodel : (denseObservedModel hd ε a hε hεhi ha hahi θ).1 =
          denseObservedLaw hd ε a hε hεhi ha hahi θ hθ := by
        unfold denseObservedModel
        simp_rw [denseClippedParameter_eq (hθ _)]
      rw [hmodel]
      exact (denseHistogram_fixedSample_risk_le hd hε hεhi ha hahi hn hB θ hθ est fallback).trans
        (add_le_add (Causalean.Stat.le_worstCaseRisk (observedRisk_bddAbove est) _) le_rfl)
    _ = _ := by simp


-- @node: dense_fixedSample_minimaxRisk_lower
/-- The Fejér dense lower experiment transfers to fixed-sample minimax risk, retaining its a²/K² order and subtracting only the explicit shortage penalty. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma dense_fixedSample_minimaxRisk_lower :
    ∃ (η C : ℝ) (D : ℕ), 0 < η ∧ 2 ≤ C ∧ 2 ≤ D ∧
      ∀ (n d : ℕ) (ε a B : ℝ),
        1 ≤ n → D ≤ d → 0 < ε → ε ≤ 1 / 2 → 0 < a → a ≤ 1 / 2 → 2 < B →
        (B * n * ε / d) * a ^ 2 ≤ η * lowerLogDegree C d →
        (5 / 2560000 : ℝ) * a ^ 2 / (lowerLogDegree C d : ℝ) ^ 2 -
          Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) ≤ minimaxRisk n d ε := by
  obtain ⟨η, C, D, hη, hC, hD, hbound⟩ := dense_full_observed_logDegree_bayesRisk_lower
  refine ⟨η, C, D, hη, hC, hD, ?_⟩
  intro n d ε a B hn hd hε hεhi ha hahi hB hband
  have hdpos : 0 < d := by omega
  have hr : 0 < B * (n : ℝ) * ε / d := by positivity
  obtain ⟨P, hP⟩ := hbound d (B * n * ε / d) a
    (B * n * (1 - ε) / (2 * d)) ε hdpos hε hεhi ha.le hahi hd hr ha hband
  letI := P.probability₀
  letI := P.probability₁
  letI : Nonempty (Estimator n d) := ⟨⟨fun _ => 0, measurable_const⟩⟩
  apply Causalean.Stat.le_minimaxValue
  intro est
  let fallback : Fin n → Obs d := fun _ => (⟨0, hdpos⟩, false, false)
  have hl := hP (lowerHistogramEstimator est fallback) (by fun_prop)
  have hu := max_le
    (denseHistogram_bayesRisk_le_fixedWorstRisk hdpos hε hεhi ha.le hahi hn hB P.ν₀ P.supported₀ est fallback)
    (denseHistogram_bayesRisk_le_fixedWorstRisk hdpos hε hεhi ha.le hahi hn hB P.ν₁ P.supported₁ est fallback)
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (show 0 ≤ Causalean.Stat.worstCaseRiskReal (observedRisk n (ε := ε)) est +
      Real.exp (-(n : ℝ) * (B - 2) ^ 2 / (4 * B)) from
        add_nonneg (Causalean.Stat.worstCaseRisk_nonneg (observedRisk_nonneg est))
          (Real.exp_nonneg _))).mp (hl.trans hu)
  linarith

end CausalSmith.Stat.OptvalueVanishingoverlapRate
