module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.Assembly

/-! # Mean-square bound for the exact seven-mark cubic score -/

public section

open MeasureTheory
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- Model membership implies square integrability of the concrete estimator
error, including the zero-statistic fallback at small sample sizes.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,A), [the stated conclusion holds](goal). -/
@[fun_prop]
-- @node: cubicEstimator_error_sq_integrable
lemma cubicEstimator_error_sq_integrable (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    Integrable (fun ω : TwoSample n n =>
      (cubicEstimator c_f C_f ω A - transportedForm P A) ^ 2)
      (dataLaw P n n) := by
  let := sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  let := targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  let : IsProbabilityMeasure (dataLaw P n n) := by
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]
    infer_instance
  by_cases hn : n < threshold
  · simpa only [cubicEstimator, if_pos hn, zero_sub, neg_sq] using
      (integrable_const (transportedForm P A ^ 2) :
        Integrable (fun _ : TwoSample n n => transportedForm P A ^ 2)
          (dataLaw P n n))
  · have hn' : threshold ≤ n := Nat.le_of_not_gt hn
    have hF := cubicEstimator_sub_projectedEstimatorMean_memLp
      c_f C_f L P n hn' hP A
    have hBi := integrable_projectedEstimatorMean_sub_transport_sq
      c_f C_f L P n hn' hP A
    have hm : trainingSigma n ≤ (inferInstance : MeasurableSpace (TwoSample n n)) := by
      rw [trainingSigma_eq_comap_flatTrainingProj]
      exact ((Causalean.Mathlib.Probability.Independence.measurable_finsetCoordProj
          (flatBlock n 0)).comp
        (MeasurableEquiv.sumPiEquivProdPi (FlatObs n)).symm.measurable).comap_le
    have hBsm : AEStronglyMeasurable (fun ω : TwoSample n n =>
        projectedEstimatorMean c_f C_f L P n hP ω A - transportedForm P A)
        (dataLaw P n n) := by
      first
      | fun_prop
      | exact (((stronglyMeasurable_projectedEstimatorMean
          c_f C_f L P n hn' hP A).mono hm).sub
          stronglyMeasurable_const).aestronglyMeasurable
    have hB := (memLp_two_iff_integrable_sq hBsm).2 hBi
    convert (hF.add hB).integrable_sq using 1 <;>
      ext ω <;> simp only [Pi.add_apply] <;> ring

-- @node: lem:marked-cubic-mse
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hf,hF,hL,hn,hP,A), [the stated result about marked cubic mse holds](goal). -/
lemma marked_cubic_mse (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hf : 0 < c_f ∧ c_f < 1) (hF : 1 < C_f) (hL : 1 < L)
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) (A : Bool) :
    (∫ ω, (cubicEstimator c_f C_f ω A - transportedForm P A) ^ 2
      ∂dataLaw P n n) ≤
      mseEnvelope c_f C_f L * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  -- Roadmap (8) is proved in `pilot_Phi_cubic_taylor_remainder_abs_le`.
  -- The clipped eighth moment and exact quadratic/cubic conditional variance
  -- bounds are proved in `pilot_eighth_moment`,
  -- `quadratic_conditional_variance`, and `cubic_conditional_variance`.
  -- The exact quadratic and cubic conditional means are proved in
  -- `condExp_quadraticTerm_eq_quadraticProjectionMean` and
  -- `condExp_cubicTerm_eq_cubicProjectionMean`.
  -- `pilot_Phi_cubic_taylor_remainder_integrated_second_moment` proves
  -- roadmap (9) for the square of the spatially integrated remainder.
  -- `pilot_error_L1_second_moment` proves the L1 part of roadmap (7).
  -- `cubic_midpoint_cell_projection_L1_bound` retains the pilot L1 error
  -- in each exact cubic cell bias, ready for the global sum in roadmap (12).
  -- `quadraticCellProjectionBias_integrated_sq_sample_rate` proves the
  -- roadmap (11) rate for the exact midpoint-frozen cell sum, and
  -- `quadraticCellProjectionBias_eq_sub_projectionMean` identifies its
  -- difference from the exact conditional mean.
  -- `quadraticCellProjectionBias_eq_spatial_sub_projectionMean` proves the
  -- nested-cell bridge, and
  -- `quadratic_spatial_projection_bias_integrated_sq_sample_rate` gives
  -- roadmap (11) for the true spatial Taylor term.
  -- `spatial_pilot_single_residual_cancellation` proves exact cancellation
  -- for pilot-derived coefficients on every nested correction cell.
  -- `cubic_spatial_projection_bias_abs_le_L1` proves the global
  -- pilot-sensitive cubic bias bound (12) for the exact projection mean.
  -- `cubic_spatial_projection_bias_integrated_sq_resolution_bound` combines
  -- the exact spatial bias with the pilot L1 second moment, retaining both
  -- resolution powers in (13); `cubicResolution_inverse_rpow_sample_rate`
  -- supplies their dyadic sample-size conversion.
  -- `cubic_spatial_projection_bias_integrated_sq_sample_rate` proves
  -- roadmap (13) with the exact BC constant, converting both actual rates
  -- n^(-7/10) and n^(-3/4) to n^(-2/3).
  -- `combined_spatial_projection_bias_second_moment` proves roadmap (14)
  -- for the exact spatial remainder and the two projection errors, with
  -- the exact constant 3(BR+BQ+BC), using an integrable remainder majorant.
  -- `projectedEstimatorMean_sub_transport_eq_spatial_bias` now identifies
  -- the exact projected mean's error with this sum, and
  -- `projectedEstimatorMean_squared_bias_sample_rate` transfers (14) to
  -- that mean, using coordinate Taylor expansions and spatial integrability.
  -- `linearProjectionMean_eq_cell_sum` proves that the linear spatial term
  -- is exactly a finite pilot-cell sum, with no projection bias;
  -- `stronglyMeasurable_linearProjectionMean` proves its training measurability.
  -- `linearTerm_sub_projectionMean_eq_centered_cell_sum` identifies the
  -- exact held-out fluctuation using the model-derived covariate support;
  -- `condExp_linearTerm_eq_linearProjectionMean` proves its exact training
  -- conditional mean. `linear_conditional_variance` proves roadmap (19)
  -- for the exact held-out statistic, retaining signed cell covariances
  -- to avoid an extra density-envelope factor. The final conditional
  -- bias--variance assembly remains open.
  -- `quadratic_conditional_variance_sample_rate` and
  -- `cubic_conditional_variance_sample_rate` now convert the exact dyadic
  -- ladders to the sample rates (17)--(18), with constants 60B2 and 310B3.
  -- `linear_conditional_variance_sample_rate` supplies (19) at the common
  -- n^(-2/3) rate. Integrability and the total conditional bias--variance
  -- identity are still needed to assemble these component estimates.
  -- `linear_conditional_variance_with_memLp` supplies square integrability
  -- of the exact centered linear correction; the quadratic and cubic
  -- `_with_memLp` lemmas supply square integrability of the full corrections.
  -- `centered_corrections_conditional_second_moment_sample_rate` combines
  -- the three dependent centered corrections with the exact constant in (20).
  -- `centered_corrections_expected_conditional_second_moment_sample_rate`
  -- integrates that bound.
  -- `cubicEstimator_sub_projectedEstimatorMean_eq_centered_corrections`
  -- identifies the full estimator fluctuation with that centered sum.
  -- `cubicEstimator_sub_projectedEstimatorMean_memLp` proves its square
  -- integrability, and `cubicEstimator_fluctuation_second_moment_sample_rate`
  -- transfers (20) to its unconditional second moment. The remaining step
  -- is the conditional bias--variance identity and final assembly.
  -- `projectionKernel_risk_bound` assumes projection bias and risk
  -- decomposition, so it cannot supply this missing connection.
  exact cubicEstimator_mse_sample_rate c_f C_f L P n hn hP A

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
