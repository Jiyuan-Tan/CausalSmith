module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.SpatialTaylorAssembly
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.ExactConditionalMeans
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.TotalVariance

/-! # Exact estimator fluctuation and its integrated variance bound

The pilot integral cancels from the fluctuation about the projected mean.
The three exact conditional means then identify this fluctuation with the
centered corrections in roadmap (20).
-/

public section

open MeasureTheory
open Causalean.Mathlib.Probability.Independence
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The full estimator fluctuation is exactly the sum of the three centered
corrections, almost surely under the two-sample experiment.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: cubicEstimator_sub_projectedEstimatorMean_eq_centered_corrections
lemma cubicEstimator_sub_projectedEstimatorMean_eq_centered_corrections
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    (fun ω : TwoSample n n => cubicEstimator c_f C_f ω A -
      projectedEstimatorMean c_f C_f L P n hP ω A) =ᵐ[dataLaw P n n]
    (fun ω =>
      (linearTerm c_f C_f ω A - condExp (trainingSigma n) (dataLaw P n n)
        (fun ξ => linearTerm c_f C_f ξ A) ω) +
      (quadraticTerm c_f C_f ω A - condExp (trainingSigma n) (dataLaw P n n)
        (fun ξ => quadraticTerm c_f C_f ξ A) ω) +
      (cubicTerm c_f C_f ω A - condExp (trainingSigma n) (dataLaw P n n)
        (fun ξ => cubicTerm c_f C_f ξ A) ω)) := by
  have hl := condExp_linearTerm_eq_linearProjectionMean c_f C_f L P n hn hP A
  have hq := condExp_quadraticTerm_eq_quadraticProjectionMean c_f C_f L P n hn hP A
  have hc := condExp_cubicTerm_eq_cubicProjectionMean c_f C_f L P n hn hP A
  filter_upwards [hl, hq, hc] with ω hl hq hc
  rw [hl, hq, hc]
  simp only [cubicEstimator, not_lt.mpr hn, ↓reduceIte, projectedEstimatorMean]
  ring

/-- The fluctuation of the exact full statistic is square integrable, using
square integrability already established by the component variance proofs.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: cubicEstimator_sub_projectedEstimatorMean_memLp
lemma cubicEstimator_sub_projectedEstimatorMean_memLp
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    MemLp (fun ω : TwoSample n n => cubicEstimator c_f C_f ω A -
      projectedEstimatorMean c_f C_f L P n hP ω A) 2 (dataLaw P n n) := by
  have hl := (linear_conditional_variance_with_memLp c_f C_f L P n hn hP A).1
  have hq := (quadratic_conditional_variance_with_memLp c_f C_f L P n hn hP A).1
  have hc := (cubic_conditional_variance_with_memLp c_f C_f L P n hn hP A).1
  have hsum := (hl.add (hq.sub (hq.condExp (m := trainingSigma n) (by norm_num)))).add
    (hc.sub (hc.condExp (m := trainingSigma n) (by norm_num)))
  exact MemLp.ae_eq
    (cubicEstimator_sub_projectedEstimatorMean_eq_centered_corrections
      c_f C_f L P n hn hP A).symm hsum

/-- Roadmap (20) bounds the unconditional second moment of the exact full
estimator's fluctuation about its projected mean.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: cubicEstimator_fluctuation_second_moment_sample_rate
lemma cubicEstimator_fluctuation_second_moment_sample_rate
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ) (hn : threshold ≤ n)
    (hP : ModelClass c_f C_f L P n) (A : Bool) :
    (∫ ω, (cubicEstimator c_f C_f ω A -
      projectedEstimatorMean c_f C_f L P n hP ω A) ^ 2 ∂dataLaw P n n) ≤
    3 * (10 * (7 : ℝ) ^ 2 * (fourthDerivativeEnvelope c_f C_f) ^ 2 +
      60 * quadVarianceConstant c_f C_f +
      310 * cubicVarianceConstant c_f C_f) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  let := sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  let := targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  let : IsProbabilityMeasure (dataLaw P n n) := by
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]
    infer_instance
  have hm : trainingSigma n ≤ (inferInstance : MeasurableSpace (TwoSample n n)) := by
    rw [trainingSigma_eq_comap_flatTrainingProj]
    exact ((measurable_finsetCoordProj (flatBlock n 0)).comp
      (MeasurableEquiv.sumPiEquivProdPi (FlatObs n)).symm.measurable).comap_le
  have heq := cubicEstimator_sub_projectedEstimatorMean_eq_centered_corrections
    c_f C_f L P n hn hP A
  have hsquare := heq.fun_comp (fun z : ℝ => z ^ 2)
  have hi := integral_congr_ae hsquare
  simp only [Function.comp_apply] at hi
  rw [hi, ← integral_condExp hm]
  exact centered_corrections_expected_conditional_second_moment_sample_rate
    c_f C_f L P n hn hP A

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
