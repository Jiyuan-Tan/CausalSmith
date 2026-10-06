module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.GridAdmissibility
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.InterventionMoments
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.PairPolynomial
public import Mathlib.Probability.Moments.Variance

/-!
# Unbiased observable empirical moments

Each retained score is square-integrable and has the same intervention mean.
Averaging the T−6 retained epochs therefore gives an unbiased observable moment.
-/

public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open MeasureTheory
open scoped BigOperators

/-- Projection to observed coordinates satisfies the [measurability conclusion](goal). -/
-- @node: binary_obsProj_measurable
@[fun_prop] lemma binary_obsProj_measurable {T : Nat} :
    Measurable (obsProj (T := T) (nX := 2) (nH := 2)) := by
  unfold obsProj curState actionAt rewardAt
  fun_prop

/-- The observed law inherits probability mass one from the trajectory law. [the stated conclusion holds](goal).-/
-- @node: binary_obsLaw_isProbability
lemma binary_obsLaw_isProbability {T : Nat} (M : RawPomdpExperiment T 2 2) :
    IsProbabilityMeasure (obsLaw M) :=
  Measure.isProbabilityMeasure_map binary_obsProj_measurable.aemeasurable

/-- Policy overlap and bounded rewards make every observable score square-integrable. [Under the listed formal conditions](hyp:hM), [the stated conclusion holds](goal).-/
-- @node: binary_score_memLp_two
lemma binary_score_memLp_two {T : Nat} {t0 zeta : ℝ}
    (M : RawPomdpExperiment T 2 2) (hM : BinaryPomdpClass t0 zeta M)
    (k : Nat) (t : Fin T) : MemLp (fun w => score k M.b M.e w t) 2 (obsLaw M) := by
  obtain ⟨hK, hI, hO, hY⟩ := finitePomdpView_laws M hM.pomdp_kernel
    hM.sequential_ignorability hM.policy_overlap
  have hL : 1 ≤ policyFactor zeta := by
    simpa only [policyFactor, Real.exp_zero] using Real.exp_le_exp.mpr hM.zeta_nonneg
  exact PomdpLatentOverlapMinimax.phiwScore_memLp (k := k) hI hO hL hY 2 t

/-- The mean of an eligible score, computed using only its observed-data law,
equals the target-policy matrix-power moment. [Under the listed formal conditions](hyp:hM,hkt), [the stated conclusion holds](goal).-/
-- @node: integral_observable_score_eq_matrixMoment
lemma integral_observable_score_eq_matrixMoment {T : Nat} {t0 zeta : ℝ}
    (M : RawPomdpExperiment T 2 2) (hM : BinaryPomdpClass t0 zeta M)
    (k : Fin 7) (t : Fin T) (hkt : k.val ≤ t.val) :
    (∫ w, score k.val M.b M.e w t ∂obsLaw M) =
      matrixMoment (stationaryLaw (policyKernel M M.b))
        (Matrix.of (policyKernel M M.e)) (rewardRegression M) k.val := by
  rw [obsLaw, integral_map
    binary_obsProj_measurable.aemeasurable
    (score_measurable k.val M.b M.e t).aestronglyMeasurable]
  exact (observable_intervention_moments M hM k t hkt).1

/-- The average over epochs seven through T is unbiased for each of the seven
intervention moments; its normalization uses exactly T−6 summands. [Under the listed formal conditions](hyp:hT,hM), [the stated conclusion holds](goal).-/
-- @node: empiricalMoment_unbiased
lemma empiricalMoment_unbiased {T : Nat} {t0 zeta : ℝ} (hT : 12 ≤ T)
    (M : RawPomdpExperiment T 2 2) (hM : BinaryPomdpClass t0 zeta M)
    (k : Fin 7) :
    (∫ w, empiricalMoment k.val M.b M.e w ∂obsLaw M) =
      matrixMoment (stationaryLaw (policyKernel M M.b))
        (Matrix.of (policyKernel M M.e)) (rewardRegression M) k.val := by
  classical
  let := binary_obsLaw_isProbability M
  let I := Finset.univ.filter (fun t : Fin T => 6 ≤ t.val)
  have hI : I = Finset.Ici (⟨6, by omega⟩ : Fin T) := by
    ext t
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
    rfl
  have hcard : I.card = T - 6 := by rw [hI, Fin.card_Ici]
  have hN : ((T - 6 : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (show T - 6 ≠ 0 by omega)
  unfold empiricalMoment
  rw [integral_const_mul, integral_finsetSum]
  · have hmean (t : Fin T) (ht : t ∈ I) :
        (∫ w, score k.val M.b M.e w t ∂obsLaw M) =
          matrixMoment (stationaryLaw (policyKernel M M.b))
            (Matrix.of (policyKernel M M.e)) (rewardRegression M) k.val := by
      apply integral_observable_score_eq_matrixMoment M hM k t
      have ht6 := (Finset.mem_filter.mp ht).2
      omega
    change ((T - 6 : Nat) : ℝ)⁻¹ * (∑ t ∈ I, _) = _
    rw [Finset.sum_congr rfl hmean]
    simp only [Finset.sum_const, nsmul_eq_mul, hcard]
    rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  · intro t ht
    exact (binary_score_memLp_two M hM k.val t).integrable one_le_two

/-- The score variance inherits the second-moment bound in the intervention
lemma. This controls the diagonal term in equation (8). [Under the listed formal conditions](hyp:hM,hkt), [the stated conclusion holds](goal).-/
-- @node: observable_score_variance_le
lemma observable_score_variance_le {T : Nat} {t0 zeta : ℝ}
    (M : RawPomdpExperiment T 2 2) (hM : BinaryPomdpClass t0 zeta M)
    (k : Fin 7) (t : Fin T) (hkt : k.val ≤ t.val) :
    ProbabilityTheory.variance (fun w => score k.val M.b M.e w t) (obsLaw M) ≤
      policyFactor zeta ^ (k.val + 1) := by
  let := binary_obsLaw_isProbability M
  apply (ProbabilityTheory.variance_le_expectation_sq
    (binary_score_memLp_two M hM k.val t).aestronglyMeasurable).trans
  change (∫ w, score k.val M.b M.e w t ^ 2 ∂obsLaw M) ≤ _
  rw [obsLaw, integral_map binary_obsProj_measurable.aemeasurable
    ((score_measurable k.val M.b M.e t).pow_const 2).aestronglyMeasurable]
  exact (observable_intervention_moments M hM k t hkt).2.1

/-- Without a separation assumption, nonnegativity of the variances of the
sum and difference controls covariance by the common score variance bound.
This is the short-lag bound in equation (8). [Under the listed formal conditions](hyp:hM,hkt,hku), [the stated conclusion holds](goal).-/
-- @node: observable_score_covariance_le
lemma observable_score_covariance_le {T : Nat} {t0 zeta : ℝ}
    (M : RawPomdpExperiment T 2 2) (hM : BinaryPomdpClass t0 zeta M)
    (k : Fin 7) (t u : Fin T) (hkt : k.val ≤ t.val) (hku : k.val ≤ u.val) :
    |ProbabilityTheory.covariance (fun w => score k.val M.b M.e w t)
      (fun w => score k.val M.b M.e w u) (obsLaw M)| ≤
      policyFactor zeta ^ (k.val + 1) := by
  let := binary_obsLaw_isProbability M
  have ht := binary_score_memLp_two M hM k.val t
  have hu := binary_score_memLp_two M hM k.val u
  have hvt := observable_score_variance_le M hM k t hkt
  have hvu := observable_score_variance_le M hM k u hku
  have hadd := ProbabilityTheory.variance_nonneg
    (fun w => score k.val M.b M.e w t + score k.val M.b M.e w u) (obsLaw M)
  have hsub := ProbabilityTheory.variance_nonneg
    (fun w => score k.val M.b M.e w t - score k.val M.b M.e w u) (obsLaw M)
  rw [ProbabilityTheory.variance_fun_add ht hu] at hadd
  rw [ProbabilityTheory.variance_fun_sub ht hu] at hsub
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The separated-window covariance estimate also holds under the observed
law used by the estimator, by measurable projection of the full trajectory. [Under the listed formal conditions](hyp:hM,hkt,hu), [the stated conclusion holds](goal).-/
-- @node: observable_score_covariance_le_separated
lemma observable_score_covariance_le_separated {T : Nat} {t0 zeta : ℝ}
    (M : RawPomdpExperiment T 2 2) (hM : BinaryPomdpClass t0 zeta M)
    (k : Fin 7) (t u : Fin T) (hkt : k.val ≤ t.val)
    (hu : k.val + 1 ≤ u.val - t.val) :
    |ProbabilityTheory.covariance (fun w => score k.val M.b M.e w t)
      (fun w => score k.val M.b M.e w u) (obsLaw M)| ≤
      mixingAlpha t0 ^ (u.val - t.val - k.val - 1) := by
  rw [obsLaw, ProbabilityTheory.covariance_map_fun
    (score_measurable k.val M.b M.e t).aestronglyMeasurable
    (score_measurable k.val M.b M.e u).aestronglyMeasurable
    binary_obsProj_measurable.aemeasurable]
  exact scoreCovariance_le_separated M hM t u hkt hu

/-- Finite averaging preserves the scores' square integrability. [Under the listed formal conditions](hyp:hM), [the stated conclusion holds](goal).-/
-- @node: empiricalMoment_memLp_two
lemma empiricalMoment_memLp_two {T : Nat} {t0 zeta : ℝ}
    (M : RawPomdpExperiment T 2 2) (hM : BinaryPomdpClass t0 zeta M)
    (k : Nat) : MemLp (empiricalMoment k M.b M.e) 2 (obsLaw M) := by
  classical
  exact (memLp_finsetSum _ (fun t _ => binary_score_memLp_two M hM k t)).const_mul _

/-- The unbiased empirical squared error is exactly the normalized finite
covariance sum, before bounding short and separated lags in equation (8). [Under the listed formal conditions](hyp:hT,hM), [the stated conclusion holds](goal).-/
-- @node: empiricalMoment_mse_eq_covariance_sum
lemma empiricalMoment_mse_eq_covariance_sum {T : Nat} {t0 zeta : ℝ}
    (hT : 12 ≤ T) (M : RawPomdpExperiment T 2 2)
    (hM : BinaryPomdpClass t0 zeta M) (k : Fin 7) :
    (∫ w, (empiricalMoment k.val M.b M.e w -
      matrixMoment (stationaryLaw (policyKernel M M.b))
        (Matrix.of (policyKernel M M.e)) (rewardRegression M) k.val) ^ 2 ∂obsLaw M) =
    ((T - 6 : Nat) : ℝ)⁻¹ ^ 2 *
      ∑ t ∈ Finset.univ.filter (fun t : Fin T => 6 ≤ t.val),
        ∑ u ∈ Finset.univ.filter (fun u : Fin T => 6 ≤ u.val),
          ProbabilityTheory.covariance (fun w => score k.val M.b M.e w t)
            (fun w => score k.val M.b M.e w u) (obsLaw M) := by
  classical
  let := binary_obsLaw_isProbability M
  rw [← empiricalMoment_unbiased hT M hM k,
    ← ProbabilityTheory.variance_eq_integral
      (empiricalMoment_memLp_two M hM k.val).aemeasurable]
  unfold empiricalMoment
  rw [ProbabilityTheory.variance_const_mul, ProbabilityTheory.variance_fun_sum']
  intro t _
  exact binary_score_memLp_two M hM k.val t

/-- The square of the maximum of seven absolute errors is bounded by their
sum of squares, pointwise, as used in equation (9). [the stated conclusion holds](goal).-/
-- @node: seven_error_max_sq_le_sum
lemma seven_error_max_sq_le_sum (x : Fin 7 → ℝ) :
    (⨆ k : Fin 7, |x k|) ^ 2 ≤ ∑ k : Fin 7, x k ^ 2 := by
  obtain ⟨k, hk⟩ := exists_eq_ciSup_of_finite (f := fun k => |x k|)
  rw [← hk, sq_abs]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ k)

/-- Integrating the maximum error costs at most the sum of the seven empirical
mean-squared errors; no independence between the seven moments is needed. [Under the listed formal conditions](hyp:hM), [the stated conclusion holds](goal).-/
-- @node: empiricalMoment_max_mse_le_sum
lemma empiricalMoment_max_mse_le_sum {T : Nat} {t0 zeta : ℝ}
    (M : RawPomdpExperiment T 2 2) (hM : BinaryPomdpClass t0 zeta M)
    (m : Fin 7 → ℝ) :
    (∫ w, (⨆ k : Fin 7, |empiricalMoment k.val M.b M.e w - m k|) ^ 2 ∂obsLaw M) ≤
      ∑ k : Fin 7, ∫ w, (empiricalMoment k.val M.b M.e w - m k) ^ 2 ∂obsLaw M := by
  classical
  let := binary_obsLaw_isProbability M
  have hint (k : Fin 7) :
      Integrable (fun w => (empiricalMoment k.val M.b M.e w - m k) ^ 2) (obsLaw M) :=
    ((empiricalMoment_memLp_two M hM k.val).sub (memLp_const (m k))).integrable_sq
  have hsum : Integrable
      (fun w => ∑ k : Fin 7, (empiricalMoment k.val M.b M.e w - m k) ^ 2)
      (obsLaw M) := integrable_finsetSum _ (fun k _ => hint k)
  have hmeas : AEStronglyMeasurable
      (fun w => (⨆ k : Fin 7, |empiricalMoment k.val M.b M.e w - m k|) ^ 2)
      (obsLaw M) := by
    apply Measurable.aestronglyMeasurable
    unfold empiricalMoment
    fun_prop
  have hmax : Integrable
      (fun w => (⨆ k : Fin 7, |empiricalMoment k.val M.b M.e w - m k|) ^ 2)
      (obsLaw M) := hsum.mono' hmeas (Filter.Eventually.of_forall (fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact seven_error_max_sq_le_sum _))
  calc
    _ ≤ ∫ w, ∑ k : Fin 7, (empiricalMoment k.val M.b M.e w - m k) ^ 2 ∂obsLaw M :=
      integral_mono hmax hsum (fun w => seven_error_max_sq_le_sum _)
    _ = _ := integral_finsetSum _ (fun k _ => hint k)

end CausalSmith.Stat.PomdpBinaryhiddenRate
