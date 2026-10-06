module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Calibration.Outside

/-!
# Averaged hybrid bias and mean squared error

Linearity, finite averaging of the column bias bounds, and the bias--variance
identity used in the last step of finite polynomial calibration.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {m d : ℕ}

/-- [Expectation commutes with the finite average of hybrid column statistics](goal). -/
-- @node: hybridMean_average
lemma hybridMean_average (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps : ℝ) (f : Fin d → ((Fin m → Fin d → Bool) × (Fin m → Fin d → Bool)) → ℝ) :
    hybridMean P eps (fun z => (d : ℝ)⁻¹ * ∑ j, f j z) =
      (d : ℝ)⁻¹ * ∑ j, hybridMean P eps (f j) := by
  letI := hybridLaw_probability (m := m) P eps
  unfold hybridMean
  integral_linearity

/-- Assume [positive dimension](hyp:hd) and [the stated hbias condition](hyp:hbias). [Uniform column bias bounds persist under averaging, without column independence](goal). -/
-- @node: hybrid_average_bias_le
lemma hybrid_average_bias_le (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps B : ℝ) (hd : 0 < d)
    (f : Fin d → ((Fin m → Fin d → Bool) × (Fin m → Fin d → Bool)) → ℝ)
    (theta : Fin d → ℝ)
    (hbias : ∀ j, abs (hybridMean P eps (f j) - abs (theta j)) ≤ B) :
    |hybridMean P eps (fun z => (d : ℝ)⁻¹ * ∑ j, f j z) - signedNorm theta| ≤ B := by
  rw [hybridMean_average, signedNorm, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul]
  rw [abs_of_nonneg (by positivity : 0 ≤ (d : ℝ)⁻¹)]
  calc
    _ ≤ (d : ℝ)⁻¹ * ∑ j, abs (hybridMean P eps (f j) - abs (theta j)) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (d : ℝ)⁻¹ * ∑ _j : Fin d, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hbias j)) (by positivity)
    _ = B := by simp [ne_of_gt (show (0 : ℝ) < d by exact_mod_cast hd)]

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated l condition](hyp:hL), [the stated d condition](hyp:hD), and [the stated dm condition](hyp:hDm). [The specified hybrid estimator inherits the calibrated column bias bound](goal). -/
-- @node: hybrid_average_bias_bound
lemma hybrid_average_bias_bound (hMean : BoundedMeanConcentration)
    (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m)
    (D : ℕ) (hL : 4096 ≤ logDim d)
    (hD : D = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊) (hDm : D ≤ m) :
    |hybridMean (m := m) P eps (fun z => (d : ℝ)⁻¹ * ∑ j, hybridColumn eps D j z) -
      signedNorm (contrast P)| ≤
      20000 * Real.sqrt (sigmaSquared d m eps) / Real.sqrt (logDim d) := by
  apply hybrid_average_bias_le P eps _ (by omega)
  intro j
  exact hybrid_bias_bound hMean hCheb P hP eps heps hd hm D hL hD hDm j

/-- [Centered hybrid squared error equals variance plus squared bias. the integrability condition](goal). -/
-- @node: hybridMean_sq_error_eq_variance_add_bias
lemma hybridMean_sq_error_eq_variance_add_bias
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (eps x : ℝ)
    (f : ((Fin m → Fin d → Bool) × (Fin m → Fin d → Bool)) → ℝ) :
    hybridMean P eps (fun z => (f z - x)^2) =
      hybridVar P eps f + (hybridMean P eps f - x)^2 := by
  letI := hybridLaw_probability (m := m) P eps
  have hv := variance_eq_sub (μ := hybridLaw P eps m)
    (X := fun z => f z - x) (MemLp.of_discrete)
  rw [variance_sub_const (by fun_prop) x, variance_eq_integral (by fun_prop)] at hv
  have hm : (∫ z, f z - x ∂hybridLaw P eps m) = hybridMean P eps f - x := by
    unfold hybridMean
    integral_linearity
    simp
  rw [hm] at hv
  change hybridVar P eps f = hybridMean P eps (fun z => (f z - x)^2) -
    (hybridMean P eps f - x)^2 at hv
  linarith

/-- Assume [the bounded-mean concentration inequality](hyp:hMean), [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated l condition](hyp:hL), [the stated d condition](hyp:hD), and [the stated dm condition](hyp:hDm). [Squaring the calibrated average bias gives its exact contribution to the MSE](goal). -/
-- @node: hybrid_average_bias_sq_bound
lemma hybrid_average_bias_sq_bound (hMean : BoundedMeanConcentration)
    (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m)
    (D : ℕ) (hL : 4096 ≤ logDim d)
    (hD : D = 2*⌊(1/1024 : ℝ)*logDim d/2⌋₊) (hDm : D ≤ m) :
    (hybridMean (m := m) P eps (fun z => (d : ℝ)⁻¹ * ∑ j, hybridColumn eps D j z) -
      signedNorm (contrast P))^2 ≤ 400000000 * sigmaSquared d m eps / logDim d := by
  have h := hybrid_average_bias_bound hMean hCheb P hP eps heps hd hm D hL hD hDm
  have hs : 0 ≤ sigmaSquared d m eps := by unfold sigmaSquared; positivity
  have hLpos : 0 < logDim d := by linarith
  have hsq := mul_self_le_mul_self (abs_nonneg _) h
  simp only [← pow_two, sq_abs] at hsq
  have heq : (20000 * Real.sqrt (sigmaSquared d m eps) / Real.sqrt (logDim d))^2 =
      400000000 * sigmaSquared d m eps / logDim d := by
    rw [div_pow, mul_pow, Real.sq_sqrt hs, Real.sq_sqrt hLpos.le]
    norm_num
  nlinarith [heq]

/-- Assume [the stated hvar condition](hyp:hvar) and [the stated hbias condition](hyp:hbias). [Finite second moments allow separate bias and variance bounds to be added. the variance, integrability, and bias bounds](goal). -/
-- @node: hybrid_mse_le_variance_add_bias_bounds
lemma hybrid_mse_le_variance_add_bias_bounds
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (eps x V B : ℝ)
    (f : ((Fin m → Fin d → Bool) × (Fin m → Fin d → Bool)) → ℝ)
    (hvar : hybridVar P eps f ≤ V) (hbias : (hybridMean P eps f - x)^2 ≤ B) :
    hybridMean P eps (fun z => (f z - x)^2) ≤ V + B := by
  rw [hybridMean_sq_error_eq_variance_add_bias]
  exact add_le_add hvar hbias

/-- Assume [positive dimension](hyp:hd) and [the stated l condition](hyp:hL). [On the hybrid resource domain, the column-variance exponential is absorbed by dimension](goal). -/
-- @node: hybrid_dimension_exp_bound
lemma hybrid_dimension_exp_bound (hd : 0 < d) (hL : 4096 ≤ logDim d) :
    (logDim d)^2 * Real.exp (logDim d/100) ≤ 4 * (d : ℝ) := by
  let L := logDim d
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hexp : L/4 ≤ Real.exp (L/4) := by linarith [Real.add_one_le_exp (L/4)]
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ L/4) hexp
  have hexp2 : Real.exp (L/4) * Real.exp (L/4) = Real.exp (L/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp2] at hsq
  have hfour : 4 ≤ Real.exp (49*L/100-1) := by
    have := Real.add_one_le_exp (49*L/100-1)
    dsimp [L] at *
    linarith
  have hdim : Real.exp (L-1) = (d : ℝ) := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    dsimp [L, logDim]
    rw [Real.exp_sub, Real.exp_log (by positivity)]
    exact mul_div_cancel_left₀ _ (Real.exp_pos _).ne'
  calc
    L^2 * Real.exp (L/100) ≤ 16 * Real.exp (L/2) * Real.exp (L/100) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith [hsq]
    _ = 16 * Real.exp (51*L/100) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 4 * Real.exp (L-1) := by
      have h := mul_le_mul_of_nonneg_left hfour (by positivity : 0 ≤ 4 * Real.exp (51*L/100))
      calc
        _ ≤ (4 * Real.exp (51*L/100)) * Real.exp (49*L/100-1) := by nlinarith [h]
        _ = _ := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
    _ = 4 * (d : ℝ) := by rw [hdim]

/-- Assume [positive dimension](hyp:hd) and [the stated l condition](hyp:hL). [The roadmap's averaged-variance envelope is at most 3200 times sigma squared over L](goal). -/
-- @node: hybrid_average_variance_envelope_le
lemma hybrid_average_variance_envelope_le (eps : ℝ) (hd : 0 < d)
    (hL : 4096 ≤ logDim d) :
    800 * sigmaSquared d m eps * logDim d * Real.exp (logDim d/100) / d ≤
      3200 * sigmaSquared d m eps / logDim d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLpos : 0 < logDim d := by linarith
  have hs : 0 ≤ sigmaSquared d m eps := by unfold sigmaSquared; positivity
  rw [div_le_div_iff₀ hdR hLpos]
  have h := mul_le_mul_of_nonneg_left (hybrid_dimension_exp_bound hd hL)
    (by positivity : 0 ≤ 800 * sigmaSquared d m eps)
  nlinarith [h]

end CausalSmith.Stat.LdpOptvalueUniformFrontier
