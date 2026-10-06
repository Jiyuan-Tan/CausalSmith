module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.GridValue

/-!
# Fixed-binary stable-grid upper bound

The finite observed-data grid estimator attains a uniform parametric
mean-squared-error bound over the six-condition binary POMDP class.
-/

public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open MeasureTheory
open scoped BigOperators

-- @node: thm:stable-grid-upper
/-- For [positive mixing time](hyp:ht0), [nonnegative overlap exponent](hyp:hzeta),
and the [stated horizon range](hyp:hT), the seven-moment stable-grid estimator
satisfies the [uniform mean-squared-error bound](goal). -/
theorem stableGrid_upper (T : Nat) (t0 zeta : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 ≤ zeta) (hT : 12 ≤ T) :
    ∀ m : ModelIndex T t0 zeta,
      Causalean.Stat.sqRisk (obsLaw m.raw)
        (stableGridEstimator T t0 m.raw.b m.raw.e)
        (targetValue m.raw) ≤
      (stabilityFactor (mixingAlpha t0) ^ 2 *
        (112 * varianceFactor (mixingAlpha t0) (policyFactor zeta) + 2)) / T := by
  intro m
  classical
  let M := m.raw
  let := binary_obsLaw_isProbability M
  let a := mixingAlpha t0
  let B := stabilityFactor a
  let V := varianceFactor a (policyFactor zeta)
  let n : ℝ := (T - 6 : Nat)
  let pop := fun k : Fin 7 => matrixMoment (stationaryLaw (policyKernel M M.b))
    (Matrix.of (policyKernel M M.e)) (rewardRegression M) k.val
  let eps := fun w : ObsView T 2 =>
    ⨆ k : Fin 7, |empiricalMoment k.val M.b M.e w - pop k|
  have ha1 : a < 1 := by
    change mixingAlpha t0 < 1
    rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr ht0)
  have hV : 0 ≤ V := by
    change 0 ≤ 13 * policyFactor zeta ^ 7 + 2 / (1 - a)
    have hden : 0 < 1 - a := sub_pos.mpr ha1
    have hL : 1 ≤ policyFactor zeta := by
      simpa only [policyFactor, Real.exp_zero] using Real.exp_le_exp.mpr hzeta
    positivity
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hn : 0 < n := by dsimp [n]; exact_mod_cast (show 0 < T - 6 by omega)
  have hnt : (T : ℝ) ≤ 2 * n := by
    have hnat : T ≤ 2 * (T - 6) := by omega
    dsimp only [n]
    exact_mod_cast hnat
  have ht1 : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  have hint (k : Fin 7) :
      Integrable (fun w => (empiricalMoment k.val M.b M.e w - pop k) ^ 2) (obsLaw M) :=
    ((empiricalMoment_memLp_two M m.mem k.val).sub (memLp_const (pop k))).integrable_sq
  have hsum : Integrable
      (fun w => ∑ k : Fin 7, (empiricalMoment k.val M.b M.e w - pop k) ^ 2)
      (obsLaw M) := integrable_finsetSum _ (fun k _ => hint k)
  have hmeas : AEStronglyMeasurable (fun w => eps w ^ 2) (obsLaw M) := by
    apply Measurable.aestronglyMeasurable
    dsimp [eps]
    fun_prop
  have heint : Integrable (fun w => eps w ^ 2) (obsLaw M) :=
    hsum.mono' hmeas (Filter.Eventually.of_forall (fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact seven_error_max_sq_le_sum _))
  have he : (∫ w, eps w ^ 2 ∂obsLaw M) ≤ 7 * V / n :=
    empiricalMoment_max_mse_le_varianceFactor hT M m.mem
  have hpoint (w : ObsView T 2) :
      (stableGridEstimator T t0 M.b M.e w - targetValue M) ^ 2 ≤
        B ^ 2 * (8 * eps w ^ 2 + 2 * (T : ℝ)⁻¹ ^ 2) := by
    have herr := stableGridEstimator_value_error hT M m.mem w
    have hs : (stableGridEstimator T t0 M.b M.e w - targetValue M) ^ 2 ≤
        (B * (2 * eps w + (T : ℝ)⁻¹)) ^ 2 := by
      rw [← sq_abs (stableGridEstimator T t0 M.b M.e w - targetValue M)]
      exact pow_le_pow_left₀ (abs_nonneg _) herr 2
    calc
      _ ≤ (B * (2 * eps w + (T : ℝ)⁻¹)) ^ 2 := hs
      _ = B ^ 2 * (2 * eps w + (T : ℝ)⁻¹) ^ 2 := mul_pow _ _ _
      _ ≤ B ^ 2 * (8 * eps w ^ 2 + 2 * (T : ℝ)⁻¹ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
        nlinarith [sq_nonneg (2 * eps w - (T : ℝ)⁻¹)]
  have hboundint : Integrable
      (fun w => B ^ 2 * (8 * eps w ^ 2 + 2 * (T : ℝ)⁻¹ ^ 2)) (obsLaw M) :=
    ((heint.const_mul 8).add (integrable_const _)).const_mul _
  have hsampling : 8 * (7 * V / n) ≤ 112 * V / T := by
    have heq : 8 * (7 * V / n) = 56 * V / n := by ring
    rw [heq]
    apply (div_le_div_iff₀ hn hTr).mpr
    have hv := mul_le_mul_of_nonneg_right hnt (show 0 ≤ 56 * V by positivity)
    nlinarith
  have hgrid : (T : ℝ)⁻¹ ^ 2 ≤ 1 / T := by
    rw [inv_pow, one_div, inv_le_inv₀ (by positivity) hTr]
    nlinarith
  unfold Causalean.Stat.sqRisk
  change (∫ w, (stableGridEstimator T t0 M.b M.e w - targetValue M) ^ 2 ∂obsLaw M) ≤ _
  calc
    _ ≤ ∫ w, B ^ 2 * (8 * eps w ^ 2 + 2 * (T : ℝ)⁻¹ ^ 2) ∂obsLaw M :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun w => sq_nonneg _))
        hboundint (Filter.Eventually.of_forall hpoint)
    _ = B ^ 2 * (8 * (∫ w, eps w ^ 2 ∂obsLaw M) + 2 * (T : ℝ)⁻¹ ^ 2) := by
      rw [integral_const_mul, integral_add (heint.const_mul 8) (integrable_const _),
        integral_const_mul, integral_const]
      simp
    _ ≤ B ^ 2 * (8 * (7 * V / n) + 2 * (T : ℝ)⁻¹ ^ 2) := by gcongr
    _ ≤ B ^ 2 * (112 * V / T + 2 * (1 / T)) := by gcongr
    _ = _ := by dsimp [B, V, a]; ring

end CausalSmith.Stat.PomdpBinaryhiddenRate
