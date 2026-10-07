module
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenIIDEnvelopes
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenMomentLowerBound
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenPrawitzBudget
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenRefinedFourierIntegral
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenRefinedLocalProduct
public import Causalean.Stat.CLT.BerryEsseen.IIDCharFunProduct
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactIntegrability
public import Causalean.Stat.CLT.BerryEsseen.PrawitzSmoothing
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.CentralLimitTheorem

/-! # Unit-variance iid Berry–Esseen inequality

The constant-one scalar probability bound is isolated at unit variance, leaving
rescaling and the one-observation endpoint to the general theorem.
The standardized sum's pushforward law transfers the iid Fourier envelopes
to the Prawitz smoothing inequality and its deterministic budget.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For [a centered](hyp:hmean_int,hmean) [unit-variance](hyp:hvar_int,hvar)
scalar law with [integrable third absolute moment at most M3](hyp:hthird_int,hthird)
and [any sample size n of at least two](hyp:hn),
[the CDF of the iid sum divided by √n differs from the standard Gaussian CDF
at every threshold x by at most M3/√n](goal). -/
theorem iid_unit_variance_berry_esseen
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M3 : ℝ)
    (hmean_int : Integrable (fun x : ℝ => x) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hvar_int : Integrable (fun x : ℝ => x ^ 2) μ)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (hthird_int : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hthird : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ M3)
    (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    |((Measure.pi (fun _ : Fin n => μ))
        {v : Fin n → ℝ |
          (∑ i : Fin n, v i) / Real.sqrt (n : ℝ) ≤ x}).toReal -
      ((gaussianReal 0 1) (Set.Iic x)).toReal| ≤
      M3 / Real.sqrt (n : ℝ) := by
  classical
  have hM3 : 1 ≤ M3 :=
    (unit_second_moment_third_absolute_moment_ge_one μ hvar_int hvar hthird_int).trans
      hthird
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hspos : 0 < Real.sqrt (n : ℝ) := by positivity
  let ρ : ℝ := M3 / Real.sqrt (n : ℝ)
  have hρ : 0 < ρ := div_pos (by linarith) hspos
  let Q : Measure (Fin n → ℝ) := Measure.pi (fun _ => μ)
  let S : (Fin n → ℝ) → ℝ := fun v => (∑ i, v i) / Real.sqrt (n : ℝ)
  have hS : Measurable S := by dsimp [S]; fun_prop
  let ν : Measure ℝ := Q.map S
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hS.aemeasurable
  have hCDF : ν (Set.Iic x) = Q {v | S v ≤ x} :=
    Measure.map_apply hS measurableSet_Iic
  change |(Q {v | S v ≤ x}).toReal -
    ((gaussianReal 0 1) (Set.Iic x)).toReal| ≤ ρ
  rw [← hCDF]
  by_cases hρ1 : 1 ≤ ρ
  · have hν1 : (ν (Set.Iic x)).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top ν Set.univ)
        (measure_mono (Set.subset_univ (Set.Iic x)))
    have hG1 : ((gaussianReal 0 1) (Set.Iic x)).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top (gaussianReal 0 1) Set.univ)
        (measure_mono (Set.subset_univ (Set.Iic x)))
    exact (abs_le.mpr ⟨by linarith [ENNReal.toReal_nonneg (a := ν (Set.Iic x))],
      by linarith [ENNReal.toReal_nonneg (a := (gaussianReal 0 1) (Set.Iic x))]⟩).trans hρ1
  have hfirst : Integrable (fun y : ℝ => y) ν := by
    apply (integrable_map_measure measurable_id.aestronglyMeasurable hS.aemeasurable).2
    exact (integrable_finsetSum Finset.univ (fun i _ =>
      integrable_comp_eval (μ := fun _ : Fin n => μ) (i := i) hmean_int)).div_const _
  have hchar (t : ℝ) : charFun ν t = (charFun μ (t / Real.sqrt (n : ℝ))) ^ n := by
    rw [charFun_apply_real, integral_map hS.aemeasurable (by fun_prop)]
    rw [← iid_sum_charFun_product μ n (t / Real.sqrt (n : ℝ))]
    congr 1
    funext v
    dsimp [S]
    congr 1
    push_cast
    ring
  let U0 : ℝ := max (3 / 2 : ℝ) (Real.sqrt (4 * Real.log (1 / ρ)))
  let U : ℝ := 12 / (5 * ρ)
  obtain ⟨hcut, hbudget⟩ := prawitz_berry_esseen_budget ρ hρ (lt_of_not_ge hρ1)
  have hU0 : 0 < U0 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 2)
    (le_max_left _ _)
  have hU : 0 < U := hU0.trans_le hcut
  obtain ⟨hlo_int, hhi_int, _, _⟩ := prawitz_four_terms_integrable ν hfirst U0 U hU0 hcut
  have hlo_env := prawitz_low_compact_intervalIntegrable ρ U U0 hρ.le hU hU0.le hcut
  have hhi_env := prawitz_high_compact_intervalIntegrable ρ U U0 U hU hU0 hcut le_rfl
  have hlo := intervalIntegral.integral_mono_on hU0.le hlo_int hlo_env (fun t ht => by
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [hchar]
    exact iid_unit_variance_charFun_prawitz_discrepancy_bound μ M3 hM3
      hmean_int hmean hvar_int hvar hthird_int hthird n hn t
      (by rw [abs_of_nonneg ht.1]; exact ht.2.trans hcut))
  have hhi := intervalIntegral.integral_mono_on hcut hhi_int hhi_env (fun t ht => by
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [hchar]
    exact iid_unit_variance_charFun_prawitz_moment_bound μ M3 hM3
      hmean_int hmean hvar_int hvar hthird_int hthird n hn t)
  have hcoef : 0 ≤ 2 / U := by positivity
  have hsmooth := normal_cdf_prawitz_smoothing ν hfirst U0 U hU0 hcut x
  apply le_trans _ hbudget
  change |(ν (Set.Iic x)).toReal -
    ((gaussianReal 0 1) (Set.Iic x)).toReal| ≤ prawitzBerryEsseenEnvelope ρ U0 U
  unfold prawitzBerryEsseenEnvelope
  exact hsmooth.trans (by
    linarith only [mul_le_mul_of_nonneg_left hlo hcoef,
      mul_le_mul_of_nonneg_left hhi hcoef])

end Causalean.Stat.CLT.BerryEsseen
