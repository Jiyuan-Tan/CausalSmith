module
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenGaussian
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenLocalProduct
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenMomentLowerBound
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenSmoothing
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenStandardize
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenTaylor
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenUnit
public import Causalean.Stat.CLT.BerryEsseen.IIDCharFunProduct
public import Mathlib.Probability.CentralLimitTheorem

/-! # Quantitative scalar normal approximation for an iid real law

This module isolates the probability-theoretic Berry–Esseen step from the
cross-fitting model. The law is on the real line and the sample has its finite
product distribution. The third absolute moment is explicitly integrable;
its numerical upper bound alone would not imply integrability in Lean.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For [a centered real law](hyp:hmean_int,hmean) with
[positive variance σ2](hyp:hσ2,hvar_int,hvar) and
[integrable third absolute moment at most M3](hyp:hthird_int,hthird), and
[any positive number n of independent draws](hyp:hn),
[the CDF of the sum divided by √n·√σ2 differs from the standard Gaussian
CDF at every threshold x by at most M3/((√σ2)³·√n)](goal): the scalar
Berry–Esseen bound with universal constant one. -/
theorem iid_real_berry_esseen
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (σ2 M3 : ℝ) (hσ2 : 0 < σ2)
    (hmean_int : Integrable (fun x : ℝ => x) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hvar_int : Integrable (fun x : ℝ => x ^ 2) μ)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = σ2)
    (hthird_int : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hthird : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ M3)
    (n : ℕ) (hn : 0 < n) (x : ℝ) :
    |((Measure.pi (fun _ : Fin n => μ))
        {v : Fin n → ℝ |
          (∑ i : Fin n, v i) / (Real.sqrt (n : ℝ) * Real.sqrt σ2) ≤ x}).toReal -
      ((gaussianReal 0 1) (Set.Iic x)).toReal| ≤
      M3 / ((Real.sqrt σ2) ^ 3 * Real.sqrt (n : ℝ)) := by
  by_cases hn2 : 2 ≤ n
  · haveI : IsProbabilityMeasure (μ.map (fun y : ℝ => y / Real.sqrt σ2)) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    obtain ⟨hi1, hm, hi2, hv, hi3, h3⟩ := standardized_law_moments μ σ2 M3 hσ2
      hmean_int hmean hvar_int hvar hthird_int hthird
    rw [standardized_iid_sum_event μ σ2 hσ2 n x]
    have h := iid_unit_variance_berry_esseen
      (μ.map (fun y : ℝ => y / Real.sqrt σ2))
      (M3 / (Real.sqrt σ2) ^ 3) hi1 hm hi2 hv hi3 h3 n hn2 x
    simpa only [div_div] using h
  · have hn1 : n = 1 := by omega
    subst n
    norm_num only [Nat.cast_one]
    have hlower := variance_third_absolute_moment_lower_bound μ σ2 M3 hσ2
      hmean_int hmean hvar_int hvar hthird_int hthird
    have hrhs : 1 ≤ M3 / ((Real.sqrt σ2) ^ 3 * Real.sqrt (1 : ℝ)) := by
      simp only [Real.sqrt_one, mul_one]
      exact (le_div_iff₀ (pow_pos (Real.sqrt_pos.2 hσ2) 3)).2 (by simpa using hlower)
    have hprob (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
        (ρ (Set.Iic x)).toReal ≤ 1 := by
      have h := ENNReal.toReal_mono (measure_ne_top ρ _)
        (measure_mono (Set.subset_univ (Set.Iic x)))
      simpa using h
    have hevent : ((Measure.pi (fun _ : Fin 1 => μ))
        {v : Fin 1 → ℝ | (∑ i : Fin 1, v i) /
          (Real.sqrt (1 : ℝ) * Real.sqrt σ2) ≤ x}).toReal ≤ 1 := by
      have h := ENNReal.toReal_mono
        (measure_ne_top (Measure.pi (fun _ : Fin 1 => μ)) _)
        (measure_mono (Set.subset_univ
          {v : Fin 1 → ℝ | (∑ i : Fin 1, v i) /
            (Real.sqrt (1 : ℝ) * Real.sqrt σ2) ≤ x}))
      simpa using h
    apply le_trans _ hrhs
    rw [abs_le]
    constructor <;> linarith [hprob (gaussianReal 0 1),
      ENNReal.toReal_nonneg (a := (gaussianReal 0 1) (Set.Iic x)),
      ENNReal.toReal_nonneg (a := (Measure.pi (fun _ : Fin 1 => μ))
        {v : Fin 1 → ℝ | (∑ i : Fin 1, v i) /
          (Real.sqrt (1 : ℝ) * Real.sqrt σ2) ≤ x})]

end Causalean.Stat.CLT.BerryEsseen
