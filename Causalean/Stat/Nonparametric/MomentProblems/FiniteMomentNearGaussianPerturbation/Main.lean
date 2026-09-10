/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.MomentProblems.FiniteMomentNearGaussianPerturbation.Carleman
import Causalean.Stat.Nonparametric.MomentProblems.FiniteMomentNearGaussianPerturbation.CumulantTransfer
import Causalean.Stat.Nonparametric.MomentProblems.FiniteMomentNearGaussianPerturbation.DensityPerturbation

/-!
# Non-Gaussian laws near the Gaussian with finitely many matching moments

This module combines a bounded finite-moment-orthogonal density perturbation with a
quantitative Gaussian moment bound.  The resulting law is a genuine non-Gaussian
probability measure arbitrarily close in testing total variation to the standard
Gaussian, matches any prescribed finite initial segment of raw moments and cumulants,
has all absolute moments, and carries an explicit divergent Carleman series.
-/

namespace Causalean.Stat.MomentProblems

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Given [a finite moment cutoff](hyp:K) of [at least three](hyp:hK) and [a strictly positive
testing-distance radius](hyp:rho,hrho), [there is a non-Gaussian probability law within that
radius of the standard Gaussian, with matching raw moments and source cumulants through the
cutoff, all absolute moments, and a divergent Hamburger--Carleman series](goal). -/
theorem exists_finiteMoment_near_gaussian_perturbation
    (K : ℕ) (rho : ℝ) (hK : 3 ≤ K) (hrho : 0 < rho) :
    ∃ F : Measure ℝ,
      IsProbabilityMeasure F ∧
      (∫ x, x ∂F) = 0 ∧
      variance id F = 1 ∧
      ¬ IsGaussianLaw F ∧
      totalVariationDistance F (gaussianReal 0 1) < rho ∧
      (∀ k, k ≤ K →
        (∫ x, x ^ k ∂F) = ∫ x, x ^ k ∂gaussianReal 0 1) ∧
      (∀ k, Integrable (fun x : ℝ => |x| ^ k) F) ∧
      (∑' s : ℕ,
        (ENNReal.ofReal |∫ x, x ^ (2 * (s + 1)) ∂F|).rpow
          (-(1 : ℝ) / (2 * (s + 1)))) = ⊤ ∧
      (∀ k, k ≤ K →
        sourceCumulant F (id : ℝ → ℝ) k =
          sourceCumulant (gaussianReal 0 1) (id : ℝ → ℝ) k) := by
  obtain ⟨h, hmeas, hbound, hnonzero, horth⟩ :=
    exists_bounded_gaussian_orthogonal_perturbation K
  let ε : ℝ := min (1 / 2) (rho / 2)
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min (by norm_num) (half_pos hrho)
  have hεone : ε < 1 := by
    have hεle : ε ≤ 1 / 2 := min_le_left _ _
    linarith
  have hερho : ε < rho := by
    have hεle : ε ≤ rho / 2 := min_le_right _ _
    linarith
  let F : Measure ℝ := gaussianPerturbation h ε
  have hspec := gaussianPerturbation_spec hmeas hbound hnonzero horth
    hεpos hεone hερho
  change IsProbabilityMeasure F ∧
      F ≠ gaussianReal 0 1 ∧
      totalVariationDistance F (gaussianReal 0 1) < rho ∧
      (∀ k, k ≤ K → rawMoment F k = rawMoment (gaussianReal 0 1) k) ∧
      (∀ k, Integrable (fun x : ℝ => |x| ^ k) F) ∧
      (∀ n : ℕ, 0 < n →
        |rawMoment F (2 * n)| ≤ 2 * (2 * n : ℝ) ^ n) at hspec
  rcases hspec with ⟨hprob, hne, htv, hmoment, habs, heven⟩
  have hmean : (∫ x, x ∂F) = 0 := by
    have hmoment_one := hmoment 1 (by omega)
    simpa [rawMoment_eq_integral] using hmoment_one
  have hvariance : variance id F = 1 := by
    have hmoment_two := hmoment 2 (by omega)
    have hgauss_two : rawMoment (gaussianReal 0 1) 2 = 1 := by
      have hv : variance id (gaussianReal 0 1) = (1 : ℝ) := by
        simpa using
          (variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)))
      change variance (fun x : ℝ => x) (gaussianReal 0 1) = 1 at hv
      rw [variance_eq_integral measurable_id'.aemeasurable] at hv
      simpa [rawMoment_eq_integral, Function.id_def] using hv
    change variance (fun x : ℝ => x) F = 1
    rw [variance_eq_integral measurable_id'.aemeasurable, hmean]
    simpa [rawMoment_eq_integral] using hmoment_two.trans hgauss_two
  have hnongaussian : ¬ IsGaussianLaw F := by
    rintro ⟨m, v, hF⟩
    have hm : m = 0 := by
      calc
        m = ∫ x, x ∂gaussianReal m v := integral_id_gaussianReal.symm
        _ = ∫ x, x ∂F := by rw [hF]
        _ = 0 := hmean
    have hv_real : (v : ℝ) = 1 := by
      calc
        (v : ℝ) = variance id (gaussianReal m v) := variance_id_gaussianReal.symm
        _ = variance id F := by rw [hF]
        _ = 1 := hvariance
    have hv : v = 1 := by
      exact_mod_cast hv_real
    apply hne
    exact hF.trans (gaussianReal_ext_iff.mpr ⟨hm, hv⟩)
  have hcarleman : hamburgerCarlemanSeries F = ⊤ :=
    hamburgerCarlemanSeries_eq_top_of_evenMoment_le F heven
  refine ⟨F, hprob, hmean, hvariance, hnongaussian, htv, ?_, habs, ?_, ?_⟩
  · intro k hk
    simpa only [rawMoment_eq_integral] using hmoment k hk
  · rw [← hamburgerCarlemanSeries_eq]
    exact hcarleman
  · exact sourceCumulant_eq_of_rawMoment_eq_up_to
      F (gaussianReal 0 1) K hmoment

end Causalean.Stat.MomentProblems
