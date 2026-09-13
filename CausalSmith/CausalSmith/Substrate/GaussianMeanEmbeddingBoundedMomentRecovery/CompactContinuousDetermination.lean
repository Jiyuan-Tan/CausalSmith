import CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery.WeightedMoments
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Continuous-test determination on a compact interval

This module isolates the Weierstrass approximation step and the standard
measure-extensionality step used in compact Gaussian moment determination.
-/

open MeasureTheory Set

noncomputable section

namespace CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery

/-- For finite measures on a common bounded interval, equality of every Gaussian-weighted
monomial integral implies equality of the integrals of every continuous real function.

Proof route: approximate `f / gaussianWeight` uniformly on `Icc (-B) B` by a polynomial,
use `gaussianWeightedPolynomial_integral_eq`, and bound both integral errors by the
approximation error times the finite total mass.  The support hypotheses turn every
pointwise bound on the interval into an almost-everywhere bound for the corresponding
measure; `gaussianWeight` is positive and at most one. -/
theorem continuousIntegral_eq_of_gaussianWeightedMoments_eq
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : ℝ) (hB : 0 ≤ B)
    (hμ : μ (Icc (-B) B)ᶜ = 0) (hν : ν (Icc (-B) B)ᶜ = 0)
    (hmom : ∀ m : ℕ,
      ∫ r, gaussianWeightedMonomial m r ∂μ =
        ∫ r, gaussianWeightedMonomial m r ∂ν)
    (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ r, f r ∂μ = ∫ r, f r ∂ν := by
  apply eq_of_forall_dist_le
  intro ε hε
  let M : ℝ := μ.real univ + ν.real univ + 1
  have hMpos : 0 < M := by
    dsimp [M]
    have hμnonneg : 0 ≤ μ.real univ := ENNReal.toReal_nonneg
    have hνnonneg : 0 ≤ ν.real univ := ENNReal.toReal_nonneg
    linarith
  let δ : ℝ := ε / M
  have hδ : 0 < δ := div_pos hε hMpos
  have hquot : Continuous (fun r : ℝ => f r / gaussianWeight r) := by
    apply hf.div
    · unfold gaussianWeight
      fun_prop
    · intro r
      unfold gaussianWeight
      exact (Real.exp_pos _).ne'
  obtain ⟨p, hp⟩ :=
    exists_polynomial_near_of_continuousOn (-B) B
      (fun r : ℝ => f r / gaussianWeight r) hquot.continuousOn δ hδ
  let g : ℝ → ℝ := fun r => gaussianWeight r * p.eval r
  have hg : Continuous g := by
    dsimp [g]
    unfold gaussianWeight
    fun_prop
  have hμmem : ∀ᵐ r ∂μ, r ∈ Icc (-B) B := by
    rw [ae_iff]
    exact hμ
  have hνmem : ∀ᵐ r ∂ν, r ∈ Icc (-B) B := by
    rw [ae_iff]
    exact hν
  have hμres : μ.restrict (Icc (-B) B) = μ :=
    Measure.restrict_eq_self_of_ae_mem hμmem
  have hνres : ν.restrict (Icc (-B) B) = ν :=
    Measure.restrict_eq_self_of_ae_mem hνmem
  have hfμ : Integrable f μ := by
    rw [← hμres]
    exact hf.integrableOn_Icc
  have hfν : Integrable f ν := by
    rw [← hνres]
    exact hf.integrableOn_Icc
  have hgμ : Integrable g μ := by
    rw [← hμres]
    exact hg.integrableOn_Icc
  have hgν : Integrable g ν := by
    rw [← hνres]
    exact hg.integrableOn_Icc
  have herror : ∀ r ∈ Icc (-B) B, ‖f r - g r‖ ≤ δ := by
    intro r hr
    have hwpos : 0 < gaussianWeight r := by
      unfold gaussianWeight
      exact Real.exp_pos _
    have hwle : gaussianWeight r ≤ 1 := by
      unfold gaussianWeight
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (sq_nonneg r)
    have happ := hp r hr
    rw [Real.norm_eq_abs]
    dsimp [g]
    have hid :
        f r - gaussianWeight r * p.eval r =
          -gaussianWeight r * (p.eval r - f r / gaussianWeight r) := by
      field_simp
      ring
    rw [hid, abs_mul, abs_neg, abs_of_pos hwpos]
    have habs := abs_nonneg (p.eval r - f r / gaussianWeight r)
    nlinarith
  have herrμ :
      ‖∫ r, (f r - g r) ∂μ‖ ≤ δ * μ.real univ := by
    apply norm_integral_le_of_norm_le_const
    filter_upwards [hμmem] with r hr
    exact herror r hr
  have herrν :
      ‖∫ r, (f r - g r) ∂ν‖ ≤ δ * ν.real univ := by
    apply norm_integral_le_of_norm_le_const
    filter_upwards [hνmem] with r hr
    exact herror r hr
  rw [integral_sub hfμ hgμ] at herrμ
  rw [integral_sub hfν hgν] at herrν
  have hpoly :
      (∫ r, g r ∂μ) = ∫ r, g r ∂ν := by
    dsimp [g]
    exact gaussianWeightedPolynomial_integral_eq μ ν hmom p
  have hmassμ : 0 ≤ μ.real univ := ENNReal.toReal_nonneg
  have hmassν : 0 ≤ ν.real univ := ENNReal.toReal_nonneg
  calc
    dist (∫ r, f r ∂μ) (∫ r, f r ∂ν) =
        ‖((∫ r, f r ∂μ) - ∫ r, g r ∂μ) +
          ((∫ r, g r ∂ν) - ∫ r, f r ∂ν)‖ := by
            rw [dist_eq_norm, hpoly]
            congr 1
            ring
    _ ≤ ‖(∫ r, f r ∂μ) - ∫ r, g r ∂μ‖ +
        ‖(∫ r, g r ∂ν) - ∫ r, f r ∂ν‖ := norm_add_le _ _
    _ = ‖(∫ r, f r ∂μ) - ∫ r, g r ∂μ‖ +
        ‖(∫ r, f r ∂ν) - ∫ r, g r ∂ν‖ := by
          congr 1
          exact norm_sub_rev _ _
    _ ≤ δ * μ.real univ + δ * ν.real univ := add_le_add herrμ herrν
    _ = δ * (μ.real univ + ν.real univ) := by ring
    _ ≤ δ * (μ.real univ + ν.real univ + 1) := by nlinarith
    _ = ε := by
      dsimp [δ, M]
      field_simp

/-- Two finite real Borel measures agreeing on the integrals of all continuous real functions
are equal. -/
theorem measure_eq_of_continuousIntegral_eq
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : ℝ → ℝ), Continuous f → ∫ r, f r ∂μ = ∫ r, f r ∂ν) :
    μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact h f f.continuous

end CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery
