module
public import Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL.Cell
public import Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL.Integral

/-!
# Conditional KL identity for selected Bernoulli laws

When two selected laws have the same covariate law and treatment propensity,
their KL divergence is the covariate expectation of the two propensity-weighted
Bernoulli divergences.
-/

public section

open MeasureTheory

noncomputable section

namespace Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL

open Causalean.Mathlib.Probability.Kernel.ThreeBernoulli

universe u

/-- [The real-valued KL divergence between two selected laws with the same covariate
law and propensity equals the covariate integral of the conditional Bernoulli KL: one
minus the propensity times the untreated-mean Bernoulli KL plus the propensity times
the treated-mean Bernoulli KL](goal) for a [probability covariate law](hyp:μ),
[measurable propensity and means](hyp:he,hq₀,hq₁,hq₀',hq₁'), and
[uniform interior bounds](hyp:hη0,heη,hq₀η,hq₁η,hq₀'η,hq₁'η).

Use `InformationTheory.toReal_klDiv_of_measure_eq`, the almost-everywhere
cellwise log ratio, `selectedLaw_integral_cell_log_eq_sum`, and
`sum_cellMass_mul_log_ratio_eq_weighted_bernoulliKL`. Install both
`selectedLaw_probability` instances after deriving `[0,1]` bounds from the
interior assumptions; the probability instances supply the finite-measure
instances and equal total masses required by the Mathlib KL identity. Rewrite
the four-cell sum inside the covariate integral pointwise using strict
positivity of every parameter and its complement.
-/
theorem selectedLaw_klDiv_toReal_eq_integral {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (e q₀ q₁ q₀' q₁' : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (hq₀' : Measurable q₀') (hq₁' : Measurable q₁')
    {η : ℝ} (hη0 : 0 < η)
    (heη : ∀ x, e x ∈ Set.Icc η (1 - η))
    (hq₀η : ∀ x, q₀ x ∈ Set.Icc η (1 - η))
    (hq₁η : ∀ x, q₁ x ∈ Set.Icc η (1 - η))
    (hq₀'η : ∀ x, q₀' x ∈ Set.Icc η (1 - η))
    (hq₁'η : ∀ x, q₁' x ∈ Set.Icc η (1 - η)) :
    (InformationTheory.klDiv (selectedLaw μ e q₀ q₁)
      (selectedLaw μ e q₀' q₁')).toReal =
      ∫ x, (1 - e x) * bernoulliKL (q₀ x) (q₀' x) +
        e x * bernoulliKL (q₁ x) (q₁' x) ∂μ := by
  have h01 (p : X → ℝ) (hp : ∀ x, p x ∈ Set.Icc η (1 - η))
      (x : X) : p x ∈ Set.Icc (0 : ℝ) 1 := by
    rcases hp x with ⟨hl, hu⟩
    constructor <;> linarith
  letI : IsProbabilityMeasure (selectedLaw μ e q₀ q₁) :=
    selectedLaw_probability μ e q₀ q₁ he hq₀ hq₁
      (h01 e heη) (h01 q₀ hq₀η) (h01 q₁ hq₁η)
  letI : IsProbabilityMeasure (selectedLaw μ e q₀' q₁') :=
    selectedLaw_probability μ e q₀' q₁' he hq₀' hq₁'
      (h01 e heη) (h01 q₀' hq₀'η) (h01 q₁' hq₁'η)
  have hac := selectedLaw_ac μ e q₀ q₁ q₀' q₁' he hq₀ hq₁ hq₀' hq₁'
    hη0 heη hq₀'η hq₁'η
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac (by simp),
    integral_congr_ae (selectedLaw_llr_ae_eq_cell_log μ e q₀ q₁ q₀' q₁'
      he hq₀ hq₁ hq₀' hq₁' hη0 heη hq₀'η hq₁'η),
    selectedLaw_integral_cell_log_eq_sum μ e q₀ q₁ q₀' q₁'
      he hq₀ hq₁ hq₀' hq₁' hη0 heη hq₀η hq₁η hq₀'η hq₁'η]
  congr 1
  funext x
  have hpos (p : ℝ) (hp : p ∈ Set.Icc η (1 - η)) :
      0 < p ∧ p < 1 := by
    rcases hp with ⟨hl, hu⟩
    constructor <;> linarith
  exact sum_cellMass_mul_log_ratio_eq_weighted_bernoulliKL
    (hpos (e x) (heη x)).1 (hpos (e x) (heη x)).2

end Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL
