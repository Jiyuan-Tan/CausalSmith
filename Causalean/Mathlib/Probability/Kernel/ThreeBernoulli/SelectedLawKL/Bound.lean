module
public import Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL.ChainRule

/-!
# Quadratic KL control for selected Bernoulli laws

The conditional KL identity and scalar Bernoulli bounds give an integrated
quadratic control of changes in the two outcome means.
-/

public section

open MeasureTheory

noncomputable section

namespace Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL

open Causalean.Mathlib.Probability.Kernel.ThreeBernoulli

universe u

/-- [The real-valued KL divergence between two selected laws is at most the covariate
integral of the propensity-weighted squared changes in the two outcome means, each
divided by the squared interior margin](goal) (untreated change weighted by one minus
the propensity, treated change by the propensity) for a
[probability covariate law](hyp:μ),
[measurable parameters](hyp:he,hq₀,hq₁,hq₀',hq₁'), and
[uniform interior bounds](hyp:hη0,heη,hq₀η,hq₁η,hq₀'η,hq₁'η).

Apply the conditional KL identity and the scalar `η⁻²` Bernoulli bound
pointwise. The square-bound integrand is measurable and uniformly bounded,
so `Integrable.of_bound` applies. `integral_mono_of_nonneg` avoids a separate
integrability proof for the Bernoulli-KL integrand; its nonnegativity follows
from `Causalean.Mathlib.Probability.bernoulliLaw_klDiv_toReal` and
`ENNReal.toReal_nonneg` under the interior hypotheses.
-/
theorem selectedLaw_klDiv_toReal_le_integral_sq {X : Type u} [MeasurableSpace X]
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
      (selectedLaw μ e q₀' q₁')).toReal ≤
      ∫ x, (1 - e x) * ((q₀ x - q₀' x) ^ 2 / η ^ 2) +
        e x * ((q₁ x - q₁' x) ^ 2 / η ^ 2) ∂μ := by
  have hηsq : 0 < η ^ 2 := sq_pos_of_pos hη0
  have hbound (p q : X → ℝ) (hp : ∀ x, p x ∈ Set.Icc η (1 - η))
      (hq : ∀ x, q x ∈ Set.Icc η (1 - η)) (x : X) :
      0 ≤ (p x - q x) ^ 2 / η ^ 2 ∧
        (p x - q x) ^ 2 / η ^ 2 ≤ 1 / η ^ 2 := by
    have hdiff : -1 ≤ p x - q x ∧ p x - q x ≤ 1 := by
      rcases hp x with ⟨hpl, hpu⟩
      rcases hq x with ⟨hql, hqu⟩
      constructor <;> linarith
    constructor
    · positivity
    · apply (div_le_div_iff₀ hηsq hηsq).2
      have hs : (p x - q x) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (p x - q x)]
      simpa using mul_le_mul_of_nonneg_right hs hηsq.le
  have hmeas : Measurable (fun x =>
      (1 - e x) * ((q₀ x - q₀' x) ^ 2 / η ^ 2) +
        e x * ((q₁ x - q₁' x) ^ 2 / η ^ 2)) := by fun_prop
  have hint : Integrable (fun x =>
      (1 - e x) * ((q₀ x - q₀' x) ^ 2 / η ^ 2) +
        e x * ((q₁ x - q₁' x) ^ 2 / η ^ 2)) μ := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable (2 / η ^ 2)
    filter_upwards [] with x
    have he0 : 0 ≤ e x ∧ e x ≤ 1 := by
      rcases heη x with ⟨hl, hu⟩
      constructor <;> linarith
    have h₀ := hbound q₀ q₀' hq₀η hq₀'η x
    have h₁ := hbound q₁ q₁' hq₁η hq₁'η x
    have hA : (1 - e x) * ((q₀ x - q₀' x) ^ 2 / η ^ 2) ≤ 1 / η ^ 2 := by
      calc
        _ ≤ (1 - e x) * (1 / η ^ 2) :=
          mul_le_mul_of_nonneg_left h₀.2 (by linarith)
        _ ≤ 1 / η ^ 2 := by
          exact mul_le_of_le_one_left (by positivity) (by linarith)
    have hB : e x * ((q₁ x - q₁' x) ^ 2 / η ^ 2) ≤ 1 / η ^ 2 := by
      calc
        _ ≤ e x * (1 / η ^ 2) := mul_le_mul_of_nonneg_left h₁.2 he0.1
        _ ≤ 1 / η ^ 2 :=
          mul_le_of_le_one_left (by positivity) he0.2
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg
      (mul_nonneg (by linarith) h₀.1) (mul_nonneg he0.1 h₁.1))]
    calc
      _ ≤ 1 / η ^ 2 + 1 / η ^ 2 := add_le_add hA hB
      _ = 2 / η ^ 2 := by ring
  rw [selectedLaw_klDiv_toReal_eq_integral μ e q₀ q₁ q₀' q₁'
    he hq₀ hq₁ hq₀' hq₁' hη0 heη hq₀η hq₁η hq₀'η hq₁'η]
  apply integral_mono_of_nonneg
  · filter_upwards [] with x
    have hpos (p q : ℝ) (hp : p ∈ Set.Icc η (1 - η))
        (hq : q ∈ Set.Icc η (1 - η)) : 0 ≤ bernoulliKL p q := by
      unfold bernoulliKL
      rw [← Causalean.Mathlib.Probability.bernoulliLaw_klDiv_toReal
        (by linarith [hp.1]) (by linarith [hp.2])
        (by linarith [hq.1]) (by linarith [hq.2])]
      exact ENNReal.toReal_nonneg
    exact add_nonneg
      (mul_nonneg (by linarith [(heη x).2]) (hpos _ _ (hq₀η x) (hq₀'η x)))
      (mul_nonneg (by linarith [(heη x).1]) (hpos _ _ (hq₁η x) (hq₁'η x)))
  · exact hint
  · filter_upwards [] with x
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (bernoulliKL_le_inv_margin_sq hη0 (hq₀η x) (hq₀'η x))
        (by linarith [(heη x).2]))
      (mul_le_mul_of_nonneg_left
        (bernoulliKL_le_inv_margin_sq hη0 (hq₁η x) (hq₁'η x))
        (by linarith [(heη x).1]))

/-- [When only the treated outcome mean changes symmetrically, selected-law KL
is at most four times the propensity-weighted squared mean difference](goal)
for a [probability covariate law](hyp:μ), [measurable propensity, common untreated
mean, and displacement](hyp:he,hq₀,htm),
[uniform interior bounds](hyp:hη0,heη,hq₀η,hplusη,hminusη), and
[small displacement](hyp:ht).

The common untreated term in the conditional KL identity vanishes because
`bernoulliKL p p = 0` for interior `p`. Apply
`bernoulliKL_symmetric_le_four` to the treated term and integrate. The right
integrand is measurable and bounded; `integral_mono_of_nonneg` needs only its
integrability and nonnegativity of the conditional-KL integrand. This
specialization preserves the coefficient `4` even when the general margin
bound has a larger coefficient.
-/
theorem selectedLaw_klDiv_toReal_le_symmetric {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (e q₀ t : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (htm : Measurable t)
    {η : ℝ} (hη0 : 0 < η)
    (heη : ∀ x, e x ∈ Set.Icc η (1 - η))
    (hq₀η : ∀ x, q₀ x ∈ Set.Icc η (1 - η))
    (hplusη : ∀ x, 1 / 2 + t x ∈ Set.Icc η (1 - η))
    (hminusη : ∀ x, 1 / 2 - t x ∈ Set.Icc η (1 - η))
    (ht : ∀ x, |t x| ≤ 1 / 32) :
    (InformationTheory.klDiv (selectedLaw μ e q₀ (fun x => 1 / 2 + t x))
      (selectedLaw μ e q₀ (fun x => 1 / 2 - t x))).toReal ≤
      ∫ x, e x * (4 * ((1 / 2 + t x) - (1 / 2 - t x)) ^ 2) ∂μ := by
  have hmeas : Measurable (fun x =>
      e x * (4 * ((1 / 2 + t x) - (1 / 2 - t x)) ^ 2)) := by fun_prop
  have hint : Integrable (fun x =>
      e x * (4 * ((1 / 2 + t x) - (1 / 2 - t x)) ^ 2)) μ := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 4
    filter_upwards [] with x
    have he0 : 0 ≤ e x ∧ e x ≤ 1 := by
      rcases heη x with ⟨hl, hu⟩
      constructor <;> linarith
    have hd : -1 ≤ (1 / 2 + t x) - (1 / 2 - t x) ∧
        (1 / 2 + t x) - (1 / 2 - t x) ≤ 1 := by
      rcases hplusη x with ⟨hpl, hpu⟩
      rcases hminusη x with ⟨hml, hmu⟩
      constructor <;> linarith
    have hs : ((1 / 2 + t x) - (1 / 2 - t x)) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ((1 / 2 + t x) - (1 / 2 - t x))]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg he0.1 (mul_nonneg (by norm_num) (sq_nonneg _)))]
    calc
      _ ≤ e x * 4 := mul_le_mul_of_nonneg_left (by nlinarith) he0.1
      _ ≤ 4 := by nlinarith
  rw [selectedLaw_klDiv_toReal_eq_integral μ e q₀
    (fun x => 1 / 2 + t x) q₀ (fun x => 1 / 2 - t x)
    he hq₀ (by fun_prop) hq₀ (by fun_prop)
    hη0 heη hq₀η hplusη hq₀η hminusη]
  have hzero (x : X) : bernoulliKL (q₀ x) (q₀ x) = 0 := by
    have hp0 : q₀ x ≠ 0 := ne_of_gt (lt_of_lt_of_le hη0 (hq₀η x).1)
    have hp1 : 1 - q₀ x ≠ 0 := ne_of_gt (by linarith [(hq₀η x).2])
    simp [bernoulliKL, div_self hp0, div_self hp1]
  have hpos (x : X) :
      0 ≤ bernoulliKL (1 / 2 + t x) (1 / 2 - t x) := by
    unfold bernoulliKL
    rw [← Causalean.Mathlib.Probability.bernoulliLaw_klDiv_toReal
      (by linarith [(hplusη x).1]) (by linarith [(hplusη x).2])
      (by linarith [(hminusη x).1]) (by linarith [(hminusη x).2])]
    exact ENNReal.toReal_nonneg
  apply integral_mono_of_nonneg
  · filter_upwards [] with x
    rw [hzero x, mul_zero, zero_add]
    exact mul_nonneg (by linarith [(heη x).1]) (hpos x)
  · exact hint
  · filter_upwards [] with x
    rw [hzero x, mul_zero, zero_add]
    exact mul_le_mul_of_nonneg_left (bernoulliKL_symmetric_le_four (ht x))
      (by linarith [(heη x).1])

end Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL
