import Causalean.Stat.Concentration.PoissonSelfNormalized.Product

/-!
# Normalized finite-product Poisson bounds

This module divides counts with means `m q_i` by a positive exposure `m`.
The resulting bound retains the local normalized scale
`sqrt ((sum_i q_i) L / m) + L / m`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal BigOperators

namespace Causalean.Stat.Concentration.PoissonSelfNormalized

/-- Given [a nonnegative exposure](hyp:m), [a nonnegative intensity](hyp:q), and [a natural-valued
count](hyp:w), the [normalized deviation](goal) is the absolute difference between count divided by
exposure and intensity. -/
noncomputable def normalizedDeviation (m : ℝ≥0) (q : ℝ≥0) (w : ℕ) : ℝ :=
  |(w : ℝ) / (m : ℝ) - (q : ℝ)|

/-- Given [a nonnegative exposure](hyp:m), [a logarithmic level](hyp:L), and [a natural-valued
count](hyp:w), the [normalized self-normalizing radius](goal) is the square root of normalized count
times normalized level, plus normalized level. -/
noncomputable def normalizedRadius (m : ℝ≥0) (L : ℝ) (w : ℕ) : ℝ :=
  Real.sqrt (((w : ℝ) / (m : ℝ)) * (L / (m : ℝ))) + L / (m : ℝ)

/-- Given [a finite coordinate index and sample space](hyp:ι,Ω), [natural-valued coordinate
counts](hyp:W), [a multiplier and logarithmic level](hyp:H,L), [a nonnegative exposure](hyp:m), and
[nonnegative coordinate intensities](hyp:q), the [normalized aggregate bad event](goal) occurs when
at least one coordinate exceeds its normalized self-normalized threshold. -/
def normalizedBadAny {ι Ω : Type*} [Fintype ι] (W : ι → Ω → ℕ)
    (H L : ℝ) (m : ℝ≥0) (q : ι → ℝ≥0) : Set Ω :=
  {ω | ∃ i, normalizedDeviation m (q i) (W i ω) >
    (H / 4) * normalizedRadius m L (W i ω)}

/-- Given [a finite coordinate index and sample space](hyp:ι,Ω), [natural-valued coordinate
counts](hyp:W), [a multiplier and logarithmic level](hyp:H,L), [a nonnegative exposure](hyp:m),
[nonnegative coordinate intensities](hyp:q), and [a sample point](hyp:ω), the [normalized aggregate
score](goal) sums the normalized deviation-plus-radius scores across coordinates. -/
noncomputable def normalizedAggregateScore {ι Ω : Type*} [Fintype ι]
    (W : ι → Ω → ℕ) (H L : ℝ) (m : ℝ≥0) (q : ι → ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, (normalizedDeviation m (q i) (W i ω) +
    H * normalizedRadius m L (W i ω))

private theorem normalizedDeviation_eq_div
    (m q : ℝ≥0) (hm : 0 < m) (w : ℕ) :
    normalizedDeviation m q w = deviation (m * q) w / (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := NNReal.coe_pos.mpr hm
  unfold normalizedDeviation deviation
  calc
    |(w : ℝ) / (m : ℝ) - (q : ℝ)| =
        |((w : ℝ) - ((m : ℝ) * (q : ℝ))) / (m : ℝ)| := by
      congr 1
      field_simp
    _ = |(w : ℝ) - ((m : ℝ) * (q : ℝ))| / |(m : ℝ)| := abs_div _ _
    _ = |(w : ℝ) - ((m * q : ℝ≥0) : ℝ)| / (m : ℝ) := by
      rw [NNReal.coe_mul, abs_of_pos hmR]

private theorem normalizedRadius_eq_div
    (m : ℝ≥0) (hm : 0 < m) (L : ℝ) (w : ℕ) :
    normalizedRadius m L w = radius L w / (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := NNReal.coe_pos.mpr hm
  unfold normalizedRadius radius
  have harg :
      ((w : ℝ) / (m : ℝ)) * (L / (m : ℝ)) =
        ((w : ℝ) * L) / ((m : ℝ) ^ 2) := by
    field_simp
  rw [harg]
  by_cases hx : 0 ≤ (w : ℝ) * L
  · rw [Real.sqrt_div hx, Real.sqrt_sq_eq_abs, abs_of_pos hmR]
    ring
  · have hx' : (w : ℝ) * L ≤ 0 := le_of_not_ge hx
    have hdiv : (w : ℝ) * L / (m : ℝ) ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hx' (sq_nonneg _)
    rw [Real.sqrt_eq_zero_of_nonpos hdiv, Real.sqrt_eq_zero_of_nonpos hx']
    ring

/-- On [a measurable sample space with a finite coordinate index](hyp:Ω,ι), let [a probability
law](hyp:μ) carry [natural-valued coordinate counts](hyp:W) with [nonnegative coordinate
intensities](hyp:q) and [a strictly positive exposure](hyp:m,hm). If [the counts are
measurable](hyp:hWmeas), [each count is Poisson with mean exposure times intensity](hyp:hWlaw), and
[the counts are mutually independent](hyp:hWindep), then under [a fixed coordinate-cardinality
cap](hyp:r,hcard), for [moment order one, two, or four](hyp:t,ht) and [a logarithmic level of at
least one](hyp:L,hL), [the normalized aggregate score moment on the union of bad coordinates
decays exponentially at the local scale determined by total intensity and exposure](goal). -/
-- Proof route after `Product` is closed: for `m > 0`, prove pointwise
-- `normalizedDeviation m q w = deviation (m*q) w / m` and
-- `normalizedRadius m L w = radius L w / m` (use `Real.sqrt_div` and
-- `Real.sqrt_sq_eq_abs`).  Hence the normalized bad set is the unnormalized
-- bad set at mean `m*q`, and the aggregate score is the corresponding score
-- divided by `m`.  Apply `independent_poisson_badAny_moment`, pull the positive
-- constant `m^(-t)` through the indicator and integral, rewrite
-- `sum_i (m*q_i)` as `m * sum_i q_i`, and identify the divided local scale
-- with `sqrt (((sum_i q_i) * L) / m) + L/m`.
theorem independent_poisson_normalized_badAny_moment
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : ι → Ω → ℕ) (q : ι → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (hWmeas : ∀ i, Measurable (W i))
    (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (m * q i)) μ)
    (hWindep : iIndepFun W μ)
    {r t : ℕ} (hcard : Fintype.card ι ≤ r)
    (ht : t = 1 ∨ t = 2 ∨ t = 4) {L : ℝ} (hL : 1 ≤ L) :
    ∫ ω, (normalizedBadAny W universalH L m q).indicator
        (fun ω => (normalizedAggregateScore W universalH L m q ω) ^ t) ω ∂μ ≤
      productMomentConstant r t * Real.exp (-20 * L) *
        (Real.sqrt (((∑ i, (q i : ℝ)) * L) / (m : ℝ)) +
          L / (m : ℝ)) ^ t := by
  classical
  have hmR : 0 < (m : ℝ) := NNReal.coe_pos.mpr hm
  let lambda : ι → ℝ≥0 := fun i => m * q i
  have hbad : normalizedBadAny W universalH L m q =
      badAny W universalH L lambda := by
    ext ω
    simp only [normalizedBadAny, badAny, Set.mem_ofPred_eq]
    apply exists_congr
    intro i
    rw [normalizedDeviation_eq_div m (q i) hm, normalizedRadius_eq_div m hm]
    change deviation (lambda i) (W i ω) / (m : ℝ) >
      (universalH / 4) * (radius L (W i ω) / (m : ℝ)) ↔ _
    rw [show (universalH / 4) * (radius L (W i ω) / (m : ℝ)) =
      ((universalH / 4) * radius L (W i ω)) / (m : ℝ) by ring]
    exact div_lt_div_iff_of_pos_right hmR
  have hagg (ω : Ω) : normalizedAggregateScore W universalH L m q ω =
      aggregateScore W universalH L lambda ω / (m : ℝ) := by
    unfold normalizedAggregateScore aggregateScore
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [normalizedDeviation_eq_div m (q i) hm, normalizedRadius_eq_div m hm]
    change deviation (lambda i) (W i ω) / (m : ℝ) +
      universalH * (radius L (W i ω) / (m : ℝ)) =
      score universalH L (lambda i) (W i ω) / (m : ℝ)
    unfold score
    ring
  have hind (ω : Ω) :
      (badAny W universalH L lambda).indicator
          (fun ω => (normalizedAggregateScore W universalH L m q ω) ^ t) ω =
        (badAny W universalH L lambda).indicator
          (fun ω => (aggregateScore W universalH L lambda ω) ^ t) ω /
            (m : ℝ) ^ t := by
    by_cases hω : ω ∈ badAny W universalH L lambda <;>
      simp [hω, hagg, div_pow]
  have hlhs :
      (∫ ω, (normalizedBadAny W universalH L m q).indicator
          (fun ω => (normalizedAggregateScore W universalH L m q ω) ^ t) ω ∂μ) =
        (∫ ω, (badAny W universalH L lambda).indicator
          (fun ω => (aggregateScore W universalH L lambda ω) ^ t) ω ∂μ) /
            (m : ℝ) ^ t := by
    rw [hbad, ← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall hind)
  have hprod := independent_poisson_badAny_moment μ W lambda hWmeas
    (by simpa [lambda] using hWlaw) hWindep hcard ht hL
  have hdiv := (div_le_div_iff_of_pos_right (pow_pos hmR t)).2 hprod
  rw [hlhs]
  calc
    (∫ ω, (badAny W universalH L lambda).indicator
        (fun ω => (aggregateScore W universalH L lambda ω) ^ t) ω ∂μ) /
          (m : ℝ) ^ t ≤
      (productMomentConstant r t * Real.exp (-20 * L) *
        (Real.sqrt ((∑ i, (lambda i : ℝ)) * L) + L) ^ t) /
          (m : ℝ) ^ t := hdiv
    _ = productMomentConstant r t * Real.exp (-20 * L) *
        (Real.sqrt (((∑ i, (q i : ℝ)) * L) / (m : ℝ)) +
          L / (m : ℝ)) ^ t := by
      have hsum : ∑ i, (lambda i : ℝ) =
          (m : ℝ) * ∑ i, (q i : ℝ) := by
        simp [lambda, Finset.mul_sum]
      rw [hsum]
      have hq0 : 0 ≤ ∑ i, (q i : ℝ) :=
        Finset.sum_nonneg fun i _ => (q i).coe_nonneg
      have hL0 : 0 ≤ L := by linarith
      have hsqrt :
          Real.sqrt (((m : ℝ) * (∑ i, (q i : ℝ))) * L) / (m : ℝ) =
            Real.sqrt (((∑ i, (q i : ℝ)) * L) / (m : ℝ)) := by
        symm
        calc
          Real.sqrt (((∑ i, (q i : ℝ)) * L) / (m : ℝ)) =
              Real.sqrt ((((m : ℝ) * (∑ i, (q i : ℝ))) * L) /
                ((m : ℝ) ^ 2)) := by
            congr 1
            field_simp
          _ = Real.sqrt (((m : ℝ) * (∑ i, (q i : ℝ))) * L) /
              Real.sqrt ((m : ℝ) ^ 2) := by
            rw [Real.sqrt_div]
            positivity
          _ = Real.sqrt (((m : ℝ) * (∑ i, (q i : ℝ))) * L) / (m : ℝ) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_pos hmR]
      have hscale :
          (Real.sqrt (((m : ℝ) * (∑ i, (q i : ℝ))) * L) + L) / (m : ℝ) =
            Real.sqrt (((∑ i, (q i : ℝ)) * L) / (m : ℝ)) + L / (m : ℝ) := by
        rw [add_div, hsqrt]
      calc
        productMomentConstant r t * Real.exp (-20 * L) *
              (Real.sqrt (((m : ℝ) * ∑ i, (q i : ℝ)) * L) + L) ^ t /
              (m : ℝ) ^ t =
            productMomentConstant r t * Real.exp (-20 * L) *
              ((Real.sqrt (((m : ℝ) * ∑ i, (q i : ℝ)) * L) + L) /
                (m : ℝ)) ^ t := by rw [div_pow]; ring
        _ = _ := by rw [hscale]

/-- On [a measurable sample space](hyp:Ω), let [a probability law](hyp:μ) carry [four natural-valued
coordinate counts](hyp:W) with [nonnegative coordinate intensities](hyp:q) and [a strictly positive
exposure](hyp:m,hm). If [the counts are measurable](hyp:hWmeas), [each count is Poisson with mean
exposure times intensity](hyp:hWlaw), and [the counts are mutually independent](hyp:hWindep), then
for [moment order one, two, or four](hyp:t,ht) and [a logarithmic level of at least
one](hyp:L,hL), [the normalized four-coordinate bad-event moment has the corresponding
exponentially decaying local-scale bound](goal). -/
-- Apply the general normalized theorem with `r = 4`.
theorem independent_poisson_normalized_badAny_moment_four
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (hWmeas : ∀ i, Measurable (W i))
    (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (m * q i)) μ)
    (hWindep : iIndepFun W μ)
    {t : ℕ} (ht : t = 1 ∨ t = 2 ∨ t = 4) {L : ℝ} (hL : 1 ≤ L) :
    ∫ ω, (normalizedBadAny W universalH L m q).indicator
        (fun ω => (normalizedAggregateScore W universalH L m q ω) ^ t) ω ∂μ ≤
      productMomentConstant 4 t * Real.exp (-20 * L) *
        (Real.sqrt (((∑ i, (q i : ℝ)) * L) / (m : ℝ)) +
          L / (m : ℝ)) ^ t := by
  exact independent_poisson_normalized_badAny_moment μ W q m hm hWmeas hWlaw hWindep
    (r := 4) (by simp) ht hL

end Causalean.Stat.Concentration.PoissonSelfNormalized
