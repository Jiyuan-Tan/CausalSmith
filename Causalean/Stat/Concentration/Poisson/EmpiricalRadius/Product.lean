module
public import Causalean.Stat.Concentration.Poisson.EmpiricalRadius
public import Causalean.Stat.Concentration.Poisson.SelfNormalized.Product

/-!
# Product empirical-radius Poisson moments

This module compares count-dependent empirical Poisson radii with self-normalized raw scores and
transfers the finite independent-product bad-event moment bound to four coordinates.
-/

@[expose] public section

open Causalean.Stat.Concentration.Poisson
open Causalean.Stat.Concentration.PoissonSelfNormalized
open scoped NNReal

namespace Causalean.Stat.Concentration.Poisson.EmpiricalRadius

private theorem scalar_normalizedDeviation_eq_div
    (m q : ℝ≥0) (hm : 0 < m) (w : ℕ) :
    normalizedDeviation m q w = deviation (m * q) w / (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := NNReal.coe_pos.mpr hm
  unfold normalizedDeviation deviation
  calc
    |(w : ℝ) / (m : ℝ) - (q : ℝ)| =
        |((w : ℝ) - (m : ℝ) * (q : ℝ)) / (m : ℝ)| := by
      congr 1
      field_simp
    _ = |(w : ℝ) - (m : ℝ) * (q : ℝ)| / |(m : ℝ)| := abs_div _ _
    _ = |(w : ℝ) - ((m * q : ℝ≥0) : ℝ)| / (m : ℝ) := by
      rw [NNReal.coe_mul, abs_of_pos hmR]

private theorem scalar_normalizedRadius_eq_div
    (m : ℝ≥0) (hm : 0 < m) (L : ℝ) (w : ℕ) :
    normalizedRadius m L w = radius L w / (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := NNReal.coe_pos.mpr hm
  unfold normalizedRadius radius
  have harg : ((w : ℝ) / (m : ℝ)) * (L / (m : ℝ)) =
      ((w : ℝ) * L) / ((m : ℝ) ^ 2) := by field_simp
  rw [harg]
  by_cases hx : 0 ≤ (w : ℝ) * L
  · rw [Real.sqrt_div hx, Real.sqrt_sq_eq_abs, abs_of_pos hmR]
    ring
  · have hx' : (w : ℝ) * L ≤ 0 := le_of_not_ge hx
    have hdiv : (w : ℝ) * L / (m : ℝ) ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hx' (sq_nonneg _)
    rw [Real.sqrt_eq_zero_of_nonpos hdiv, Real.sqrt_eq_zero_of_nonpos hx']
    ring

/-- For [a positive exposure](hyp:m,hm), [an intensity](hyp:q), [a multiplier and level](hyp:H,L)
with [the standard lower bounds](hyp:hH,hL), [every empirical-radius bad count belongs to the
universal raw-score bad event](goal). -/
-- Rewrite normalized deviation and empirical radius as the corresponding raw
-- quantities divided by m; compare thresholds using H ≥ universalH.
theorem empiricalRadius_bad_subset_raw (q m : ℝ≥0) (hm : 0 < m)
    (H L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L) :
    {w : ℕ | normalizedDeviation m q w >
      empiricalRadius H m (L / (m : ℝ)) w / 4} ⊆
      badEvent universalH L (m * q) := by
  intro w hw
  have hmR : 0 < (m : ℝ) := NNReal.coe_pos.mpr hm
  have hr : 0 ≤ radius L w := by
    unfold radius
    positivity
  change normalizedDeviation m q w >
    empiricalRadius H m (L / (m : ℝ)) w / 4 at hw
  rw [scalar_normalizedDeviation_eq_div m q hm,
    empiricalRadius_eq_normalizedRadius,
    scalar_normalizedRadius_eq_div m hm] at hw
  change deviation (m * q) w > (universalH / 4) * radius L w
  have hthreshold : (universalH / 4) * radius L w ≤
      H * (radius L w / (m : ℝ)) / 4 * (m : ℝ) := by
    rw [show H * (radius L w / (m : ℝ)) / 4 * (m : ℝ) =
      (H / 4) * radius L w by field_simp]
    exact mul_le_mul_of_nonneg_right (by linarith : universalH / 4 ≤ H / 4) hr
  have := (lt_div_iff₀ hmR).mp hw
  exact lt_of_le_of_lt hthreshold this

/-- For [a positive exposure](hyp:m,hm), [an intensity](hyp:q), [a multiplier and level](hyp:H,L)
with [the standard lower bounds](hyp:hH,hL), [each empirical deviation-plus-radius score is
at most the scaled universal raw score](goal). -/
-- Use the same normalized/raw identities as the subset lemma, then the
-- nonnegativity of the raw deviation and H/universalH ≥ 1.
theorem empiricalRadius_score_le_raw (q m : ℝ≥0) (hm : 0 < m)
    (H L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L) (w : ℕ) :
    normalizedDeviation m q w + empiricalRadius H m (L / (m : ℝ)) w ≤
      (H / universalH) * (score universalH L (m * q) w / (m : ℝ)) := by
  have hmR : 0 < (m : ℝ) := NNReal.coe_pos.mpr hm
  have hu : 0 < universalH := universalH_pos
  have hd : 0 ≤ deviation (m * q) w := by simp [deviation]
  have hr : 0 ≤ radius L w := by unfold radius; positivity
  rw [scalar_normalizedDeviation_eq_div m q hm,
    empiricalRadius_eq_normalizedRadius,
    scalar_normalizedRadius_eq_div m hm]
  unfold score
  have hc : 1 ≤ H / universalH := (le_div_iff₀ hu).2 (by simpa using hH)
  have hdev : deviation (m * q) w ≤
      (H / universalH) * deviation (m * q) w := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) hd]
  have hid : (H / universalH) *
      (deviation (m * q) w + universalH * radius L w) =
      (H / universalH) * deviation (m * q) w + H * radius L w := by
    field_simp
  calc
    deviation (m * q) w / (m : ℝ) + H * (radius L w / (m : ℝ)) =
        (deviation (m * q) w + H * radius L w) / (m : ℝ) := by ring
    _ ≤ ((H / universalH) *
        (deviation (m * q) w + universalH * radius L w)) / (m : ℝ) := by
      apply (div_le_div_iff_of_pos_right hmR).2
      rw [hid]
      linarith
    _ = _ := by ring

/-- For [an intensity and positive exposure](hyp:q,m,hm) and [a level of at least one](hyp:L,hL),
[the raw local scale divided by exposure equals the normalized local scale](goal). -/
-- Rewrite sqrt ((m*q)*L)/m using sqrt_div and sqrt (m²) = m.
theorem empiricalRadius_localScale_div (q m : ℝ≥0) (hm : 0 < m)
    (L : ℝ) (hL : 1 ≤ L) :
    localScale (m * q) L / (m : ℝ) =
      Real.sqrt ((q : ℝ) * L / (m : ℝ)) + L / (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := NNReal.coe_pos.mpr hm
  have hsqrt :
      Real.sqrt (((m : ℝ) * (q : ℝ)) * L) / (m : ℝ) =
        Real.sqrt (((q : ℝ) * L) / (m : ℝ)) := by
    symm
    calc
      Real.sqrt (((q : ℝ) * L) / (m : ℝ)) =
          Real.sqrt ((((m : ℝ) * (q : ℝ)) * L) / ((m : ℝ) ^ 2)) := by
        congr 1
        field_simp
      _ = Real.sqrt (((m : ℝ) * (q : ℝ)) * L) /
          Real.sqrt ((m : ℝ) ^ 2) := by
            rw [Real.sqrt_div]
            positivity
      _ = Real.sqrt (((m : ℝ) * (q : ℝ)) * L) / (m : ℝ) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hmR]
  unfold localScale
  rw [NNReal.coe_mul, add_div, hsqrt]

end Causalean.Stat.Concentration.Poisson.EmpiricalRadius
open Causalean.Stat.Concentration.Poisson
open Causalean.Stat.Concentration.PoissonSelfNormalized
open scoped NNReal BigOperators

namespace Causalean.Stat.Concentration.Poisson.EmpiricalRadius

/-- For [finite count coordinates](hyp:ι,Ω,W), [an exposure and intensities](hyp:m,q), and
[a multiplier and level](hyp:H,L), [the empirical bad union](goal) contains precisely the
outcomes where some normalized deviation exceeds one quarter of its empirical radius. -/
def empiricalBadAny {ι Ω : Type*} [Fintype ι] (W : ι → Ω → ℕ)
    (H L : ℝ) (m : ℝ≥0) (q : ι → ℝ≥0) : Set Ω :=
  {ω | ∃ i, normalizedDeviation m (q i) (W i ω) >
    empiricalRadius H m (L / (m : ℝ)) (W i ω) / 4}

/-- For [finite count coordinates](hyp:ι,Ω,W), [an exposure and intensities](hyp:m,q),
[a multiplier and level](hyp:H,L), and [an outcome](hyp:ω), [the empirical aggregate score](goal)
sums each coordinate's normalized deviation and count-dependent radius. -/
noncomputable def empiricalAggregateScore {ι Ω : Type*} [Fintype ι]
    (W : ι → Ω → ℕ) (H L : ℝ) (m : ℝ≥0) (q : ι → ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, (normalizedDeviation m (q i) (W i ω) +
    empiricalRadius H m (L / (m : ℝ)) (W i ω))

/-- For [finite count coordinates](hyp:ι,Ω,W), [positive exposure](hyp:m,hm),
[intensities](hyp:q), and [a multiplier and level with their lower bounds](hyp:H,L,hH,hL),
[the empirical bad union is contained in the universal raw-score bad union](goal). -/
-- Unpack the witnessing coordinate and apply empiricalRadius_bad_subset_raw.
theorem empiricalBadAny_subset_raw {ι Ω : Type*} [Fintype ι]
    (W : ι → Ω → ℕ) (q : ι → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (H L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L) :
    empiricalBadAny W H L m q ⊆
      badAny W universalH L (fun i => m * q i) := by
  intro ω hω
  obtain ⟨i, hi⟩ := hω
  exact ⟨i, empiricalRadius_bad_subset_raw (q i) m hm H L hH hL hi⟩

/-- For [finite count coordinates](hyp:ι,Ω,W), [positive exposure](hyp:m,hm),
[intensities](hyp:q), and [a multiplier and level with their lower bounds](hyp:H,L,hH,hL),
[the empirical aggregate score is bounded by the scaled universal raw aggregate score](goal)
at [every outcome](hyp:ω). -/
-- Sum empiricalRadius_score_le_raw over coordinates and use Finset.sum_div.
theorem empiricalAggregateScore_le_raw {ι Ω : Type*} [Fintype ι]
    (W : ι → Ω → ℕ) (q : ι → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (H L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L) (ω : Ω) :
    empiricalAggregateScore W H L m q ω ≤
      (H / universalH) *
        (aggregateScore W universalH L (fun i => m * q i) ω / (m : ℝ)) := by
  unfold empiricalAggregateScore aggregateScore
  calc
    (∑ i, (normalizedDeviation m (q i) (W i ω) +
      empiricalRadius H m (L / (m : ℝ)) (W i ω))) ≤
        ∑ i, (H / universalH) *
          (score universalH L (m * q i) (W i ω) / (m : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact empiricalRadius_score_le_raw (q i) m hm H L hH hL (W i ω)
    _ = (H / universalH) *
        ((∑ i, score universalH L (m * q i) (W i ω)) / (m : ℝ)) := by
      rw [← Finset.mul_sum, Finset.sum_div]

/-- For [finite intensities](hyp:ι,q), [positive exposure](hyp:m,hm), and
[a level of at least one](hyp:L,hL), [the total raw local scale divided by exposure
equals the normalized scale of the total intensity](goal). -/
-- Convert the NNReal sum of m*q_i to m times the NNReal sum q_i, apply
-- empiricalRadius_localScale_div, and rewrite the cast of the sum.
theorem empiricalRadius_totalLocalScale_div {ι : Type*} [Fintype ι]
    (q : ι → ℝ≥0) (m : ℝ≥0) (hm : 0 < m) (L : ℝ) (hL : 1 ≤ L) :
    localScale (∑ i, m * q i) L / (m : ℝ) =
      Real.sqrt ((∑ i, (q i : ℝ)) * L / (m : ℝ)) + L / (m : ℝ) := by
  have hsum : (∑ i, m * q i) = m * (∑ i, q i) := by
    rw [Finset.mul_sum]
  rw [hsum, empiricalRadius_localScale_div (∑ i, q i) m hm L hL,
    NNReal.coe_sum]

end Causalean.Stat.Concentration.Poisson.EmpiricalRadius
open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.Poisson
open Causalean.Stat.Concentration.PoissonSelfNormalized
open scoped NNReal BigOperators

namespace Causalean.Stat.Concentration.Poisson.EmpiricalRadius

/-- Under [a probability law](hyp:μ), [four measurable Poisson counts](hyp:W,hWmeas,hWlaw)
with [intensities and positive exposure](hyp:q,m,hm) and [mutual independence](hyp:hWindep),
for [moment order one, two, or four](hyp:t,ht) and [a multiplier and level above their
universal thresholds](hyp:H,L,hH,hL), [the empirical aggregate score moment on the union of
empirical-radius bad events obeys the explicit exponentially decaying product bound](goal). -/
-- Apply empiricalBadAny_subset_raw and empiricalAggregateScore_le_raw
-- pointwise. Use the integrability of the universal raw indicator score
-- (from the product theorem's supporting lemmas), integral_mono_of_nonneg,
-- and independent_poisson_badAny_moment_four; pull out
-- (H/universalH)^t/m^t and use empiricalRadius_totalLocalScale_div.
theorem independent_poisson_empiricalRadius_badAny_moment_four
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (hWmeas : ∀ i, Measurable (W i))
    (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (m * q i)) μ)
    (hWindep : iIndepFun W μ)
    {t : ℕ} (ht : t = 1 ∨ t = 2 ∨ t = 4)
    (H L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L) :
    ∫ ω, (empiricalBadAny W H L m q).indicator
        (fun ω => (empiricalAggregateScore W H L m q ω) ^ t) ω ∂μ ≤
      (H / universalH) ^ t * productMomentConstant 4 t * Real.exp (-20 * L) *
        (Real.sqrt ((∑ i, (q i : ℝ)) * L / (m : ℝ)) + L / (m : ℝ)) ^ t := by
  classical
  let lambda : Fin 4 → ℝ≥0 := fun i => m * q i
  let c : ℝ := H / universalH
  have ht4 : t ≤ 4 := by rcases ht with rfl | rfl | rfl <;> norm_num
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (le_trans universalH_pos.le hH) universalH_pos.le
  have hmR : 0 < (m : ℝ) := NNReal.coe_pos.mpr hm
  have hscoreInt (i : Fin 4) :
      Integrable (fun ω => (score universalH L (lambda i) (W i ω)) ^ t) μ := by
    have h := integrable_score_pow (lambda i) hL ht4
    have hmap : μ.map (W i) = poissonMeasure (lambda i) := (hWlaw i).map_eq
    rw [← hmap] at h
    exact h.comp_aemeasurable (hWlaw i).aemeasurable
  have hdomInt : Integrable
      (fun ω => (4 : ℝ) ^ (t - 1) *
        ∑ i, (score universalH L (lambda i) (W i ω)) ^ t) μ := by
    exact (integrable_finsetSum _ fun i _ => hscoreInt i).const_mul _
  have hscore0 (i : Fin 4) (ω : Ω) :
      0 ≤ score universalH L (lambda i) (W i ω) := by
    unfold score deviation radius
    exact add_nonneg (abs_nonneg _) (mul_nonneg universalH_pos.le (by positivity))
  have hraw0 (ω : Ω) : 0 ≤
      (badAny W universalH L lambda).indicator
        (fun ω => (aggregateScore W universalH L lambda ω) ^ t) ω := by
    by_cases hb : ω ∈ badAny W universalH L lambda
    · rw [Set.indicator_of_mem hb]
      apply pow_nonneg
      unfold aggregateScore
      exact Finset.sum_nonneg fun i _ => hscore0 i ω
    · simp [hb]
  have hrawDom (ω : Ω) :
      (badAny W universalH L lambda).indicator
        (fun ω => (aggregateScore W universalH L lambda ω) ^ t) ω ≤
      (4 : ℝ) ^ (t - 1) *
        ∑ i, (score universalH L (lambda i) (W i ω)) ^ t := by
    have hpow : (aggregateScore W universalH L lambda ω) ^ t ≤
        (4 : ℝ) ^ (t - 1) *
          ∑ i, (score universalH L (lambda i) (W i ω)) ^ t := by
      unfold aggregateScore
      rcases ht with rfl | rfl | rfl
      · simp
      · simpa using (pow_sum_le_card_mul_sum_pow
          (s := (Finset.univ : Finset (Fin 4)))
          (f := fun i => score universalH L (lambda i) (W i ω))
          (fun i _ => hscore0 i ω) 1)
      · simpa using (pow_sum_le_card_mul_sum_pow
          (s := (Finset.univ : Finset (Fin 4)))
          (f := fun i => score universalH L (lambda i) (W i ω))
          (fun i _ => hscore0 i ω) 3)
    by_cases hb : ω ∈ badAny W universalH L lambda
    · simpa [hb] using hpow
    · rw [Set.indicator_of_notMem hb]
      exact mul_nonneg (pow_nonneg (by norm_num) _) (Finset.sum_nonneg fun i _ =>
        pow_nonneg (hscore0 i ω) _)
  have hrawMeas : Measurable
      (fun ω => (badAny W universalH L lambda).indicator
        (fun ω => (aggregateScore W universalH L lambda ω) ^ t) ω) := by
    unfold badAny aggregateScore score deviation radius
    measurability
  have hrawInt : Integrable
      (fun ω => (badAny W universalH L lambda).indicator
        (fun ω => (aggregateScore W universalH L lambda ω) ^ t) ω) μ := by
    exact integrable_of_le_of_le hrawMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => hraw0 ω)
      (Filter.Eventually.of_forall fun ω => hrawDom ω)
      (integrable_zero _ _ _) hdomInt
  have hemp0 (ω : Ω) : 0 ≤ empiricalAggregateScore W H L m q ω := by
    unfold empiricalAggregateScore
    apply Finset.sum_nonneg
    intro i _
    have hd : 0 ≤ normalizedDeviation m (q i) (W i ω) := by
      unfold normalizedDeviation
      positivity
    have hr : 0 ≤ empiricalRadius H m (L / (m : ℝ)) (W i ω) := by
      rw [empiricalRadius_eq_normalizedRadius]
      unfold normalizedRadius
      have hH0 : 0 ≤ H := le_trans universalH_pos.le hH
      positivity
    positivity
  have hpoint (ω : Ω) :
      (empiricalBadAny W H L m q).indicator
          (fun ω => (empiricalAggregateScore W H L m q ω) ^ t) ω ≤
        (c / (m : ℝ)) ^ t * (badAny W universalH L lambda).indicator
          (fun ω => (aggregateScore W universalH L lambda ω) ^ t) ω := by
    by_cases hb : ω ∈ empiricalBadAny W H L m q
    · have hrb : ω ∈ badAny W universalH L lambda :=
        empiricalBadAny_subset_raw W q m hm H L hH hL hb
      simp only [Set.indicator_of_mem hb, Set.indicator_of_mem hrb]
      calc
        (empiricalAggregateScore W H L m q ω) ^ t ≤
            (c * (aggregateScore W universalH L lambda ω / (m : ℝ))) ^ t :=
          pow_le_pow_left₀ (hemp0 ω)
            (empiricalAggregateScore_le_raw W q m hm H L hH hL ω) t
        _ = (c / (m : ℝ)) ^ t * (aggregateScore W universalH L lambda ω) ^ t := by
          have heq : c * (aggregateScore W universalH L lambda ω / (m : ℝ)) =
              (c / (m : ℝ)) * aggregateScore W universalH L lambda ω := by ring
          rw [heq, mul_pow]
    · rw [Set.indicator_of_notMem hb]
      exact mul_nonneg (pow_nonneg (div_nonneg hc hmR.le) _) (hraw0 ω)
  have hempIndicator0 : 0 ≤ᵐ[μ] fun ω =>
      (empiricalBadAny W H L m q).indicator
        (fun ω => (empiricalAggregateScore W H L m q ω) ^ t) ω := by
    filter_upwards [] with ω
    by_cases hb : ω ∈ empiricalBadAny W H L m q
    · rw [Set.indicator_of_mem hb]
      exact pow_nonneg (hemp0 ω) _
    · simp [hb]
  have hmono :
      ∫ ω, (empiricalBadAny W H L m q).indicator
          (fun ω => (empiricalAggregateScore W H L m q ω) ^ t) ω ∂μ ≤
        (c / (m : ℝ)) ^ t *
          ∫ ω, (badAny W universalH L lambda).indicator
            (fun ω => (aggregateScore W universalH L lambda ω) ^ t) ω ∂μ := by
    calc
      _ ≤ ∫ ω, (c / (m : ℝ)) ^ t *
          (badAny W universalH L lambda).indicator
            (fun ω => (aggregateScore W universalH L lambda ω) ^ t) ω ∂μ := by
        apply integral_mono_of_nonneg hempIndicator0
          (hrawInt.const_mul _)
        exact Filter.Eventually.of_forall hpoint
      _ = _ := integral_const_mul _ _
  have hprod := independent_poisson_badAny_moment_four μ W lambda hWmeas
    (by simpa [lambda] using hWlaw) hWindep ht hL
  have hscale :
      (Real.sqrt ((∑ i, (lambda i : ℝ)) * L) + L) / (m : ℝ) =
        Real.sqrt ((∑ i, (q i : ℝ)) * L / (m : ℝ)) + L / (m : ℝ) := by
    change localScale (∑ i, m * q i) L / (m : ℝ) = _
    exact empiricalRadius_totalLocalScale_div q m hm L hL
  calc
    ∫ ω, (empiricalBadAny W H L m q).indicator
        (fun ω => (empiricalAggregateScore W H L m q ω) ^ t) ω ∂μ ≤
      (c / (m : ℝ)) ^ t *
        ∫ ω, (badAny W universalH L lambda).indicator
          (fun ω => (aggregateScore W universalH L lambda ω) ^ t) ω ∂μ := hmono
    _ ≤ (c / (m : ℝ)) ^ t *
        (productMomentConstant 4 t * Real.exp (-20 * L) *
          (Real.sqrt ((∑ i, (lambda i : ℝ)) * L) + L) ^ t) := by
        exact mul_le_mul_of_nonneg_left hprod
          (pow_nonneg (div_nonneg hc hmR.le) _)
    _ = (H / universalH) ^ t * productMomentConstant 4 t * Real.exp (-20 * L) *
        (Real.sqrt ((∑ i, (q i : ℝ)) * L / (m : ℝ)) + L / (m : ℝ)) ^ t := by
      rw [← hscale]
      dsimp [c]
      simp only [div_pow]
      ring

end Causalean.Stat.Concentration.Poisson.EmpiricalRadius
