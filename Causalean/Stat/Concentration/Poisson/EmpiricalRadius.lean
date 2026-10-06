module
public import Causalean.Stat.Concentration.Poisson.SelfNormalized.Scaling

/-!
# Empirical Poisson radii and bad-event moments

These bounds use the count-dependent radius `H * (sqrt ((w/m) * δ) + δ)`.
The established self-normalized Poisson estimates provide exponential bad-event
probabilities and second/fourth moment envelopes, including zero intensity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open Causalean.Stat.Concentration.PoissonSelfNormalized

namespace Causalean.Stat.Concentration.Poisson

/-- [The empirical Poisson radius](goal) with [multiplier H](hyp:H),
[exposure m](hyp:m), [level δ](hyp:δ), and [observed count w](hyp:w) is [H
times the sum of √((w/m)·δ) and δ](step:1). -/
noncomputable def empiricalRadius (H : ℝ) (m : ℝ≥0) (δ : ℝ)
    (w : ℕ) : ℝ :=
  H * (Real.sqrt (((w : ℝ) / (m : ℝ)) * δ) + δ)

/-- [The empirical radius with multiplier H at level L/m equals H times the
normalized radius at level numerator L](goal), for every [nonnegative
exposure m](hyp:m) and count w. -/
theorem empiricalRadius_eq_normalizedRadius (H L : ℝ) (m : ℝ≥0)
    (w : ℕ) :
    empiricalRadius H m (L / (m : ℝ)) w =
      H * normalizedRadius m L w := by
  rfl

private theorem empirical_normalizedDeviation_eq_div
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

private theorem empirical_normalizedRadius_eq_div
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

private theorem empirical_bad_subset (q m : ℝ≥0) (hm : 0 < m)
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
  rw [empirical_normalizedDeviation_eq_div m q hm,
    empiricalRadius_eq_normalizedRadius,
    empirical_normalizedRadius_eq_div m hm] at hw
  change deviation (m * q) w > (universalH / 4) * radius L w
  have hthreshold : (universalH / 4) * radius L w ≤
      H * (radius L w / (m : ℝ)) / 4 * (m : ℝ) := by
    rw [show H * (radius L w / (m : ℝ)) / 4 * (m : ℝ) =
      (H / 4) * radius L w by field_simp]
    exact mul_le_mul_of_nonneg_right (by linarith : universalH / 4 ≤ H / 4) hr
  have := (lt_div_iff₀ hmR).mp hw
  exact lt_of_le_of_lt hthreshold this

/-- For a Poisson count with mean m·q, built from [a nonnegative intensity q
and exposure m](hyp:q,m), where [the exposure is positive](hyp:hm), [the radius multiplier H is at least the universal
constant 1024](hyp:hH), and [the level L is at least 1](hyp:hL), [the
probability that the normalized deviation |w/m − q| exceeds a quarter of the
empirical radius at level L/m is at most 2·exp(−40 L)](goal). -/
-- Rewrite the normalized deviation and radius with the private algebra in
-- `SelfNormalized.Scaling`; on `H ≥ universalH`, include this bad event in
-- `badEvent universalH L (m*q)` and apply `poisson_badEvent_probability`.
theorem poisson_empiricalRadius_bad_probability
    (q m : ℝ≥0) (hm : 0 < m) (H L : ℝ) (hH : universalH ≤ H)
    (hL : 1 ≤ L) :
    poissonMeasure (m * q)
      {w : ℕ | normalizedDeviation m q w >
        empiricalRadius H m (L / (m : ℝ)) w / 4} ≤
      ENNReal.ofReal (2 * Real.exp (-40 * L)) := by
  calc
    _ ≤ poissonMeasure (m * q) (badEvent universalH L (m * q)) :=
      measure_mono (empirical_bad_subset q m hm H L hH hL)
    _ ≤ 2 * ENNReal.ofReal (Real.exp (-(scalarDecay * L))) :=
      poisson_badEvent_probability (m * q) hL
    _ = ENNReal.ofReal (2 * Real.exp (-40 * L)) := by
      rw [show scalarDecay = (40 : ℝ) by rfl,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num

private theorem empirical_score_le (q m : ℝ≥0) (hm : 0 < m)
    (H L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L) (w : ℕ) :
    normalizedDeviation m q w + empiricalRadius H m (L / (m : ℝ)) w ≤
      (H / universalH) * (score universalH L (m * q) w / (m : ℝ)) := by
  have hmR : 0 < (m : ℝ) := NNReal.coe_pos.mpr hm
  have hu : 0 < universalH := universalH_pos
  have hd : 0 ≤ deviation (m * q) w := by simp [deviation]
  have hr : 0 ≤ radius L w := by unfold radius; positivity
  rw [empirical_normalizedDeviation_eq_div m q hm,
    empiricalRadius_eq_normalizedRadius,
    empirical_normalizedRadius_eq_div m hm]
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

private theorem empirical_localScale_div (q m : ℝ≥0) (hm : 0 < m)
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

private theorem empirical_bad_moment (q m : ℝ≥0) (hm : 0 < m)
    (H L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    {t : ℕ} (ht : t = 1 ∨ t = 2 ∨ t = 4) :
    ∫ w : ℕ,
      (if normalizedDeviation m q w > empiricalRadius H m (L / (m : ℝ)) w / 4
       then (normalizedDeviation m q w + empiricalRadius H m (L / (m : ℝ)) w) ^ t
       else 0) ∂poissonMeasure (m * q) ≤
      (H / universalH) ^ t * scalarBadMomentConstant t *
        Real.exp (-20 * L) *
        (Real.sqrt ((q : ℝ) * L / (m : ℝ)) + L / (m : ℝ)) ^ t := by
  let μ := poissonMeasure (m * q)
  let B := badEvent universalH L (m * q)
  let c : ℝ := (H / universalH) ^ t / (m : ℝ) ^ t
  have hmR : 0 < (m : ℝ) := NNReal.coe_pos.mpr hm
  have hH0 : 0 ≤ H := le_trans universalH_pos.le hH
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (pow_nonneg (div_nonneg hH0 universalH_pos.le) t)
      (pow_nonneg hmR.le t)
  have ht4 : t ≤ 4 := by rcases ht with rfl | rfl | rfl <;> omega
  have hgi : Integrable (fun w : ℕ => c * B.indicator
      (fun w => (score universalH L (m * q) w) ^ t) w) μ :=
    ((integrable_score_pow (m * q) hL ht4).indicator
      (measurableSet_badEvent universalH L (m * q))).const_mul c
  have hpoint (w : ℕ) :
      (if normalizedDeviation m q w > empiricalRadius H m (L / (m : ℝ)) w / 4
       then (normalizedDeviation m q w + empiricalRadius H m (L / (m : ℝ)) w) ^ t
       else 0) ≤ c * B.indicator
        (fun w => (score universalH L (m * q) w) ^ t) w := by
    by_cases hw : normalizedDeviation m q w >
        empiricalRadius H m (L / (m : ℝ)) w / 4
    · have hmem : w ∈ B := empirical_bad_subset q m hm H L hH hL hw
      simp only [if_pos hw, Set.indicator_of_mem hmem]
      have hscore := empirical_score_le q m hm H L hH hL w
      have hpow :
          (normalizedDeviation m q w + empiricalRadius H m (L / (m : ℝ)) w) ^ t ≤
            ((H / universalH) *
              (score universalH L (m * q) w / (m : ℝ))) ^ t := by
        exact pow_le_pow_left₀ (by
          have hd : 0 ≤ normalizedDeviation m q w := by simp [normalizedDeviation]
          have hr : 0 ≤ empiricalRadius H m (L / (m : ℝ)) w := by
            unfold empiricalRadius
            positivity
          positivity) hscore t
      calc
        _ ≤ ((H / universalH) *
            (score universalH L (m * q) w / (m : ℝ))) ^ t := hpow
        _ = c * score universalH L (m * q) w ^ t := by
          dsimp [c]
          rw [mul_pow, div_pow]
          ring
    · simp only [if_neg hw]
      exact mul_nonneg hc0 (by
        by_cases hmem : w ∈ B
        · simp [hmem]
          exact pow_nonneg (by unfold score deviation radius universalH; positivity) t
        · simp [hmem])
  have hmono :
      (∫ w : ℕ,
        (if normalizedDeviation m q w > empiricalRadius H m (L / (m : ℝ)) w / 4
         then (normalizedDeviation m q w + empiricalRadius H m (L / (m : ℝ)) w) ^ t
         else 0) ∂μ) ≤
        c * ∫ w : ℕ, B.indicator
          (fun w => (score universalH L (m * q) w) ^ t) w ∂μ := by
    calc
      _ ≤ ∫ w : ℕ, c * B.indicator
          (fun w => (score universalH L (m * q) w) ^ t) w ∂μ :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun w => by
            by_cases hw : normalizedDeviation m q w >
                empiricalRadius H m (L / (m : ℝ)) w / 4
            · simp [hw]
              have hd : 0 ≤ normalizedDeviation m q w := by simp [normalizedDeviation]
              have hr : 0 ≤ empiricalRadius H m (L / (m : ℝ)) w := by
                unfold empiricalRadius
                positivity
              positivity
            · simp [hw])) hgi (Filter.Eventually.of_forall hpoint)
      _ = _ := by rw [integral_const_mul]
  have hweighted := poisson_weighted_bad_moment (m * q) hL ht
  have hdecay : Real.exp (-(scalarDecay * L)) ≤ Real.exp (-20 * L) := by
    apply Real.exp_le_exp.mpr
    dsimp [scalarDecay]
    nlinarith
  calc
    _ ≤ c * ∫ w : ℕ, B.indicator
        (fun w => (score universalH L (m * q) w) ^ t) w ∂μ := hmono
    _ ≤ c * (scalarBadMomentConstant t * Real.exp (-(scalarDecay * L)) *
        (localScale (m * q) L) ^ t) :=
      mul_le_mul_of_nonneg_left hweighted hc0
    _ ≤ c * (scalarBadMomentConstant t * Real.exp (-20 * L) *
        (localScale (m * q) L) ^ t) := by
      gcongr
      · exact pow_nonneg (by unfold localScale; positivity) t
      · exact (scalarBadMomentConstant_pos t).le
    _ = _ := by
      dsimp [c]
      calc
        (H / universalH) ^ t / (m : ℝ) ^ t *
            (scalarBadMomentConstant t * Real.exp (-20 * L) *
              localScale (m * q) L ^ t) =
          (H / universalH) ^ t * scalarBadMomentConstant t *
            Real.exp (-20 * L) *
            (localScale (m * q) L / (m : ℝ)) ^ t := by
          rw [div_pow]
          ring
        _ = _ := by rw [empirical_localScale_div q m hm L hL]

/-- For a Poisson count with mean m·q, built from [a nonnegative intensity q
and exposure m](hyp:q,m), where [the exposure is positive](hyp:hm), [the radius multiplier H is at least the universal
constant 1024](hyp:hH), and [the level L is at least 1](hyp:hL), [the
expected squared failure score — the square of the normalized deviation plus
the empirical radius at level L/m, taken on the event that the deviation
exceeds a quarter of that radius and zero otherwise — is at most
(H/1024)^2 times the order-2 bad-moment constant times exp(−20 L) times
(√(qL/m) + L/m)^2](goal). -/
-- On the larger universal bad event, compare the H-score to
-- `(H/universalH) * score universalH`; then apply
-- `poisson_weighted_bad_moment` at `t=2` and divide by `m^2`.
theorem poisson_empiricalRadius_bad_second_moment
    (q m : ℝ≥0) (hm : 0 < m) (H L : ℝ)
    (hH : universalH ≤ H) (hL : 1 ≤ L) :
    ∫ w : ℕ,
      (if normalizedDeviation m q w > empiricalRadius H m (L / (m : ℝ)) w / 4
       then (normalizedDeviation m q w + empiricalRadius H m (L / (m : ℝ)) w) ^ 2
       else 0) ∂poissonMeasure (m * q) ≤
      (H / universalH) ^ 2 * scalarBadMomentConstant 2 *
        Real.exp (-20 * L) *
        (Real.sqrt ((q : ℝ) * L / (m : ℝ)) + L / (m : ℝ)) ^ 2 := by
  exact empirical_bad_moment q m hm H L hH hL (Or.inr (Or.inl rfl))

/-- For a Poisson count with mean m·q, built from [a nonnegative intensity q
and exposure m](hyp:q,m), where [the exposure is positive](hyp:hm), [the radius multiplier H is at least the universal
constant 1024](hyp:hH), and [the level L is at least 1](hyp:hL), [the
expected fourth-power failure score — the fourth power of the normalized
deviation plus the empirical radius at level L/m, taken on the event that
the deviation exceeds a quarter of that radius and zero otherwise — is at
most (H/1024)^4 times the order-4 bad-moment constant times exp(−20 L) times
(√(qL/m) + L/m)^4](goal). -/
-- Same comparison as the second moment, using the existing scalar theorem at
-- `t=4`; its `exp (-40L)` decay is stronger than the displayed `exp (-20L)`.
theorem poisson_empiricalRadius_bad_fourth_moment
    (q m : ℝ≥0) (hm : 0 < m) (H L : ℝ)
    (hH : universalH ≤ H) (hL : 1 ≤ L) :
    ∫ w : ℕ,
      (if normalizedDeviation m q w > empiricalRadius H m (L / (m : ℝ)) w / 4
       then (normalizedDeviation m q w + empiricalRadius H m (L / (m : ℝ)) w) ^ 4
       else 0) ∂poissonMeasure (m * q) ≤
      (H / universalH) ^ 4 * scalarBadMomentConstant 4 *
        Real.exp (-20 * L) *
        (Real.sqrt ((q : ℝ) * L / (m : ℝ)) + L / (m : ℝ)) ^ 4 := by
  exact empirical_bad_moment q m hm H L hH hL (Or.inr (Or.inr rfl))

end Causalean.Stat.Concentration.Poisson
