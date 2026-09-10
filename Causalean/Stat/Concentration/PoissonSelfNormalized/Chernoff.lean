import Causalean.Stat.Concentration.PoissonSelfNormalized.Basic
import Mathlib.Probability.Moments.Basic

/-!
# Exponential moments and Bernstein tails for a Poisson count

This module records the exact centered moment-generating function and derives
the two-sided Bernstein deviation inequality, including the zero-mean case.
It also isolates the deterministic comparison which turns a sufficiently
large self-normalized failure into a remote Bernstein-tail event.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace Causalean.Stat.Concentration.PoissonSelfNormalized

/-- Under [a Poisson law with a nonnegative mean](hyp:lambda), the exponential of its centered count
at [a real tilt](hyp:theta) is [integrable](goal). -/
theorem integrable_exp_centered_poisson (lambda : ℝ≥0) (theta : ℝ) :
    Integrable (fun w : ℕ => Real.exp (theta * ((w : ℝ) - (lambda : ℝ))))
      (poissonMeasure lambda) := by
  rw [integrable_poissonMeasure_iff]
  have hs := Real.summable_pow_div_factorial
    ((lambda : ℝ) * Real.exp theta)
  apply (hs.mul_left
    (Real.exp (-(lambda : ℝ)) * Real.exp (-(theta * (lambda : ℝ))))).congr
  intro w
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [show Real.exp (theta * ((w : ℝ) - (lambda : ℝ))) =
      (Real.exp theta) ^ w * Real.exp (-(theta * (lambda : ℝ))) by
    calc
      Real.exp (theta * ((w : ℝ) - (lambda : ℝ))) =
          Real.exp ((w : ℝ) * theta - theta * (lambda : ℝ)) := by congr 1; ring
      _ = Real.exp ((w : ℝ) * theta) / Real.exp (theta * (lambda : ℝ)) :=
        Real.exp_sub _ _
      _ = (Real.exp theta) ^ w * Real.exp (-(theta * (lambda : ℝ))) := by
        rw [Real.exp_nat_mul, Real.exp_neg]
        ring]
  ring

/-- For [a Poisson law with a nonnegative mean](hyp:lambda) and [a real tilt](hyp:theta), the
[centered moment-generating function equals the exponential of the mean times the exponential
remainder](goal). -/
theorem integral_exp_centered_poisson (lambda : ℝ≥0) (theta : ℝ) :
    ∫ w : ℕ, Real.exp (theta * ((w : ℝ) - (lambda : ℝ))) ∂poissonMeasure lambda =
      Real.exp ((lambda : ℝ) * (Real.exp theta - 1 - theta)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  calc
    ∑' w : ℕ, Real.exp (-(lambda : ℝ)) * (lambda : ℝ) ^ w / Nat.factorial w *
          Real.exp (theta * ((w : ℝ) - (lambda : ℝ))) =
        (Real.exp (-(lambda : ℝ)) * Real.exp (-(theta * (lambda : ℝ)))) *
          ∑' w : ℕ, (((lambda : ℝ) * Real.exp theta) ^ w / Nat.factorial w) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro w
      rw [show Real.exp (theta * ((w : ℝ) - (lambda : ℝ))) =
          (Real.exp theta) ^ w * Real.exp (-(theta * (lambda : ℝ))) by
        calc
          Real.exp (theta * ((w : ℝ) - (lambda : ℝ))) =
              Real.exp ((w : ℝ) * theta - theta * (lambda : ℝ)) := by congr 1; ring
          _ = Real.exp ((w : ℝ) * theta) / Real.exp (theta * (lambda : ℝ)) :=
            Real.exp_sub _ _
          _ = (Real.exp theta) ^ w * Real.exp (-(theta * (lambda : ℝ))) := by
            rw [Real.exp_nat_mul, Real.exp_neg]
            ring]
      ring
    _ = (Real.exp (-(lambda : ℝ)) * Real.exp (-(theta * (lambda : ℝ)))) *
          Real.exp ((lambda : ℝ) * Real.exp theta) := by
      have hseries := (NormedSpace.expSeries_div_hasSum_exp
        ((lambda : ℝ) * Real.exp theta)).tsum_eq
      rw [← Real.exp_eq_exp_ℝ] at hseries
      rw [hseries]
    _ = Real.exp ((lambda : ℝ) * (Real.exp theta - 1 - theta)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

/-- For [a Poisson law with a nonnegative mean](hyp:lambda) and [a nonnegative deviation
level](hyp:z,hz), [the probability of exceeding the upper Bernstein threshold is at most the
exponential of minus that level](goal). -/
-- Proof strategy: split `lambda = 0`; otherwise apply
-- `measure_ge_le_exp_mul_mgf` to the centered count at the Bennett tilt
-- `log (1 + x / lambda)`, where
-- `x = sqrt (2 * lambda * z) + 2 * z`.  Rewrite the MGF with
-- `integral_exp_centered_poisson`, use
-- `Real.le_log_one_add_of_nonneg` to lower-bound the Bennett exponent by
-- `x^2 / (2 * lambda + x)`, and finish from the defining value of `x`.
-- Convert the resulting `Measure.real` inequality back to `ENNReal` with
-- `ENNReal.ofReal_measureReal`; the strict event is first included in the
-- corresponding weak half-line.
theorem poisson_upper_bernstein (lambda : ℝ≥0) {z : ℝ} (hz : 0 ≤ z) :
    poissonMeasure lambda
        {w : ℕ | (w : ℝ) - (lambda : ℝ) >
          Real.sqrt (2 * (lambda : ℝ) * z) + 2 * z} ≤
      ENNReal.ofReal (Real.exp (-z)) := by
  by_cases hlambda : lambda = 0
  · subst lambda
    have hnull : poissonMeasure 0 {w : ℕ | w ≠ 0} = 0 := by
      simpa only [Pi.zero_apply] using (ae_iff.mp poissonMeasure_zero_ae)
    have hsubset :
        {w : ℕ | (w : ℝ) - (0 : ℝ) > Real.sqrt (2 * (0 : ℝ) * z) + 2 * z} ⊆
          {w : ℕ | w ≠ 0} := by
      intro w hw hzero
      subst w
      simp only [Set.mem_ofPred_eq, Nat.cast_zero, sub_zero, mul_zero, zero_mul,
        Real.sqrt_zero, zero_add] at hw
      linarith
    change poissonMeasure 0
      {w : ℕ | (w : ℝ) - (0 : ℝ) >
        Real.sqrt (2 * (0 : ℝ) * z) + 2 * z} ≤ _
    rw [measure_mono_null hsubset hnull]
    exact bot_le
  · have hlambda_pos : 0 < (lambda : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hlambda)
    let x : ℝ := Real.sqrt (2 * (lambda : ℝ) * z) + 2 * z
    let theta : ℝ := Real.log (1 + x / (lambda : ℝ))
    have hx_nonneg : 0 ≤ x := by
      dsimp [x]
      positivity
    have htheta_nonneg : 0 ≤ theta := by
      dsimp [theta]
      exact Real.log_nonneg (by
        have := div_nonneg hx_nonneg hlambda_pos.le
        linarith)
    have hden_pos : 0 < 2 * (lambda : ℝ) + x := by positivity
    have hsqrt_sq : (Real.sqrt (2 * (lambda : ℝ) * z)) ^ 2 =
        2 * (lambda : ℝ) * z := by
      rw [Real.sq_sqrt]
      positivity
    have hz_frac : z ≤ x ^ 2 / (2 * (lambda : ℝ) + x) := by
      rw [le_div_iff₀ hden_pos]
      dsimp [x]
      nlinarith [Real.sqrt_nonneg (2 * (lambda : ℝ) * z)]
    have hlog :
        2 * (x / (lambda : ℝ)) / (x / (lambda : ℝ) + 2) ≤ theta := by
      dsimp [theta]
      exact Real.le_log_one_add_of_nonneg (div_nonneg hx_nonneg hlambda_pos.le)
    have hfrac_bennett :
        x ^ 2 / (2 * (lambda : ℝ) + x) ≤
          ((lambda : ℝ) + x) * theta - x := by
      have hscale :
          ((lambda : ℝ) + x) *
              (2 * (x / (lambda : ℝ)) / (x / (lambda : ℝ) + 2)) - x =
            x ^ 2 / (2 * (lambda : ℝ) + x) := by
        field_simp
        ring
      rw [← hscale]
      gcongr
    have hmgf :
        mgf (fun w : ℕ => (w : ℝ) - (lambda : ℝ))
            (poissonMeasure lambda) theta =
          Real.exp ((lambda : ℝ) * (Real.exp theta - 1 - theta)) := by
      exact integral_exp_centered_poisson lambda theta
    have hexp_theta : Real.exp theta = 1 + x / (lambda : ℝ) := by
      dsimp [theta]
      rw [Real.exp_log]
      positivity
    have hchernoff := measure_ge_le_exp_mul_mgf
      (X := fun w : ℕ => (w : ℝ) - (lambda : ℝ))
      (μ := poissonMeasure lambda) x htheta_nonneg
      (integrable_exp_centered_poisson lambda theta)
    rw [hmgf] at hchernoff
    have hreal :
        (poissonMeasure lambda).real
            {w : ℕ | x ≤ (w : ℝ) - (lambda : ℝ)} ≤ Real.exp (-z) := by
      refine hchernoff.trans ?_
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [hexp_theta]
      have hidentity :
          -theta * x + (lambda : ℝ) *
              (1 + x / (lambda : ℝ) - 1 - theta) =
            -(((lambda : ℝ) + x) * theta - x) := by
        field_simp
        ring
      rw [hidentity]
      linarith [hz_frac.trans hfrac_bennett]
    have hsubset :
        {w : ℕ | (w : ℝ) - (lambda : ℝ) >
            Real.sqrt (2 * (lambda : ℝ) * z) + 2 * z} ⊆
          {w : ℕ | x ≤ (w : ℝ) - (lambda : ℝ)} := by
      intro w hw
      change (w : ℝ) - (lambda : ℝ) > x at hw
      change x ≤ (w : ℝ) - (lambda : ℝ)
      exact hw.le
    calc
      poissonMeasure lambda
          {w : ℕ | (w : ℝ) - (lambda : ℝ) >
            Real.sqrt (2 * (lambda : ℝ) * z) + 2 * z} ≤
          poissonMeasure lambda {w : ℕ | x ≤ (w : ℝ) - (lambda : ℝ)} :=
        measure_mono hsubset
      _ = ENNReal.ofReal ((poissonMeasure lambda).real
          {w : ℕ | x ≤ (w : ℝ) - (lambda : ℝ)}) := by
        symm
        exact ofReal_measureReal (measure_ne_top _ _)
      _ ≤ ENNReal.ofReal (Real.exp (-z)) := ENNReal.ofReal_le_ofReal hreal

/-- For [a Poisson law with a nonnegative mean](hyp:lambda) and [a nonnegative deviation
level](hyp:z,hz), [the probability of exceeding the lower Gaussian threshold is at most the
exponential of minus that level](goal). -/
-- Proof strategy: split the zero-mean and zero-threshold cases, and note that
-- the event is empty when `sqrt (2 * lambda * z) ≥ lambda`.  Otherwise put
-- `x = sqrt (2 * lambda * z)` and apply
-- `measure_le_le_exp_mul_mgf` to the centered count at tilt `-x / lambda`.
-- The elementary estimate
-- `exp (-u) - 1 + u ≤ u^2 / 2` for `u ≥ 0` turns the exact MGF into
-- `exp (-x^2 / (2 * lambda)) = exp (-z)`.  One convenient proof of that
-- estimate uses `Real.quadratic_le_exp_of_nonneg`, `Real.exp_neg`, and the
-- identity `(1-u+u^2/2)*(1+u+u^2/2) = 1+u^4/4`.
theorem poisson_lower_bernstein (lambda : ℝ≥0) {z : ℝ} (hz : 0 ≤ z) :
    poissonMeasure lambda
        {w : ℕ | (lambda : ℝ) - (w : ℝ) >
          Real.sqrt (2 * (lambda : ℝ) * z)} ≤
      ENNReal.ofReal (Real.exp (-z)) := by
  by_cases hlambda : lambda = 0
  · subst lambda
    have hempty :
        {w : ℕ | (0 : ℝ) - (w : ℝ) >
          Real.sqrt (2 * (0 : ℝ) * z)} = ∅ := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hw
      have hw_nonneg : 0 ≤ (w : ℝ) := Nat.cast_nonneg w
      have hsqrt_nonneg := Real.sqrt_nonneg (2 * (0 : ℝ) * z)
      linarith
    change poissonMeasure 0
      {w : ℕ | (0 : ℝ) - (w : ℝ) >
        Real.sqrt (2 * (0 : ℝ) * z)} ≤ _
    rw [hempty, measure_empty]
    exact bot_le
  · have hlambda_pos : 0 < (lambda : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hlambda)
    by_cases hz_zero : z = 0
    · subst z
      calc
        poissonMeasure lambda
            {w : ℕ | (lambda : ℝ) - (w : ℝ) >
              Real.sqrt (2 * (lambda : ℝ) * 0)} ≤
            poissonMeasure lambda Set.univ := measure_mono (Set.subset_univ _)
        _ = ENNReal.ofReal (Real.exp (-(0 : ℝ))) := by simp
    · have hz_pos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz_zero)
      let x : ℝ := Real.sqrt (2 * (lambda : ℝ) * z)
      have hx_nonneg : 0 ≤ x := Real.sqrt_nonneg _
      have hx_pos : 0 < x := by
        dsimp [x]
        positivity
      have hx_sq : x ^ 2 = 2 * (lambda : ℝ) * z := by
        dsimp [x]
        rw [Real.sq_sqrt]
        positivity
      by_cases hx_large : (lambda : ℝ) ≤ x
      · have hempty :
          {w : ℕ | (lambda : ℝ) - (w : ℝ) >
            Real.sqrt (2 * (lambda : ℝ) * z)} = ∅ := by
          ext w
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          intro hw
          change (lambda : ℝ) - (w : ℝ) > x at hw
          have hw_nonneg : 0 ≤ (w : ℝ) := Nat.cast_nonneg w
          linarith
        rw [hempty, measure_empty]
        exact bot_le
      · have hx_lt : x < (lambda : ℝ) := lt_of_not_ge hx_large
        let u : ℝ := x / (lambda : ℝ)
        let theta : ℝ := -u
        have hu_nonneg : 0 ≤ u := div_nonneg hx_nonneg hlambda_pos.le
        have htheta_nonpos : theta ≤ 0 := by
          dsimp [theta]
          exact neg_nonpos.mpr hu_nonneg
        have hexp_quad : Real.exp (-u) - 1 + u ≤ u ^ 2 / 2 := by
          have hquad := Real.quadratic_le_exp_of_nonneg hu_nonneg
          have hright_nonneg : 0 ≤ 1 - u + u ^ 2 / 2 := by
            nlinarith [sq_nonneg (u - 1)]
          have hprod :
              1 ≤ (1 + u + u ^ 2 / 2) * (1 - u + u ^ 2 / 2) := by
            calc
              (1 : ℝ) ≤ 1 + u ^ 4 / 4 :=
                le_add_of_nonneg_right (div_nonneg (by positivity) (by norm_num))
              _ = (1 + u + u ^ 2 / 2) * (1 - u + u ^ 2 / 2) := by ring
          have hinv : (Real.exp u)⁻¹ ≤ 1 - u + u ^ 2 / 2 := by
            rw [inv_eq_one_div, div_le_iff₀ (Real.exp_pos u)]
            calc
              (1 : ℝ) ≤ (1 + u + u ^ 2 / 2) *
                  (1 - u + u ^ 2 / 2) := hprod
              _ ≤ Real.exp u * (1 - u + u ^ 2 / 2) :=
                mul_le_mul_of_nonneg_right hquad hright_nonneg
              _ = (1 - u + u ^ 2 / 2) * Real.exp u := by ring
          rw [Real.exp_neg]
          linarith
        have hmgf :
            mgf (fun w : ℕ => (w : ℝ) - (lambda : ℝ))
                (poissonMeasure lambda) theta =
              Real.exp ((lambda : ℝ) * (Real.exp theta - 1 - theta)) := by
          exact integral_exp_centered_poisson lambda theta
        have hchernoff := measure_le_le_exp_mul_mgf
          (X := fun w : ℕ => (w : ℝ) - (lambda : ℝ))
          (μ := poissonMeasure lambda) (-x) htheta_nonpos
          (integrable_exp_centered_poisson lambda theta)
        rw [hmgf] at hchernoff
        have hreal :
            (poissonMeasure lambda).real
                {w : ℕ | (w : ℝ) - (lambda : ℝ) ≤ -x} ≤ Real.exp (-z) := by
          refine hchernoff.trans ?_
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have htheta_eq : theta = -(x / (lambda : ℝ)) := rfl
          rw [htheta_eq]
          have hquad_scaled :
              (lambda : ℝ) *
                  (Real.exp (-(x / (lambda : ℝ))) - 1 + x / (lambda : ℝ)) ≤
                x ^ 2 / (2 * (lambda : ℝ)) := by
            have := mul_le_mul_of_nonneg_left hexp_quad hlambda_pos.le
            dsimp [u] at this
            calc
              (lambda : ℝ) *
                    (Real.exp (-(x / (lambda : ℝ))) - 1 + x / (lambda : ℝ)) ≤
                  (lambda : ℝ) * ((x / (lambda : ℝ)) ^ 2 / 2) := this
              _ = x ^ 2 / (2 * (lambda : ℝ)) := by
                field_simp [ne_of_gt hlambda_pos]
          have hidentity :
              -(-(x / (lambda : ℝ))) * -x +
                  (lambda : ℝ) *
                    (Real.exp (-(x / (lambda : ℝ))) - 1 - (-(x / (lambda : ℝ)))) =
                -(x ^ 2 / (lambda : ℝ)) +
                  (lambda : ℝ) *
                    (Real.exp (-(x / (lambda : ℝ))) - 1 + x / (lambda : ℝ)) := by
            field_simp
            ring
          rw [hidentity]
          have hz_identity : x ^ 2 / (2 * (lambda : ℝ)) = z := by
            rw [hx_sq]
            field_simp
          rw [hz_identity] at hquad_scaled
          have hxdiv : x ^ 2 / (lambda : ℝ) = 2 * z := by
            rw [hx_sq]
            field_simp
          rw [hxdiv]
          linarith
        have hsubset :
            {w : ℕ | (lambda : ℝ) - (w : ℝ) >
                Real.sqrt (2 * (lambda : ℝ) * z)} ⊆
              {w : ℕ | (w : ℝ) - (lambda : ℝ) ≤ -x} := by
          intro w hw
          simp only [Set.mem_ofPred_eq] at hw ⊢
          change (lambda : ℝ) - (w : ℝ) > x at hw
          linarith
        calc
          poissonMeasure lambda
              {w : ℕ | (lambda : ℝ) - (w : ℝ) >
                Real.sqrt (2 * (lambda : ℝ) * z)} ≤
              poissonMeasure lambda
                {w : ℕ | (w : ℝ) - (lambda : ℝ) ≤ -x} := measure_mono hsubset
          _ = ENNReal.ofReal ((poissonMeasure lambda).real
              {w : ℕ | (w : ℝ) - (lambda : ℝ) ≤ -x}) := by
            symm
            exact ofReal_measureReal (measure_ne_top _ _)
          _ ≤ ENNReal.ofReal (Real.exp (-z)) := ENNReal.ofReal_le_ofReal hreal

/-- For [a Poisson law with a nonnegative mean](hyp:lambda) and [a nonnegative deviation
level](hyp:z,hz), [the probability that the absolute deviation exceeds the Bernstein threshold is
at most twice the exponential of minus that level](goal), including when the mean is zero. -/
-- Proof strategy: rewrite `deviation`, split the absolute-value event into
-- upper and lower deviations, apply `measure_union_le`, and use the preceding
-- one-sided bounds.  The lower event with the larger displayed threshold is
-- contained in the lower Bernstein event with threshold `sqrt (2 lambda z)`.
theorem poisson_abs_bernstein (lambda : ℝ≥0) {z : ℝ} (hz : 0 ≤ z) :
    poissonMeasure lambda
        {w : ℕ | deviation lambda w >
          Real.sqrt (2 * (lambda : ℝ) * z) + 2 * z} ≤
      2 * ENNReal.ofReal (Real.exp (-z)) := by
  let s : ℝ := Real.sqrt (2 * (lambda : ℝ) * z)
  let T : ℝ := s + 2 * z
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    positivity
  have hsubset :
      {w : ℕ | deviation lambda w >
          Real.sqrt (2 * (lambda : ℝ) * z) + 2 * z} ⊆
        {w : ℕ | (w : ℝ) - (lambda : ℝ) >
            Real.sqrt (2 * (lambda : ℝ) * z) + 2 * z} ∪
          {w : ℕ | (lambda : ℝ) - (w : ℝ) >
            Real.sqrt (2 * (lambda : ℝ) * z)} := by
    intro w hw
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hw ⊢
    change |(w : ℝ) - (lambda : ℝ)| > T at hw
    by_cases hu : (w : ℝ) - (lambda : ℝ) > T
    · left
      exact hu
    · right
      change (lambda : ℝ) - (w : ℝ) > s
      by_contra hl
      have hl' : (lambda : ℝ) - (w : ℝ) ≤ s := le_of_not_gt hl
      have hu' : (w : ℝ) - (lambda : ℝ) ≤ T := le_of_not_gt hu
      have hlower : -T ≤ (w : ℝ) - (lambda : ℝ) := by
        dsimp [T]
        linarith
      have habs : |(w : ℝ) - (lambda : ℝ)| ≤ T :=
        (abs_le.mpr ⟨hlower, hu'⟩)
      linarith
  calc
    poissonMeasure lambda
        {w : ℕ | deviation lambda w >
          Real.sqrt (2 * (lambda : ℝ) * z) + 2 * z} ≤
      poissonMeasure lambda
          ({w : ℕ | (w : ℝ) - (lambda : ℝ) >
              Real.sqrt (2 * (lambda : ℝ) * z) + 2 * z} ∪
            {w : ℕ | (lambda : ℝ) - (w : ℝ) >
              Real.sqrt (2 * (lambda : ℝ) * z)}) := measure_mono hsubset
    _ ≤ poissonMeasure lambda
          {w : ℕ | (w : ℝ) - (lambda : ℝ) >
            Real.sqrt (2 * (lambda : ℝ) * z) + 2 * z} +
        poissonMeasure lambda
          {w : ℕ | (lambda : ℝ) - (w : ℝ) >
            Real.sqrt (2 * (lambda : ℝ) * z)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-z)) + ENNReal.ofReal (Real.exp (-z)) :=
      add_le_add (poisson_upper_bernstein lambda hz)
        (poisson_lower_bernstein lambda hz)
    _ = 2 * ENNReal.ofReal (Real.exp (-z)) := by ring

/-- For [a Poisson law with a nonnegative mean](hyp:lambda) and [a logarithmic level of at least
one](hyp:L,hL), [the universal self-normalized bad event is contained in the Bernstein event at
forty times that level](goal). -/
-- Proof strategy: contrapose and put `d = deviation lambda w`.  From
-- `lambda ≤ w + d`, monotonicity and subadditivity of `sqrt` turn the remote
-- Bernstein threshold into
-- `sqrt 80 * sqrt (w * L) + sqrt (80 * d * L) + 80 * L`.
-- Young's inequality `sqrt (80 * d * L) ≤ d / 2 + 40 * L` then gives
-- `d ≤ 2 * sqrt 80 * sqrt (w * L) + 240 * L`, which is at most
-- `256 * (sqrt (w * L) + L) = (universalH / 4) * radius L w`.
-- The former value `universalH = 512` is invalid: `L = 1`, `w = 0`, and
-- `lambda = 129` is a counterexample.
theorem badEvent_subset_remote_bernstein (lambda : ℝ≥0) {L : ℝ} (hL : 1 ≤ L) :
    badEvent universalH L lambda ⊆
      {w : ℕ | deviation lambda w >
        Real.sqrt (2 * (lambda : ℝ) * (scalarDecay * L)) +
          2 * (scalarDecay * L)} := by
  intro w hw
  simp only [Set.mem_ofPred_eq] at hw ⊢
  change deviation lambda w >
    (1024 / 4) * (Real.sqrt ((w : ℝ) * L) + L) at hw
  have hconst : (1024 : ℝ) / 4 = 256 := by norm_num
  rw [hconst] at hw
  by_contra hnot
  change ¬ deviation lambda w >
    Real.sqrt (2 * (lambda : ℝ) * (40 * L)) + 2 * (40 * L) at hnot
  have hupper :
      deviation lambda w ≤
        Real.sqrt (2 * (lambda : ℝ) * (40 * L)) + 80 * L := by
    nlinarith [le_of_not_gt hnot]
  have hL0 : 0 ≤ L := by linarith
  have hw0 : 0 ≤ (w : ℝ) := Nat.cast_nonneg w
  have hlambda0 : 0 ≤ (lambda : ℝ) := lambda.coe_nonneg
  have hd0 : 0 ≤ deviation lambda w := by
    simp [deviation]
  have hs0 : 0 ≤ Real.sqrt ((w : ℝ) * L) := Real.sqrt_nonneg _
  have hq0 :
      0 ≤ Real.sqrt (2 * (lambda : ℝ) * (40 * L)) := Real.sqrt_nonneg _
  have hs_sq :
      (Real.sqrt ((w : ℝ) * L)) ^ 2 = (w : ℝ) * L := by
    rw [Real.sq_sqrt]
    positivity
  have hq_sq :
      (Real.sqrt (2 * (lambda : ℝ) * (40 * L))) ^ 2 =
        2 * (lambda : ℝ) * (40 * L) := by
    rw [Real.sq_sqrt]
    positivity
  have hlambda_le :
      (lambda : ℝ) ≤ (w : ℝ) + deviation lambda w := by
    simp only [deviation]
    nlinarith [neg_le_abs ((w : ℝ) - (lambda : ℝ))]
  have hdiff0 : 0 ≤ deviation lambda w - 80 * L := by
    nlinarith
  have hsquare :
      (deviation lambda w - 80 * L) ^ 2 ≤
        (Real.sqrt (2 * (lambda : ℝ) * (40 * L))) ^ 2 := by
    nlinarith
  nlinarith

/-- For [a Poisson law with a nonnegative mean](hyp:lambda) and [a logarithmic level of at least
one](hyp:L,hL), [the universal self-normalized bad event has probability at most twice the
exponential of minus forty times that level](goal). -/
-- Apply `measure_mono` to `badEvent_subset_remote_bernstein`, then invoke
-- `poisson_abs_bernstein` at `z = scalarDecay * L`; `hL` makes this level
-- nonnegative and the threshold is definitionally the same after unfolding.
theorem poisson_badEvent_probability (lambda : ℝ≥0) {L : ℝ} (hL : 1 ≤ L) :
    poissonMeasure lambda (badEvent universalH L lambda) ≤
      2 * ENNReal.ofReal (Real.exp (-(scalarDecay * L))) := by
  calc
    poissonMeasure lambda (badEvent universalH L lambda) ≤
        poissonMeasure lambda
          {w : ℕ | deviation lambda w >
            Real.sqrt (2 * (lambda : ℝ) * (scalarDecay * L)) +
              2 * (scalarDecay * L)} :=
      measure_mono (badEvent_subset_remote_bernstein lambda hL)
    _ ≤ 2 * ENNReal.ofReal (Real.exp (-(scalarDecay * L))) := by
      apply poisson_abs_bernstein lambda
      have hL0 : 0 ≤ L := by linarith
      exact mul_nonneg (le_trans (by norm_num) forty_le_scalarDecay) hL0

end Causalean.Stat.Concentration.PoissonSelfNormalized

/-! ## Quarter-mean Poisson overflow -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Causalean.Stat.Concentration.PoissonSelfNormalized

open Causalean.Stat.Concentration.PoissonSelfNormalized

/-- For [a positive sample size](hyp:hn), [a Poisson count with mean one quarter
of that size overshoots the sample size with probability at most
`exp (-n/8)`](goal). -/
theorem poisson_quarter_overflow_le_exp (n : ℕ) (hn : 0 < n) :
    (poissonMeasure ((n : ℝ≥0) / 4)).real (Set.Ioi n) ≤
      Real.exp (-(n : ℝ) / 8) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt :
      Real.sqrt (2 * (((n : ℝ≥0) / 4 : ℝ≥0) : ℝ) * ((n : ℝ) / 8)) =
        (n : ℝ) / 4 := by
    rw [show 2 * (((n : ℝ≥0) / 4 : ℝ≥0) : ℝ) * ((n : ℝ) / 8) =
        ((n : ℝ) / 4) ^ 2 by norm_num; ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  have hsubset :
      Set.Ioi n ⊆
        {w : ℕ | (w : ℝ) - (((n : ℝ≥0) / 4 : ℝ≥0) : ℝ) >
          Real.sqrt (2 * (((n : ℝ≥0) / 4 : ℝ≥0) : ℝ) * ((n : ℝ) / 8)) +
            2 * ((n : ℝ) / 8)} := by
    intro w hw
    simp only [Set.mem_Ioi] at hw ⊢
    have hwR : (n : ℝ) < (w : ℝ) := by exact_mod_cast hw
    rw [hsqrt]
    norm_num
    nlinarith
  have hbern := poisson_upper_bernstein ((n : ℝ≥0) / 4)
    (z := (n : ℝ) / 8) (by positivity)
  have hmono :
      poissonMeasure ((n : ℝ≥0) / 4) (Set.Ioi n) ≤
        poissonMeasure ((n : ℝ≥0) / 4)
          {w : ℕ | (w : ℝ) - (((n : ℝ≥0) / 4 : ℝ≥0) : ℝ) >
            Real.sqrt (2 * (((n : ℝ≥0) / 4 : ℝ≥0) : ℝ) * ((n : ℝ) / 8)) +
              2 * ((n : ℝ) / 8)} :=
    measure_mono hsubset
  simpa only [Measure.real_def, ENNReal.toReal_ofReal (Real.exp_pos _).le, neg_div] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmono.trans hbern)

/-- For [a positive sample size](hyp:hn), [a Poisson count with mean one quarter
of that size overshoots the sample size with probability at most `8 / n`](goal). -/
theorem poisson_quarter_overflow_le_inv (n : ℕ) (hn : 0 < n) :
    (poissonMeasure ((n : ℝ≥0) / 4)).real (Set.Ioi n) ≤
      8 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hx : 0 < (n : ℝ) / 8 := by positivity
  have hexp : (n : ℝ) / 8 ≤ Real.exp ((n : ℝ) / 8) := by
    linarith [Real.add_one_le_exp ((n : ℝ) / 8)]
  calc
    (poissonMeasure ((n : ℝ≥0) / 4)).real (Set.Ioi n) ≤
        Real.exp (-(n : ℝ) / 8) :=
      poisson_quarter_overflow_le_exp n hn
    _ = 1 / Real.exp ((n : ℝ) / 8) := by
      rw [show -(n : ℝ) / 8 = -((n : ℝ) / 8) by ring, Real.exp_neg, one_div]
    _ ≤ 1 / ((n : ℝ) / 8) :=
      one_div_le_one_div_of_le hx hexp
    _ = 8 / (n : ℝ) := by
      field_simp

end Causalean.Stat.Concentration.PoissonSelfNormalized

