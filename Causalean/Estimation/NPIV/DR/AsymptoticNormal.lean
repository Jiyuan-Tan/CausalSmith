/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Consequences of the abstract TRAE-DR remainder criterion

This file derives limit results from the abstract unconditional remainder
criterion in `AsymptoticLinear.lean`:

* the rescaled TRAE-DR estimator converges in distribution to
  `N(0, σ₀²)` along the estimation fold, where
  `σ₀² := ∫ ρ₀(w)² dP_W`;
* under a consistent standard-deviation estimator `σ̂_n`, the studentized statistic
  converges to `N(0, 1)`;
* assuming an event-probability bridge from the studentized interval to the
  Wald interval, the Wald coverage probability has the corresponding limit.

The first theorem is a direct composition of `trae_dr_isAsymLinear` with
`IsAsymLinear.tendsto_normal_foldB` (`Causalean/Stat/PartialFoldCLT.lean`).

The studentized statement parameterizes over a standard-deviation-estimator sequence
`σ_hat_n` together with its `Tendsto_inProb` consistency hypothesis. The
Wald statement additionally assumes that its coverage event and the
studentized interval event have asymptotically equal probabilities; it is a
transfer theorem, not a derivation of that event bridge.
-/

module
public import Causalean.Estimation.NPIV.DR.PrimalRate
public import Causalean.Stat.Inference.Studentize
public import Causalean.Stat.SampleSplit.PartialFoldCLT

/-!
Derives asymptotic normality for the doubly robust NPIV estimator from
asymptotic linearity, Gaussian score limits, and
studentization/continuous-mapping inputs.
-/

public section

namespace Causalean
namespace Estimation
namespace NPIV
namespace DR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat

/-! ## Headline asymptotic-normality theorem

The portmanteau / Gaussian-boundary helpers and the convergence-in-probability
primitives used below now live in `Causalean/Stat/Studentize.lean` and
`Causalean/Stat/ContinuousMapping.lean` (public, estimator-agnostic). -/

/-- **TRAE-DR asymptotic normality from abstract remainder bounds.** For [an inverse-problem
system](hyp:S), [a dual solution](hyp:hq₀), [an i.i.d. sample](hyp:sample), [a one-shot
split](hyp:split), [primal nuisance functions](hyp:h_hat), and [dual nuisance
functions](hyp:q_hat), assume [the abstract remainder conditions](hyp:_hyps), [the
observation-law bridge](hyp:h_law_W), [measurability of the oracle score](hyp:_h_ρ₀_meas),
[measurability of the rescaled estimator](hyp:h_meas_θ), and [measurability of its normalized
oracle-score sum](hyp:_h_meas_sum). Then [the rescaled estimator converges along the evaluation
folds to the centered Gaussian law whose variance is the oracle score's second moment](goal).

Under the hypotheses of `trae_dr_isAsymLinear`, the rescaled estimator
converges in distribution to `N(0, σ₀²)` along the estimation-fold
horizon, where `σ₀² := ∫ ρ₀(w)² dP_W`.

This is the direct composition of `trae_dr_isAsymLinear` with
`IsAsymLinear.tendsto_normal_foldB`.  The conclusion is at the fold-B
rate `√|B(n)|`; for the √n form under a fixed split ratio
`|B(n)|/n → c`, the variance inflates to `σ₀²/c` (apply
`IsAsymLinear.tendsto_normal_foldB_sqrt_n` instead). -/
theorem trae_dr_asymp_normal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    (hq₀ : S.DualSolution q₀)
    {P_W : Measure S.𝒲} [IsProbabilityMeasure P_W]
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (h_hat : ℕ → Ω → (S.𝒳 → ℝ))
    (q_hat : ℕ → Ω → (S.𝒵 → ℝ))
    (_hyps : TRAEDRRemainderHyps S hq₀ sample split h_hat q_hat)
    (h_law_W : μ.map S.W = P_W)
    (_h_ρ₀_meas : Measurable (ρ₀ S q₀))
    (h_meas_θ : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (trae_dr_estimator S sample split h_hat q_hat) S.θ₀ split.foldB n) μ)
    (_h_meas_sum : ∀ n, AEMeasurable
      (IsAsymLinear.normalizedSum sample (ρ₀ S q₀) split.foldB n) μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator
        (trae_dr_estimator S sample split h_hat q_hat) S.θ₀ split.foldB)
      (gaussianMeasure 0 (∫ w, (ρ₀ S q₀ w) ^ 2 ∂P_W))
      μ
      h_meas_θ := by
  have hAL : IsAsymLinear
      (trae_dr_estimator S sample split h_hat q_hat)
      S.θ₀
      (ρ₀ S q₀)
      sample
      split.foldB := by
    exact trae_dr_isAsymLinear S hq₀ sample split h_hat q_hat _hyps h_law_W _h_ρ₀_meas
  exact hAL.tendsto_normal_foldB split _h_ρ₀_meas h_meas_θ _h_meas_sum

/-! ## Studentized convergence -/

/-- **Studentized TRAE-DR convergence.** For [an inverse-problem system](hyp:S), [a dual
solution](hyp:hq₀), [an i.i.d. sample](hyp:sample), [a one-shot split](hyp:split), [primal
nuisance functions](hyp:h_hat), and [dual nuisance functions](hyp:q_hat), assume [the abstract
remainder conditions](hyp:_hyps), [the observation-law bridge](hyp:h_law_W), [a
standard-deviation estimator](hyp:σ_hat_n), [a positive limiting standard deviation satisfying
the oracle second-moment identity](hyp:σ₀,_hσ₀_pos,_hσ_eq), [its consistency in
probability](hyp:_hσ_consistent), [measurability of the oracle score](hyp:h_ρ₀_meas), and
[the required estimator, oracle-sum, and studentized-statistic measurability
conditions](hyp:h_meas_θ,h_meas_sum,h_studentized_meas). Then [the studentized statistic
converges in distribution to the standard normal law](goal).

Given any standard-deviation-estimator sequence `σ_hat_n : ℕ → Ω → ℝ` satisfying
`σ̂_n →_p σ₀` and `σ₀ > 0`,

    √|B(n)| · (θ̂_n − θ₀) / σ̂_n  ⇒  N(0, 1).

A direct application of `Tendsto_dist.const_mul_tendsto_gaussian` to
`trae_dr_asymp_normal` plus Slutsky absorption of `1/σ̂_n` against the
constant `1/σ₀`. -/
theorem trae_dr_studentized
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    (hq₀ : S.DualSolution q₀)
    {P_W : Measure S.𝒲} [IsProbabilityMeasure P_W]
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (h_hat : ℕ → Ω → (S.𝒳 → ℝ))
    (q_hat : ℕ → Ω → (S.𝒵 → ℝ))
    (_hyps : TRAEDRRemainderHyps S hq₀ sample split h_hat q_hat)
    (h_law_W : μ.map S.W = P_W)
    (σ_hat_n : ℕ → Ω → ℝ) (σ₀ : ℝ)
    (_hσ₀_pos : 0 < σ₀)
    (_hσ_eq : σ₀ ^ 2 = ∫ w, (ρ₀ S q₀ w) ^ 2 ∂P_W)
    (_hσ_consistent : Tendsto_inProb σ_hat_n (fun _ => σ₀) μ)
    (h_ρ₀_meas : Measurable (ρ₀ S q₀))
    (h_meas_θ : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (trae_dr_estimator S sample split h_hat q_hat) S.θ₀ split.foldB n) μ)
    (h_meas_sum : ∀ n, AEMeasurable
      (IsAsymLinear.normalizedSum sample (ρ₀ S q₀) split.foldB n) μ)
    (h_studentized_meas : ∀ n, AEMeasurable
      (fun ω =>
        Real.sqrt ((split.foldB n).card : ℝ) *
          (trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀)
          / σ_hat_n n ω) μ) :
    Tendsto_dist
      (fun n ω =>
        Real.sqrt ((split.foldB n).card : ℝ) *
          (trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀)
          / σ_hat_n n ω)
      (gaussianMeasure 0 1)
      μ
      h_studentized_meas := by
  let Xn : ℕ → Ω → ℝ :=
    IsAsymLinear.rescaledEstimator
      (trae_dr_estimator S sample split h_hat q_hat) S.θ₀ split.foldB
  have hAN : Tendsto_dist Xn (gaussianMeasure 0 (σ₀ ^ 2)) μ h_meas_θ := by
    have h :=
      trae_dr_asymp_normal S hq₀ sample split h_hat q_hat _hyps h_law_W
        h_ρ₀_meas h_meas_θ h_meas_sum
    simpa [Xn, _hσ_eq] using h
  -- The studentized statistic is `Xn / σ̂ₙ`; apply the generic studentized CLT
  -- (`Tendsto_dist.div_tendsto_inProb_gaussian` in `Causalean/Stat/Studentize.lean`).
  have hdiv : ∀ n, AEMeasurable (fun ω => Xn n ω / σ_hat_n n ω) μ := by
    intro n
    simpa [Xn, IsAsymLinear.rescaledEstimator] using h_studentized_meas n
  have hres :=
    Tendsto_dist.div_tendsto_inProb_gaussian _hσ₀_pos h_meas_θ hAN
      _hσ_consistent hdiv
  simpa [Xn, IsAsymLinear.rescaledEstimator] using hres

/-! ## Wald-coverage transfer from an event-probability bridge -/

/-- **Wald-coverage transfer from a probability bridge.** For [an inverse-problem
system](hyp:S), [a dual solution `q₀`](hyp:hq₀), [an i.i.d. sample](hyp:sample),
[a one-shot split](hyp:split), [primal nuisance estimators](hyp:h_hat), and
[dual nuisance estimators](hyp:q_hat) [satisfying the TRAE-DR remainder
conditions](hyp:_hyps), assume [the sample's `W`-marginal is
`P_W`](hyp:h_law_W), [a standard-deviation-estimator sequence](hyp:σ_hat_n), [a limiting
standard deviation](hyp:σ₀), [its strict positivity](hyp:_hσ₀_pos), [the
oracle variance identity](hyp:_hσ_eq), [standard-deviation consistency in
probability](hyp:_hσ_consistent), and [measurability of `ρ₀`, the rescaled
estimator, its normalized-sum representation, and the studentized
statistic](hyp:h_ρ₀_meas,h_meas_θ,h_meas_sum,h_studentized_meas). For [a
cutoff](hyp:z), if [the Wald coverage
probability and the studentized interval probability become asymptotically
equal](hyp:h_wald_studentized), then [the Wald coverage probability converges
to the standard-normal mass on `[-z,z]`](goal).

The hypothesis `h_wald_studentized` is the event-rewrite/exceptional-set
bridge: it says the Wald coverage event and the studentized interval event
have asymptotically equal probabilities.  It is separated from the
distributional argument so callers can discharge it from positivity of
`σ̂_n` and the fold-B cardinality in the concrete estimator setup.

After the bridge is supplied, taking `z = z_{1-α/2}` gives asymptotic
coverage `1 − α` for the Wald interval

    θ̂_n ± z_{1-α/2} · σ̂_n / √|B(n)|.

The conclusion is phrased as a `Tendsto` on the coverage probability;
plugging in the standard-normal quantile is left to the user. -/
theorem trae_dr_wald_coverage_of_event_bridge
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    (hq₀ : S.DualSolution q₀)
    {P_W : Measure S.𝒲} [IsProbabilityMeasure P_W]
    (sample : IIDSample Ω S.𝒲 μ P_W)
    (split : OneShotSplit sample)
    (h_hat : ℕ → Ω → (S.𝒳 → ℝ))
    (q_hat : ℕ → Ω → (S.𝒵 → ℝ))
    (_hyps : TRAEDRRemainderHyps S hq₀ sample split h_hat q_hat)
    (h_law_W : μ.map S.W = P_W)
    (σ_hat_n : ℕ → Ω → ℝ) (σ₀ : ℝ)
    (_hσ₀_pos : 0 < σ₀)
    (_hσ_eq : σ₀ ^ 2 = ∫ w, (ρ₀ S q₀ w) ^ 2 ∂P_W)
    (_hσ_consistent : Tendsto_inProb σ_hat_n (fun _ => σ₀) μ)
    (h_ρ₀_meas : Measurable (ρ₀ S q₀))
    (h_meas_θ : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (trae_dr_estimator S sample split h_hat q_hat) S.θ₀ split.foldB n) μ)
    (h_meas_sum : ∀ n, AEMeasurable
      (IsAsymLinear.normalizedSum sample (ρ₀ S q₀) split.foldB n) μ)
    (h_studentized_meas : ∀ n, AEMeasurable
      (fun ω =>
        Real.sqrt ((split.foldB n).card : ℝ) *
          (trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀)
          / σ_hat_n n ω) μ)
    (z : ℝ)
    (h_wald_studentized : Tendsto
      (fun n =>
        (μ {ω | |trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀|
            ≤ z * σ_hat_n n ω / Real.sqrt ((split.foldB n).card : ℝ)}).toReal
        -
        (μ {ω |
          Real.sqrt ((split.foldB n).card : ℝ) *
            (trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀)
            / σ_hat_n n ω ∈ Set.Icc (-z) z}).toReal)
      atTop
      (𝓝 0)) :
    Tendsto
      (fun n =>
        (μ {ω | |trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀|
            ≤ z * σ_hat_n n ω / Real.sqrt ((split.foldB n).card : ℝ)}).toReal)
      atTop
      (𝓝 ((gaussianMeasure 0 1) (Set.Icc (-z) z)).toReal) := by
  let studentized : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((split.foldB n).card : ℝ) *
      (trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀)
      / σ_hat_n n ω
  let coverProb : ℕ → ℝ := fun n =>
    (μ {ω | |trae_dr_estimator S sample split h_hat q_hat n ω - S.θ₀|
        ≤ z * σ_hat_n n ω / Real.sqrt ((split.foldB n).card : ℝ)}).toReal
  let studProb : ℕ → ℝ := fun n =>
    (μ {ω | studentized n ω ∈ Set.Icc (-z) z}).toReal
  change Tendsto (fun n => coverProb n - studProb n) atTop (𝓝 0) at h_wald_studentized
  have hStud :
      Tendsto_dist studentized (gaussianMeasure 0 1) μ h_studentized_meas := by
    simpa [studentized] using
      trae_dr_studentized S hq₀ sample split h_hat q_hat _hyps
        h_law_W σ_hat_n σ₀ _hσ₀_pos _hσ_eq _hσ_consistent
        h_ρ₀_meas h_meas_θ h_meas_sum h_studentized_meas
  have hfrontier :
      gaussianMeasure 0 1 (frontier (Set.Icc (-z) z)) = 0 := by
    by_cases hz : 0 ≤ z
    · have hle : -z ≤ z := by linarith
      rw [frontier_Icc hle]
      rw [show ({-z, z} : Set ℝ) = {-z} ∪ {z} by ext x; simp [or_comm]]
      exact le_antisymm
        (by
          calc
            gaussianMeasure 0 1 (({-z} : Set ℝ) ∪ {z})
                ≤ gaussianMeasure 0 1 ({-z} : Set ℝ) +
                    gaussianMeasure 0 1 ({z} : Set ℝ) := measure_union_le _ _
            _ = 0 := by simp [gaussianMeasure_zero_one_singleton])
        zero_le
    · rw [Set.Icc_eq_empty (by linarith)]
      simp
  have hpm := Tendsto_dist.tendsto_measure_of_null_frontier
    h_studentized_meas hStud hfrontier
  have hstudent_event :
      Tendsto studProb atTop
        (nhds ((gaussianMeasure 0 1) (Set.Icc (-z) z)).toReal) := by
    refine hpm.congr' ?_
    filter_upwards with n
    rw [Measure.map_apply_of_aemeasurable (h_studentized_meas n) measurableSet_Icc]
    rfl
  have hsum := hstudent_event.add h_wald_studentized
  have hsum' : Tendsto (fun n => studProb n + (coverProb n - studProb n)) atTop
      (nhds ((gaussianMeasure 0 1) (Set.Icc (-z) z)).toReal) := by
    simpa using hsum
  refine (hsum'.congr' ?_)
  filter_upwards with n
  simp [coverProb]

end DR
end NPIV
end Estimation
end Causalean
