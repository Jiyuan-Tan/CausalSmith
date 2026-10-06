/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Consistency of extremum (M-)estimators

The separated-maximum consistency theorem for extremum estimators
(van der Vaart 1998, Theorem 5.7).  An
estimator `θ̂ₙ` that maximizes a sample criterion `θ ↦ Pₙ m(θ, ·)` is consistent
for the population maximizer `θ₀` of `θ ↦ P m(θ, ·)` provided

1. **uniform convergence** of the criterion (a Glivenko–Cantelli condition on
   the class `{m(θ, ·) : θ ∈ Θ}`), and
2. a **well-separated maximum**: outside every `ε`-ball around `θ₀` the
   population criterion stays bounded away from its value at `θ₀`.

The proof is the classical sandwich

    M(θ₀) − M(θ̂ₙ)
      = (M(θ₀) − Mₙ(θ₀)) + (Mₙ(θ₀) − Mₙ(θ̂ₙ)) + (Mₙ(θ̂ₙ) − M(θ̂ₙ))
      ≤ 2 · sup_θ |Mₙ(θ) − M(θ)|,

(the middle term is `≤ 0` because `θ̂ₙ` maximizes `Mₙ`), combined with the
separation gap `η`.  This file **consumes** the `GlivenkoCantelli` engine from
`GlivenkoCantelli.lean`: the uniform-convergence hypothesis is exactly
`WeakGlivenkoCantelli` for the criterion class `m`.
-/

module
public import Causalean.Stat.EmpiricalProcess.GlivenkoCantelli
public import Mathlib.Topology.MetricSpace.Basic

/-! # M-Estimator Consistency

This file proves consistency for extremum estimators from uniform convergence of the
sample criterion and a well-separated population maximum. It is the empirical-process
bridge from Glivenko-Cantelli classes to econometric consistency theorems.  The
theorem `mEstimator_consistent_of_glivenkoCantelli` consumes an abstract uniform
law, while `mEstimator_consistent_of_bracketing` supplies that law from finite
`L¹(P)` bracketing. -/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- **Separated-maximum consistency of extremum estimators** (van der Vaart 1998,
Theorem 5.7). Let `m` be a
criterion function of a parameter ranging over a pseudo-metric space `Θ`, with population
objective `M(θ)` equal to the expectation of `m(θ,·)` under `P` and sample objective the
empirical mean of `m(θ,·)` along an i.i.d. sample `S`. If [the criterion class
`{m(θ,·) : θ ∈ Θ}` obeys the Glivenko–Cantelli uniform law, so the worst-case gap between
the sample and population objectives vanishes in probability](hyp:hGC), [the estimator
sequence `thetaHat` attains the sample objective at `θ₀` up to an error that vanishes in
probability](hyp:hApprox,hSlack), and [the population
objective has a well-separated maximum at `θ₀`, meaning that for every `ε>0` there is a
gap `η>0` such that the objective at any `θ` at distance at least `ε` from `θ₀` falls short
of the objective at `θ₀` by at least `η`](hyp:hSep), then [`thetaHat` is consistent for
`θ₀`: for every `ε>0` the probability that `thetaHat n` lies at distance at least `ε` from
`θ₀` tends to zero as the sample size `n` grows](goal). -/
theorem mEstimator_consistent_of_glivenkoCantelli
    {Θ : Type*} [PseudoMetricSpace Θ]
    (S : IIDSample Ω X μ P) (m : Θ → X → ℝ) (θ₀ : Θ)
    (thetaHat : ℕ → Ω → Θ)
    (hGC : WeakGlivenkoCantelli S m)
    (slack : ℕ → Ω → ℝ)
    (hSlack : Tendsto_inProb slack (fun _ => 0) μ)
    (hApprox : ∀ n ω,
      S.sampleMean (m θ₀) n ω ≤ S.sampleMean (m (thetaHat n ω)) n ω + slack n ω)
    (hSep : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ θ : Θ, ε ≤ dist θ θ₀ → (∫ x, m θ x ∂P) + η ≤ ∫ x, m θ₀ x ∂P) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ε ≤ dist (thetaHat n ω) θ₀}) atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨η, hη, hsep⟩ := hSep ε hε
  have hη3 : 0 < η / 3 := by linarith
  -- A distant approximate maximizer forces either a uniform deviation or a large slack.
  have hsub : ∀ n, {ω | ε ≤ dist (thetaHat n ω) θ₀}
      ⊆ {ω | ∃ θ, η / 3 ≤ |S.sampleMean (m θ) n ω - ∫ x, m θ x ∂P|} ∪
        {ω | η / 3 ≤ |slack n ω|} := by
    intro n ω hω
    have hfar : ε ≤ dist (thetaHat n ω) θ₀ := hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_le] at hcon
    have h0 := abs_lt.mp (hcon.1 θ₀)
    have h1 := abs_lt.mp (hcon.1 (thetaHat n ω))
    have hr := abs_lt.mp hcon.2
    have ha := hApprox n ω
    have hs := hsep (thetaHat n ω) hfar
    linarith [h0.1, h0.2, h1.1, h1.2, hr.1, hr.2, ha, hs]
  have hSlackTail : Tendsto (fun n => μ {ω | η / 3 ≤ |slack n ω|}) atTop (nhds 0) := by
    have h := (tendstoInMeasure_iff_norm.mp hSlack) (η / 3) hη3
    simpa [Real.norm_eq_abs] using h
  have hbad : Tendsto (fun n =>
      μ {ω | ∃ θ, η / 3 ≤ |S.sampleMean (m θ) n ω - ∫ x, m θ x ∂P|} +
        μ {ω | η / 3 ≤ |slack n ω|}) atTop (nhds 0) := by
    simpa using (hGC (η / 3) hη3).add hSlackTail
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    hbad (Eventually.of_forall fun n => zero_le)
    (Eventually.of_forall fun n =>
      (measure_mono (hsub n)).trans (measure_union_le _ _))

/-- **Bracketing corollary** (the econometrician's headline). Let `m` be a criterion
function of a parameter ranging over a pseudo-metric space `Θ`, observed along an
i.i.d. sample `S` drawn from `P`. If [each `m(θ,·)` is measurable](hyp:hmeas), [the
criterion class has, for every target width, a finite collection of integrable
upper/lower bracket functions sandwiching the class members almost everywhere with
`L¹(P)`-gap at most that width](hyp:hbr), [the estimator sequence `thetaHat` attains a
sample-objective value at every sample size and outcome that is at least as large as the
sample objective at `θ₀` up to an error vanishing in probability](hyp:hApprox,hSlack),
and [the population objective has a well-separated
maximum at `θ₀`, meaning that for every `ε>0` there is a gap `η>0` such that the objective
at any `θ` at distance at least `ε` from `θ₀` falls short of the objective at `θ₀` by at
least `η`](hyp:hSep), then [`thetaHat` is consistent for `θ₀`: for every `ε>0` the
probability that `thetaHat n` lies at distance at least `ε` from `θ₀` tends to zero as the
sample size `n` grows](goal).

Pure composition of `glivenkoCantelli_of_hasL1Bracketing` (which discharges the
uniform-LLN hypothesis) with `mEstimator_consistent_of_glivenkoCantelli`. -/
theorem mEstimator_consistent_of_bracketing
    {Θ : Type*} [PseudoMetricSpace Θ] [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) (m : Θ → X → ℝ) (θ₀ : Θ)
    (thetaHat : ℕ → Ω → Θ)
    (hmeas : ∀ θ, Measurable (m θ))
    (hbr : HasL1Bracketing m P)
    (slack : ℕ → Ω → ℝ)
    (hSlack : Tendsto_inProb slack (fun _ => 0) μ)
    (hApprox : ∀ n ω,
      S.sampleMean (m θ₀) n ω ≤ S.sampleMean (m (thetaHat n ω)) n ω + slack n ω)
    (hSep : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ θ : Θ, ε ≤ dist θ θ₀ → (∫ x, m θ x ∂P) + η ≤ ∫ x, m θ₀ x ∂P) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ε ≤ dist (thetaHat n ω) θ₀}) atTop (𝓝 0) :=
  mEstimator_consistent_of_glivenkoCantelli S m θ₀ thetaHat
    (glivenkoCantelli_of_hasL1Bracketing S m hmeas hbr) slack hSlack hApprox hSep

end Causalean.Stat
