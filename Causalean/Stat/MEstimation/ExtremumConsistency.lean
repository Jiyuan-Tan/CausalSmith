/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Discharging Z-estimator consistency for asymptotic linearity

The headline parametric-inference theorem `zEstimator_asymLinear`
(`Causalean/Stat/MEstimation/ZEstimatorCLT.lean`) assumes the estimator is
consistent,

    hConsistent : ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω − θ₀‖}) atTop (𝓝 0),

as a black-box input. Classically (Newey–McFadden 1994, Theorem 2.1; van der
Vaart 1998, Theorem 5.7) consistency is derived from primitive conditions on the
optimisation problem: a **Glivenko–Cantelli** criterion class plus a
**well-separated population maximum**. This file connects those extremum
conditions to Z-estimator asymptotic linearity. These reductions conclude
asymptotic linearity, not a central limit theorem.

The direct `hConsistent`-taking statements remain available for callers who
establish consistency by other means.

* `consistent_lt_norm_of_le_dist` — format bridge: turn the consistency
  conclusion of the empirical-process layer (`ε ≤ dist (θ̂ n) θ₀`) into the
  `ε < ‖θ̂ n − θ₀‖` form the CLT layer consumes.  Pure metric/squeeze argument.
* `zEstimator_asymLinear_of_extremum` — the Z-estimator asymptotic-linear result with `hConsistent`
  replaced by an extremum-consistency package `(m, hGC, hArgmax, hSep)`: the
  estimator is a sample maximiser of a Glivenko–Cantelli criterion `m` whose
  population maximum is well separated at `θ₀`.  (Typically `ψ = ∂m/∂θ`, so the
  same estimator satisfies the score FOC `hMoment` and the argmax condition
  `hArgmax`; we keep `m` and `ψ` as independent inputs so the reduction needs no
  differentiability bookkeeping.)

The parallel GMM reductions reuse
`consistent_lt_norm_of_le_dist` from here but live beside `oracleGMM_asymLinear`
in `Causalean/Stat/GMM/AsymptoticNormality.lean`.
-/

module
public import Causalean.Stat.MEstimation.ZEstimatorCLT
public import Causalean.Stat.EmpiricalProcess.MEstimatorConsistency
public import Causalean.Stat.EmpiricalProcess.Equicontinuity.Modulus

/-! # Extremum consistency for M-estimation

This module packages primitive extremum-estimation conditions that imply the
consistency assumptions used by Z-estimator and GMM asymptotic-linearity results.  The
format bridge `consistent_lt_norm_of_le_dist` adapts the empirical-process
consistency theorem to the linearization layer, while `zEstimator_asymLinear_of_extremum`,
`zEstimator_asymLinear_of_asymptoticEquicont`, and
`zEstimator_asymLinear_of_extremum_asymptoticEquicont` discharge
opaque consistency and equicontinuity hypotheses from Glivenko-Cantelli,
well-separated-optimum, and class-level equicontinuity inputs.  (The parallel GMM
reductions live in `Causalean/Stat/GMM/AsymptoticNormality.lean`.)
-/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- **Format bridge.**  On a normed group `dist x θ₀ = ‖x − θ₀‖`, so the
consistency statement produced by `mEstimator_consistent_of_glivenkoCantelli`
(phrased with `ε ≤ dist (θn n) θ₀`) implies the strictly-larger-radius form
`ε < ‖θn n − θ₀‖` consumed by the CLT layer.  `{ε < ‖·‖} ⊆ {ε ≤ dist}`, so the
measures are squeezed to `0`. -/
theorem consistent_lt_norm_of_le_dist {E : Type*} [NormedAddCommGroup E]
    (θn : ℕ → Ω → E) (θ₀ : E)
    (h : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ε ≤ dist (θn n ω) θ₀}) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0) := by
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h ε hε)
    (Eventually.of_forall fun n => zero_le)
    (Eventually.of_forall fun n => measure_mono ?_)
  intro ω hω
  simp only [Set.mem_setOf_eq, dist_eq_norm] at hω ⊢
  exact le_of_lt hω

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Z-estimator asymptotic linearity from extremum primitives.**  Identical conclusion to
`zEstimator_asymLinear`,
but with consistency derived rather than assumed: given an auxiliary criterion function `m`,
suppose [the criterion class indexed by the parameter obeys a uniform law of large numbers, i.e.
is Glivenko–Cantelli](hyp:hGC), [the estimator approximately maximises the empirical criterion
with a slack vanishing in probability](hyp:hApprox,hSlack), and [the population criterion has a well-separated maximum at the
target parameter](hyp:hSep). Then, provided [the score process is stochastically equicontinuous
at the target parameter along the estimator sequence](hyp:hStochEquicont), [the estimator
has a normalized empirical-score residual that is negligible in
probability](hyp:hMoment), then [the estimator is
asymptotically linear at the target parameter, with influence function minus the inverse
Jacobian applied to the score at the target](goal).

Consistency `θn →_p θ₀` is derived via `mEstimator_consistent_of_glivenkoCantelli` and fed to
`zEstimator_asymLinear`; the remaining inputs are otherwise unchanged from
`zEstimator_asymLinear`. -/
theorem zEstimator_asymLinear_of_extremum
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : ZEstimatorRegularity ψ θ₀ P)
    [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (m : E → X → ℝ)
    (hGC : WeakGlivenkoCantelli S m)
    (slack : ℕ → Ω → ℝ)
    (hSlack : Tendsto_inProb slack (fun _ => 0) μ)
    (hApprox : ∀ n ω,
      S.sampleMean (m θ₀) n ω ≤ S.sampleMean (m (θn n ω)) n ω + slack n ω)
    (hSep : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ θ : E, ε ≤ dist θ θ₀ → (∫ x, m θ x ∂P) + η ≤ ∫ x, m θ₀ x ∂P)
    (hStochEquicont : StochEquicontAt ψ θ₀ P μ S θn)
    (hMoment : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ) :
    IsAsymLinearVec (E := E) θn θ₀
      (fun z => -(reg.J₀_inv (ψ θ₀ z))) S (fun n => Finset.range n) :=
  zEstimator_asymLinear ψ θ₀ P reg S θn
    (consistent_lt_norm_of_le_dist θn θ₀
      (mEstimator_consistent_of_glivenkoCantelli S m θ₀ θn hGC slack hSlack hApprox hSep))
    hStochEquicont hMoment

/-- **Z-estimator asymptotic linearity with the equicontinuity hypothesis discharged.** If
[the estimator converges in probability to the target](hyp:hConsistent),
[the score family is locally asymptotically equicontinuous](hyp:hAEC), and
[the normalized empirical-score residual is negligible in probability](hyp:hMoment), then
[the estimator is asymptotically linear with the inverse-Jacobian score influence function](goal).

This has the same conclusion as `zEstimator_asymLinear`; its estimator-specific
stochastic-equicontinuity hypothesis is reconstructed from `hAEC` and consistency via
`stochEquicontAt_of_asymptoticEquicont`. -/
theorem zEstimator_asymLinear_of_asymptoticEquicont
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : ZEstimatorRegularity ψ θ₀ P)
    [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0))
    (hAEC : AsymptoticEquicont ψ θ₀ P μ S)
    (hMoment : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ) :
    IsAsymLinearVec (E := E) θn θ₀
      (fun z => -(reg.J₀_inv (ψ θ₀ z))) S (fun n => Finset.range n) :=
  zEstimator_asymLinear ψ θ₀ P reg S θn hConsistent
    (stochEquicontAt_of_asymptoticEquicont ψ θ₀ S θn hAEC hConsistent)
    hMoment

/-- **Z-estimator asymptotic linearity from primitive conditions: both opaque hypotheses
discharged.** If [the criterion class is Glivenko–Cantelli](hyp:hGC),
[the estimator approximately maximizes it with vanishing slack](hyp:hApprox,hSlack),
[the population criterion has a well-separated target maximum](hyp:hSep),
[the score family is locally asymptotically equicontinuous](hyp:hAEC), and
[the normalized empirical-score residual is negligible in probability](hyp:hMoment), then
[the estimator is asymptotically linear with the inverse-Jacobian score influence function](goal).

This combines `zEstimator_asymLinear_of_extremum` and
`zEstimator_asymLinear_of_asymptoticEquicont`. Neither consistency nor
estimator-specific stochastic equicontinuity is assumed directly. -/
theorem zEstimator_asymLinear_of_extremum_asymptoticEquicont
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (reg : ZEstimatorRegularity ψ θ₀ P)
    [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (m : E → X → ℝ)
    (hGC : WeakGlivenkoCantelli S m)
    (slack : ℕ → Ω → ℝ)
    (hSlack : Tendsto_inProb slack (fun _ => 0) μ)
    (hApprox : ∀ n ω,
      S.sampleMean (m θ₀) n ω ≤ S.sampleMean (m (θn n ω)) n ω + slack n ω)
    (hSep : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ θ : E, ε ≤ dist θ θ₀ → (∫ x, m θ x ∂P) + η ≤ ∫ x, m θ₀ x ∂P)
    (hAEC : AsymptoticEquicont ψ θ₀ P μ S)
    (hMoment : IsLittleOp
      (fun n ω => ‖(Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, ψ (θn n ω) (S.Z i ω)‖)
      (fun _ => (1 : ℝ)) μ) :
    IsAsymLinearVec (E := E) θn θ₀
      (fun z => -(reg.J₀_inv (ψ θ₀ z))) S (fun n => Finset.range n) :=
  have hcons := consistent_lt_norm_of_le_dist θn θ₀
    (mEstimator_consistent_of_glivenkoCantelli S m θ₀ θn hGC slack hSlack hApprox hSep)
  zEstimator_asymLinear ψ θ₀ P reg S θn hcons
    (stochEquicontAt_of_asymptoticEquicont ψ θ₀ S θn hAEC hcons)
    hMoment

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

-- The GMM analogues of the Z-estimator CLT corollaries
-- (`gmm_asymLinear_of_extremum` / `_of_asymptoticEquicont` /
-- `_of_extremum_asymptoticEquicont`)
-- now live beside `oracleGMM_asymLinear` in
-- `Causalean/Stat/GMM/AsymptoticNormality.lean`, so this M-estimation module no
-- longer depends on the GMM layer.

end Causalean.Stat
