/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Z- / M-estimator regularity (parametric inference workhorse, structure layer)

Regularity bundle `ZEstimatorRegularity` for the parametric Z/M-estimator CLT
(`def:par-z-clt`).  The headline theorem `zEstimator_asymLinear` lives downstream in
`Causalean/Stat/MEstimation/ZEstimatorCLT.lean` because its proof pulls in
`Causalean/Stat/MEstimation/EmpiricalExpansion.lean`, which in turn imports this file for
`ZEstimatorRegularity`.  Splitting the structure (here) from the theorem (in
`ZEstimatorCLT.lean`) keeps the import DAG acyclic.

Reference: van der Vaart (1998), §5.6, Theorem 5.41; Newey & McFadden (1994).
Spec: `def:par-smoothness`, `thm:par-z-clt` in
`doc/basic_concepts/Semi-parametric Inference/parametric_inference.tex`.
-/

module
public import Causalean.Stat.CLT.AsymptoticLinearity
public import Causalean.Stat.Limit.Convergence
public import Causalean.Stat.Sample
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-! # Z-estimator regularity

This module records the public regularity bundle `ZEstimatorRegularity` for
parametric Z-estimator and M-estimator central limit theorems.  The structure
collects population identification, derivative invertibility, finite variance,
measurability, and local integrability. Empirical-process control is supplied
separately by the smooth-score, local-Lipschitz, or high-level stochastic-
equicontinuity routes.
-/

@[expose] public section


namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Regularity conditions** for the Z-estimator central limit theorem. Bundles, for a score
function and target parameter θ₀ under a sampling law, [the population identification condition
that the score vanishes in mean at the truth](hyp:identification), [a Jacobian of the population
score at θ₀ together with a witnessed inverse](hyp:J₀,J₀_inv,J₀_inverse,J₀_spec), [finite
variance of the score at the truth](hyp:finite_var), [measurability of the score at every
parameter value](hyp:psi_meas), and [local integrability of the score on a neighborhood of
θ₀](hyp:psi_int_neighborhood).

Existing fields (population identification + smoothness + measurability):

* `identification`     : `∫ ψ(z; θ₀) dP = 0` (population moment vanishes at the
                          truth).
* `J₀`                 : Jacobian of the population moment at `θ₀`,
                          `J₀ := ∂_θ ∫ ψ(z; θ) dP |_{θ=θ₀}`.
* `J₀_inv`             : inverse of `J₀`.
* `J₀_inverse`         : witness `J₀ ∘ J₀_inv = id`.
* `J₀_spec`            : `J₀` is the Fréchet derivative of
                          `θ ↦ ∫ ψ(z; θ) dP` at `θ₀`.
* `finite_var`         : `∫ ‖ψ(z; θ₀)‖² dP < ∞`.
* `psi_meas`           : `ψ(·; θ)` is measurable for every `θ`.

* `psi_int_neighborhood` : `ψ(·;θ)` is `P`-integrable on a neighborhood of
                            `θ₀`, ensuring `∫ ψ(·;θ) dP` is well-defined for
                            all `θ` close enough to `θ₀`.

No observationwise smoothness or Lipschitz envelope is bundled here. This is
deliberate: Newey--McFadden (1994), Theorem 7.2, and the estimator-indexed
conclusion of van der Vaart (1998), Lemma 19.24, cover nonsmooth scores through
an external `StochEquicontAt` hypothesis. -/
structure ZEstimatorRegularity
    (ψ : E → X → E) (θ₀ : E) (P : Measure X) where
  identification : ∫ z, ψ θ₀ z ∂P = 0
  J₀             : E →L[ℝ] E
  J₀_inv         : E →L[ℝ] E
  J₀_inverse     : J₀.comp J₀_inv = ContinuousLinearMap.id ℝ E
  J₀_spec        : HasFDerivAt (fun θ => ∫ z, ψ θ z ∂P) J₀ θ₀
  finite_var     : Integrable (fun z => ‖ψ θ₀ z‖^2) P
  psi_meas       : ∀ θ, Measurable (ψ θ)
  /-- `ψ(·;θ)` is `P`-integrable on a neighborhood of `θ₀`. -/
  psi_int_neighborhood :
    ∃ δ : ℝ, 0 < δ ∧ ∀ θ : E, ‖θ - θ₀‖ < δ → Integrable (ψ θ) P

end Causalean.Stat
