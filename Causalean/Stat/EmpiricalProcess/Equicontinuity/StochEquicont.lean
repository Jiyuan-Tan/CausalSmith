/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Stochastic equicontinuity of a score family at a point

Definition of estimator-indexed asymptotic (stochastic) equicontinuity,
`StochEquicontAt`: the empirical-process hypothesis controlling the centered
score-difference gap `R_n` along an estimator sequence `θn → θ₀`.  It is consumed
by the parametric `Z`-estimator expansion in `MEstimation/EmpiricalExpansion.lean`
and discharged from the class-level `AsymptoticEquicont` in
`Equicontinuity/Modulus.lean`.  It lives in the empirical-process layer (rather
than beside the M-estimation expansion) so the foundational equicontinuity
modules do not depend on the higher-level estimator machinery.

Causal-agnostic; candidate for upstream contribution to Mathlib.
-/

import Causalean.Stat.Sample
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Stochastic equicontinuity at a point

Provides `Causalean.Stat.StochEquicontAt`, the estimator-indexed asymptotic
equicontinuity property of a score family, used by the parametric `Z`-estimator
expansion and supplied from class-level equicontinuity. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On [a measurable observation space](hyp:X) and [a normed real vector space](hyp:E), for [a
score function taking a parameter and an observation to a vector](hyp:ψ), [a distinguished
parameter value](hyp:θ₀), [an observation-space measure](hyp:P), [a measurable sample space](hyp:Ω),
[a measure on that sample space](hyp:μ), [an independent
identically distributed sample with that observation law](hyp:S), and [a sequence of
sample-dependent parameter estimates](hyp:θn), the [stochastic equicontinuity property at the
distinguished parameter](goal) holds when, for every positive tolerance, there is [a positive
radius](step:1) such that [the probability of the stated large empirical-process gap while the
estimate lies within that radius converges to zero as the sample size tends to infinity](step:2).

The empirical-process gap is

  `R_n(ω) := (√n)⁻¹ • ∑_{i<n} (ψ(θn,Z_i) − ψ(θ₀,Z_i))
              − √n • ∫ (ψ(θn,·) − ψ(θ₀,·)) dP`

eventually has vanishing probability of exceeding `ε` on the event
`{‖θn − θ₀‖ < δ}`.  This is the standard "asymptotic equicontinuity"
package: under a Donsker condition for the class
`{ψ(·;θ) − ψ(·;θ₀) : ‖θ − θ₀‖ < δ}` together with `L²`-continuity at
`θ₀`, it follows from van der Vaart (1998), Lemma 19.24 / §19.4.  We
expose it as a hypothesis so applications can supply it from a Donsker,
chaining, or problem-specific empirical-process argument; see also the
chaining/Dudley infrastructure in
the concentration and empirical-process modules in this library.

The conditioning on `{‖θn − θ₀‖ < δ}` is removed downstream by combining
with the consistency hypothesis `hConsistent`. -/
def StochEquicontAt
    (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    Tendsto (fun n =>
      μ {ω | ‖θn n ω - θ₀‖ < δ ∧
              ε < ‖(Real.sqrt (n : ℝ))⁻¹ •
                    (∑ i ∈ Finset.range n,
                      (ψ (θn n ω) (S.Z i ω) - ψ θ₀ (S.Z i ω)))
                  - Real.sqrt (n : ℝ) •
                      ∫ z, (ψ (θn n ω) z - ψ θ₀ z) ∂P‖})
      atTop (𝓝 0)

end Causalean.Stat
