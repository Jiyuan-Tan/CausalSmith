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

module
public import Causalean.Stat.Sample
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Stochastic equicontinuity at a point

Provides `Causalean.Stat.StochEquicontAt`, the estimator-indexed asymptotic
equicontinuity property of a score family, used by the parametric `Z`-estimator
expansion and supplied from class-level equicontinuity. -/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {X Θ V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- [Stochastic equicontinuity at the distinguished parameter](goal) says that
the centered empirical-process gap along [a sequence of sample-dependent
estimates](hyp:θn) becomes negligible whenever the estimates remain near [the
reference parameter](hyp:θ₀).  For [a vector-valued score family](hyp:ψ) on [a
measurable observation space](hyp:X) with [normed output](hyp:V), [population
law](hyp:P), [measurable sample space and law](hyp:Ω,μ), and [an i.i.d.
sample](hyp:S), every positive tolerance admits [a positive radius](step:1) for
which [the corresponding large-gap probability tends to zero](step:2).

This is the estimator-indexed conclusion form of van der Vaart (1998), Lemma
19.24: class-level asymptotic equicontinuity, evaluated along a consistent
random index, makes the centered empirical-process increment negligible. It is
not Newey--McFadden (1994), Theorem 7.2(v)'s normalized-supremum assumption.

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
    (ψ : Θ → X → V) (θ₀ : Θ) (P : Measure X)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → Θ) : Prop :=
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
