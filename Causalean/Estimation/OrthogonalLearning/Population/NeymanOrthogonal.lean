/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Neyman orthogonality of an orthogonal statistical-learning loss

`NeymanOrthogLoss S Dθ Dg M` says the *integrated* mixed directional
derivative `∫ M.dℓ_θg θ g z dP_Z` vanishes for every admissible target
direction `θ ∈ Θ_set` and nuisance direction `g ∈ G_set`.  This is the
loss-side analogue of `Estimation.OrthogonalMoments.NeymanOrthogonal`.

We also state difference-quotient envelope predicates
`DiffQuotientEnvelopeTheta` and `DiffQuotientEnvelopeG` for the two coordinate
directions, mirroring `Estimation.OrthogonalMoments.DiffQuotientEnvelope`.
They record domination conditions for future limit--integral bridges; no
theorem below derives such a bridge from these predicates.

Finally, `neymanOrthog_iff_score_deriv_zero` reformulates orthogonality in
terms of the map from a nuisance value to the integral of the bundled
pointwise target derivative. The required nuisance-direction limit--integral
swap is packaged as `MixedScoreDCTBridge`. Identifying this integral-valued
map with a derivative of the population risk would additionally require a
target-direction limit--integral bridge, which is not proved here.

See `doc/basic_concepts/po/estimation/orthogonal_statistical_learning.tex`,
`def:est-osl-neyman-loss`.
-/

module
public import Causalean.Estimation.OrthogonalLearning.Population.DirectionalDeriv

/-! # Neyman Orthogonality for Losses

This file formulates Neyman orthogonality for an orthogonal
statistical-learning loss as the vanishing of the integrated mixed directional
derivative in every admissible target and nuisance direction. It also records
domination predicates intended for limit--integral interchange arguments.

The main predicate is `NeymanOrthogLoss`. The auxiliary predicates
`DiffQuotientEnvelopeTheta`, `DiffQuotientEnvelopeG`, and `MixedScoreDCTBridge`
package dominated-convergence hypotheses, and
`neymanOrthog_iff_score_deriv_zero` proves the score-derivative reformulation
under the bridge hypothesis. -/

@[expose] public section

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- For [an orthogonal statistical-learning system](hyp:S) and
[mixed target--nuisance derivative data](hyp:M), the
[Neyman-orthogonality condition for the loss](goal) states that every admissible target and
nuisance direction has zero observation-law integral of its mixed directional derivative.

Neyman orthogonality of the loss: for every admissible target and
nuisance direction, the integrated mixed directional derivative at
`(θ₀, g₀)` vanishes. -/
def NeymanOrthogLoss
    (S : LearningSystem Ω μ Z P_Z Θ G) (M : HasMixedDirDeriv S) : Prop :=
  ∀ θ ∈ S.Θ_set, ∀ g ∈ S.G_set, ∫ z, M.dℓ_θg θ g z ∂P_Z = 0

/-- For [an orthogonal statistical-learning system](hyp:S) and
[a nuisance function](hyp:g), the
[target-direction difference-quotient envelope condition](goal) gives each candidate target
[a positive neighborhood radius](step:1) and an integrable envelope that bounds the absolute
loss difference quotient almost everywhere for every smaller nonzero perturbation.

L¹(P_Z) envelope dominating the *target-direction* difference quotient
of the loss locally near `t = 0`, uniformly in `θ ∈ Θ_set`.  Mirrors
`Estimation.OrthogonalMoments.DiffQuotientEnvelope`. -/
def DiffQuotientEnvelopeTheta
    (S : LearningSystem Ω μ Z P_Z Θ G) (g : G) : Prop :=
  ∀ θ ∈ S.Θ_set, ∃ δ : ℝ, 0 < δ ∧ ∃ env : Z → ℝ,
    Integrable env P_Z ∧
    ∀ᵐ z ∂P_Z, ∀ t : ℝ, t ∈ Set.Ioo (-δ) δ → t ≠ 0 →
      ‖(S.ℓ z (S.θ₀ + t • (θ - S.θ₀)) g - S.ℓ z S.θ₀ g) / t‖ ≤ env z

/-- For [an orthogonal statistical-learning system](hyp:S), the
[nuisance-direction difference-quotient envelope condition](goal) gives each admissible nuisance
[a positive neighborhood radius](step:1) and an integrable envelope that bounds the absolute
loss difference quotient almost everywhere for every smaller nonzero perturbation.

L¹(P_Z) envelope dominating the *nuisance-direction* difference quotient
of the loss locally near `t = 0`, uniformly in `g ∈ G_set`.  Mirrors
`Estimation.OrthogonalMoments.DiffQuotientEnvelope`. -/
def DiffQuotientEnvelopeG
    (S : LearningSystem Ω μ Z P_Z Θ G) : Prop :=
  ∀ g ∈ S.G_set, ∃ δ : ℝ, 0 < δ ∧ ∃ env : Z → ℝ,
    Integrable env P_Z ∧
    ∀ᵐ z ∂P_Z, ∀ t : ℝ, t ∈ Set.Ioo (-δ) δ → t ≠ 0 →
      ‖(S.ℓ z S.θ₀ (S.g₀ + t • (g - S.g₀)) - S.ℓ z S.θ₀ S.g₀) / t‖ ≤ env z

/-- For [an orthogonal statistical-learning system](hyp:S) and
[mixed target--nuisance derivative data](hyp:M), the
[mixed-derivative limit--integral bridge](goal) says the integrated centered quotient along
every admissible nuisance perturbation tends to the integral of the corresponding mixed
directional derivative.

DCT-bridge hypothesis for the score reformulation: for every admissible
target direction `ν_θ = θ - θ₀` and nuisance direction `ν_g = g - g₀`,
the integrated centred difference quotient of the target dir derivatives
along the nuisance perturbation tends to the integrated mixed dir
derivative `∫ z, M.dℓ_θg θ g z ∂P_Z` as `t → 0` along `𝓝[≠] 0`.

A concrete sufficient envelope for these target-derivative difference
quotients is not supplied here. We package the limit conclusion directly as a
hypothesis so that the integrated-derivative reformulation can be stated
abstractly. -/
def MixedScoreDCTBridge
    (S : LearningSystem Ω μ Z P_Z Θ G) (M : HasMixedDirDeriv S) : Prop :=
  ∀ θ ∈ S.Θ_set, ∀ g ∈ S.G_set,
    Tendsto (fun t : ℝ =>
      ((∫ z, (M.Dθ_at (S.g₀ + t • (g - S.g₀))).dℓ_θ θ z ∂P_Z)
        - (∫ z, (M.Dθ_at S.g₀).dℓ_θ θ z ∂P_Z)) / t)
      (𝓝[≠] 0) (𝓝 (∫ z, M.dℓ_θg θ g z ∂P_Z))

/-- **Integrated-derivative reformulation of Neyman orthogonality.** Assume
[the stated limit--integral bridge for the bundled derivatives](hyp:hBridge). Then
[Neyman orthogonality is equivalent to zero directional derivative of the integrated map](goal)
for every admissible target and nuisance direction.

Operationally, this is the statement that the difference quotient
`((Dθ_at(g₀ + t • (g - g₀))).dℓ_θ θ z - (Dθ_at g₀).dℓ_θ θ z) / t`
integrates to zero in the limit `t → 0` for every admissible `(θ, g)`,
which is exactly `NeymanOrthogLoss S M` after bridging through the mixed
DD bundle `M`.

The bridge between the integrated centred difference quotient and
`∫ z, M.dℓ_θg θ g z ∂P_Z` (DCT swap) is captured by
`MixedScoreDCTBridge S M`; under that hypothesis the iff is a routine
limit-uniqueness argument. -/
theorem neymanOrthog_iff_score_deriv_zero
    (S : LearningSystem Ω μ Z P_Z Θ G) (M : HasMixedDirDeriv S)
    (hBridge : MixedScoreDCTBridge S M) :
    NeymanOrthogLoss S M ↔
      ∀ θ ∈ S.Θ_set, ∀ g ∈ S.G_set,
        Tendsto (fun t : ℝ =>
          ((∫ z, (M.Dθ_at (S.g₀ + t • (g - S.g₀))).dℓ_θ θ z ∂P_Z)
           - (∫ z, (M.Dθ_at S.g₀).dℓ_θ θ z ∂P_Z)) / t)
          (𝓝[≠] 0) (𝓝 0) := by
  refine ⟨?_, ?_⟩
  · intro hNO θ hθ g hg
    have hbr := hBridge θ hθ g hg
    have hzero : (∫ z, M.dℓ_θg θ g z ∂P_Z) = 0 := hNO θ hθ g hg
    simpa [hzero] using hbr
  · intro hScore θ hθ g hg
    have hbr := hBridge θ hθ g hg
    have hScr := hScore θ hθ g hg
    haveI : (𝓝[≠] (0 : ℝ)).NeBot := NormedField.nhdsNE_neBot 0
    exact tendsto_nhds_unique hbr hScr

end OrthogonalLearning
end Estimation
end Causalean
