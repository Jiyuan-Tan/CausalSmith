/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Integrated target-derivative difference for a `LearningSystem`

`Bias_n` packages the difference between two population integrals of bundled
pointwise target-direction derivatives: one at the true nuisance and one at a
plug-in nuisance. It does not identify either integral with a directional
derivative of the population risk. Such an identification requires a separate
limit--integral interchange theorem.

See `doc/basic_concepts/po/estimation/orthogonal_statistical_learning.tex`,
`def:est-osl-second-order-bias`.
-/

module
public import Causalean.Estimation.OrthogonalLearning.Population.DirectionalDeriv

/-! # Integrated Target-Derivative Difference in Orthogonal Statistical Learning

This file defines the nuisance-induced bias term for a sample-split
orthogonal statistical learning system. The term compares the integrated
target-direction derivative at the true nuisance with the corresponding
integrated pointwise derivative at a plug-in nuisance.

The exported definition is `Bias_n`. Relating it to a population-risk
derivative or to a quantitative Taylor expansion requires additional analytic
bridges that are not exported here. -/

@[expose] public section

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- The [integrated pointwise target-derivative difference](goal) measures, in
[an orthogonal statistical-learning system](hyp:S), how the integrated derivative data at
[the true nuisance](hyp:Dθ_truth) changes when replaced by [derivative data at a plug-in
nuisance](hyp:Dθ_at_ghat), evaluated at [a target estimate](hyp:θhat). It is the first population
integral minus the corresponding plug-in integral.

Integrated pointwise target-derivative difference for a sample-split plug-in ERM.

Given:
* `S`            — orthogonal statistical-learning system,
* `Dθ_truth`     — target-direction DD bundle anchored at the *true*
                   nuisance `g₀`,
* `Dθ_at_ghat`   — target-direction DD bundle anchored at the *plug-in*
                   nuisance `g` (typically `ĝ_n ω`),
* `θhat`         — plug-in target estimator,

`Bias_n` returns
`(∫ z, Dθ_truth.dℓ_θ θhat z ∂P_Z) - (∫ z, Dθ_at_ghat.dℓ_θ θhat z ∂P_Z)`.

No equality with a directional derivative of the integrated population risk is asserted
without a separate limit--integral interchange theorem. -/
noncomputable def Bias_n
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (Dθ_truth : HasDirDerivTheta S S.g₀)
    {g : G} (Dθ_at_ghat : HasDirDerivTheta S g)
    (θhat : Θ) : ℝ :=
  (∫ z, Dθ_truth.dℓ_θ θhat z ∂P_Z)
    - (∫ z, Dθ_at_ghat.dℓ_θ θhat z ∂P_Z)

/-
The note's `def:est-osl-second-order-bias` records the second-order Taylor identity
  `Bias_n(g) = -(1/2) D_g² D_θ L(θ₀, ḡ)[θhat - θ₀, g - g₀, g - g₀]`
for some path point `ḡ` between `g₀` and `g`. Relating the formal `Bias_n` to that
identity first requires a limit--integral bridge; formalising the expansion also requires a
second-order DD bundle `D²_g` and a one-dimensional Taylor formula on the integrated risk.
These are deferred. No vacuous existential Taylor-form witness is exported here; the concrete
integral product bound lives in
`Estimation/CATE/OrthogonalLearning/SecondOrderBias.lean`.
-/

end OrthogonalLearning
end Estimation
end Causalean
