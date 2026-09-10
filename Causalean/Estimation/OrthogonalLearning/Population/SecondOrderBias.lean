/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Second-order nuisance bias for a `LearningSystem`

`Bias_n` packages the loss-gradient nuisance bias from
`def:est-osl-second-order-bias`:

  `Bias_n(g) := D_θL(θ₀, g₀)[θ̂ - θ₀]  -  D_θL(θ₀, g)[θ̂ - θ₀]`.

Note on bookkeeping.  The natural-language definition refers to the
directional derivative of the *population risk* `L` at `(θ₀, g)` in the
direction `θ̂ - θ₀`.  In our formalisation, this quantity is captured by
`HasDirDerivTheta S g`'s integrated derivative
`∫ z, (Dθ_at_g).dℓ_θ θ̂ z ∂P_Z`: by construction of `HasDirDerivTheta`,
`(Dθ_at_g).dℓ_θ θ z` is the value of the dir derivative at `(θ₀, g)` in
the direction `θ - θ₀`, so evaluating at `θ = θ̂` gives the desired
quantity (this is what "directional derivative along `θ₀ → θ̂`" means).

The optional theorem `Bias_taylor_form` records the second-order Taylor
identity from the note as an existential witness.  A later, more quantitative
API can refine this with a concrete `(1/2) D_g² D_θ L` representation once a
`SecondOrderDirDeriv` bundle is available.

See `doc/basic_concepts/po/estimation/orthogonal_statistical_learning.tex`,
`def:est-osl-second-order-bias`.
-/

import Causalean.Estimation.OrthogonalLearning.Population.DirectionalDeriv

/-! # Second-Order Bias in Orthogonal Statistical Learning

This file defines the nuisance-induced bias term for a sample-split
orthogonal statistical learning system. The term compares the integrated
target-direction derivative at the true nuisance with the corresponding
derivative at a plug-in nuisance, and the file records the intended
second-order Taylor representation.

The exported definition is `Bias_n`, the difference between the target-gradient
population-risk derivative at the true nuisance and at the plug-in nuisance,
evaluated in the estimator direction. The quantitative Taylor expansion is
documented as a later API extension rather than exported here. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- For [an orthogonal statistical-learning system](hyp:S), [a target-direction derivative bundle at its true nuisance function](hyp:Dθ_truth), [a target-direction derivative bundle at a nuisance function](hyp:Dθ_at_ghat), and [a target estimate](hyp:θhat), the [loss-gradient nuisance bias](goal) is the population integral of the first bundle evaluated at the target estimate minus the corresponding population integral of the second bundle.

Loss-gradient nuisance bias for a sample-split plug-in ERM.

Given:
* `S`            — orthogonal statistical-learning system,
* `Dθ_truth`     — target-direction DD bundle anchored at the *true*
                   nuisance `g₀`,
* `Dθ_at_ghat`   — target-direction DD bundle anchored at the *plug-in*
                   nuisance `g` (typically `ĝ_n ω`),
* `θhat`         — plug-in target estimator,

`Bias_n` returns
`(∫ z, Dθ_truth.dℓ_θ θhat z ∂P_Z) - (∫ z, Dθ_at_ghat.dℓ_θ θhat z ∂P_Z)`.

By construction (see file-header note), this equals
`D_θL(θ₀, g₀)[θhat - θ₀] - D_θL(θ₀, g)[θhat - θ₀]`. -/
noncomputable def Bias_n
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (Dθ_truth : HasDirDerivTheta S S.g₀)
    {g : G} (Dθ_at_ghat : HasDirDerivTheta S g)
    (θhat : Θ) : ℝ :=
  (∫ z, Dθ_truth.dℓ_θ θhat z ∂P_Z)
    - (∫ z, Dθ_at_ghat.dℓ_θ θhat z ∂P_Z)

/-
The note's `def:est-osl-second-order-bias` further records the second-order
Taylor identity
  `Bias_n(g) = -(1/2) D_g² D_θ L(θ₀, ḡ)[θhat - θ₀, g - g₀, g - g₀]`
for some path point `ḡ` between `g₀` and `g`.  Formalising it requires a
second-order DD bundle `D²_g` and a one-dimensional Taylor formula on the
integrated risk; both are deferred to a later API extension.  No vacuous
existential Taylor-form witness is exported here — the concrete quantitative
double-robustness content lives in `Estimation/CATE/SecondOrderBias.lean`.
-/

end OrthogonalLearning
end Estimation
end Causalean
