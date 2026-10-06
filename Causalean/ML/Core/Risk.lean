/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.ML.Core.Hypothesis
public import Causalean.Stat.Sample
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Empirical and population risk

Risk criteria for the ML spine, in both the parametric and extensional views.
`Loss` is a pointwise prediction-label loss, `empiricalRisk` and
`empiricalRiskP` are nonempty finite-sample averages, `populationRisk` and
`populationRiskP` are Bochner-integral population criteria, and
`iidEmpiricalRisk` expresses empirical risk through `Stat.IIDSample.sampleMean`.
The separate predicate `HasFinitePopulationRisk` records when the population
integral has the usual finite expected-loss interpretation.
-/

@[expose] public section

namespace Causalean.ML

open MeasureTheory

/-- [A pointwise loss](goal) assigns a real penalty to [predicted and observed labels](hyp:Y) by
[comparing one label-space value with another](step:1). -/
abbrev Loss (Y : Type*) := Y → Y → ℝ

/-- [Empirical risk](goal) is [average loss over a nonempty finite sample](step:1). It evaluates
[a prediction rule](hyp:h) with [a pointwise loss](hyp:loss) on
[sampled input--label pairs](hyp:S) indexed by [a finite nonempty set](hyp:ι), with
[input and label spaces](hyp:X,Y). -/
noncomputable def empiricalRisk {ι X Y : Type*} [Fintype ι] [Nonempty ι]
    (loss : Loss Y) (S : ι → X × Y) (h : X → Y) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, loss (h (S i).1) (S i).2

/-- [Parametric empirical risk](goal) assigns [a parameter value](hyp:θ)
[the sample-average loss of its prediction rule](step:1). The rule comes from
[a parametrized predictor](hyp:M) on [parameter, input, and label spaces](hyp:Θ,X,Y), using
[the chosen loss and sample](hyp:loss,S) over [a nonempty finite index set](hyp:ι). -/
noncomputable def empiricalRiskP {ι Θ X Y : Type*} [Fintype ι] [Nonempty ι]
    (M : Predictor Θ X Y) (loss : Loss Y) (S : ι → X × Y) (θ : Θ) : ℝ :=
  empiricalRisk loss S (M.predict θ)

/-- [Population risk](goal) is [the expected pointwise prediction loss](step:1) of
[a prediction rule](hyp:h) under [a joint input--label law](hyp:P), using
[a chosen loss function](hyp:loss) on [measurable input and label spaces](hyp:X,Y).

This definition does not by itself assert integrability or finite expected loss. -/
noncomputable def populationRisk {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (loss : Loss Y) (P : Measure (X × Y)) (h : X → Y) : ℝ :=
  ∫ z, loss (h z.1) z.2 ∂P

/-- [Parametric population risk](goal) assigns [a parameter value](hyp:θ)
[the expected loss of its prediction rule](step:1). The rule comes from
[a parametrized predictor](hyp:M)
on [parameter, measurable input, and measurable label spaces](hyp:Θ,X,Y), and is evaluated
with [the chosen loss](hyp:loss) under [the joint input--label law](hyp:P). -/
noncomputable def populationRiskP {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (M : Predictor Θ X Y) (loss : Loss Y) (P : Measure (X × Y)) (θ : Θ) : ℝ :=
  populationRisk loss P (M.predict θ)

/-- [The i.i.d. empirical risk](goal) is [random average loss over the requested prefix](step:1)
from [an i.i.d. input--label sample](hyp:S). It evaluates [a prediction rule](hyp:h) with
[the chosen loss](hyp:loss) at [the sample size](hyp:n), under
[experiment and population laws](hyp:μ,P) on
[the measurable sample, input, and label spaces](hyp:Ω,X,Y). -/
noncomputable def iidEmpiricalRisk {Ω X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace (X × Y)]
    {μ : Measure Ω} {P : Measure (X × Y)}
    (S : Causalean.Stat.IIDSample Ω (X × Y) μ P)
    (loss : Loss Y) (h : X → Y) (n : ℕ) : Ω → ℝ :=
  S.sampleMean (fun z => loss (h z.1) z.2) n

/-- [Finite population risk](goal) requires
[integrability of prediction loss under the joint law](step:1). It applies to
[a prediction rule](hyp:h) and
[pointwise loss](hyp:loss) under [that joint law](hyp:P) on
[measurable input and label spaces](hyp:X,Y). -/
def HasFinitePopulationRisk {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (loss : Loss Y) (P : Measure (X × Y)) (h : X → Y) : Prop :=
  Integrable (fun z => loss (h z.1) z.2) P

end Causalean.ML
