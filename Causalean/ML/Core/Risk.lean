/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core.Hypothesis
import Causalean.Stat.Sample
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Empirical and population risk

Risk criteria for the ML spine, in both the parametric and extensional views.
`Loss` is a pointwise prediction-label loss, `empiricalRisk` and
`empiricalRiskP` are nonempty finite-sample averages, `populationRisk` and
`populationRiskP` are Bochner-integral population criteria, and
`iidEmpiricalRisk` expresses empirical risk through `Stat.IIDSample.sampleMean`.
The separate predicate `HasFinitePopulationRisk` records when the population
integral has the usual finite expected-loss interpretation.
-/

namespace Causalean.ML

open MeasureTheory

/-- For [a label space](hyp:Y), [a pointwise loss](goal) is a real-valued function that compares a predicted label with an observed label. -/
abbrev Loss (Y : Type*) := Y → Y → ℝ

/-- For [a nonempty finite sample index set](hyp:ι), [an input space](hyp:X), [a label space](hyp:Y), [a pointwise loss](hyp:loss), [a sample of input--label pairs](hyp:S), and [a prediction rule](hyp:h), [the empirical risk](goal) is the average, over all sample indices, of the loss comparing the rule's prediction at that observation's input with that observation's label. -/
noncomputable def empiricalRisk {ι X Y : Type*} [Fintype ι] [Nonempty ι]
    (loss : Loss Y) (S : ι → X × Y) (h : X → Y) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, loss (h (S i).1) (S i).2

/-- For [a nonempty finite sample index set](hyp:ι), [a parameter space](hyp:Θ), [an input space](hyp:X), [a label space](hyp:Y), [a parametric predictor](hyp:M), [a pointwise loss](hyp:loss), [a sample of input--label pairs](hyp:S), and [a parameter value](hyp:θ), [the parametric empirical risk](goal) is the empirical average loss of the prediction rule selected by that parameter value. -/
noncomputable def empiricalRiskP {ι Θ X Y : Type*} [Fintype ι] [Nonempty ι]
    (M : Predictor Θ X Y) (loss : Loss Y) (S : ι → X × Y) (θ : Θ) : ℝ :=
  empiricalRisk loss S (M.predict θ)

/-- For [a measurable input space](hyp:X), [a measurable label space](hyp:Y), [a pointwise loss](hyp:loss), [a joint input--label measure](hyp:P), and [a prediction rule](hyp:h), [the population risk](goal) is the integral under that joint measure of the loss comparing the rule's prediction at the input with the observed label.

This definition does not by itself assert integrability or finite expected loss. -/
noncomputable def populationRisk {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (loss : Loss Y) (P : Measure (X × Y)) (h : X → Y) : ℝ :=
  ∫ z, loss (h z.1) z.2 ∂P

/-- For [a parameter space](hyp:Θ), [a measurable input space](hyp:X), [a measurable label space](hyp:Y), [a parametric predictor](hyp:M), [a pointwise loss](hyp:loss), [a joint input--label measure](hyp:P), and [a parameter value](hyp:θ), [the parametric population risk](goal) is the population risk of the prediction rule selected by that parameter value. -/
noncomputable def populationRiskP {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (M : Predictor Θ X Y) (loss : Loss Y) (P : Measure (X × Y)) (θ : Θ) : ℝ :=
  populationRisk loss P (M.predict θ)

/-- For [a measurable sample space](hyp:Ω), [an input space and a label space equipped jointly with a measurable structure](hyp:X,Y), [an experiment measure](hyp:μ), [a joint input--label measure](hyp:P), [an independent and identically distributed sample with those measures](hyp:S), [a pointwise loss](hyp:loss), [a prediction rule](hyp:h), and [a sample size](hyp:n), [the i.i.d. empirical risk](goal) is the random sample average of the loss comparing the rule's prediction with the observed label over the first $n$ sample observations. -/
noncomputable def iidEmpiricalRisk {Ω X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace (X × Y)]
    {μ : Measure Ω} {P : Measure (X × Y)}
    (S : Causalean.Stat.IIDSample Ω (X × Y) μ P)
    (loss : Loss Y) (h : X → Y) (n : ℕ) : Ω → ℝ :=
  S.sampleMean (fun z => loss (h z.1) z.2) n

/-- For [a measurable input space](hyp:X), [a measurable label space](hyp:Y), [a pointwise loss](hyp:loss), [a joint input--label measure](hyp:P), and [a prediction rule](hyp:h), [the finite-population-risk condition](goal) holds exactly when the loss comparing the rule's prediction with the observed label is integrable under the joint measure. -/
def HasFinitePopulationRisk {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (loss : Loss Y) (P : Measure (X × Y)) (h : X → Y) : Prop :=
  Integrable (fun z => loss (h z.1) z.2) P

end Causalean.ML
