module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.Completion

/-! Finite-moment point-CATE frontier: TCausalCompletion. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


-- @node: prop:causal-completion
/-- With [a valid public tuple](hyp:κ,hκ) and [a model law](hyp:law,hmodel),
[the completion recovers the observed law, consistency, conditional exchangeability and the point
CATE through its unique continuous version](goal). -/
theorem causal_completion (κ : Params) (hκ : κ.Valid) (law : ObservedLaw) (hmodel : InModel κ law) :
  (causalCompletion law).map observe = law.P ∧
  (∀ᵐ r ∂causalCompletion law, observedY r =
    (if completionA r then (1 : ℝ) else 0) * Y1 r +
    (1-(if completionA r then (1 : ℝ) else 0)) * Y0 r) ∧
  CondIndepFun (MeasurableSpace.comap completionX inferInstance) measurable_completionX.comap_le
    completionA (fun r => (Y0 r, Y1 r)) (causalCompletion law) ∧
  Integrable Y0 (causalCompletion law) ∧ Integrable Y1 (causalCompletion law) ∧
  ((causalCompletion law)[fun r => Y1 r - Y0 r | MeasurableSpace.comap completionX inferInstance]
    =ᵐ[causalCompletion law] fun r => law.tau (completionX r)) ∧
  (∀ f : unitInterval → ℝ, Continuous f → f =ᵐ[design] law.tau → f = law.tau) ∧
  (∀ law' : ObservedLaw, InModel κ law' → law'.P = law.P → law'.theta = law.theta) ∧
  (∃ f : unitInterval → ℝ, Continuous f ∧
    ((causalCompletion law)[fun r => Y1 r - Y0 r | MeasurableSpace.comap completionX inferInstance]
      =ᵐ[causalCompletion law] fun r => f (completionX r)) ∧ f xstar = law.theta ∧ f = law.tau)  := by
  obtain ⟨hY0, hY1⟩ := completion_outcomes_integrable κ hκ law hmodel
  have hmean := completion_contrast_conditional_mean κ hκ law hmodel
  have hidentified :
      ∀ law' : ObservedLaw, InModel κ law' → law'.P = law.P → law'.theta = law.theta := by
    intro law' hm' hP
    exact congrArg (fun f : unitInterval → ℝ => f xstar)
      (original_contrast_identified κ law law' hmodel hm' hP)
  have hcontinuous : Continuous law.tau := hmodel.effectHolder.1
  refine ⟨completion_observed_marginal law hmodel.uniform, Filter.Eventually.of_forall completion_consistency, completion_exchangeability law,
    hY0, hY1, hmean, ?_, hidentified, ?_⟩
  · intro f hf heq
    exact continuous_eq_of_design_ae_eq hf hcontinuous heq
  · exact ⟨law.tau, hcontinuous, hmean, rfl, rfl⟩

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
