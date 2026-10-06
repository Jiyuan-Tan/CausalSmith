module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.CompletionObservation
public import Mathlib.Probability.Kernel.CondDistrib

/-! Conditional arm means in the independent potential-outcome completion. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The completion retains the original uniform covariate marginal. [This is the stated conclusion](goal). -/
-- @node: completion_covariate_marginal
lemma completion_covariate_marginal (law : ObservedLaw) :
    (causalCompletion law).map completionX = design := by
  let := bernKernel_markov law
  let : IsProbabilityMeasure design :=
    (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
  exact Measure.fst_compProd design _

/-- Conditional on the covariate, the remaining coordinates have the defining product kernel. [This is the stated conclusion](goal). -/
-- @node: completion_condDistrib
lemma completion_condDistrib (law : ObservedLaw) :
    condDistrib (Prod.snd : CausalRecord → Bool × ℝ × ℝ) completionX
      (causalCompletion law) =ᵐ[design]
      (bernKernel law).prod ((law.Q false).prod (law.Q true)) := by
  let := bernKernel_markov law
  have h := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := causalCompletion law) measurable_completionX measurable_snd
    (κ := (bernKernel law).prod ((law.Q false).prod (law.Q true))) (by
      rw [completion_covariate_marginal]
      change (causalCompletion law).map id = causalCompletion law
      exact Measure.map_id)
  rwa [completion_covariate_marginal] at h

/-- The treatment conditional distribution is the completion's Bernoulli kernel. [This is the stated conclusion](goal). -/
-- @node: completion_treatment_condDistrib
lemma completion_treatment_condDistrib (law : ObservedLaw) :
    condDistrib completionA completionX (causalCompletion law) =ᵐ[design]
      bernKernel law := by
  let := bernKernel_markov law
  have h := condDistrib_comp (mβ := inferInstance) completionX
    (μ := causalCompletion law) measurable_snd.aemeasurable
    (f := (Prod.fst : Bool × ℝ × ℝ → Bool)) measurable_fst
  rw [completion_covariate_marginal] at h
  filter_upwards [h, completion_condDistrib law] with x hx hk
  change condDistrib completionA completionX (causalCompletion law) x = _ at hx
  rw [hx, Kernel.map_apply _ measurable_fst, hk, Kernel.prod_apply,
    Measure.map_fst_prod]
  simp only [measure_univ, one_smul]

/-- The potential pair conditional distribution is the product of its two arm kernels. [This is the stated conclusion](goal). -/
-- @node: completion_potential_pair_condDistrib
lemma completion_potential_pair_condDistrib (law : ObservedLaw) :
    condDistrib (fun r => (Y0 r, Y1 r)) completionX (causalCompletion law) =ᵐ[design]
      (law.Q false).prod (law.Q true) := by
  let := bernKernel_markov law
  have h := condDistrib_comp (mβ := inferInstance) completionX
    (μ := causalCompletion law) measurable_snd.aemeasurable
    (f := (Prod.snd : Bool × ℝ × ℝ → ℝ × ℝ)) measurable_snd
  rw [completion_covariate_marginal] at h
  filter_upwards [h, completion_condDistrib law] with x hx hk
  change condDistrib (fun r => (Y0 r, Y1 r)) completionX (causalCompletion law) x = _ at hx
  rw [hx, Kernel.map_apply _ measurable_snd, hk, Kernel.prod_apply,
    Measure.map_snd_prod]
  simp only [measure_univ, one_smul]

/-- The defining conditional product law makes treatment independent of the potential pair. [This is the stated conclusion](goal). -/
-- @node: completion_conditional_independence
lemma completion_conditional_independence (law : ObservedLaw) :
    CondIndepFun (MeasurableSpace.comap completionX inferInstance)
      measurable_completionX.comap_le (fun r => (Y0 r, Y1 r)) completionA
      (causalCompletion law) := by
  let := bernKernel_markov law
  let : IsProbabilityMeasure design :=
    (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
  have hA : Measurable completionA := by unfold completionA; fun_prop
  have hY : Measurable (fun r => (Y0 r, Y1 r)) := by unfold Y0 Y1; fun_prop
  apply CondIndepFun.symm
  apply (condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    hA hY measurable_completionX).mpr
  rw [completion_covariate_marginal, ← Measure.compProd_eq_comp_prod]
  have hk : (condDistrib completionA completionX (causalCompletion law)).prod
      (condDistrib (fun r => (Y0 r, Y1 r)) completionX (causalCompletion law))
      =ᵐ[design] (bernKernel law).prod ((law.Q false).prod (law.Q true)) := by
    filter_upwards [completion_treatment_condDistrib law,
      completion_potential_pair_condDistrib law] with x hx hy
    simp only [Kernel.prod_apply, hx, hy]
  rw [Measure.compProd_congr hk]
  change (causalCompletion law).map id = causalCompletion law
  exact Measure.map_id

/-- Integrating a potential outcome over the completion fibre integrates its arm kernel. [This is the stated conclusion](goal). -/
-- @node: completion_arm_integral_fiber
lemma completion_arm_integral_fiber (law : ObservedLaw) (a : Bool) (x : unitInterval) :
    (∫ r : Bool × ℝ × ℝ, (if a then r.2.2 else r.2.1)
      ∂((bernKernel law).prod ((law.Q false).prod (law.Q true))) x) =
      ∫ y, y ∂law.Q a x := by
  let := bernKernel_markov law
  simp only [Kernel.prod_apply]
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [integral_fun_snd (fun r : ℝ × ℝ => r.1), integral_fun_fst (fun y : ℝ => y)]
    simp only [probReal_univ, one_smul]
  · rw [integral_fun_snd (fun r : ℝ × ℝ => r.2), integral_fun_snd (fun y : ℝ => y)]
    simp only [probReal_univ, one_smul]

/-- An integrable potential outcome has conditional mean equal to its original arm mean. This statement assumes [the hi condition](hyp:hi). [This is the stated conclusion](goal). -/
-- @node: completion_arm_condExp
lemma completion_arm_condExp (law : ObservedLaw) (a : Bool)
    (hi : Integrable (fun r => if a then Y1 r else Y0 r) (causalCompletion law)) :
    (causalCompletion law)[fun r => if a then Y1 r else Y0 r |
      MeasurableSpace.comap completionX inferInstance] =ᵐ[causalCompletion law]
      fun r => ∫ y, y ∂law.Q a (completionX r) := by
  have h := condExp_ae_eq_integral_condDistrib measurable_completionX
    (μ := causalCompletion law) measurable_snd.aemeasurable
    (f := fun r : Bool × ℝ × ℝ => if a then r.2.2 else r.2.1)
    (by cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop) hi
  have hk : ∀ᵐ r ∂causalCompletion law,
      condDistrib (Prod.snd : CausalRecord → Bool × ℝ × ℝ) completionX
        (causalCompletion law) (completionX r) =
        ((bernKernel law).prod ((law.Q false).prod (law.Q true))) (completionX r) := by
    apply ae_of_ae_map (μ := causalCompletion law)
      (p := fun x => condDistrib (Prod.snd : CausalRecord → Bool × ℝ × ℝ)
        completionX (causalCompletion law) x =
        ((bernKernel law).prod ((law.Q false).prod (law.Q true))) x)
      measurable_completionX.aemeasurable
    rw [completion_covariate_marginal]
    exact completion_condDistrib law
  filter_upwards [h, hk] with r hr hkr
  exact hr.trans (by rw [hkr]; exact completion_arm_integral_fiber law a (completionX r))

/-- Subtracting the two original arm means yields the original continuous causal effect. This statement assumes [the hi0 condition](hyp:hi0), [the hi1 condition](hyp:hi1). [This is the stated conclusion](goal). -/
-- @node: completion_conditional_effect
lemma completion_conditional_effect (law : ObservedLaw)
    (hi0 : Integrable Y0 (causalCompletion law))
    (hi1 : Integrable Y1 (causalCompletion law)) :
    (causalCompletion law)[fun r => Y1 r - Y0 r |
      MeasurableSpace.comap completionX inferInstance] =ᵐ[causalCompletion law]
      fun r => law.tau (completionX r) := by
  have hm0 : ∀ᵐ r ∂causalCompletion law,
      law.m0 (completionX r) = ∫ y, y ∂law.Q false (completionX r) := by
    apply ae_of_ae_map (μ := causalCompletion law)
      (p := fun x => law.m0 x = ∫ y, y ∂law.Q false x)
      measurable_completionX.aemeasurable
    rw [completion_covariate_marginal]
    exact law.mean0_version
  have hm1 : ∀ᵐ r ∂causalCompletion law,
      law.m0 (completionX r) + law.tau (completionX r) =
        ∫ y, y ∂law.Q true (completionX r) := by
    apply ae_of_ae_map (μ := causalCompletion law)
      (p := fun x => law.m0 x + law.tau x = ∫ y, y ∂law.Q true x)
      measurable_completionX.aemeasurable
    rw [completion_covariate_marginal]
    exact law.mean1_version
  have h0 := completion_arm_condExp law false hi0
  have h1 := completion_arm_condExp law true hi1
  have hs := condExp_sub hi1 hi0
    (MeasurableSpace.comap completionX inferInstance)
  filter_upwards [hs, h0, h1, hm0, hm1] with r hsr h0r h1r hm0r hm1r
  simp only [Bool.false_eq_true, ↓reduceIte] at h0r h1r
  calc
    _ = (causalCompletion law)[Y1 | MeasurableSpace.comap completionX inferInstance] r -
        (causalCompletion law)[Y0 | MeasurableSpace.comap completionX inferInstance] r := hsr
    _ = _ := by rw [h1r, h0r, ← hm0r, ← hm1r]; ring

end CausalSmith.Stat.FinitepHomogeneityDensegamma
