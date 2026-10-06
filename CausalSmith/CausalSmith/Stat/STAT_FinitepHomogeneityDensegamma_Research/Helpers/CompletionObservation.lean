module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.Completion
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.MarkedTable

/-! The independent potential-outcome completion recovers the original record law. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The propensity mixture is a probability kernel. [This is the stated conclusion](goal). -/
-- @node: bernKernel_markov
lemma bernKernel_markov (law : ObservedLaw) : IsMarkovKernel (bernKernel law) := by
  constructor
  intro x
  constructor
  change bernMeasure law.e x Set.univ = 1
  simp only [bernMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem, Set.mem_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (law.e_range x).1 (sub_nonneg.mpr (law.e_range x).2)]
  norm_num

/-- Integrating out the unused potential outcome leaves the original arm mixture. This statement assumes [the f condition](hyp:f), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: completion_observe_fiber
lemma completion_observe_fiber (law : ObservedLaw) (x : unitInterval)
    (f : Bool × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ r : Bool × ℝ × ℝ, f (r.1, if r.1 then r.2.2 else r.2.1)
      ∂((bernKernel law).prod ((law.Q false).prod (law.Q true))) x) =
    ∫⁻ r, f r ∂recordKernel law.e law.e.continuous.measurable law.Q x := by
  let := bernKernel_markov law
  have hsel : Measurable (fun r : Bool × ℝ × ℝ =>
      f (r.1, if r.1 then r.2.2 else r.2.1)) :=
    hf.comp (measurable_fst.prodMk
      (Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
        measurable_snd.snd measurable_snd.fst))
  rw [Kernel.lintegral_prod _ _ _ hsel]
  change (∫⁻ a, ∫⁻ r : ℝ × ℝ, f (a, if a then r.2 else r.1)
    ∂((law.Q false).prod (law.Q true)) x ∂bernMeasure law.e x) = _
  rw [bernMeasure, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure]
  rw [lintegral_dirac' _ (measurable_of_countable _),
    lintegral_dirac' _ (measurable_of_countable _)]
  simp only [Bool.false_eq_true, ↓reduceIte, Kernel.prod_apply]
  rw [MeasureTheory.lintegral_prod_symm _ (by fun_prop),
    MeasureTheory.lintegral_prod _ (by fun_prop)]
  simp only [lintegral_const, measure_univ, mul_one]
  change _ = ∫⁻ r, f r ∂recordMeasure law.e law.Q x
  rw [recordMeasure, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, Measure.dirac_prod, Measure.dirac_prod,
    lintegral_map hf measurable_prodMk_left, lintegral_map hf measurable_prodMk_left]

/-- Selecting the recorded outcome is a Borel map. [This is the stated conclusion](goal). -/
-- @node: measurable_observe
@[fun_prop] lemma measurable_observe : Measurable observe := by
  change Measurable (fun r : CausalRecord =>
    (r.1, r.2.1, if r.2.1 then r.2.2.2 else r.2.2.1))
  exact measurable_fst.prodMk (measurable_snd.fst.prodMk
    (Measurable.ite (measurableSet_eq_fun measurable_snd.fst measurable_const)
      measurable_snd.snd.snd measurable_snd.snd.fst))

/-- Under the uniform-design predicate, the completion has the original observed marginal. This statement assumes [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: completion_observed_marginal
lemma completion_observed_marginal (law : ObservedLaw) (hu : UniformDesign law) :
    (causalCompletion law).map observe = law.P := by
  let := bernKernel_markov law
  let : IsProbabilityMeasure design :=
    (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
  let : IsMarkovKernel (recordKernel law.e law.e.continuous.measurable law.Q) :=
    recordKernel_markov _ _ _ law.e_range law.markov
  have hmap : (causalCompletion law).map observe =
      design ⊗ₘ recordKernel law.e law.e.continuous.measurable law.Q := by
    apply Measure.ext_of_lintegral
    intro f hf
    rw [lintegral_map hf measurable_observe]
    simp only [causalCompletion]
    have hfobs : Measurable (fun r : CausalRecord => f (observe r)) :=
      hf.comp measurable_observe
    rw [Measure.lintegral_compProd hfobs,
      Measure.lintegral_compProd hf]
    apply lintegral_congr
    intro x
    exact completion_observe_fiber law x (fun r => f (x,r)) (by fun_prop)
  rw [hmap, law.record_version]
  change design ⊗ₘ _ = covariateLaw law ⊗ₘ _
  rw [hu]

end CausalSmith.Stat.FinitepHomogeneityDensegamma
