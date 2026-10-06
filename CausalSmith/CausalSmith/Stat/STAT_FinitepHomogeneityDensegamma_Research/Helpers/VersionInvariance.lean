module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.MarkedTable
public import Causalean.Mathlib.MeasureTheory.UnitInterval.OpenPos
public import Mathlib.Probability.Kernel.CompProdEqIff

/-! Conditional record versions determine the propensity and, under overlap,
both arm kernels. Continuity then identifies the original mean representatives. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Restricting a conditional record law to one treatment label isolates its arm law. [This is the stated conclusion](goal). -/
-- @node: recordMeasure_arm_slice
lemma recordMeasure_arm_slice (law : ObservedLaw) (x : unitInterval)
    (a : Bool) (s : Set ℝ) (_hs : MeasurableSet s) :
    recordMeasure law.e law.Q x ({a} ×ˢ s) =
      ENNReal.ofReal (if a then law.e x else 1-law.e x) * law.Q a x s := by
  cases a <;> simp [recordMeasure, Measure.prod_prod]

/-- Continuous representatives that agree almost everywhere on the design agree everywhere. This statement assumes [the h condition](hyp:h). [This is the stated conclusion](goal). -/
-- @node: continuous_representative_unique
lemma continuous_representative_unique (f g : Nuisance)
    (h : (f : unitInterval → ℝ) =ᵐ[design] g) : f = g := by
  apply ContinuousMap.coe_injective
  exact Measure.eq_of_ae_eq (μ := (volume : Measure unitInterval)) h f.continuous g.continuous

/-- Versions of one observed law have the same conditional record measure almost everywhere. This statement assumes [the hu condition](hyp:hu), [the hu' condition](hyp:hu'), [the hP condition](hyp:hP). [This is the stated conclusion](goal). -/
-- @node: observed_record_versions_ae
lemma observed_record_versions_ae (law law' : ObservedLaw)
    (hu : UniformDesign law) (hu' : UniformDesign law') (hP : law'.P = law.P) :
    ∀ᵐ x ∂design, recordMeasure law'.e law'.Q x = recordMeasure law.e law.Q x := by
  let : IsProbabilityMeasure design :=
    (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
  let : IsMarkovKernel (recordKernel law.e law.e.continuous.measurable law.Q) :=
    recordKernel_markov _ _ _ law.e_range law.markov
  let : IsMarkovKernel (recordKernel law'.e law'.e.continuous.measurable law'.Q) :=
    recordKernel_markov _ _ _ law'.e_range law'.markov
  change (recordKernel law'.e law'.e.continuous.measurable law'.Q :
    unitInterval → Measure (Bool × ℝ)) =ᵐ[design]
    (recordKernel law.e law.e.continuous.measurable law.Q)
  apply Kernel.ae_eq_of_compProd_eq
  have hp : law.P = design ⊗ₘ recordKernel law.e law.e.continuous.measurable law.Q := by
    rw [law.record_version, show law.P.map X = design from hu]
  have hp' : law'.P = design ⊗ₘ recordKernel law'.e law'.e.continuous.measurable law'.Q := by
    rw [law'.record_version, show law'.P.map X = design from hu']
  exact hp'.symm.trans (hP.trans hp)

/-- A conditional record measure determines propensity through its treatment marginal. This statement assumes [the h condition](hyp:h). [This is the stated conclusion](goal). -/
-- @node: recordMeasure_propensity_unique
lemma recordMeasure_propensity_unique (law law' : ObservedLaw) (x : unitInterval)
    (h : recordMeasure law'.e law'.Q x = recordMeasure law.e law.Q x) :
    law'.e x = law.e x := by
  have he := congrArg (fun μ : Measure (Bool × ℝ) => μ ({true} ×ˢ (Set.univ : Set ℝ))) h
  rw [recordMeasure_arm_slice _ _ _ _ MeasurableSet.univ,
    recordMeasure_arm_slice _ _ _ _ MeasurableSet.univ] at he
  simp only [↓reduceIte, measure_univ, mul_one] at he
  have := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (law'.e_range x).1,
    ENNReal.toReal_ofReal (law.e_range x).1] using this

/-- Overlap allows cancellation of the treatment weight, so both arm versions coincide. This statement assumes [the ho condition](hyp:ho), [the h condition](hyp:h). [This is the stated conclusion](goal). -/
-- @node: recordMeasure_arm_unique
lemma recordMeasure_arm_unique (law law' : ObservedLaw) (ho : Overlap law)
    (x : unitInterval)
    (h : recordMeasure law'.e law'.Q x = recordMeasure law.e law.Q x)
    (a : Bool) : law'.Q a x = law.Q a x := by
  have he := recordMeasure_propensity_unique law law' x h
  apply Measure.ext
  intro s hs
  have hh := congrArg (fun μ : Measure (Bool × ℝ) => μ ({a} ×ˢ s)) h
  rw [recordMeasure_arm_slice _ _ _ _ hs, recordMeasure_arm_slice _ _ _ _ hs, he] at hh
  have hw : ENNReal.ofReal (if a then law.e x else 1-law.e x) ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      linarith [(ho x).1, (ho x).2]
  exact (ENNReal.mul_right_inj hw ENNReal.ofReal_ne_top).mp hh

/-- The observed law determines its continuous propensity and original arm-mean contrast. This statement assumes [the hu condition](hyp:hu), [the hu' condition](hyp:hu'), [the ho condition](hyp:ho), [the hP condition](hyp:hP). [This is the stated conclusion](goal). -/
-- @node: observed_continuous_versions_unique
lemma observed_continuous_versions_unique (law law' : ObservedLaw)
    (hu : UniformDesign law) (hu' : UniformDesign law') (ho : Overlap law)
    (hP : law'.P = law.P) :
    law'.e = law.e ∧ law'.m0 = law.m0 ∧ law'.tau = law.tau := by
  have hrecord := observed_record_versions_ae law law' hu hu' hP
  have he : law'.e = law.e := by
    apply continuous_representative_unique
    filter_upwards [hrecord] with x hx
    exact recordMeasure_propensity_unique law law' x hx
  have h0 : law'.m0 = law.m0 := by
    apply continuous_representative_unique
    filter_upwards [hrecord, law'.mean0_version, law.mean0_version] with x hx hx' hx0
    rw [hx', hx0, recordMeasure_arm_unique law law' ho x hx false]
  have h1 : law'.m1 = law.m1 := by
    apply continuous_representative_unique
    filter_upwards [hrecord, law'.mean1_version, law.mean1_version] with x hx hx' hx1
    change law'.m0 x + law'.tau x = law.m0 x + law.tau x
    rw [hx', hx1, recordMeasure_arm_unique law law' ho x hx true]
  refine ⟨he, h0, ?_⟩
  apply ContinuousMap.coe_injective
  funext x
  have hx := congrArg (fun f : Nuisance => f x) h1
  change law'.m0 x + law'.tau x = law.m0 x + law.tau x at hx
  rw [h0] at hx
  exact add_left_cancel hx

end CausalSmith.Stat.FinitepHomogeneityDensegamma
