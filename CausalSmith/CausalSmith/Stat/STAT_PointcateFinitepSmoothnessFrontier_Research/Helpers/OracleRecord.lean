module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.OracleScoreMoments
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperTruncatedExpectation

/-! Bounded-score disintegration on the original record experiment. -/
public section
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- A bounded record function integrates against the two original arm kernels. -/
-- @node: oracle_record_bounded_integral
lemma oracle_record_bounded_integral (law : ObservedLaw) (x : unitInterval)
    (f : Bool × ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ r, |f r| ≤ C) :
    (∫ r, f r ∂recordMeasure law.e law.Q x) =
      law.e x * (∫ y, f (true,y) ∂law.Q true x) +
      (1-law.e x) * (∫ y, f (false,y) ∂law.Q false x) := by
  have hi (a : Bool) : Integrable f ((Measure.dirac a).prod (law.Q a x)) :=
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun r => by
      simpa only [Real.norm_eq_abs] using hb r)
  have he (a : Bool) : (∫ r, f r ∂((Measure.dirac a).prod (law.Q a x))) =
      ∫ y, f (a,y) ∂law.Q a x := by
    rw [Measure.dirac_prod, integral_map (by fun_prop) hf.aestronglyMeasurable]
  unfold recordMeasure
  rw [integral_add_measure ((hi true).smul_measure ENNReal.ofReal_ne_top)
    ((hi false).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, smul_eq_mul, he]
  rw [ENNReal.toReal_ofReal (law.e_range x).1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (law.e_range x).2)]

/-- Uniform design disintegrates any bounded measurable function of the original record. -/
-- @node: oracle_observed_bounded_integral
lemma oracle_observed_bounded_integral (law : ObservedLaw) (hu : UniformDesign law)
    (f : O → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ o, |f o| ≤ C) :
    (∫ o, f o ∂law.P) = ∫ x,
      law.e x * (∫ y, f (x,true,y) ∂law.Q true x) +
      (1-law.e x) * (∫ y, f (x,false,y) ∂law.Q false x) ∂design := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  letI := completion_record_kernel_markov law
  have hi : Integrable f law.P := Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun o => by simpa only [Real.norm_eq_abs] using hb o)
  have hv : law.P = design ⊗ₘ recordKernel law.e law.e_measurable law.Q :=
    law.record_version.trans (by rw [hu])
  rw [hv] at hi ⊢
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  exact ae_of_all _ fun x => oracle_record_bounded_integral law x
    (fun r => f (x,r)) (hf.comp (by fun_prop)) C (fun r => hb (x,r))

/-- Conditional integration preserves integrability of a bounded record function. -/
-- @node: oracle_conditional_bounded_integrable
lemma oracle_conditional_bounded_integrable (law : ObservedLaw)
    (f : O → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ o, |f o| ≤ C) :
    Integrable (fun x => law.e x * (∫ y, f (x,true,y) ∂law.Q true x) +
      (1-law.e x) * (∫ y, f (x,false,y) ∂law.Q false x)) design := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  letI := completion_record_kernel_markov law
  have hi : Integrable (fun x => ∫ r, f (x,r)
      ∂recordKernel law.e law.e_measurable law.Q x) design := by
    apply Integrable.of_bound hf.stronglyMeasurable.integral_kernel_prod_right'.aestronglyMeasurable C
    apply ae_of_all
    intro x
    have hnorm : ∀ᵐ r ∂recordKernel law.e law.e_measurable law.Q x,
        ‖f (x,r)‖ ≤ C := ae_of_all _ fun r => by
      simpa only [Real.norm_eq_abs] using hb (x,r)
    simpa using norm_integral_le_of_norm_le_const hnorm
  apply hi.congr
  exact ae_of_all _ fun x => oracle_record_bounded_integral law x
    (fun r => f (x,r)) (hf.comp (by fun_prop)) C (fun r => hb (x,r))

/-- A windowed bounded score has exactly the localized conditional arm integral. -/
-- @node: oracle_windowed_bounded_integral
lemma oracle_windowed_bounded_integral (law : ObservedLaw) (hu : UniformDesign law)
    (h : ℝ) (f : O → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ o, |f o| ≤ C) :
    (∫ o, (if X o ∈ window h then f o else 0) ∂law.P) = ∫ x in window h,
      law.e x * (∫ y, f (x,true,y) ∂law.Q true x) +
      (1-law.e x) * (∫ y, f (x,false,y) ∂law.Q false x) ∂design := by
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  have hm : Measurable (fun o => if X o ∈ window h then f o else 0) :=
    Measurable.ite (hw.preimage (by unfold X; fun_prop)) hf measurable_const
  have hC : 0 ≤ C := (abs_nonneg _).trans (hb (xstar,true,0))
  rw [oracle_observed_bounded_integral law hu _ hm C (fun o => by
    split_ifs
    · exact hb o
    · simpa using hC)]
  rw [← integral_indicator hw]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  by_cases hx : x ∈ window h <;> simp [X, hx, Set.indicator]

/-- The original windowed score obeys the conditional localization bias and square bounds. -/
-- @node: oracle_record_local_bounds
lemma oracle_record_local_bounds (κ : Params) (hκ : κ.Valid) (law : ObservedLaw)
    (hm : InModel κ law) (h T : ℝ) (hh : 0 < h ∧ h ≤ 1) (hT : 0 < T) :
    let f : O → ℝ := fun o => if X o ∈ window h then
      trunc T (suppliedScore (sideE law) o) else 0
    |h⁻¹ * (∫ o, f o ∂law.P) - law.theta| ≤
      20*h^κ.γ + oracleMoment κ*T^(1-κ.p) ∧
    h⁻¹ * (∫ o, (f o)^2 ∂law.P) ≤ oracleMoment κ*T^(2-κ.p) := by
  let F : O → ℝ := fun o => trunc T (suppliedScore (sideE law) o)
  have hF : Measurable F := (measurable_trunc T).comp (measurable_suppliedScore.comp
    (by fun_prop : Measurable (fun o : O => (sideE law,o))))
  have hb : ∀ o, |F o| ≤ |T| := fun o => upper_trunc_abs_bound T _
  have hs : ∀ o, |(F o)^2| ≤ |T|^2 := by
    intro o
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hb o, abs_nonneg (F o), sq_abs (F o)]
  have hmean := oracle_windowed_bounded_integral law hm.uniform h F hF _ hb
  have hsquare := oracle_windowed_bounded_integral law hm.uniform h
    (fun o => (F o)^2) (hF.pow_const 2) _ hs
  have hi := (oracle_conditional_bounded_integrable law F hF _ hb).restrict (s := window h)
  have hlocal := oracle_local_truncation_bounds κ hκ law hm h T hh hT
  have hmodel : F = fun o => trunc T (scoreZ law.e o) := by
    funext o
    dsimp only [F]
    rw [suppliedScore_eq_model κ law hm]
  rw [hmodel] at hmean hsquare hi
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hmass : (design.restrict (window h)).real univ = h := by
    simp [Measure.real, design_window h hh, ENNReal.toReal_ofReal hh.1.le]
  have hsub := integral_sub hi (integrable_const law.theta)
  rw [integral_const, hmass, smul_eq_mul] at hsub
  dsimp only
  constructor
  · change |h⁻¹ * (∫ o, if X o ∈ window h then F o else 0 ∂law.P) - law.theta| ≤ _
    rw [hmodel, hmean]
    have heq : h⁻¹ * (∫ x in window h,
        law.e x * (∫ y, trunc T (scoreZ law.e (x,true,y)) ∂law.Q true x) +
        (1-law.e x) * (∫ y, trunc T (scoreZ law.e (x,false,y)) ∂law.Q false x)
        ∂design) - law.theta = h⁻¹ * (∫ x in window h,
        law.e x * (∫ y, trunc T (scoreZ law.e (x,true,y)) ∂law.Q true x) +
        (1-law.e x) * (∫ y, trunc T (scoreZ law.e (x,false,y)) ∂law.Q false x) -
        law.theta ∂design) := by
      rw [hsub]
      field_simp [hh.1.ne']
    rw [heq]
    exact hlocal.1
  · have heq : (fun o : O =>
        (if X o ∈ window h then trunc T (suppliedScore (sideE law) o) else 0)^2) =
        (fun o => if X o ∈ window h then (F o)^2 else 0) := by
      funext o
      split_ifs <;> simp [F]
    rw [heq, hmodel, hsquare]
    exact hlocal.2

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
