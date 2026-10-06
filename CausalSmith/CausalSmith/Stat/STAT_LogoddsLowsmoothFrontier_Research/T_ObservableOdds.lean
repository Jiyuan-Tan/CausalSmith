module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Defs.Calibration
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # T ObservableOdds

Paper-owned scaffold obligations; proofs are filled in Stage 3. -/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Both conditional arm risks are strictly interior.](goal) Under [the stated assumptions](hyp:x). -/
-- @node: armRisk_interior
lemma armRisk_interior (P : ObservedLaw) (a : Bool) (x : Covariate) :
    0 < armRisk P a x ∧ armRisk P a x < 1 := by
  have h0 := (P.interior_cells a false x).1
  have h1 := (P.interior_cells a true x).1
  unfold armRisk
  constructor
  · exact div_pos h1 (add_pos h0 h1)
  · exact (div_lt_one (add_pos h0 h1)).2 (by linarith)

/-- [The Bernoulli factorization recovers each of the original four cells.](goal) Under [the stated assumptions](hyp:x). -/
-- @node: cellProbability_eq_cells
lemma cellProbability_eq_cells (P : ObservedLaw) (a y : Bool) (x : Covariate) :
    cellProbability P a y x = P.cells a y x := by
  have hn := P.normalized_cells x
  simp only [Fintype.sum_bool] at hn
  have h0 : P.cells false false x + P.cells false true x ≠ 0 :=
    ne_of_gt (add_pos (P.interior_cells false false x).1
      (P.interior_cells false true x).1)
  have h1 : P.cells true false x + P.cells true true x ≠ 0 :=
    ne_of_gt (add_pos (P.interior_cells true false x).1
      (P.interior_cells true true x).1)
  have hc : 1 - (P.cells true false x + P.cells true true x) =
      P.cells false false x + P.cells false true x := by linarith
  cases a <;> cases y <;> simp only [cellProbability, propensity, armRisk,
    Bool.false_eq_true, ↓reduceIte]
  all_goals try rw [hc]
  all_goals field_simp
  all_goals ring

/-- [The conditional outcome mean is the sum of the two outcome-one cells.](goal) Under [the stated assumptions](hyp:x). -/
-- @node: marginalMean_eq_cells
lemma marginalMean_eq_cells (P : ObservedLaw) (x : Covariate) :
    marginalMean P x = P.cells false true x + P.cells true true x := by
  rw [← cellProbability_eq_cells P false true x,
    ← cellProbability_eq_cells P true true x]
  rfl

/-- [Expanding the two margins yields the determinant of the binary table.](goal) Under [the stated assumptions](hyp:x). -/
-- @node: conditional_covariance_eq_determinant
lemma conditional_covariance_eq_determinant (P : ObservedLaw) (x : Covariate) :
    P.cells true true x - propensity P x * marginalMean P x =
      P.cells true true x * P.cells false false x -
        P.cells true false x * P.cells false true x := by
  have hn := P.normalized_cells x
  simp only [Fintype.sum_bool] at hn
  rw [marginalMean_eq_cells]
  unfold propensity
  have hc : P.cells false false x =
      1 - P.cells true true x - P.cells true false x - P.cells false true x := by
    linarith
  rw [hc]
  ring

/-- [Log odds invert the logistic map on every real argument. [the stated conclusion](goal) holds. -/
-- @node: logit_logistic
lemma logit_logistic (t : ℝ) : logit (logistic t) = t := by
  have hs : logistic t / (1 - logistic t) = Real.exp t := by
    unfold logistic
    rw [← Real.sigmoid_neg, ← Real.sigmoid_mul_rexp_neg]
    rw [mul_comm, div_mul_cancel_right₀ (ne_of_gt (Real.sigmoid_pos t))]
    simp [Real.exp_neg]
  rw [logit, hs, Real.log_exp]

/-- Homogeneity gives the same log-odds contrast at every covariate. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: homogeneous_logit_difference
lemma homogeneous_logit_difference (P : ObservedLaw) (h : HomogeneousLogit P)
    (x : Covariate) :
    logit (armRisk P true x) - logit (armRisk P false x) = effect P := by
  rw [h x, logit_logistic]
  change logit (armRisk P false x) + effect P - logit (armRisk P false x) = effect P
  ring

/-- [Homogeneous log odds give the four-cell odds-ratio identity pointwise.](goal) Under [the stated assumptions](hyp:h,x). -/
-- @node: homogeneous_cell_odds
lemma homogeneous_cell_odds (P : ObservedLaw) (h : HomogeneousLogit P)
    (x : Covariate) :
    P.cells true true x * P.cells false false x =
      Real.exp (effect P) * (P.cells true false x * P.cells false true x) := by
  have h0 := armRisk_interior P false x
  have h1 := armRisk_interior P true x
  have he : Real.exp (effect P) =
      (armRisk P true x / (1-armRisk P true x)) /
        (armRisk P false x / (1-armRisk P false x)) := by
    rw [← homogeneous_logit_difference P h x, logit, logit, Real.exp_sub,
      Real.exp_log (div_pos h1.1 (sub_pos.mpr h1.2)),
      Real.exp_log (div_pos h0.1 (sub_pos.mpr h0.2))]
  rw [← cellProbability_eq_cells P true true x,
    ← cellProbability_eq_cells P false false x,
    ← cellProbability_eq_cells P true false x,
    ← cellProbability_eq_cells P false true x, he]
  simp only [cellProbability, Bool.false_eq_true, ↓reduceIte]
  field_simp [ne_of_gt h0.1, ne_of_gt (sub_pos.mpr h0.2),
    ne_of_gt (sub_pos.mpr h1.2)]

/-- [Division by the positive denominator recovers the scalar effect.](goal) Under [the stated assumptions](hyp:hS). Under [the stated assumptions](hyp:hC). -/
-- @node: effect_eq_log_of_coordinates
lemma effect_eq_log_of_coordinates (P : ObservedLaw)
    (hC : covarianceCoordinate P =
      (Real.exp (effect P) - 1) * denominatorCoordinate P)
    (hS : denominatorFloor ≤ denominatorCoordinate P) :
    effect P = Real.log (1+covarianceCoordinate P/denominatorCoordinate P) := by
  have hs : denominatorCoordinate P ≠ 0 := by
    have hf : 0 < denominatorFloor := by norm_num [denominatorFloor]
    exact ne_of_gt (lt_of_lt_of_le hf hS)
  rw [hC, mul_div_cancel_right₀ _ hs]
  simp only [add_sub_cancel]
  exact (Real.log_exp (effect P)).symm

/-- [The observed outcome obeys literal potential-outcome consistency. [the stated conclusion](goal) holds. -/
-- @node: observedMap_consistency
lemma observedMap_consistency (o : FullRecord) :
    outcome (observedMap o) =
      (1-(if o.2 then 1 else 0 : ℝ))*potentialControl o +
      (if o.2 then 1 else 0 : ℝ)*potentialTreated o := by
  rcases o with ⟨⟨x, y0, y1⟩, a⟩
  cases a <;> simp [outcome, observedMap, potentialControl, potentialTreated]

/-- Conditional treatment is independent of the potential-outcome pair. Under the stated assumptions. [The stated hypotheses](hyp:hΓ) hold, and [the stated conclusion follows](goal). -/
-- @node: fullConditionalLaw_independent
lemma fullConditionalLaw_independent (P : ObservedLaw)
    (Γ : Kernel Covariate (Bool × Bool)) (hΓ : AdmissibleCoupling P Γ)
    (x : Covariate) : IndepFun Prod.fst Prod.snd (fullConditionalLaw P Γ x) := by
  let : IsMarkovKernel Γ := hΓ.1
  let : IsProbabilityMeasure (bernoulliLaw (propensity P x)) :=
    bernoulliLaw_probability _ (propensity_interior P x).1.le
      (propensity_interior P x).2.le
  exact indepFun_prod measurable_id measurable_id

/-- [A Bernoulli law has its parameter as the binary expectation.](goal) Under [the stated assumptions](hyp:hp). -/
-- @node: bernoulliLaw_mean
lemma bernoulliLaw_mean (p : ℝ) (hp : 0 ≤ p) :
    (∫ b : Bool, (if b then 1 else 0 : ℝ) ∂bernoulliLaw p) = p := by
  unfold bernoulliLaw
  rw [integral_add_measure
    (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top)
    (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top)]
  simp [integral_smul_measure, ENNReal.toReal_ofReal hp]

/-- [Admissible coupling margins give the two potential-outcome means.](goal) Under [the stated assumptions](hyp:hΓ,x). -/
-- @node: admissibleCoupling_means
lemma admissibleCoupling_means (P : ObservedLaw)
    (Γ : Kernel Covariate (Bool × Bool)) (hΓ : AdmissibleCoupling P Γ)
    (x : Covariate) :
    (∫ b, (if b.1 then 1 else 0 : ℝ) ∂Γ x) = armRisk P false x ∧
    (∫ b, (if b.2 then 1 else 0 : ℝ) ∂Γ x) = armRisk P true x := by
  have hm : Measurable (fun b : Bool => (if b then 1 else 0 : ℝ)) := by fun_prop
  constructor
  · rw [← integral_map measurable_fst.aemeasurable hm.aestronglyMeasurable,
      (hΓ.2 x).1]
    exact bernoulliLaw_mean _ (armRisk_interior P false x).1.le
  · rw [← integral_map measurable_snd.aemeasurable hm.aestronglyMeasurable,
      (hΓ.2 x).2]
    exact bernoulliLaw_mean _ (armRisk_interior P true x).1.le

/-- [Continuous marks integrate against the explicit conditional cell disintegration.](goal) Under [the stated assumptions](hyp:hU,f,hf). -/
-- @node: integral_observed_cells
lemma integral_observed_cells (P : ObservedLaw) (hU : UniformDesign P)
    (f : Record → ℝ) (hf : Continuous f) :
    (∫ o, f o ∂P.measure) =
      ∑ a : Bool, ∑ y : Bool, ∫ x, P.cells a y x * f (x,a,y) ∂uniformLaw := by
  have hm (a y : Bool) : Measurable (fun x => ENNReal.ofReal (P.cells a y x)) :=
    ENNReal.measurable_ofReal.comp (P.continuous_cells a y).measurable
  have hi (a y : Bool) : Integrable f
      (Measure.map (fun x : Covariate => (x,a,y))
        (uniformLaw.withDensity (fun x => ENNReal.ofReal (P.cells a y x)))) := by
    apply (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).2
    apply (integrable_withDensity_iff_integrable_smul' (hm a y)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).2
    simp only [ENNReal.toReal_ofReal (P.interior_cells a y _).1.le, smul_eq_mul]
    exact ((P.continuous_cells a y).mul (hf.comp (by fun_prop))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [P.disintegration, hU]
  unfold jointLaw
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [integral_finsetSum_measure (fun y _ => hi a y)]
    apply Finset.sum_congr rfl
    intro y hy
    rw [integral_map (by fun_prop) hf.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul (hm a y)
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (P.interior_cells a y _).1.le, smul_eq_mul]
  · intro a ha
    exact integrable_finsetSum_measure.2 (fun y _ => hi a y)

/-- [The treatment-outcome product has conditional expectation equal to the (1,1) cell.](goal) Under [the stated assumptions](hyp:hU). -/
-- @node: treatment_outcome_mean
lemma treatment_outcome_mean (P : ObservedLaw) (hU : UniformDesign P) :
    (∫ o, treatment o * outcome o ∂P.measure) = ∫ x, P.cells true true x ∂uniformLaw := by
  have hb : Continuous (fun b : Bool => (if b then 1 else 0 : ℝ)) :=
    continuous_of_discreteTopology
  have ht : Continuous treatment := hb.comp (continuous_snd.fst)
  have hy : Continuous outcome := hb.comp (continuous_snd.snd)
  rw [integral_observed_cells P hU (fun o => treatment o * outcome o) (ht.mul hy)]
  simp [Fintype.sum_bool, treatment, outcome]

/-- [Integrating the homogeneous determinant identity gives the observable covariance coordinate.](goal) Under [the stated assumptions](hyp:hU,hH). -/
-- @node: covarianceCoordinate_eq_odds
lemma covarianceCoordinate_eq_odds (P : ObservedLaw) (hU : UniformDesign P)
    (hH : HomogeneousLogit P) :
    covarianceCoordinate P = (Real.exp (effect P)-1) * denominatorCoordinate P := by
  have he : Continuous (propensity P) :=
    (P.continuous_cells true false).add (P.continuous_cells true true)
  have hm : Continuous (marginalMean P) := by
    rw [show marginalMean P = fun x => P.cells false true x + P.cells true true x
      from funext (marginalMean_eq_cells P)]
    exact (P.continuous_cells false true).add (P.continuous_cells true true)
  have hi : Integrable (fun x => propensity P x * marginalMean P x) uniformLaw :=
    (he.mul hm).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (P.cells true true) uniformLaw :=
    (P.continuous_cells true true).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold covarianceCoordinate denominatorCoordinate
  rw [treatment_outcome_mean P hU, ← integral_sub hj hi, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [conditional_covariance_eq_determinant, homogeneous_cell_odds P hH,
    cellProbability_eq_cells, cellProbability_eq_cells]
  ring

/-- [Logistic and log odds are inverse at interior probabilities.](goal) Under [the stated assumptions](hyp:hp,hp1). -/
-- @node: logistic_logit
lemma logistic_logit (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    logistic (logit p) = p := by
  rw [logistic, Real.sigmoid_def, logit, Real.exp_neg,
    Real.exp_log (div_pos hp (sub_pos.mpr hp1))]
  field_simp
  <;> ring

/-- [Numerical exponential bounds certify the two envelope endpoint values. [the stated conclusion](goal) holds. -/
-- @node: logistic_envelope_endpoints
lemma logistic_envelope_endpoints :
    (4/15 : ℝ) ≤ logistic (-1) ∧ (2/11 : ℝ) ≤ logistic (-(3/2)) := by
  have h1 : Real.exp 1 < (11/4 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h15 : Real.exp (3/2 : ℝ) < (9/2 : ℝ) := by
    have he : Real.exp (3/2 : ℝ) ^ 2 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      norm_num
    have hb : Real.exp 1 < (2719/1000 : ℝ) :=
      lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hc := pow_lt_pow_left₀ hb (Real.exp_pos 1).le (by norm_num : 3 ≠ 0)
    nlinarith [Real.exp_pos (3/2 : ℝ)]
  simp only [logistic, Real.sigmoid_def, neg_neg]
  constructor
  · rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity)).2
    linarith
  · rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity)).2
    linarith

/-- The native logit envelopes bound all four Bernoulli factors away from zero. Under the stated assumptions. [The stated hypotheses](hyp:hP) hold, and [the stated conclusion follows](goal). -/
-- @node: model_bernoulli_factors_lower
lemma model_bernoulli_factors_lower (α β : ℝ) (P : ObservedLaw)
    (hP : Model α β P) (x : Covariate) :
    (4/15 : ℝ) ≤ propensity P x ∧ (4/15 : ℝ) ≤ 1-propensity P x ∧
    (2/11 : ℝ) ≤ armRisk P false x ∧ (2/11 : ℝ) ≤ 1-armRisk P true x := by
  have he := abs_le.mp (hP.propensity_envelope x)
  have hn := abs_le.mp (hP.prognosis_envelope x)
  have ht := abs_le.mp hP.effect_envelope
  have ep := propensity_interior P x
  have mp := armRisk_interior P false x
  have hr : logistic (propensityLogit P x) = propensity P x :=
    logistic_logit _ ep.1 ep.2
  have hm : logistic (prognosisLogit P x) = armRisk P false x :=
    logistic_logit _ mp.1 mp.2
  have hneg (t : ℝ) : logistic (-t) = 1-logistic t := Real.sigmoid_neg t
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact logistic_envelope_endpoints.1.trans (hr ▸ Real.sigmoid_le he.1)
  · rw [← hr, ← hneg]
    exact logistic_envelope_endpoints.1.trans (Real.sigmoid_le (by linarith))
  · have hl : (4/15 : ℝ) ≤ logistic (prognosisLogit P x) :=
      logistic_envelope_endpoints.1.trans (Real.sigmoid_le hn.1)
    rw [hm] at hl
    linarith
  · rw [hP.homogeneous x, ← hneg]
    exact logistic_envelope_endpoints.2.trans (Real.sigmoid_le (by linarith))

/-- [The off-diagonal product exceeds the public numerical denominator floor pointwise.](goal) Under [the stated assumptions](hyp:hP,x). -/
-- @node: model_cell_product_lower
lemma model_cell_product_lower (α β : ℝ) (P : ObservedLaw)
    (hP : Model α β P) (x : Covariate) :
    denominatorFloor ≤ cellProbability P true false x * cellProbability P false true x := by
  obtain ⟨he, he', hm, ht⟩ := model_bernoulli_factors_lower α β P hP x
  have hl : (4/15 : ℝ)*(2/11)*(4/15)*(2/11) ≤
      propensity P x * (1-armRisk P true x) * (1-propensity P x) * armRisk P false x := by
    gcongr <;> linarith
  simp only [cellProbability, Bool.false_eq_true, ↓reduceIte]
  unfold denominatorFloor
  nlinarith [hl]

/-- [Integration of the pointwise floor under the known uniform probability design.](goal) Under [the stated assumptions](hyp:hP). -/
-- @node: denominatorCoordinate_lower
lemma denominatorCoordinate_lower (α β : ℝ) (P : ObservedLaw)
    (hP : Model α β P) : denominatorFloor ≤ denominatorCoordinate P := by
  letI : IsProbabilityMeasure uniformLaw := hP.uniform ▸
    Measure.isProbabilityMeasure_map (by unfold covariate; fun_prop : Measurable covariate).aemeasurable
  have hi : Integrable (fun x => P.cells true false x * P.cells false true x) uniformLaw :=
    ((P.continuous_cells true false).mul (P.continuous_cells false true)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun x => cellProbability P true false x *
      cellProbability P false true x) uniformLaw := by
    simpa only [cellProbability_eq_cells] using hi
  have hl := integral_mono (integrable_const denominatorFloor) hj
    (model_cell_product_lower α β P hP)
  simpa [denominatorCoordinate] using hl

/-- [Integrating a binary test function against the explicit Bernoulli law.](goal) Under [the stated assumptions](hyp:f). -/
-- @node: lintegral_bernoulliLaw
lemma lintegral_bernoulliLaw (p : ℝ) (f : Bool → ℝ≥0∞) :
    (∫⁻ b, f b ∂bernoulliLaw p) =
      ENNReal.ofReal (1-p) * f false + ENNReal.ofReal p * f true := by
  simp [bernoulliLaw, lintegral_add_measure, lintegral_smul_measure]

/-- [Coupling margins determine every nonnegative test of either potential outcome.](goal) Under [the stated assumptions](hyp:hΓ,x,f). -/
-- @node: lintegral_coupling_arm
lemma lintegral_coupling_arm (P : ObservedLaw)
    (Γ : Kernel Covariate (Bool × Bool)) (hΓ : AdmissibleCoupling P Γ)
    (x : Covariate) (a : Bool) (f : Bool → ℝ≥0∞) :
    (∫⁻ b, f (if a then b.2 else b.1) ∂Γ x) =
      ENNReal.ofReal (1-armRisk P a x) * f false +
      ENNReal.ofReal (armRisk P a x) * f true := by
  have hf : Measurable f := by fun_prop
  cases a
  · rw [show (fun b : Bool × Bool => f (if false then b.2 else b.1)) =
        (fun b => f b.1) from rfl,
      ← lintegral_map hf measurable_fst, (hΓ.2 x).1, lintegral_bernoulliLaw]
  · rw [show (fun b : Bool × Bool => f (if true then b.2 else b.1)) =
        (fun b => f b.2) from rfl,
      ← lintegral_map hf measurable_snd, (hΓ.2 x).2, lintegral_bernoulliLaw]

/-- [The conditional observation test recovers the four original cells.](goal) Under [the stated assumptions](hyp:hΓ,x,f). -/
-- @node: lintegral_conditional_observation
lemma lintegral_conditional_observation (P : ObservedLaw)
    (Γ : Kernel Covariate (Bool × Bool)) (hΓ : AdmissibleCoupling P Γ)
    (x : Covariate) (f : Bool → Bool → ℝ≥0∞) :
    (∫⁻ b, ∫⁻ a, f a (if a then b.2 else b.1)
      ∂bernoulliLaw (propensity P x) ∂Γ x) =
      ∑ a : Bool, ∑ y : Bool, ENNReal.ofReal (P.cells a y x) * f a y := by
  simp_rw [lintegral_bernoulliLaw]
  rw [lintegral_add_left (by fun_prop),
    lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop)]
  have h0 := lintegral_coupling_arm P Γ hΓ x false (f false)
  have h1 := lintegral_coupling_arm P Γ hΓ x true (f true)
  simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1 ⊢
  rw [h0, h1]
  simp only [Fintype.sum_bool, mul_add, ← mul_assoc, ← ENNReal.ofReal_mul
    (propensity_interior P x).1.le, ← ENNReal.ofReal_mul
    (sub_nonneg.mpr (propensity_interior P x).2.le)]
  simp only [← cellProbability_eq_cells, cellProbability, Bool.false_eq_true, ↓reduceIte]
  ring

/-- [The conditional cell construction integrates any nonnegative measurable test.](goal) Under [the stated assumptions](hyp:f,hf). -/
-- @node: lintegral_jointLaw_cells
lemma lintegral_jointLaw_cells (P : ObservedLaw) (f : Record → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ o, f o ∂jointLaw uniformLaw P.cells) =
      ∫⁻ x, ∑ a : Bool, ∑ y : Bool,
        ENNReal.ofReal (P.cells a y x) * f (x,a,y) ∂uniformLaw := by
  have hm (a y : Bool) : Measurable (fun x => ENNReal.ofReal (P.cells a y x)) :=
    ENNReal.measurable_ofReal.comp (P.continuous_cells a y).measurable
  have hi (a y : Bool) : Measurable (fun x : Covariate => f (x,a,y)) := by fun_prop
  calc
    _ = ∑ a : Bool, ∑ y : Bool, ∫⁻ x,
        ENNReal.ofReal (P.cells a y x) * f (x,a,y) ∂uniformLaw := by
      simp only [jointLaw, lintegral_finsetSum_measure]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro y hy
      rw [lintegral_map hf (by fun_prop : Measurable (fun x : Covariate => (x,a,y))),
        lintegral_withDensity_eq_lintegral_mul _ (hm a y) (hi a y)]
      rfl
    _ = _ := by
      rw [lintegral_finset_sum]
      · apply Finset.sum_congr rfl
        intro a ha
        rw [lintegral_finset_sum]
        exact fun y _ => (hm a y).mul (hi a y)
      · intro a ha
        exact Finset.measurable_sum _ (fun y _ => (hm a y).mul (hi a y))

/-- [The full-data extension has precisely the original observed marginal.](goal) Under [the stated assumptions](hyp:hU,hΓ). -/
-- @node: causalExtension_observed_marginal
lemma causalExtension_observed_marginal (P : ObservedLaw) (hU : UniformDesign P)
    (Γ : Kernel Covariate (Bool × Bool)) (hΓ : AdmissibleCoupling P Γ) :
    Measure.map observedMap (causalExtension P Γ) = P.measure := by
  letI : IsMarkovKernel Γ := hΓ.1
  letI : IsMarkovKernel (treatmentKernel P) := ⟨fun z =>
    bernoulliLaw_probability _ (propensity_interior P z.1).1.le
      (propensity_interior P z.1).2.le⟩
  have ho : Measurable observedMap := by
    unfold observedMap
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.prodMk (by fun_prop)
    exact Measurable.ite (measurable_snd (measurableSet_singleton true))
      (by fun_prop) (by fun_prop)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf ho, causalExtension,
    Measure.lintegral_compProd (show Measurable (fun o => f (observedMap o)) from hf.comp ho),
    Measure.lintegral_compProd]
  · change (∫⁻ x, ∫⁻ b, ∫⁻ a, f (x,a,if a then b.2 else b.1)
        ∂bernoulliLaw (propensity P x) ∂Γ x ∂uniformLaw) = _
    rw [P.disintegration, hU, lintegral_jointLaw_cells P f hf]
    exact lintegral_congr (fun x =>
      lintegral_conditional_observation P Γ hΓ x (fun a y => f (x,a,y)))
  · exact (hf.comp ho).lintegral_kernel_prod_right'

-- @node: lem:observable-odds
/-- On the public exponent domain 0 < β < 1/4 and β < α ≤ 1, each model law has the observable odds identity, denominator floor, and causal interpretation. The full conditional laws disintegrate the causal extension by the canonical reassociation from X × ((Y⁰, Y¹) × A) to (X × (Y⁰, Y¹)) × A. the documented result Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hD,hP) hold, and [the stated conclusion follows](goal). -/
lemma observable_odds (α β : ℝ) (hD : ExponentDomain α β)
    (P : ObservedLaw) (hP : Model α β P) :
  covarianceCoordinate P = (Real.exp (effect P) - 1) * denominatorCoordinate P ∧
  denominatorFloor ≤ denominatorCoordinate P ∧
  effect P = Real.log (1+covarianceCoordinate P/denominatorCoordinate P) ∧
  ∀ (Γ : Kernel Covariate (Bool × Bool)) (hΓ : AdmissibleCoupling P Γ),
    Measure.map observedMap (causalExtension P Γ) = P.measure ∧
    (∀ o : FullRecord, outcome (observedMap o) =
      (1-(if o.2 then 1 else 0 : ℝ))*potentialControl o +
      (if o.2 then 1 else 0 : ℝ)*potentialTreated o) ∧
    (causalExtension P Γ =
      (uniformLaw.compProd Γ).compProd (treatmentKernel P) ∧
      ∀ x, IndepFun Prod.fst Prod.snd (fullConditionalLaw P Γ x)) ∧
    (∀ x, logit (∫ b, (if b.2 then 1 else 0 : ℝ) ∂Γ x) -
      logit (∫ b, (if b.1 then 1 else 0 : ℝ) ∂Γ x) = effect P) ∧
    causalExtension P Γ = Measure.map
      (fun z : Covariate × ((Bool × Bool) × Bool) => ((z.1, z.2.1), z.2.2))
      (uniformLaw.compProd
        ({ toFun := fullConditionalLaw P Γ
           measurable' := fullConditionalLaw_measurable P Γ hΓ } :
          Kernel Covariate ((Bool × Bool) × Bool))) := by
  have hC : covarianceCoordinate P =
      (Real.exp (effect P) - 1) * denominatorCoordinate P := by
    exact covarianceCoordinate_eq_odds P hP.uniform hP.homogeneous
  have hS : denominatorFloor ≤ denominatorCoordinate P := by
    exact denominatorCoordinate_lower α β P hP
  refine ⟨hC, hS, effect_eq_log_of_coordinates P hC hS, ?_⟩
  intro Γ hΓ
  have hconditional : causalExtension P Γ = Measure.map
      (fun z : Covariate × ((Bool × Bool) × Bool) => ((z.1, z.2.1), z.2.2))
      (uniformLaw.compProd
        ({ toFun := fullConditionalLaw P Γ
           measurable' := fullConditionalLaw_measurable P Γ hΓ } :
          Kernel Covariate ((Bool × Bool) × Bool))) := by
    have hk : ({ toFun := fullConditionalLaw P Γ
                 measurable' := fullConditionalLaw_measurable P Γ hΓ } :
        Kernel Covariate ((Bool × Bool) × Bool)) = Γ ⊗ₖ treatmentKernel P := by
      ext x : 1
      exact fullConditionalLaw_eq_compProd P Γ hΓ x
    rw [hk]
    exact (Measure.compProd_assoc (μ := uniformLaw) (κ := Γ)
      (η := treatmentKernel P)).symm
  refine ⟨?_, observedMap_consistency, ?_, ?_, hconditional⟩
  · exact causalExtension_observed_marginal P hP.uniform Γ hΓ
  · exact ⟨rfl, fullConditionalLaw_independent P Γ hΓ⟩
  · intro x
    rw [(admissibleCoupling_means P Γ hΓ x).1,
      (admissibleCoupling_means P Γ hΓ x).2]
    exact homogeneous_logit_difference P hP.homogeneous x
end CausalSmith.Stat.LogoddsLowsmoothFrontier
