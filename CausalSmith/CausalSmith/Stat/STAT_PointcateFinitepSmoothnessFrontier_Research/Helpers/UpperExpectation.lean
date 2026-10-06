module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.PhaseAlgebra
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.Completion
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.TwoBlockLegs
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.TLocalCovarianceBias

/-! Original-record expectation identities for the public two-block denominator. -/
public section
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- The Bernoulli mark integrates a covariate-only treatment term exactly. -/
-- @node: upper_record_treatment_integral
lemma upper_record_treatment_integral (law : ObservedLaw) (x : unitInterval) (c : ℝ) :
    (∫ r : Bool × ℝ, bit r.1 * c ∂recordMeasure law.e law.Q x) = law.e x * c := by
  have hi (a : Bool) : Integrable (fun r : Bool × ℝ => bit r.1 * c)
      ((Measure.dirac a).prod (law.Q a x)) := by
    apply Integrable.of_bound (by fun_prop) |c|
    exact Filter.Eventually.of_forall fun r => by cases r.1 <;> simp [bit, Real.norm_eq_abs]
  have he (a : Bool) : (∫ r : Bool × ℝ, bit r.1 * c
      ∂((Measure.dirac a).prod (law.Q a x))) = bit a * c := by
    rw [Measure.dirac_prod, integral_map (by fun_prop) (by fun_prop)]
    simp
  unfold recordMeasure
  rw [integral_add_measure ((hi true).smul_measure ENNReal.ofReal_ne_top)
    ((hi false).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, smul_eq_mul, he]
  simp [bit, ENNReal.toReal_ofReal (law.e_range x).1]

/-- Uniform design and the observational kernel identify every bounded treatment-weighted
covariate integral, without involving outcomes or an estimated propensity. -/
-- @node: upper_treatment_integral
lemma upper_treatment_integral (law : ObservedLaw) (hu : UniformDesign law)
    (f : unitInterval → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) :
    (∫ o, bit (A o) * f (X o) ∂law.P) = ∫ x, law.e x * f x ∂design := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  let := completion_record_kernel_markov law
  have hi : Integrable (fun o => bit (A o) * f (X o)) law.P := by
    apply Integrable.of_bound (by unfold X A; fun_prop) C
    exact Filter.Eventually.of_forall fun o => by
      cases ha : A o <;> simp [bit, ha, Real.norm_eq_abs]
      · exact (abs_nonneg (f (X o))).trans (hb (X o))
      · exact hb (X o)
  have hv : law.P = design ⊗ₘ recordKernel law.e law.e_measurable law.Q :=
    law.record_version.trans (by rw [hu])
  rw [hv] at hi ⊢
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => upper_record_treatment_integral law x (f x)

/-- The public split has two nonempty disjoint blocks at every allowed sample size. -/
-- @node: upper_blocks_nonempty_disjoint
lemma upper_blocks_nonempty_disjoint (n : ℕ) (hn : 2 ≤ n) :
    (treatmentBlock n).Nonempty ∧ (outcomeBlock n).Nonempty ∧
      Disjoint (treatmentBlock n) (outcomeBlock n) := by
  have hhalf : 0 < n/2 := Nat.div_pos hn (by norm_num)
  have hlt : n/2 < n := Nat.div_lt_self (by omega) (by norm_num)
  refine ⟨⟨⟨0, by omega⟩, ?_⟩, ⟨⟨n/2, hlt⟩, ?_⟩, ?_⟩
  · simpa [treatmentBlock] using hhalf
  · simp [outcomeBlock]
  · apply Finset.disjoint_left.mpr
    intro i ht hy
    simp only [treatmentBlock, outcomeBlock, Finset.mem_filter,
      Finset.mem_univ, true_and] at ht hy
    omega

/-- The treatment-only histogram kernel has a deterministic bound and hence an L² norm. -/
-- @node: upper_denominator_kernel_memLp
lemma upper_denominator_kernel_memLp (law : ObservedLaw) (h : ℝ) (J : ℕ) :
    MemLp (fun oz : O × O => h⁻¹ * (bit (A oz.1) * bit (A oz.2) *
      projKernel h J (X oz.1) (X oz.2))) 2 (law.P.prod law.P) := by
  apply MemLp.of_bound (by unfold A X; fun_prop) (|h⁻¹| * |(cellLen h J)⁻¹|)
  apply Filter.Eventually.of_forall
  intro oz
  rw [Real.norm_eq_abs, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  cases ha : A oz.1 <;> cases hb : A oz.2 <;>
    simp only [bit, ha, hb, Bool.false_eq_true, ↓reduceIte, zero_mul, mul_zero,
      one_mul, mul_one, abs_zero]
  all_goals first
    | exact abs_nonneg _
    | unfold projKernel; split_ifs <;> simp

/-- Integrating the donor treatment mark produces the projected propensity. -/
-- @node: upper_denominator_kernel_section
lemma upper_denominator_kernel_section (law : ObservedLaw) (hu : UniformDesign law)
    (h : ℝ) (J : ℕ) (o : O) :
    (∫ z, h⁻¹ * (bit (A o) * bit (A z) * projKernel h J (X o) (X z)) ∂law.P) =
      h⁻¹ * bit (A o) * projOp h J law.e (X o) := by
  have hb (x : unitInterval) : |projKernel h J (X o) x| ≤ |(cellLen h J)⁻¹| := by
    unfold projKernel; split_ifs <;> simp
  have he := upper_treatment_integral law hu (projKernel h J (X o))
    (by fun_prop) _ hb
  calc
    _ = h⁻¹ * bit (A o) * (∫ z, bit (A z) * projKernel h J (X o) (X z) ∂law.P) := by
      rw [← integral_const_mul]
      congr 1
      funext z
      ring
    _ = h⁻¹ * bit (A o) * projOp h J law.e (X o) := by
      rw [he]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => mul_comm _ _

/-- The projected propensity is bounded globally, including outside the window. -/
-- @node: upper_projected_propensity_bound
lemma upper_projected_propensity_bound (law : ObservedLaw) (h : ℝ) (J : ℕ) :
    ∀ x, |projOp h J law.e x| ≤ |(cellLen h J)⁻¹| := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  intro x
  have hb : ∀ᵐ z ∂design, ‖projKernel h J x z * law.e z‖ ≤ |(cellLen h J)⁻¹| := by
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (law.e_range z).1]
    have hk : |projKernel h J x z| ≤ |(cellLen h J)⁻¹| := by
      unfold projKernel; split_ifs <;> simp
    exact (mul_le_mul_of_nonneg_right hk (law.e_range z).1).trans
      (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (law.e_range z).2 (abs_nonneg ((cellLen h J)⁻¹)))
  simpa only [projOp, Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hb

/-- The denominator's product mean is the propensity paired with its histogram projection. -/
-- @node: upper_denominator_kernel_mean
lemma upper_denominator_kernel_mean (law : ObservedLaw) (hu : UniformDesign law)
    (h : ℝ) (J : ℕ) :
    (∫ o, ∫ z, h⁻¹ * (bit (A o) * bit (A z) *
      projKernel h J (X o) (X z)) ∂law.P ∂law.P) =
      h⁻¹ * ∫ x in window h, law.e x * projOp h J law.e x ∂design := by
  simp_rw [upper_denominator_kernel_section law hu]
  rw [show (fun o => h⁻¹ * bit (A o) * projOp h J law.e (X o)) =
    (fun o => h⁻¹ * (bit (A o) * projOp h J law.e (X o))) by funext; ring,
    integral_const_mul,
    upper_treatment_integral law hu _
      (covariance_measurable_projOp h J law.e law.e_measurable) _
      (upper_projected_propensity_bound law h J)]
  congr 1
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  rw [← integral_indicator hw]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ window h
  · simp [hx]
  · have hp : projOp h J law.e x = 0 := by simp [projOp, projKernel, hx]
    simp [hx, hp]

/-- The denominator uses exactly the generic linear-minus-bilinear two-block statistic. -/
-- @node: upper_denominator_twoBlock
lemma upper_denominator_twoBlock (κ : Params) (n : ℕ) :
    denominatorHat κ n = twoBlockStatistic (treatmentBlock n) (outcomeBlock n)
      (fun o => (upperH κ n)⁻¹ * (if X o ∈ window (upperH κ n) then bit (A o) else 0))
      (fun o z => (upperH κ n)⁻¹ * (bit (A o) * bit (A z) *
        projKernel (upperH κ n) (upperJ κ n) (X o) (X z))) := by
  funext o
  simp only [denominatorHat, twoBlockStatistic, ← Finset.mul_sum, mul_inv]
  ring

/-- The raw localized treatment mean is the integral of the propensity on the window. -/
-- @node: upper_denominator_linear_mean
lemma upper_denominator_linear_mean (law : ObservedLaw) (hu : UniformDesign law) (h : ℝ) :
    (∫ o, h⁻¹ * (if X o ∈ window h then bit (A o) else 0) ∂law.P) =
      h⁻¹ * ∫ x in window h, law.e x ∂design := by
  rw [integral_const_mul]
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  have he := upper_treatment_integral law hu ((window h).indicator (fun _ => 1))
    (measurable_const.indicator hw) 1 (fun x => by by_cases hx : x ∈ window h <;> simp [hx])
  have hleft : (fun o => bit (A o) * (window h).indicator (fun _ => (1 : ℝ)) (X o)) =
      (fun o => if X o ∈ window h then bit (A o) else 0) := by
    funext o; by_cases hx : X o ∈ window h <;> simp [hx]
  have hright : (fun x => law.e x * (window h).indicator (fun _ => (1 : ℝ)) x) =
      (window h).indicator law.e := by
    funext x; by_cases hx : x ∈ window h <;> simp [hx]
  rw [hleft, hright, integral_indicator hw] at he
  exact congrArg (fun v : ℝ => h⁻¹ * v) he

/-- Independence of the two public blocks and projection orthogonality give the exact
untruncated denominator expectation required by the bias ledger. -/
-- @node: upper_denominator_expectation
lemma upper_denominator_expectation (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n)
    (law : ObservedLaw) (hm : InModel κ law) :
    (∫ o, denominatorHat κ n o ∂Measure.pi (fun _ : Fin n => law.P)) =
      localDenominator law (upperH κ n) (upperJ κ n) := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  let h := upperH κ n
  let J := upperJ κ n
  have hF : MemLp (fun o => h⁻¹ * (if X o ∈ window h then bit (A o) else 0)) 2 law.P := by
    have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
    have hmeas : Measurable (fun o : O => if X o ∈ window h then bit (A o) else 0) :=
      Measurable.ite (hw.preimage (by unfold X; fun_prop))
        (by unfold A; fun_prop) measurable_const
    apply MemLp.of_bound (hmeas.const_mul _).aestronglyMeasurable |h⁻¹|
    apply Filter.Eventually.of_forall
    intro o
    rw [Real.norm_eq_abs]
    by_cases hx : X o ∈ window h
    · cases ha : A o <;> simp [hx, bit, ha]
    · simp [hx]
  obtain ⟨ht, hy, hd⟩ := upper_blocks_nonempty_disjoint n hn
  rw [upper_denominator_twoBlock]
  rw [twoBlock_expectation law.P _ _ hd ht hy _ _ hF
    (upper_denominator_kernel_memLp law h J)]
  rw [upper_denominator_linear_mean law hm.uniform,
    upper_denominator_kernel_mean law hm.uniform]
  have he := covariance_memLp_of_bound h law.e law.e_measurable 20 hm.propensityHolder.2.1
  have hpe := covariance_projOp_memLp h J law.e law.e_measurable 20
    (by norm_num) hm.propensityHolder.2.1
  have hp := covariance_projection_residual_pairing h
    (upper_bandwidth_certificate κ hκ n hn).1 J law.e law.e he he hpe
  have hp' : (∫ x in window h, (projOp h J law.e x)^2 ∂design) =
      ∫ x in window h, law.e x * projOp h J law.e x ∂design := by
    simpa only [pow_two] using hp
  change h⁻¹ * (∫ x in window h, law.e x ∂design) -
    h⁻¹ * (∫ x in window h, law.e x * projOp h J law.e x ∂design) = _
  change _ = h⁻¹ * ∫ x in window h, law.e x - (projOp h J law.e x)^2 ∂design
  rw [integral_sub (he.integrable (by norm_num)) hpe.integrable_sq, hp']
  ring

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
