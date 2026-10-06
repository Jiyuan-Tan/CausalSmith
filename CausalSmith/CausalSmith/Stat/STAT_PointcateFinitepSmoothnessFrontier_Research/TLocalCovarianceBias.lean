module
public import Causalean.Tactic.IntegralLinearity
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.Kernels

/-! Local covariance decomposition, denominator positivity, and Holder bias bounds. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


/-- Bounded Borel functions belong to the window L² space. -/
-- @node: covariance_memLp_of_bound
lemma covariance_memLp_of_bound (h : ℝ) (f : unitInterval → ℝ)
    (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) :
    MemLp f 2 (design.restrict (window h)) := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  exact MemLp.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))

/-- Integrating the Borel histogram kernel gives a Borel average. -/
-- @node: covariance_measurable_projOp
@[fun_prop] lemma covariance_measurable_projOp (h : ℝ) (j : ℕ)
    (f : unitInterval → ℝ) (hf : Measurable f) : Measurable (projOp h j f) := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hm : Measurable (fun xz : unitInterval × unitInterval =>
      projKernel h j xz.1 xz.2 * f xz.2) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- A bounded input has bounded histogram averages even before cell normalization is used. -/
-- @node: covariance_projOp_memLp
lemma covariance_projOp_memLp (h : ℝ) (j : ℕ) (f : unitInterval → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) :
    MemLp (projOp h j f) 2 (design.restrict (window h)) := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  apply covariance_memLp_of_bound h _ (covariance_measurable_projOp h j f hf)
    (|(cellLen h j)⁻¹| * C)
  intro x
  have hp : ∀ᵐ z ∂design, ‖projKernel h j x z * f z‖ ≤ |(cellLen h j)⁻¹| * C := by
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_mul]
    have hk : |projKernel h j x z| ≤ |(cellLen h j)⁻¹| := by
      simp only [projKernel]; split_ifs <;> simp
    exact mul_le_mul hk (hb z) (abs_nonneg _) (abs_nonneg _)
  have hi := norm_integral_le_of_norm_le_const hp
  simpa only [projOp, Real.norm_eq_abs, probReal_univ, mul_one] using hi

/-- Histogram averaging is local: equal window inputs have equal averages. -/
-- @node: covariance_projOp_congr
lemma covariance_projOp_congr (h : ℝ) (j : ℕ) (f g : unitInterval → ℝ)
    (heq : ∀ x ∈ window h, f x = g x) (x : unitInterval) :
    projOp h j f x = projOp h j g x := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases hz : z ∈ window h
  · dsimp only
    rw [heq z hz]
  · simp [projKernel, hz]

/-- The coarse average of one is one on the window. -/
-- @node: covariance_projOp_zero_one
lemma covariance_projOp_zero_one (h : ℝ) (hh : 0 < h ∧ h ≤ 1)
    (x : unitInterval) (hx : x ∈ window h) : projOp h 0 (fun _ => 1) x = 1 := by
  rw [projOp_eq_window_integral]
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  calc
    _ = ∫ z in window h, h⁻¹ ∂design := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hw] with z hz
      simp only [projKernel_zero_on_window h x z hx hz, mul_one]
    _ = 1 := by
      simp [integral_const, Measure.real, design_window h hh,
        ENNReal.toReal_ofReal hh.1.le, hh.1.ne']

/-- Nestedness propagates preservation of one to every resolution. -/
-- @node: covariance_projOp_one
lemma covariance_projOp_one (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (x : unitInterval) (hx : x ∈ window h) : projOp h j (fun _ => 1) x = 1 := by
  have hf := covariance_memLp_of_bound h (fun _ => 1) measurable_const 1 (by intro; norm_num)
  have hn := (dyadic_projection_geometry h 0 hh).1 _ _ hf hf |>.2.2.1 j 0 x hx
  rw [covariance_projOp_congr h j _ (fun _ => 1)
    (covariance_projOp_zero_one h hh) x] at hn
  simpa only [Nat.min_zero, covariance_projOp_zero_one h hh x hx] using hn

/-- Positivity and normalization of histogram averaging preserve any bounded range. -/
-- @node: covariance_projOp_range
lemma covariance_projOp_range (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (f : unitInterval → ℝ) (hf : MemLp f 2 (design.restrict (window h)))
    (a b : ℝ) (hb : ∀ x, a ≤ f x ∧ f x ≤ b) (x : unitInterval)
    (hx : x ∈ window h) : a ≤ projOp h j f x ∧ projOp h j f x ≤ b := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hc (c : ℝ) : projOp h j (fun _ => c) x = c := by
    calc
      _ = projOp h j (fun _ => 1) x * c := by
        simp only [projOp, mul_one, integral_mul_const]
      _ = c := by rw [covariance_projOp_one h hh j x hx, one_mul]
  have hk (z : unitInterval) : 0 ≤ projKernel h j x z := by
    simp only [projKernel]; split_ifs
    · exact inv_nonneg.mpr (div_nonneg hh.1.le (by positivity))
    · exact le_rfl
  have hca := integrable_projKernel_mul h j (fun _ => a) (memLp_const a) x
  have hcb := integrable_projKernel_mul h j (fun _ => b) (memLp_const b) x
  have hfi := integrable_projKernel_mul h j f hf x
  constructor
  · rw [← hc a]
    exact integral_mono hca hfi (fun z => mul_le_mul_of_nonneg_left (hb z).1 (hk z))
  · rw [← hc b]
    exact integral_mono hfi hcb (fun z => mul_le_mul_of_nonneg_left (hb z).2 (hk z))

/-- Self-adjointness and preservation of one conserve the window integral. -/
-- @node: covariance_projOp_integral
lemma covariance_projOp_integral (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (f : unitInterval → ℝ) (hf : MemLp f 2 (design.restrict (window h))) :
    (∫ x in window h, projOp h j f x ∂design) = ∫ x in window h, f x ∂design := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have he := projOp_self_adjoint h j f (fun _ => 1) hf (memLp_const 1)
  simp only [mul_one] at he
  rw [he]
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hw] with x hx
  rw [covariance_projOp_one h hh j x hx, mul_one]

/-- A projection residual is orthogonal to every projected bounded input. -/
-- @node: covariance_projection_residual_pairing
lemma covariance_projection_residual_pairing (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (f g : unitInterval → ℝ) (hf : MemLp f 2 (design.restrict (window h)))
    (hg : MemLp g 2 (design.restrict (window h)))
    (hpg : MemLp (projOp h j g) 2 (design.restrict (window h))) :
    (∫ x in window h, projOp h j f x * projOp h j g x ∂design) =
      ∫ x in window h, f x * projOp h j g x ∂design := by
  rw [projOp_self_adjoint h j f (projOp h j g) hf hpg]
  have hn := (dyadic_projection_geometry h 0 hh).1 g g hg hg |>.2.2.1
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hw] with x hx
  rw [hn j j x hx, min_self]

/-- Conserved cell averages and overlap give the public positive covariance denominator. -/
-- @node: covariance_denominator_lower
lemma covariance_denominator_lower (κ : Params) (law : ObservedLaw) (hm : InModel κ law)
    (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (J : ℕ) :
    3/16 ≤ localDenominator law h J := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have he := covariance_memLp_of_bound h law.e hm.propensityHolder.1.measurable 20
    hm.propensityHolder.2.1
  have hpe := covariance_projOp_memLp h J law.e hm.propensityHolder.1.measurable 20
    (by norm_num) hm.propensityHolder.2.1
  have hei := he.integrable (by norm_num)
  have hpei := hpe.integrable (by norm_num)
  have hpe2 := hpe.integrable_sq
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  have hlower : h * (3/16 : ℝ) ≤
      ∫ x in window h, projOp h J law.e x - (projOp h J law.e x)^2 ∂design := by
    calc
      _ = ∫ x in window h, (3/16 : ℝ) ∂design := by
        simp [integral_const, Measure.real, design_window h hh, ENNReal.toReal_ofReal hh.1.le]
      _ ≤ _ := by
        apply integral_mono_ae (integrable_const _) (hpei.sub hpe2)
        filter_upwards [ae_restrict_mem hw] with x hx
        change (3/16 : ℝ) ≤ projOp h J law.e x - (projOp h J law.e x)^2
        have hp := covariance_projOp_range h hh J law.e he (1/4) (3/4) hm.overlap x hx
        nlinarith [mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hp.2)]
  have hmean := covariance_projOp_integral h hh J law.e he
  rw [integral_sub hpei hpe2, hmean] at hlower
  unfold localDenominator
  integral_linearity
  have hs := mul_le_mul_of_nonneg_left hlower (inv_nonneg.mpr hh.1.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hh.1.ne', one_mul] using hs

/-- Orthogonal residuals and the original mean decomposition give the exact covariance identity. -/
-- @node: covariance_bias_identity
lemma covariance_bias_identity (κ : Params) (law : ObservedLaw) (hm : InModel κ law)
    (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (J : ℕ) :
    localNumerator law h J - law.theta * localDenominator law h J =
      h⁻¹ * (∫ x in window h, (law.e x - projOp h J law.e x) *
        (law.m0 x - projOp h J law.m0 x) ∂design) +
      h⁻¹ * (∫ x in window h, law.e x * (1-projOp h J law.e x) *
        (law.tau x-law.theta) ∂design) := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have he := covariance_memLp_of_bound h law.e hm.propensityHolder.1.measurable 20
    hm.propensityHolder.2.1
  have hm0 := covariance_memLp_of_bound h law.m0 hm.baselineHolder.1.measurable 20
    hm.baselineHolder.2.1
  have hpe := covariance_projOp_memLp h J law.e hm.propensityHolder.1.measurable 20
    (by norm_num) hm.propensityHolder.2.1
  have hpm := covariance_projOp_memLp h J law.m0 hm.baselineHolder.1.measurable 20
    (by norm_num) hm.baselineHolder.2.1
  have het : MemLp (fun x => law.e x * law.tau x) 2 (design.restrict (window h)) := by
    apply covariance_memLp_of_bound h _ (by
      have := hm.propensityHolder.1.measurable
      have := hm.effectHolder.1.measurable
      fun_prop) 400
    intro x
    rw [abs_mul]
    nlinarith [hm.propensityHolder.2.1 x, hm.effectHolder.2.1 x,
      abs_nonneg (law.e x), abs_nonneg (law.tau x)]
  have hi_e := he.integrable (by norm_num)
  have hi_e2 := hpe.integrable_sq
  have hi_em := he.integrable_mul hm0
  have hi_pm := hpe.integrable_mul hm0
  have hi_epm := he.integrable_mul hpm
  have hi_ppm := hpe.integrable_mul hpm
  have hi_epe := he.integrable_mul hpe
  have hi_et := het.integrable (by norm_num)
  have hi_pet := hpe.integrable_mul het
  have hi_res := (he.sub hpe).integrable_mul (hm0.sub hpm)
  simp only [Pi.mul_def, Pi.sub_def] at hi_em hi_pm hi_epm hi_ppm hi_epe hi_pet hi_res
  have hpairm := covariance_projection_residual_pairing h hh J law.e law.m0 he hm0 hpm
  have hpaire := covariance_projection_residual_pairing h hh J law.e law.e he he hpe
  have hpaire' : (∫ x in window h, (projOp h J law.e x)^2 ∂design) =
      ∫ x in window h, law.e x * projOp h J law.e x ∂design := by
    simpa only [pow_two] using hpaire
  have hres : (∫ x in window h, (law.e x - projOp h J law.e x) *
      (law.m0 x - projOp h J law.m0 x) ∂design) =
      (∫ x in window h, law.e x * law.m0 x ∂design) -
        ∫ x in window h, projOp h J law.e x * law.m0 x ∂design := by
    simp only [sub_mul, mul_sub]
    have h1 := hi_em.sub hi_pm
    have h2 := hi_epm.sub hi_ppm
    simp only [Pi.sub_def] at h1 h2
    integral_linearity
    rw [hpairm]
    ring
  have hnum : localNumerator law h J = h⁻¹ *
      ((∫ x in window h, law.e x * law.m0 x ∂design) -
       (∫ x in window h, projOp h J law.e x * law.m0 x ∂design) +
       (∫ x in window h, law.e x * law.tau x ∂design) -
       (∫ x in window h, projOp h J law.e x * (law.e x * law.tau x) ∂design)) := by
    unfold localNumerator ObservedLaw.m1 ObservedLaw.g
    simp only [mul_add]
    have h1 := hi_em.add hi_et
    have h2 := hi_pm.add hi_pet
    simp only [Pi.add_def] at h1 h2
    integral_linearity
    ring
  have hden : localDenominator law h J = h⁻¹ *
      ((∫ x in window h, law.e x ∂design) -
       ∫ x in window h, law.e x * projOp h J law.e x ∂design) := by
    unfold localDenominator
    integral_linearity
    rw [hpaire']
  have heffect : (∫ x in window h, law.e x * (1-projOp h J law.e x) *
      (law.tau x-law.theta) ∂design) =
      (∫ x in window h, law.e x * law.tau x ∂design) -
      (∫ x in window h, projOp h J law.e x * (law.e x * law.tau x) ∂design) -
      law.theta * ((∫ x in window h, law.e x ∂design) -
        ∫ x in window h, law.e x * projOp h J law.e x ∂design) := by
    have heq (x : unitInterval) : law.e x * (1-projOp h J law.e x) *
        (law.tau x-law.theta) = law.e x * law.tau x -
        projOp h J law.e x * (law.e x * law.tau x) -
        law.theta * (law.e x - law.e x * projOp h J law.e x) := by ring
    simp_rw [heq]
    have h1 := hi_et.sub hi_pet
    have h2 := hi_e.sub hi_epe
    have h3 := h2.const_mul law.theta
    simp only [Pi.sub_def] at h1 h2 h3
    integral_linearity
  rw [hnum, hden, hres, heffect]
  ring

/-- A uniform window bound controls the normalized Lebesgue integral. -/
-- @node: covariance_normalized_integral_bound
lemma covariance_normalized_integral_bound (h : ℝ) (hh : 0 < h ∧ h ≤ 1)
    (f : unitInterval → ℝ) (C : ℝ) (hb : ∀ x ∈ window h, |f x| ≤ C) :
    |h⁻¹ * ∫ x in window h, f x ∂design| ≤ C := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  have hn : ∀ᵐ x ∂(design.restrict (window h)), ‖f x‖ ≤ C := by
    filter_upwards [ae_restrict_mem hw] with x hx
    simpa only [Real.norm_eq_abs] using hb x hx
  have hi := norm_integral_le_of_norm_le_const hn
  have hmass : (design.restrict (window h)).real univ = h := by
    simp [Measure.real, design_window h hh, ENNReal.toReal_ofReal hh.1.le]
  rw [hmass, Real.norm_eq_abs] at hi
  rw [abs_mul, abs_of_pos (inv_pos.mpr hh.1)]
  calc
    _ ≤ h⁻¹ * (C * h) := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hh.1.le)
    _ = C := by field_simp [hh.1.ne']

/-- The two Holder approximation errors give the product-smoothness bias. -/
-- @node: covariance_baseline_bias_bound
lemma covariance_baseline_bias_bound (κ : Params) (hκ : κ.Valid)
    (law : ObservedLaw) (hm : InModel κ law) (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (J : ℕ) :
    |h⁻¹ * ∫ x in window h, (law.e x - projOp h J law.e x) *
      (law.m0 x - projOp h J law.m0 x) ∂design| ≤ 400 * cellLen h J ^ sumReg κ := by
  have hg := (dyadic_projection_geometry h J hh).2.2.2
  have he := (hg κ.α law.e hκ.2.1 hm.propensityHolder).1
  have hm0 := (hg κ.β law.m0 hκ.2.2.1 hm.baselineHolder).1
  apply covariance_normalized_integral_bound h hh
  intro x hx
  have hc : 0 < cellLen h J := div_pos hh.1 (by positivity)
  rw [abs_mul, sumReg, Real.rpow_add hc]
  calc
    _ ≤ (20 * cellLen h J ^ κ.α) * (20 * cellLen h J ^ κ.β) :=
      mul_le_mul (he J x hx) (hm0 J x hx) (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- Effect smoothness on the centered window gives the public effect-bias ledger. -/
-- @node: covariance_effect_bias_bound
lemma covariance_effect_bias_bound (κ : Params) (hκ : κ.Valid)
    (law : ObservedLaw) (hm : InModel κ law) (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (J : ℕ) :
    |h⁻¹ * ∫ x in window h, law.e x * (1-projOp h J law.e x) *
      (law.tau x-law.theta) ∂design| ≤ 15 * h ^ κ.γ := by
  have he := covariance_memLp_of_bound h law.e hm.propensityHolder.1.measurable 20
    hm.propensityHolder.2.1
  apply covariance_normalized_integral_bound h hh
  intro x hx
  have hp := covariance_projOp_range h hh J law.e he (1/4) (3/4) hm.overlap x hx
  have hex := hm.overlap x
  have hdist : |(x : ℝ) - (xstar : ℝ)| ≤ h := by
    change (x : ℝ) ∈ Icc (1/2-h/2) (1/2+h/2) at hx
    change |(x : ℝ) - 1/2| ≤ h
    exact abs_le.mpr ⟨by linarith [hx.1, hh.1], by linarith [hx.2, hh.1]⟩
  have ht : |law.tau x - law.theta| ≤ 20 * h ^ κ.γ := by
    exact (hm.effectHolder.2.2 x xstar).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hdist hκ.2.2.2.1.le)
        (by norm_num))
  have hw : 0 ≤ law.e x * (1-projOp h J law.e x) ∧
      law.e x * (1-projOp h J law.e x) ≤ 9/16 := by
    constructor
    · exact mul_nonneg (by linarith [hex.1]) (by linarith [hp.2])
    · nlinarith [mul_nonneg (sub_nonneg.mpr hex.2) (by linarith [hp.2] : 0 ≤ 1-projOp h J law.e x)]
  rw [abs_mul, abs_of_nonneg hw.1]
  calc
    _ ≤ (9/16 : ℝ) * (20*h^κ.γ) :=
      mul_le_mul hw.2 ht (abs_nonneg _) (by norm_num)
    _ ≤ 15*h^κ.γ := by nlinarith [Real.rpow_nonneg hh.1.le κ.γ]

-- @node: lem:local-covariance-bias
/-- The localized covariance identity has a positive denominator and the full Holder bias bound. -/
lemma local_covariance_bias (κ : Params) (hκ : κ.Valid) (law : ObservedLaw) (hm : InModel κ law)
    (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (J : ℕ) :
  3/16 ≤ localDenominator law h J ∧
  localNumerator law h J - law.theta * localDenominator law h J =
    h⁻¹ * (∫ x in window h, (law.e x - projOp h J law.e x) * (law.m0 x - projOp h J law.m0 x) ∂design) +
    h⁻¹ * (∫ x in window h, law.e x * (1-projOp h J law.e x) * (law.tau x-law.theta) ∂design) ∧
  |localNumerator law h J-law.theta * localDenominator law h J| ≤
    400 * cellLen h J ^ sumReg κ + 15 * h ^ κ.γ := by
  have hid := covariance_bias_identity κ law hm h hh J
  refine ⟨covariance_denominator_lower κ law hm h hh J, hid, ?_⟩
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add
    (covariance_baseline_bias_bound κ hκ law hm h hh J)
    (covariance_effect_bias_bound κ hκ law hm h hh J))

/-- Lowering the propensity exponent preserves the localized covariance bias calculation. -/
-- @node: local_covariance_bias_of_holder
lemma local_covariance_bias_of_holder (κ : Params) (hκ : κ.Valid) (law : ObservedLaw) (hm : InModel κ law)
    (a : ℝ) (ha : 0 < a ∧ a ≤ 1) (he : holderBall a law.e)
    (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (J : ℕ) :
  3/16 ≤ localDenominator law h J ∧
  |localNumerator law h J-law.theta * localDenominator law h J| ≤
    400 * cellLen h J ^ (a+κ.β) + 15 * h ^ κ.γ := by
  let κa : Params := ⟨κ.p, a, κ.β, κ.γ⟩
  have hκa : κa.Valid := ⟨hκ.1, ha, hκ.2.2⟩
  have hma : InModel κa law :=
    ⟨hm.uniform, hm.overlap, he, hm.baselineHolder, hm.effectHolder,
      hm.effectRange, hm.conditionalMoment⟩
  have hb := local_covariance_bias κa hκa law hma h hh J
  exact ⟨hb.1, hb.2.2⟩

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
