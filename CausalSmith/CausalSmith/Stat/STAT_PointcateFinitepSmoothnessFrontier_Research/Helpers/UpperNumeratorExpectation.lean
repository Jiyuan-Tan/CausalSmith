module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperTruncatedExpectation
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperTruncation

/-! Exact original-record expectations for the multiscale numerator. -/
public section
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- A single clipped histogram product has a deterministic envelope on the product law. -/
-- @node: upper_projected_clipped_memLp
lemma upper_projected_clipped_memLp (law : ObservedLaw) (h : ℝ) (j : ℕ) (T : ℝ) :
    MemLp (fun oz : O × O => bit (A oz.1) *
      (projKernel h j (X oz.1) (X oz.2) * trunc T (Y oz.2))) 2 (law.P.prod law.P) := by
  apply MemLp.of_bound (by unfold A X Y; fun_prop) (|(cellLen h j)⁻¹| * |T|)
  apply Filter.Eventually.of_forall
  intro oz
  rw [Real.norm_eq_abs]
  have hk : |projKernel h j (X oz.1) (X oz.2)| ≤ |(cellLen h j)⁻¹| := by
    unfold projKernel; split_ifs <;> simp
  have hb := mul_le_mul hk (upper_trunc_abs_bound T (Y oz.2))
    (abs_nonneg _) (abs_nonneg _)
  cases ha : A oz.1 <;> simp only [bit, ha, Bool.false_eq_true, ↓reduceIte,
    zero_mul, one_mul, abs_zero]
  · positivity
  · simpa only [abs_mul] using hb

/-- Integrating the treatment record first pairs its projected propensity with the
clipped conditional marginal mean of the same outcome record. -/
-- @node: upper_projected_clipped_mean
lemma upper_projected_clipped_mean (law : ObservedLaw) (hu : UniformDesign law)
    (h : ℝ) (j : ℕ) (T : ℝ) :
    (∫ o, ∫ z, bit (A o) * (projKernel h j (X o) (X z) * trunc T (Y z))
      ∂law.P ∂law.P) =
      ∫ x in window h, projOp h j law.e x * truncatedMean law T x ∂design := by
  rw [integral_integral_swap ((upper_projected_clipped_memLp law h j T).integrable (by norm_num))]
  have hs (z : O) :
      (∫ o, bit (A o) * (projKernel h j (X o) (X z) * trunc T (Y z)) ∂law.P) =
        projOp h j law.e (X z) * trunc T (Y z) := by
    have hk (x : unitInterval) : |projKernel h j x (X z)| ≤ |(cellLen h j)⁻¹| := by
      unfold projKernel; split_ifs <;> simp
    rw [show (fun o => bit (A o) * (projKernel h j (X o) (X z) * trunc T (Y z))) =
      (fun o => (bit (A o) * projKernel h j (X o) (X z)) * trunc T (Y z)) by funext; ring,
      integral_mul_const, upper_treatment_integral law hu _ (by fun_prop) _ hk]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by dsimp only; rw [projKernel_symm]; ring
  simp_rw [hs]
  rw [upper_marginal_truncated_integral law hu _
    (covariance_measurable_projOp h j law.e law.e_measurable) _
    (upper_projected_propensity_bound law h j)]
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  rw [← integral_indicator hw]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ window h <;> simp [hx, projOp, projKernel]

/-- Adjacent clipped histogram terms are square integrable as a difference. -/
-- @node: upper_band_clipped_memLp
lemma upper_band_clipped_memLp (law : ObservedLaw) (h : ℝ) (j : ℕ) (T : ℝ) :
    MemLp (fun oz : O × O => bit (A oz.1) *
      (bandKernel h j (X oz.1) (X oz.2) * trunc T (Y oz.2))) 2 (law.P.prod law.P) := by
  convert (upper_projected_clipped_memLp law h j T).sub
    (upper_projected_clipped_memLp law h (j-1) T) using 1
  funext oz
  simp only [bandKernel, Pi.sub_apply]
  ring

/-- The conditional mean of an adjacent clipped histogram term is the band pairing. -/
-- @node: upper_band_clipped_mean
lemma upper_band_clipped_mean (law : ObservedLaw) (hu : UniformDesign law)
    (h : ℝ) (j : ℕ) (T : ℝ) :
    (∫ o, ∫ z, bit (A o) * (bandKernel h j (X o) (X z) * trunc T (Y z))
      ∂law.P ∂law.P) =
      ∫ x in window h, bandOp h j law.e x * truncatedMean law T x ∂design := by
  have he := covariance_memLp_of_bound h law.e law.e_measurable 1
    (fun x => by rw [abs_of_nonneg (law.e_range x).1]; exact (law.e_range x).2)
  have hc : MemLp (truncatedMean law T) 2 (design.restrict (window h)) := by
    let : IsProbabilityMeasure design := by unfold design; infer_instance
    apply MemLp.of_bound (by fun_prop) (2*|T|)
    apply Filter.Eventually.of_forall
    intro x
    have hb (a : Bool) : |∫ y, trunc T y ∂law.Q a x| ≤ |T| := by
      have hn : ∀ᵐ y ∂law.Q a x, ‖trunc T y‖ ≤ |T| :=
        Filter.Eventually.of_forall fun y => by
          simpa only [Real.norm_eq_abs] using upper_trunc_abs_bound T y
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const hn
    have hp := abs_add_le (law.e x * ∫ y, trunc T y ∂law.Q true x)
      ((1-law.e x) * ∫ y, trunc T y ∂law.Q false x)
    rw [abs_mul, abs_mul, abs_of_nonneg (law.e_range x).1,
      abs_of_nonneg (sub_nonneg.mpr (law.e_range x).2)] at hp
    have hp' := add_le_add (mul_le_mul_of_nonneg_left (hb true) (law.e_range x).1)
      (mul_le_mul_of_nonneg_left (hb false) (sub_nonneg.mpr (law.e_range x).2))
    change |truncatedMean law T x| ≤ _
    exact hp.trans (hp'.trans (by nlinarith [abs_nonneg T]))
  have hi (k : ℕ) := (upper_projected_clipped_memLp law h k T).integrable (by norm_num)
  rw [← integral_prod _ ((upper_band_clipped_memLp law h j T).integrable (by norm_num))]
  simp only [bandKernel, sub_mul, mul_sub]
  rw [integral_sub (hi j) (hi (j-1)), integral_prod _ (hi j), integral_prod _ (hi (j-1)),
    upper_projected_clipped_mean law hu, upper_projected_clipped_mean law hu]
  simp_rw [bandOp_eq_sub h j law.e he, sub_mul]
  exact (integral_sub ((projOp_memLp h j law.e).integrable_mul hc)
    ((projOp_memLp h (j-1) law.e).integrable_mul hc)).symm

/-- The heavy kernel is a finite sum of bounded clipped histogram products. -/
-- @node: upper_heavy_kernel_memLp
lemma upper_heavy_kernel_memLp (law : ObservedLaw) (h : ℝ) (J : ℕ)
    (T : Fin (J+1) → ℝ) :
    MemLp (fun oz : O × O => heavyKernel h J T oz.1 oz.2) 2 (law.P.prod law.P) := by
  have hs : MemLp (fun oz : O × O => ∑ j : Fin J,
      bit (A oz.1) * (bandKernel h (j.val+1) (X oz.1) (X oz.2) *
        trunc (T j.succ) (Y oz.2))) 2 (law.P.prod law.P) :=
    memLp_finsetSum _ (fun j _ => upper_band_clipped_memLp law h (j.val+1) (T j.succ))
  convert ((upper_projected_clipped_memLp law h 0 (T 0)).add hs).const_mul h⁻¹ using 1
  funext oz
  simp only [heavyKernel, bit, div_eq_mul_inv, Pi.add_apply, ← Finset.mul_sum]
  ring

/-- The expectation of the heavy kernel is the sum of the propensity-side clipped pairings. -/
-- @node: upper_heavy_kernel_mean
lemma upper_heavy_kernel_mean (law : ObservedLaw) (hu : UniformDesign law)
    (h : ℝ) (J : ℕ) (T : Fin (J+1) → ℝ) :
    (∫ o, ∫ z, heavyKernel h J T o z ∂law.P ∂law.P) =
      h⁻¹ * (∫ x in window h, projOp h 0 law.e x * truncatedMean law (T 0) x ∂design) +
      ∑ j : Fin J, h⁻¹ * ∫ x in window h,
        bandOp h (j.val+1) law.e x * truncatedMean law (T j.succ) x ∂design := by
  have hi := (upper_heavy_kernel_memLp law h J T).integrable (by norm_num)
  have hp := (upper_projected_clipped_memLp law h 0 (T 0)).integrable (by norm_num)
  have hb (j : Fin J) :=
    (upper_band_clipped_memLp law h (j.val+1) (T j.succ)).integrable (by norm_num)
  rw [← integral_prod _ hi]
  have heq : (fun oz : O × O => heavyKernel h J T oz.1 oz.2) =
      (fun oz => h⁻¹ * (bit (A oz.1) *
        (projKernel h 0 (X oz.1) (X oz.2) * trunc (T 0) (Y oz.2)) +
        ∑ j : Fin J, bit (A oz.1) * (bandKernel h (j.val+1) (X oz.1) (X oz.2) *
          trunc (T j.succ) (Y oz.2)))) := by
    funext oz
    simp only [heavyKernel, bit, div_eq_mul_inv, ← Finset.mul_sum]
    ring
  rw [heq, integral_const_mul, integral_add hp (integrable_finsetSum _ (fun j _ => hb j)),
    integral_finsetSum _ (fun j _ => hb j), integral_prod _ hp,
    upper_projected_clipped_mean law hu, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_prod _ (hb j), upper_band_clipped_mean law hu]

/-- The clipped treated linear term has its exact localized conditional expectation. -/
-- @node: upper_numerator_linear_mean
lemma upper_numerator_linear_mean (law : ObservedLaw) (hu : UniformDesign law)
    (h T : ℝ) :
    (∫ o, h⁻¹ * (if X o ∈ window h then bit (A o)*trunc T (Y o) else 0) ∂law.P) =
      h⁻¹ * ∫ x in window h, law.e x * (∫ y, trunc T y ∂law.Q true x) ∂design := by
  rw [integral_const_mul]
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  have he := upper_marked_truncated_integral law hu ((window h).indicator (fun _ => 1))
    (measurable_const.indicator hw) 1 (fun x => by by_cases hx : x ∈ window h <;> simp [hx]) T
  have hl : (fun o => (window h).indicator (fun _ => (1 : ℝ)) (X o) *
      (bit (A o)*trunc T (Y o))) =
      (fun o => if X o ∈ window h then bit (A o)*trunc T (Y o) else 0) := by
    funext o; by_cases hx : X o ∈ window h <;> simp [hx]
  have hr : (fun x => (window h).indicator (fun _ => (1 : ℝ)) x *
      (law.e x * ∫ y, trunc T y ∂law.Q true x)) =
      (window h).indicator (fun x => law.e x * ∫ y, trunc T y ∂law.Q true x) := by
    funext x; by_cases hx : x ∈ window h <;> simp [hx]
  rw [hl, hr, integral_indicator hw] at he
  exact congrArg (fun v : ℝ => h⁻¹ * v) he

/-- The sample numerator is precisely the public two-block statistic. -/
-- @node: upper_numerator_twoBlock
lemma upper_numerator_twoBlock (κ : Params) (n : ℕ) :
    numeratorHat κ n = twoBlockStatistic (treatmentBlock n) (outcomeBlock n)
      (fun o => (upperH κ n)⁻¹ * (if X o ∈ window (upperH κ n)
        then bit (A o)*trunc (upperT κ n 0) (Y o) else 0))
      (heavyKernel (upperH κ n) (upperJ κ n) (upperT κ n)) := by
  funext o
  simp only [numeratorHat, twoBlockStatistic, ← Finset.mul_sum, mul_inv]
  ring

/-- Independence gives the exact clipped numerator expectation before any bias bound. -/
-- @node: upper_numerator_expectation
lemma upper_numerator_expectation (κ : Params) (n : ℕ) (hn : 2 ≤ n)
    (law : ObservedLaw) (hu : UniformDesign law) :
    (∫ o, numeratorHat κ n o ∂Measure.pi (fun _ : Fin n => law.P)) =
      (upperH κ n)⁻¹ * (∫ x in window (upperH κ n),
        law.e x * (∫ y, trunc (upperT κ n 0) y ∂law.Q true x) ∂design) -
      ((upperH κ n)⁻¹ * (∫ x in window (upperH κ n),
        projOp (upperH κ n) 0 law.e x * truncatedMean law (upperT κ n 0) x ∂design) +
       ∑ j : Fin (upperJ κ n), (upperH κ n)⁻¹ * ∫ x in window (upperH κ n),
         bandOp (upperH κ n) (j.val+1) law.e x *
           truncatedMean law (upperT κ n j.succ) x ∂design) := by
  let h := upperH κ n
  let T := upperT κ n
  have hF : MemLp (fun o => h⁻¹ * (if X o ∈ window h
      then bit (A o)*trunc (T 0) (Y o) else 0)) 2 law.P := by
    have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
    have hm : Measurable (fun o : O => if X o ∈ window h
        then bit (A o)*trunc (T 0) (Y o) else 0) :=
      Measurable.ite (hw.preimage (by unfold X; fun_prop))
        (by unfold A Y; fun_prop) measurable_const
    apply MemLp.of_bound (hm.const_mul _).aestronglyMeasurable (|h⁻¹| * |T 0|)
    apply Filter.Eventually.of_forall
    intro o
    rw [Real.norm_eq_abs, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    by_cases hx : X o ∈ window h
    · cases ha : A o <;> simp only [hx, ↓reduceIte, bit, ha, Bool.false_eq_true,
        zero_mul, one_mul, abs_zero]
      · exact abs_nonneg _
      · exact upper_trunc_abs_bound _ _
    · simp [hx]
  obtain ⟨ht, hy, hd⟩ := upper_blocks_nonempty_disjoint n hn
  rw [upper_numerator_twoBlock, twoBlock_expectation law.P _ _ hd ht hy _ _ hF
    (upper_heavy_kernel_memLp law h (upperJ κ n) T),
    upper_numerator_linear_mean law hu, upper_heavy_kernel_mean law hu]

/-- The finite-index version of the histogram telescoping identity. -/
-- @node: upper_propensity_telescope
lemma upper_propensity_telescope (law : ObservedLaw) (h : ℝ) (J : ℕ) (x : unitInterval) :
    projOp h J law.e x = projOp h 0 law.e x +
      ∑ j : Fin J, bandOp h (j.val+1) law.e x := by
  have he := covariance_memLp_of_bound h law.e law.e_measurable 1
    (fun x => by rw [abs_of_nonneg (law.e_range x).1]; exact (law.e_range x).2)
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [bandOp_eq_sub h (J+1) law.e he x]
    simp only [Nat.add_sub_cancel]
    linarith [ih]

/-- Conditional clipped arm means have a bounded window L² representative. -/
-- @node: upper_arm_clipped_memLp
lemma upper_arm_clipped_memLp (law : ObservedLaw) (h T : ℝ) (a : Bool) :
    MemLp (fun x => ∫ y, trunc T y ∂law.Q a x) 2 (design.restrict (window h)) := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hm : Measurable (fun x => ∫ y, trunc T y ∂law.Q a x) := by
    first | fun_prop | exact (measurable_trunc T).stronglyMeasurable.integral_kernel.measurable
  apply covariance_memLp_of_bound h _ hm |T|
  intro x
  have hn : ∀ᵐ y ∂law.Q a x, ‖trunc T y‖ ≤ |T| :=
    Filter.Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs] using upper_trunc_abs_bound T y
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hn

/-- Telescoping the untruncated propensity and subtracting conditional means gives
exactly the three kinds of error controlled by the conditional truncation ledger. -/
-- @node: upper_conditional_error_identity
lemma upper_conditional_error_identity (κ : Params) (hκ : κ.Valid)
    (law : ObservedLaw) (hm : InModel κ law) (h : ℝ) (hh : 0 < h ∧ h ≤ 1)
    (J : ℕ) (T : Fin (J+1) → ℝ) (hT : ∀ j, 1 ≤ T j) :
    (h⁻¹ * (∫ x in window h, law.e x * (∫ y, trunc (T 0) y ∂law.Q true x) ∂design) -
      (h⁻¹ * (∫ x in window h, projOp h 0 law.e x * truncatedMean law (T 0) x ∂design) +
       ∑ j : Fin J, h⁻¹ * ∫ x in window h,
         bandOp h (j.val+1) law.e x * truncatedMean law (T j.succ) x ∂design)) -
      localNumerator law h J =
    (h⁻¹ * ∫ x in window h,
      law.e x * ((∫ y, trunc (T 0) y ∂law.Q true x)-law.m1 x) ∂design) -
    (h⁻¹ * ∫ x in window h,
      projOp h 0 law.e x * (truncatedMean law (T 0) x-law.g x) ∂design) -
    ∑ j : Fin J, h⁻¹ * ∫ x in window h,
      bandOp h (j.val+1) law.e x * (truncatedMean law (T j.succ) x-law.g x) ∂design := by
  have he := covariance_memLp_of_bound h law.e law.e_measurable 20 hm.propensityHolder.2.1
  have hm0 := covariance_memLp_of_bound h law.m0 hm.baselineHolder.1.measurable 20
    hm.baselineHolder.2.1
  have htau := covariance_memLp_of_bound h law.tau hm.effectHolder.1.measurable 20
    hm.effectHolder.2.1
  have hm1 : MemLp law.m1 2 (design.restrict (window h)) := hm0.add htau
  have het : MemLp (fun x => law.e x * law.tau x) 2 (design.restrict (window h)) := by
    apply covariance_memLp_of_bound h _ (by
      have := law.e_measurable
      have := hm.effectHolder.1.measurable
      fun_prop) 400
    intro x
    rw [abs_mul]
    calc
      _ ≤ 20*20 := mul_le_mul (hm.propensityHolder.2.1 x) (hm.effectHolder.2.1 x)
        (abs_nonneg _) (by norm_num)
      _ = 400 := by norm_num
  have hg : MemLp law.g 2 (design.restrict (window h)) := hm0.add het
  have hgt (j : Fin (J+1)) : MemLp (truncatedMean law (T j)) 2 (design.restrict (window h)) :=
    (window_energy_of_abs_bound h hh _ (measurable_truncatedMean law (T j)) _
      ((marginal_mean_truncation_bounds κ hκ law hm (T j) (hT j)).mono fun x hx => hx.2.1)).1
  have hipg (j : ℕ) := (projOp_memLp h j law.e).integrable_mul hg
  have hipgt (j : ℕ) (k : Fin (J+1)) := (projOp_memLp h j law.e).integrable_mul (hgt k)
  have hibg (j : Fin J) := (bandOp_memLp h (j.val+1) law.e he).integrable_mul hg
  have hibgt (j : Fin J) := (bandOp_memLp h (j.val+1) law.e he).integrable_mul (hgt j.succ)
  have hie := he.integrable_mul hm1
  have hiet := he.integrable_mul (upper_arm_clipped_memLp law h (T 0) true)
  simp only [Pi.mul_def] at hipg hipgt hibg hibgt hie hiet
  have htel : (∫ x in window h, projOp h J law.e x * law.g x ∂design) =
      (∫ x in window h, projOp h 0 law.e x * law.g x ∂design) +
      ∑ j : Fin J, ∫ x in window h, bandOp h (j.val+1) law.e x * law.g x ∂design := by
    simp_rw [upper_propensity_telescope law h J, add_mul, Finset.sum_mul]
    rw [integral_add (hipg 0) (integrable_finsetSum _ (fun j _ => hibg j)),
      integral_finsetSum _ (fun j _ => hibg j)]
  have hband (j : Fin J) :
      (h⁻¹ * ∫ x in window h, bandOp h (j.val+1) law.e x *
        (truncatedMean law (T j.succ) x-law.g x) ∂design) =
      h⁻¹ * (∫ x in window h, bandOp h (j.val+1) law.e x *
        truncatedMean law (T j.succ) x ∂design) -
      h⁻¹ * ∫ x in window h, bandOp h (j.val+1) law.e x * law.g x ∂design := by
    simp only [mul_sub]
    rw [integral_sub (hibgt j) (hibg j)]
    ring
  simp_rw [hband]
  simp only [mul_sub]
  rw [integral_sub hiet hie, integral_sub (hipgt 0 0) (hipg 0), localNumerator,
    integral_sub hie (hipg J), htel, Finset.sum_sub_distrib]
  simp only [mul_sub, mul_add, Finset.mul_sum]
  ring

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
