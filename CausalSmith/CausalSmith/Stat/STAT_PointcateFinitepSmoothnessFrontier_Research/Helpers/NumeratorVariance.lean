module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.DenominatorVariance
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperNumeratorExpectation
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.TObservableHeavyProjections

/-! Second-moment and Hoeffding-leg bounds for the actual clipped numerator. -/
public section
set_option linter.style.longLine false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- The window-supported treated clipped linear term is square integrable. -/
-- @node: upper_numerator_linear_memLp
lemma upper_numerator_linear_memLp (law : ObservedLaw) (h T : ℝ) :
    MemLp (fun o => h⁻¹ * (if X o ∈ window h then bit (A o)*trunc T (Y o) else 0))
      2 law.P := by
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  apply MemLp.of_bound (by
    have hm : Measurable (fun o : O => h⁻¹ *
        (if X o ∈ window h then bit (A o)*trunc T (Y o) else 0)) := by
      apply Measurable.const_mul
      apply Measurable.ite (hw.preimage (show Measurable X by unfold X; fun_prop))
      · exact ((measurable_of_finite bit).comp (by unfold A; fun_prop)).mul
          ((measurable_trunc T).comp (by unfold Y; fun_prop))
      · exact measurable_const
    exact hm.aestronglyMeasurable) (|h⁻¹| * |T|)
  filter_upwards [] with o
  rw [Real.norm_eq_abs]
  by_cases hx : X o ∈ window h
  · cases ha : A o <;> simp only [hx, if_true, bit, ha, Bool.false_eq_true,
      ↓reduceIte, zero_mul, one_mul, mul_zero, abs_zero]
    · positivity
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (upper_trunc_abs_bound T (Y o)) (abs_nonneg _)
  · simp [hx]; positivity

/-- The conditional moment envelope gives the sharp localized squared energy
of the numerator's raw linear term. -/
-- @node: upper_numerator_linear_energy
lemma upper_numerator_linear_energy (κ : Params) (hκ : κ.Valid) (law : ObservedLaw)
    (hm : InModel κ law) (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (T : ℝ) (hT : 1 ≤ T) :
    (∫ o, (h⁻¹ * (if X o ∈ window h then bit (A o)*trunc T (Y o) else 0))^2
      ∂law.P) ≤ 10/h * T^(2-κ.p) := by
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  let g := fun o : O => (window h).indicator (fun _ => (trunc T (Y o))^2) (X o)
  have hg : Integrable g law.P := by
    apply ((trunc_comp_memLp law.P Y (by unfold Y; fun_prop) T
      (le_trans (by norm_num) hT)).integrable_sq.indicator
      (hw.preimage (show Measurable X by unfold X; fun_prop))).congr
    exact Filter.Eventually.of_forall fun o => by
      by_cases hx : X o ∈ window h <;> simp [g, hx]
  calc
    _ ≤ ∫ o, (h⁻¹)^2 * g o ∂law.P := by
      apply integral_mono (upper_numerator_linear_memLp law h T).integrable_sq (hg.const_mul _)
      intro o
      by_cases hx : X o ∈ window h
      · cases ha : A o <;> simp [g, hx, bit, ha, mul_pow] <;> positivity
      · simp [g, hx]
    _ = (h⁻¹)^2 * ∫ o, g o ∂law.P := integral_const_mul _ _
    _ ≤ (h⁻¹)^2 * (10*h*T^(2-κ.p)) :=
      mul_le_mul_of_nonneg_left (localized_trunc_square_bound κ hκ law hm h hh T hT)
        (sq_nonneg _)
    _ = _ := by field_simp; <;> ring

/-- A centered coordinate average has variance equal to its uncentered
one-record variance divided by its block size. -/
-- @node: upper_centered_average_variance
lemma upper_centered_average_variance {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (S : Finset (Fin n))
    (hS : S.Nonempty) (f : Ω → ℝ) (hf : MemLp f 2 P) (b : ℝ) (sign : ℝ)
    (hsign : sign^2 = 1) :
    variance (fun o : Fin n → Ω => sign * (S.card : ℝ)⁻¹ * ∑ i ∈ S, (f (o i)-b))
      (Measure.pi (fun _ => P)) = variance f P / S.card := by
  rw [upper_coordinate_average_variance P S hS (fun o => f o-b)
    (hf.sub (memLp_const _)), variance_sub_const hf.aestronglyMeasurable,
    mul_pow, hsign, one_mul]
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hS.card_pos
  field_simp

/-- Orthogonal histogram sections and product-law centering bound the actual
heavy numerator's degenerate two-block variance. -/
-- @node: upper_numerator_degenerate_variance
lemma upper_numerator_degenerate_variance (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (law : ObservedLaw) (hm : InModel κ law)
    (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (J : ℕ)
    (T : Fin (J+1) → ℝ) (hT : ∀ j, 1 ≤ T j) :
    variance (degenerateTerm law.P (treatmentBlock n) (outcomeBlock n) (heavyKernel h J T))
      (Measure.pi (fun _ : Fin n => law.P)) ≤
      ((10/h^2) * (T 0^(2-κ.p) + ∑ j : Fin J, (2 : ℝ)^j.val*T j.succ^(2-κ.p))) /
        ((treatmentBlock n).card * (outcomeBlock n).card) := by
  obtain ⟨ht, hy, hd⟩ := upper_blocks_nonempty_disjoint n hn
  have hB := heavyKernel_memLp law h J T (fun j => le_trans (by norm_num) (hT j))
  rw [twoBlock_degenerate_variance law.P _ _ hd ht hy _ hB]
  exact div_le_div_of_nonneg_right
    ((centeredKernel_energy_contraction law.P _ hB).trans
      (heavyKernel_energy_bound κ hκ law hm h hh J T hT)) (by positivity)

/-- The treatment projection of the heavy kernel is the treatment mark times
its multiscale projected clipped mean, with no independent records per level. -/
-- @node: upper_numerator_row_section
lemma upper_numerator_row_section (law : ObservedLaw) (hu : UniformDesign law)
    (h : ℝ) (J : ℕ) (T : Fin (J+1) → ℝ) (o : O) :
    (∫ z, heavyKernel h J T o z ∂law.P) =
      h⁻¹ * bit (A o) * projectionField law h J T (X o) := by
  have hp (j : ℕ) (t : ℝ) : Integrable
      (fun z : O => projKernel h j (X o) (X z) * trunc t (Y z)) law.P := by
    apply Integrable.of_bound (by unfold X Y; fun_prop) (|(cellLen h j)⁻¹| * |t|)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (projKernel_abs_bound h j _ _) (upper_trunc_abs_bound t (Y z))
      (abs_nonneg _) (abs_nonneg _)
  have he (j : ℕ) (t : ℝ) :
      (∫ z, projKernel h j (X o) (X z) * trunc t (Y z) ∂law.P) =
        projOp h j (truncatedMean law t) (X o) :=
    upper_marginal_truncated_integral law hu _ (by fun_prop) _
      (fun x => projKernel_abs_bound h j (X o) x) t
  have hb (j : Fin J) : Integrable
      (fun z : O => bandKernel h (j.val+1) (X o) (X z) * trunc (T j.succ) (Y z))
      law.P := by
    convert (hp (j.val+1) (T j.succ)).sub (hp j.val (T j.succ)) using 1
    funext z
    simp only [bandKernel, Nat.add_sub_cancel, sub_mul, Pi.sub_apply]
  have hbe (j : Fin J) :
      (∫ z, bandKernel h (j.val+1) (X o) (X z) * trunc (T j.succ) (Y z) ∂law.P) =
        bandOp h (j.val+1) (truncatedMean law (T j.succ)) (X o) := by
    simp only [bandKernel, sub_mul]
    rw [integral_sub (hp _ _) (hp _ _), he, he]
    have ht : MemLp (truncatedMean law (T j.succ)) 2 (design.restrict (window h)) := by
      let : IsProbabilityMeasure design := by unfold design; infer_instance
      apply MemLp.of_bound (by fun_prop) (2*|T j.succ|)
      filter_upwards [] with x
      rw [Real.norm_eq_abs]
      have h0 := norm_integral_le_of_norm_le_const (μ := law.Q false x) (f := trunc (T j.succ)) (C := |T j.succ|)
        (Filter.Eventually.of_forall fun y => by
          simpa [Real.norm_eq_abs] using upper_trunc_abs_bound (T j.succ) y)
      have h1 := norm_integral_le_of_norm_le_const (μ := law.Q true x) (f := trunc (T j.succ)) (C := |T j.succ|)
        (Filter.Eventually.of_forall fun y => by
          simpa [Real.norm_eq_abs] using upper_trunc_abs_bound (T j.succ) y)
      simp only [Real.norm_eq_abs, probReal_univ, mul_one] at h0 h1
      unfold truncatedMean
      calc
        _ ≤ |law.e x| * |∫ y, trunc (T j.succ) y ∂law.Q true x| +
            |1-law.e x| * |∫ y, trunc (T j.succ) y ∂law.Q false x| := by
              simpa only [abs_mul] using abs_add_le
                (law.e x * ∫ y, trunc (T j.succ) y ∂law.Q true x)
                ((1-law.e x) * ∫ y, trunc (T j.succ) y ∂law.Q false x)
        _ ≤ 2*|T j.succ| := by
          rw [abs_of_nonneg (law.e_range x).1,
            abs_of_nonneg (sub_nonneg.mpr (law.e_range x).2)]
          nlinarith [mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr (law.e_range x).2),
            mul_le_mul_of_nonneg_left h1 (law.e_range x).1, abs_nonneg (T j.succ)]
    rw [bandOp_eq_sub h (j.val+1) _ ht]
  simp only [heavyKernel, integral_const_mul]
  rw [integral_add (hp _ _) (integrable_finsetSum _ (fun j _ => hb j)),
    integral_finsetSum _ (fun j _ => hb j), he]
  simp_rw [hbe]
  simp only [projectionField, bit, div_eq_mul_inv]
  ring

/-- Every multiscale projection field vanishes outside its localization window. -/
-- @node: upper_projectionField_support
lemma upper_projectionField_support (law : ObservedLaw) (h : ℝ) (J : ℕ)
    (T : Fin (J+1) → ℝ) (x : unitInterval) (hx : x ∉ window h) :
    projectionField law h J T x = 0 := by
  simp [projectionField, projOp, bandOp, bandKernel, projKernel, hx]

/-- Finite clipped means give a square-integrable field on the window. -/
-- @node: upper_projectionField_memLp
lemma upper_projectionField_memLp (κ : Params) (hκ : κ.Valid) (law : ObservedLaw)
    (hm : InModel κ law) (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (J : ℕ)
    (T : Fin (J+1) → ℝ) (hT : ∀ j, 1 ≤ T j) :
    MemLp (projectionField law h J T) 2 (design.restrict (window h)) := by
  have hf (j : Fin (J+1)) :
      MemLp (truncatedMean law (T j)) 2 (design.restrict (window h)) :=
    (window_energy_of_abs_bound h hh _ (by fun_prop) ((10 : ℝ)^(1/κ.p))
      ((marginal_mean_truncation_bounds κ hκ law hm (T j) (hT j)).mono
        fun x hx => hx.2.1)).1
  exact (projOp_memLp h 0 _).add
    (memLp_finsetSum Finset.univ (fun j _ => bandOp_memLp h (j.val+1) _ (hf j.succ)))

/-- Dropping the binary treatment mark and using the exact covariate marginal
transfers the treatment projection's second moment to window field energy. -/
-- @node: upper_numerator_treatment_energy
lemma upper_numerator_treatment_energy (κ : Params) (hκ : κ.Valid) (law : ObservedLaw)
    (hm : InModel κ law) (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (J : ℕ)
    (T : Fin (J+1) → ℝ) (hT : ∀ j, 1 ≤ T j) :
    (∫ o, (h⁻¹ * bit (A o) * projectionField law h J T (X o))^2 ∂law.P) ≤
      (h⁻¹)^2 * ∫ x in window h, (projectionField law h J T x)^2 ∂design := by
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  have hg := (memLp_indicator_iff_restrict hw).2
    (upper_projectionField_memLp κ hκ law hm h hh J T hT)
  have hs : (window h).indicator (projectionField law h J T) =
      projectionField law h J T := by
    funext x
    by_cases hx : x ∈ window h
    · simp [hx]
    · simp [hx, upper_projectionField_support law h J T x hx]
  rw [hs] at hg
  have hX : MeasurePreserving X law.P design :=
    ⟨by unfold X; fun_prop, hm.uniform⟩
  have hi := (hg.comp_measurePreserving hX).integrable_sq.const_mul ((h⁻¹)^2)
  have hr := centeredKernel_row_mean_memLp law.P (heavyKernel h J T)
    (heavyKernel_memLp law h J T (fun j => le_trans (by norm_num) (hT j)))
  have he : (fun o => ∫ z, heavyKernel h J T o z ∂law.P) =
      (fun o => h⁻¹ * bit (A o) * projectionField law h J T (X o)) := by
    funext o
    exact upper_numerator_row_section law hm.uniform h J T o
  rw [he] at hr
  calc
    _ ≤ ∫ o, (h⁻¹)^2 * (projectionField law h J T (X o))^2 ∂law.P := by
      apply integral_mono hr.integrable_sq hi
      intro o
      cases ha : A o <;> simp [bit, ha, mul_pow] <;> positivity
    _ = (h⁻¹)^2 * ∫ x, (projectionField law h J T x)^2 ∂design := by
      rw [integral_const_mul]
      congr 1
      rw [← hm.uniform]
      exact (integral_map hX.measurable.aemeasurable
        (hm.uniform.symm ▸ hg.integrable_sq.aestronglyMeasurable)).symm
    _ = _ := by
      congr 1
      rw [← integral_indicator hw]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ window h
        · simp [hx]
        · simp [hx, upper_projectionField_support law h J T x hx]

/-- The treatment projection variance is controlled by the sharp capped-prefix
field bound, before summing the deterministic threshold ledger. -/
-- @node: upper_numerator_treatment_variance
lemma upper_numerator_treatment_variance (κ : Params) (hκ : κ.Valid) (law : ObservedLaw)
    (hm : InModel κ law) (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (J : ℕ)
    (T : Fin (J+1) → ℝ) (hT : ∀ j, 1 ≤ T j)
    (j0 : ℕ) (hj0 : j0 ≤ J) (hcap : ∀ j, j.val ≤ j0 → T j = T 0) :
    variance (fun o => h⁻¹ * bit (A o) * projectionField law h J T (X o)) law.P ≤
      h⁻¹ * (3*(10 : ℝ)^(2/κ.p) + 200*(∑ j : Fin J,
        if j0 < j.val+1 then T j.succ^(-2*(κ.p-1)) else 0)) := by
  have hr := centeredKernel_row_mean_memLp law.P (heavyKernel h J T)
    (heavyKernel_memLp law h J T (fun j => le_trans (by norm_num) (hT j)))
  have he : (fun o => ∫ z, heavyKernel h J T o z ∂law.P) =
      (fun o => h⁻¹ * bit (A o) * projectionField law h J T (X o)) := by
    funext o
    exact upper_numerator_row_section law hm.uniform h J T o
  rw [he] at hr
  apply (variance_le_expectation_sq hr.aestronglyMeasurable).trans
  apply (upper_numerator_treatment_energy κ hκ law hm h hh J T hT).trans
  have hb := mul_le_mul_of_nonneg_left
    (projectionField_energy_bound κ hκ law hm h hh J T hT j0 hj0 hcap)
    (inv_nonneg.mpr hh.1.le)
  simpa only [pow_two, mul_assoc] using hb

/-- The actual numerator's mean absolute deviation is bounded by the two
single-record projection standard deviations and the sharp multiscale kernel
energy. Only deterministic tuning estimates remain after this assembly. -/
-- @node: upper_numerator_deviation_unscaled
lemma upper_numerator_deviation_unscaled (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (law : ObservedLaw) (hm : InModel κ law) :
    let h := upperH κ n
    let J := upperJ κ n
    let T := upperT κ n
    let B := heavyKernel h J T
    let F := fun o : O => h⁻¹ * (if X o ∈ window h then bit (A o)*trunc (T 0) (Y o) else 0)
    (∫ o, |numeratorHat κ n o - ∫ z, numeratorHat κ n z
      ∂Measure.pi (fun _ : Fin n => law.P)| ∂Measure.pi (fun _ : Fin n => law.P)) ≤
      Real.sqrt (variance (fun o => h⁻¹ * bit (A o) * projectionField law h J T (X o)) law.P /
        (treatmentBlock n).card) +
      Real.sqrt (variance (fun o => F o - ∫ v, B v o ∂law.P) law.P /
        (outcomeBlock n).card) +
      Real.sqrt (((10/h^2) * (T 0^(2-κ.p) +
        ∑ j : Fin J, (2 : ℝ)^j.val*T j.succ^(2-κ.p))) /
        ((treatmentBlock n).card * (outcomeBlock n).card)) := by
  dsimp only
  let h := upperH κ n
  let J := upperJ κ n
  let T := upperT κ n
  let B := heavyKernel h J T
  let F := fun o : O => h⁻¹ * (if X o ∈ window h then bit (A o)*trunc (T 0) (Y o) else 0)
  obtain ⟨ht, hy, hd⟩ := upper_blocks_nonempty_disjoint n hn
  have hF := upper_numerator_linear_memLp law h (T 0)
  have hB := upper_heavy_kernel_memLp law h J T
  have hr := centeredKernel_row_mean_memLp law.P B hB
  have hswap : MemLp (fun oz : O × O => B oz.2 oz.1) 2 (law.P.prod law.P) :=
    (memLp_two_iff_integrable_sq hB.aestronglyMeasurable.prod_swap).2 hB.integrable_sq.swap
  have hc := centeredKernel_row_mean_memLp law.P (fun o z => B z o) hswap
  have hvT : variance (treatmentTerm law.P (treatmentBlock n) B)
      (Measure.pi (fun _ : Fin n => law.P)) =
      variance (fun o => h⁻¹ * bit (A o) * projectionField law h J T (X o)) law.P /
        (treatmentBlock n).card := by
    unfold treatmentTerm
    have hv := upper_centered_average_variance law.P _ ht _ hr
      (∫ v, ∫ w, B v w ∂law.P ∂law.P) (-1) (by norm_num)
    simp only [neg_one_mul] at hv
    rw [hv]
    congr 2
    funext o
    exact upper_numerator_row_section law hm.uniform h J T o
  have hvY : variance (outcomeTerm law.P (outcomeBlock n) F B)
      (Measure.pi (fun _ : Fin n => law.P)) =
      variance (fun o => F o - ∫ v, B v o ∂law.P) law.P / (outcomeBlock n).card := by
    unfold outcomeTerm
    simpa only [one_mul] using upper_centered_average_variance law.P _ hy
      (fun o => F o - ∫ v, B v o ∂law.P) (hF.sub hc) _ 1 (by norm_num)
  have hdev := twoBlock_deviation_bound law.P _ _ hd ht hy F B hF hB
  have hex := twoBlock_expectation law.P _ _ hd ht hy F B hF hB
  rw [← upper_numerator_twoBlock κ n] at hex hdev
  rw [← hex, hvT, hvY] at hdev
  have hvc := upper_numerator_degenerate_variance κ hκ n hn law hm h
    (upper_tuning κ hκ n hn).1 J T (upper_threshold_positive κ hκ n hn)
  exact hdev.trans (add_le_add le_rfl (Real.sqrt_le_sqrt hvc))

/-- Inserting the capped-prefix field estimate removes the treatment projection
variance from the actual numerator certificate. -/
-- @node: upper_numerator_deviation_field_energy
lemma upper_numerator_deviation_field_energy (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (law : ObservedLaw) (hm : InModel κ law)
    (j0 : ℕ) (hj0 : j0 ≤ upperJ κ n)
    (hcap : ∀ j, j.val ≤ j0 → upperT κ n j = upperT κ n 0) :
    let h := upperH κ n
    let J := upperJ κ n
    let T := upperT κ n
    let B := heavyKernel h J T
    let F := fun o : O => h⁻¹ * (if X o ∈ window h then bit (A o)*trunc (T 0) (Y o) else 0)
    (∫ o, |numeratorHat κ n o - ∫ z, numeratorHat κ n z
      ∂Measure.pi (fun _ : Fin n => law.P)| ∂Measure.pi (fun _ : Fin n => law.P)) ≤
      Real.sqrt ((h⁻¹ * (3*(10 : ℝ)^(2/κ.p) + 200*(∑ j : Fin J,
        if j0 < j.val+1 then T j.succ^(-2*(κ.p-1)) else 0))) /
        (treatmentBlock n).card) +
      Real.sqrt (variance (fun o => F o - ∫ v, B v o ∂law.P) law.P /
        (outcomeBlock n).card) +
      Real.sqrt (((10/h^2) * (T 0^(2-κ.p) +
        ∑ j : Fin J, (2 : ℝ)^j.val*T j.succ^(2-κ.p))) /
        ((treatmentBlock n).card * (outcomeBlock n).card)) := by
  dsimp only
  apply (upper_numerator_deviation_unscaled κ hκ n hn law hm).trans
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_right
    (upper_numerator_treatment_variance κ hκ law hm _ (upper_tuning κ hκ n hn).1
      _ _ (upper_threshold_positive κ hκ n hn) j0 hj0 hcap) (by positivity)

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
