module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.NumeratorVariance
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperBias

/-! The shared-record outcome projection of the multiscale numerator. -/
public section
set_option linter.style.longLine false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- Integrating the treatment donor identifies the outcome projection at every record. -/
-- @node: upper_numerator_column_section
lemma upper_numerator_column_section (law : ObservedLaw) (hu : UniformDesign law)
    (h : ℝ) (J : ℕ) (T : Fin (J+1) → ℝ) (o : O) :
    (∫ z, heavyKernel h J T z o ∂law.P) = h⁻¹ *
      (projOp h 0 law.e (X o) * trunc (T 0) (Y o) +
        ∑ j : Fin J, bandOp h (j.val+1) law.e (X o) * trunc (T j.succ) (Y o)) := by
  have he := covariance_memLp_of_bound h law.e law.e_measurable 1
    (fun x => by rw [abs_of_nonneg (law.e_range x).1]; exact (law.e_range x).2)
  have hi (j : ℕ) (t : ℝ) : Integrable
      (fun z : O => bit (A z) * (projKernel h j (X z) (X o) * trunc t (Y o))) law.P := by
    apply Integrable.of_bound (by unfold A X; fun_prop) (|(cellLen h j)⁻¹| * |t|)
    filter_upwards [] with z
    rw [Real.norm_eq_abs]
    cases ha : A z <;> simp only [bit, ha, Bool.false_eq_true, ↓reduceIte,
      zero_mul, one_mul, abs_zero]
    · positivity
    · rw [abs_mul]
      exact mul_le_mul (projKernel_abs_bound h j _ _) (upper_trunc_abs_bound t (Y o))
        (abs_nonneg _) (abs_nonneg _)
  have hp (j : ℕ) (t : ℝ) :
      (∫ z, bit (A z) * (projKernel h j (X z) (X o) * trunc t (Y o)) ∂law.P) =
        projOp h j law.e (X o) * trunc t (Y o) := by
    rw [show (fun z : O => bit (A z) * (projKernel h j (X z) (X o) * trunc t (Y o))) =
      (fun z => (bit (A z) * projKernel h j (X z) (X o)) * trunc t (Y o)) by funext; ring,
      integral_mul_const, upper_treatment_integral law hu _ (by fun_prop) _
        (fun x => projKernel_abs_bound h j x (X o))]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [projKernel_symm h j x (X o)]
      ring
  have hb (j : Fin J) : Integrable
      (fun z : O => bit (A z) * (bandKernel h (j.val+1) (X z) (X o) *
        trunc (T j.succ) (Y o))) law.P := by
    convert (hi (j.val+1) (T j.succ)).sub (hi j.val (T j.succ)) using 1
    funext z
    simp only [bandKernel, Nat.add_sub_cancel, Pi.sub_apply]
    ring
  have hbe (j : Fin J) :
      (∫ z, bit (A z) * (bandKernel h (j.val+1) (X z) (X o) *
        trunc (T j.succ) (Y o)) ∂law.P) =
        bandOp h (j.val+1) law.e (X o) * trunc (T j.succ) (Y o) := by
    simp only [bandKernel, Nat.add_sub_cancel, sub_mul, mul_sub]
    rw [integral_sub (hi _ _) (hi _ _), hp, hp,
      bandOp_eq_sub h (j.val+1) law.e he, Nat.add_sub_cancel]
    ring
  have hex : (fun z => heavyKernel h J T z o) =
      (fun z => h⁻¹ * (bit (A z) * (projKernel h 0 (X z) (X o) * trunc (T 0) (Y o)) +
        ∑ j : Fin J, bit (A z) * (bandKernel h (j.val+1) (X z) (X o) *
          trunc (T j.succ) (Y o)))) := by
    funext z
    simp only [heavyKernel, ← Finset.mul_sum, bit]
    ring
  rw [hex, integral_const_mul, integral_add (hi _ _)
    (integrable_finsetSum _ (fun j _ => hb j)), integral_finsetSum _ (fun j _ => hb j), hp]
  simp_rw [hbe]

/-- Nested hard truncations on one response have nested absolute values. -/
-- @node: upper_trunc_abs_mono
lemma upper_trunc_abs_mono (t T y : ℝ) (ht : t ≤ T) :
    |trunc t y| ≤ |trunc T y| := by
  by_cases hy : |y| ≤ t
  · simp [trunc, hy, hy.trans ht]
  · simp only [trunc, hy, if_false, abs_zero]
    exact abs_nonneg _

/-- The smooth propensity gives a geometric envelope for the entire outcome
projection, retaining the same clipped response at every scale. -/
-- @node: upper_numerator_outcome_envelope
lemma upper_numerator_outcome_envelope (law : ObservedLaw) (hu : UniformDesign law)
    (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (a : ℝ) (ha : 0 < a ∧ a ≤ 1)
    (he : holderBall a law.e) (J : ℕ) (T : Fin (J+1) → ℝ)
    (hT : ∀ j, T j ≤ T 0) (o : O) :
    |h⁻¹ * (if X o ∈ window h then bit (A o)*trunc (T 0) (Y o) else 0) -
      ∫ z, heavyKernel h J T z o ∂law.P| ≤
      h⁻¹ * (1+40/(1-(2 : ℝ)^(-a))) *
        (if X o ∈ window h then |trunc (T 0) (Y o)| else 0) := by
  rw [upper_numerator_column_section law hu]
  by_cases hx : X o ∈ window h
  · have hlp := covariance_memLp_of_bound h law.e law.e_measurable 1
      (fun x => by rw [abs_of_nonneg (law.e_range x).1]; exact (law.e_range x).2)
    have hp := covariance_projOp_range h hh 0 law.e hlp 0 1 law.e_range (X o) hx
    have hb : |bit (A o)-projOp h 0 law.e (X o)| ≤ 1 := by
      cases ha : A o <;> simp only [bit, ha, Bool.false_eq_true, ↓reduceIte]
      · simpa [abs_of_nonneg hp.1] using hp.2
      · rw [abs_of_nonneg (sub_nonneg.mpr hp.2)]
        linarith [hp.1]
    have hs : |∑ j : Fin J, bandOp h (j.val+1) law.e (X o) * trunc (T j.succ) (Y o)| ≤
        40/(1-(2 : ℝ)^(-a)) * |trunc (T 0) (Y o)| := by
      calc
        _ ≤ ∑ j : Fin J, |bandOp h (j.val+1) law.e (X o) * trunc (T j.succ) (Y o)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin J, (40 * cellLen h (j.val+1)^a) * |trunc (T 0) (Y o)| := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          exact mul_le_mul (bandOp_holder_bound h hh a law.e ha he _ (by omega) _ hx)
            (upper_trunc_abs_mono _ _ _ (hT j.succ)) (abs_nonneg _) (mul_nonneg (by norm_num) (Real.rpow_nonneg
              (div_nonneg hh.1.le (pow_nonneg (by norm_num) _)) _))
        _ = 40 * (∑ j ∈ Finset.range J, cellLen h (j+1)^a) * |trunc (T 0) (Y o)| := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
          congr 2
          exact Fin.sum_univ_eq_sum_range (fun j => cellLen h (j+1)^a) J
        _ ≤ _ := by
          have hs := upper_cell_positive_sum h hh a ha.1 J
          simpa only [div_eq_mul_inv, one_mul] using
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 40))
              (abs_nonneg (trunc (T 0) (Y o)))
    simp only [hx, if_true]
    rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr hh.1.le)]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hh.1.le)
    calc
      _ = |(bit (A o)-projOp h 0 law.e (X o))*trunc (T 0) (Y o) -
          ∑ j : Fin J, bandOp h (j.val+1) law.e (X o)*trunc (T j.succ) (Y o)| := by
            congr 1; ring
      _ ≤ |(bit (A o)-projOp h 0 law.e (X o))*trunc (T 0) (Y o)| +
          |∑ j : Fin J, bandOp h (j.val+1) law.e (X o)*trunc (T j.succ) (Y o)| := abs_sub _ _
      _ ≤ 1 * |trunc (T 0) (Y o)| +
          40/(1-(2 : ℝ)^(-a)) * |trunc (T 0) (Y o)| := by
            rw [abs_mul]
            exact add_le_add (mul_le_mul_of_nonneg_right hb (abs_nonneg _)) hs
      _ = _ := by ring
  · simp [hx, projOp, projKernel, bandOp, bandKernel]

/-- The localized conditional moment bound controls the shared-record outcome
projection without any independence between its scale terms. -/
-- @node: upper_numerator_outcome_variance
lemma upper_numerator_outcome_variance (κ : Params) (hκ : κ.Valid) (law : ObservedLaw)
    (hm : InModel κ law) (h : ℝ) (hh : 0 < h ∧ h ≤ 1)
    (a : ℝ) (ha : 0 < a ∧ a ≤ 1) (he : holderBall a law.e)
    (J : ℕ) (T : Fin (J+1) → ℝ) (hT : ∀ j, 1 ≤ T j) (hmax : ∀ j, T j ≤ T 0) :
    variance (fun o => h⁻¹ * (if X o ∈ window h then bit (A o)*trunc (T 0) (Y o) else 0) -
      ∫ z, heavyKernel h J T z o ∂law.P) law.P ≤
      10/h * T 0^(2-κ.p) * (1+40/(1-(2 : ℝ)^(-a)))^2 := by
  let B := heavyKernel h J T
  let f := fun o : O => h⁻¹ *
    (if X o ∈ window h then bit (A o)*trunc (T 0) (Y o) else 0) - ∫ z, B z o ∂law.P
  let C := 1+40/(1-(2 : ℝ)^(-a))
  have hB := heavyKernel_memLp law h J T (fun j => le_trans (by norm_num) (hT j))
  have hswap : MemLp (fun oz : O × O => B oz.2 oz.1) 2 (law.P.prod law.P) :=
    (memLp_two_iff_integrable_sq hB.aestronglyMeasurable.prod_swap).2 hB.integrable_sq.swap
  have hf : MemLp f 2 law.P := (upper_numerator_linear_memLp law h (T 0)).sub
    (centeredKernel_row_mean_memLp law.P (fun o z => B z o) hswap)
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  let g := fun o : O => (window h).indicator (fun _ => (trunc (T 0) (Y o))^2) (X o)
  have hg : Integrable g law.P := by
    apply ((trunc_comp_memLp law.P Y (by unfold Y; fun_prop) (T 0)
      (le_trans (by norm_num) (hT 0))).integrable_sq.indicator
      (hw.preimage (show Measurable X by unfold X; fun_prop))).congr
    exact Filter.Eventually.of_forall fun o => by
      by_cases hx : X o ∈ window h <;> simp [g, hx]
  have hC : 0 ≤ C := by
    have hd : 0 < 1-(2 : ℝ)^(-a) := sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
    dsimp [C]
    positivity
  have hb (o : O) : f o ^ 2 ≤ (h⁻¹)^2*C^2*g o := by
    have he := upper_numerator_outcome_envelope law hm.uniform h hh a ha he J T hmax o
    change |f o| ≤ h⁻¹ * C * (if X o ∈ window h then |trunc (T 0) (Y o)| else 0) at he
    have hs := mul_self_le_mul_self (abs_nonneg (f o)) he
    simp only [← pow_two, sq_abs] at hs
    by_cases hx : X o ∈ window h
    · simpa only [g, hx, Set.indicator_of_mem, if_true, mul_pow, sq_abs, mul_assoc] using hs
    · simpa [g, hx, pow_two] using hs
  calc
    _ ≤ ∫ o, f o^2 ∂law.P := variance_le_expectation_sq hf.aestronglyMeasurable
    _ ≤ ∫ o, (h⁻¹)^2*C^2*g o ∂law.P :=
      integral_mono hf.integrable_sq (hg.const_mul _) hb
    _ = (h⁻¹)^2*C^2 * ∫ o, g o ∂law.P := integral_const_mul _ _
    _ ≤ (h⁻¹)^2*C^2 * (10*h*T 0^(2-κ.p)) :=
      mul_le_mul_of_nonneg_left (localized_trunc_square_bound κ hκ law hm h hh (T 0) (hT 0))
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by dsimp [C]; field_simp <;> ring

/-- Every public level is capped by the coarse threshold. -/
-- @node: upper_threshold_le_coarse
lemma upper_threshold_le_coarse (κ : Params) (n : ℕ) (j : Fin (upperJ κ n+1)) :
    upperT κ n j ≤ upperT κ n 0 := by
  simp only [upperT, Fin.val_zero, ↓reduceIte]
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- The actual outcome projection's variance is now a deterministic tuning expression. -/
-- @node: upper_numerator_outcome_variance_public
lemma upper_numerator_outcome_variance_public (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (law : ObservedLaw) (hm : InModel κ law) :
    variance (fun o => (upperH κ n)⁻¹ *
      (if X o ∈ window (upperH κ n) then bit (A o)*trunc (upperT κ n 0) (Y o) else 0) -
        ∫ z, heavyKernel (upperH κ n) (upperJ κ n) (upperT κ n) z o ∂law.P) law.P ≤
      10/upperH κ n * upperT κ n 0^(2-κ.p) * (1+40/constantA κ)^2 := by
  have ha : 0 < effectiveA κ ∧ effectiveA κ ≤ 1 :=
    ⟨(phase_algebra κ hκ).2.2.1, (min_le_left _ _).trans hκ.2.1.2⟩
  exact upper_numerator_outcome_variance κ hκ law hm _ (upper_tuning κ hκ n hn).1
    _ ha (upper_effective_propensity_holder κ hκ law hm) _ _
    (upper_threshold_positive κ hκ n hn) (upper_threshold_le_coarse κ n)

/-- The coarse clipped second moment divided by sample bandwidth is exactly
the square of the coarse moment noise scale. -/
-- @node: upper_coarse_variance_identity
lemma upper_coarse_variance_identity (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) :
    upperT κ n 0^(2-κ.p) / ((n : ℝ)*upperH κ n) =
      (((n : ℝ)*upperH κ n)^(-qExp κ))^2 := by
  have hh := (upper_tuning κ hκ n hn).1.1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx : 0 < (n : ℝ)*upperH κ n := mul_pos hnpos hh
  have hp : κ.p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hκ.1.1)
  simp only [upperT, Fin.val_zero, ↓reduceIte]
  have hdiv (b : ℝ) : ((n : ℝ)*upperH κ n)^b / ((n : ℝ)*upperH κ n) =
      ((n : ℝ)*upperH κ n)^(b-1) := by
    rw [Real.rpow_sub hx, Real.rpow_one]
  rw [← Real.rpow_mul hx.le, hdiv, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 1
  unfold qExp
  field_simp
  ring

/-- The averaged outcome projection is bounded by its exact public noise ledger term. -/
-- @node: upper_numerator_outcome_sd_rate
lemma upper_numerator_outcome_sd_rate (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (law : ObservedLaw) (hm : InModel κ law) :
    Real.sqrt (variance (fun o => (upperH κ n)⁻¹ *
      (if X o ∈ window (upperH κ n) then bit (A o)*trunc (upperT κ n 0) (Y o) else 0) -
        ∫ z, heavyKernel (upperH κ n) (upperJ κ n) (upperT κ n) z o ∂law.P) law.P /
          (outcomeBlock n).card) ≤
      Real.sqrt 30 * (1+40/constantA κ) * rate κ n := by
  have ht := upper_tuning κ hκ n hn
  have hh := ht.1.1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hy := (upper_block_card_bounds n hn).2
  have hypos : 0 < ((outcomeBlock n).card : ℝ) := lt_of_lt_of_le (by positivity) hy
  have hu := ht.2.2.1
  have hr : 0 ≤ rate κ n := (Real.rpow_pos_of_pos (mul_pos hnpos hh) _).le.trans hu
  have hC : 0 ≤ 1+40/constantA κ := by
    have hd := (phase_algebra κ hκ).2.2.2.2.1
    positivity
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  have hv := div_le_div_of_nonneg_right
    (upper_numerator_outcome_variance_public κ hκ n hn law hm) hypos.le
  have hscale : (10/upperH κ n * upperT κ n 0^(2-κ.p) * (1+40/constantA κ)^2) /
      (outcomeBlock n).card ≤
        30 * (upperT κ n 0^(2-κ.p) / ((n : ℝ)*upperH κ n)) * (1+40/constantA κ)^2 := by
    have hi := one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ)/3) hy
    have he := mul_le_mul_of_nonneg_left hi
      (show 0 ≤ 10/upperH κ n * upperT κ n 0^(2-κ.p) * (1+40/constantA κ)^2 by
        have hT := upper_threshold_positive κ hκ n hn 0
        positivity)
    calc
      _ = (10/upperH κ n * upperT κ n 0^(2-κ.p) * (1+40/constantA κ)^2) *
          (1 / (outcomeBlock n).card) := by ring
      _ ≤ (10/upperH κ n * upperT κ n 0^(2-κ.p) * (1+40/constantA κ)^2) *
          (1 / ((n : ℝ)/3)) := he
      _ = _ := by field_simp <;> ring
  apply (hv.trans hscale).trans
  rw [upper_coarse_variance_identity κ hκ n hn]
  have hs := (sq_le_sq₀ (Real.rpow_pos_of_pos (mul_pos hnpos hh) _).le hr).2 hu
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 30))
    (sq_nonneg (1+40/constantA κ))
  simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 30), mul_assoc, mul_left_comm, mul_comm] using hb

/-- Both one-record projections have been bounded; only the treatment and
degenerate threshold ledgers remain in the numerator certificate. -/
-- @node: upper_numerator_deviation_outcome_rate
lemma upper_numerator_deviation_outcome_rate (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (law : ObservedLaw) (hm : InModel κ law)
    (j0 : ℕ) (hj0 : j0 ≤ upperJ κ n)
    (hcap : ∀ j, j.val ≤ j0 → upperT κ n j = upperT κ n 0) :
    let h := upperH κ n
    let J := upperJ κ n
    let T := upperT κ n
    (∫ o, |numeratorHat κ n o - ∫ z, numeratorHat κ n z
      ∂Measure.pi (fun _ : Fin n => law.P)| ∂Measure.pi (fun _ : Fin n => law.P)) ≤
      Real.sqrt ((h⁻¹ * (3*(10 : ℝ)^(2/κ.p) + 200*(∑ j : Fin J,
        if j0 < j.val+1 then T j.succ^(-2*(κ.p-1)) else 0))) /
        (treatmentBlock n).card) +
      Real.sqrt 30 * (1+40/constantA κ) * rate κ n +
      Real.sqrt (((10/h^2) * (T 0^(2-κ.p) +
        ∑ j : Fin J, (2 : ℝ)^j.val*T j.succ^(2-κ.p))) /
        ((treatmentBlock n).card * (outcomeBlock n).card)) := by
  dsimp only
  apply (upper_numerator_deviation_field_energy κ hκ n hn law hm j0 hj0 hcap).trans
  exact add_le_add (add_le_add le_rfl
    (upper_numerator_outcome_sd_rate κ hκ n hn law hm)) le_rfl

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
