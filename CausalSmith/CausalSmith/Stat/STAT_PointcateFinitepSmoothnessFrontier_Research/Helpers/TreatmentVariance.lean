module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.OutcomeVariance

/-! Geometric tail ledger for the treatment projection of the numerator. -/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- The inverse squared uncapped threshold separates into a public factor and a mesh power. -/
-- @node: upper_uncapped_tail_identity
lemma upper_uncapped_tail_identity (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (j : ℕ) :
    (((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) j^(1+2*effectiveA κ))^(1/κ.p))^(-2*(κ.p-1)) =
      ((n : ℝ)^2*upperH κ n)^(-2*qExp κ) *
        cellLen (upperH κ n) j^(- (2*qExp κ*(1+2*effectiveA κ))) := by
  have hh := (upper_bandwidth_certificate κ hκ n hn).1.1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hc : 0 < cellLen (upperH κ n) j := div_pos hh (by positivity)
  have hp : κ.p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hκ.1.1)
  rw [← Real.rpow_mul (by positivity)]
  have he : (1/κ.p)*(-2*(κ.p-1)) = -2*qExp κ := by
    unfold qExp
    field_simp
  rw [he, Real.mul_rpow (by positivity) (Real.rpow_nonneg hc.le _),
    ← Real.rpow_mul hc.le]
  congr 1
  ring

/-- The uncapped treatment tail is bounded by the public geometric denominator. -/
-- @node: upper_treatment_tail_ledger
lemma upper_treatment_tail_ledger (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (j0 : ℕ)
    (huncap : ∀ j : Fin (upperJ κ n+1), j0 < j.val → upperT κ n j =
      ((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) j.val^(1+2*effectiveA κ))^(1/κ.p)) :
    (∑ j : Fin (upperJ κ n), if j0 < j.val+1 then
      upperT κ n j.succ^(-2*(κ.p-1)) else 0) ≤ 1/constantF κ := by
  have hh := (upper_bandwidth_certificate κ hκ n hn).1.1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hp : 0 < κ.p := lt_trans (by norm_num) hκ.1.1
  have hq : 0 < qExp κ := div_pos (sub_pos.mpr hκ.1.1) hp
  have ha := (phase_algebra κ hκ).2.2.1
  let s := 2*qExp κ*(1+2*effectiveA κ)
  let C := ((n : ℝ)^2*upperH κ n)^(-2*qExp κ)
  have hs : 0 < s := by dsimp [s]; positivity
  have hC : 0 ≤ C := Real.rpow_nonneg (by positivity) _
  have hd : 0 < 1-(2 : ℝ)^(-s) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hF := (phase_algebra κ hκ).2.2.2.2.2.2
  have hden : constantF κ ≤ 1-(2 : ℝ)^(-s) := by
    unfold constantF
    have he : -s ≤ -2*qExp κ := by dsimp [s]; nlinarith
    linarith [Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he]
  by_cases hJ : upperJ κ n = 0
  · have : IsEmpty (Fin (upperJ κ n)) := hJ ▸ inferInstance
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact div_nonneg (by norm_num) hF.le
  have hJpos : 0 < upperJ κ n := by omega
  have hf : 1 ≤
      ((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) (upperJ κ n)^(1+2*effectiveA κ))^(1/κ.p) := by
    have ht := upper_threshold_positive κ hκ n hn ⟨upperJ κ n, by omega⟩
    simp only [upperT, hJ, ↓reduceIte] at ht
    exact ht.trans (min_le_right _ _)
  have hfin : C * cellLen (upperH κ n) (upperJ κ n)^(-s) ≤ 1 := by
    rw [← upper_uncapped_tail_identity κ hκ n hn]
    exact Real.rpow_le_one_of_one_le_of_nonpos hf (by linarith [hκ.1.1])
  calc
    _ ≤ ∑ j : Fin (upperJ κ n), C * cellLen (upperH κ n) (j.val+1)^(-s) := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hj
      · rw [huncap j.succ hj, upper_uncapped_tail_identity κ hκ n hn]
        rfl
      · exact mul_nonneg hC (Real.rpow_nonneg (by unfold cellLen; positivity) _)
    _ = C * ∑ j ∈ Finset.range (upperJ κ n), cellLen (upperH κ n) (j+1)^(-s) := by
      rw [← Finset.mul_sum]
      congr 1
      exact Fin.sum_univ_eq_sum_range (fun j => cellLen (upperH κ n) (j+1)^(-s)) _
    _ ≤ C * (cellLen (upperH κ n) (upperJ κ n)^(-s)/(1-(2 : ℝ)^(-s))) :=
      mul_le_mul_of_nonneg_left (upper_cell_negative_sum _ hh s hs _) hC
    _ = (C * cellLen (upperH κ n) (upperJ κ n)^(-s))/(1-(2 : ℝ)^(-s)) := by ring
    _ ≤ 1/(1-(2 : ℝ)^(-s)) := div_le_div_of_nonneg_right hfin hd.le
    _ ≤ 1/constantF κ := one_div_le_one_div_of_le hF hden

/-- The treatment projection standard deviation obeys its public noise term. -/
-- @node: upper_numerator_treatment_sd_rate
lemma upper_numerator_treatment_sd_rate (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (j0 : ℕ)
    (huncap : ∀ j : Fin (upperJ κ n+1), j0 < j.val → upperT κ n j =
      ((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) j.val^(1+2*effectiveA κ))^(1/κ.p)) :
    Real.sqrt (((upperH κ n)⁻¹ * (3*(10 : ℝ)^(2/κ.p) +
      200*(∑ j : Fin (upperJ κ n), if j0 < j.val+1 then
        upperT κ n j.succ^(-2*(κ.p-1)) else 0))) / (treatmentBlock n).card) ≤
      Real.sqrt (3*(cG κ+200/constantF κ)) * rate κ n := by
  have ht := upper_tuning κ hκ n hn
  have hh := ht.1.1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hcard := (upper_block_card_bounds n hn).1
  have hcardpos : 0 < ((treatmentBlock n).card : ℝ) := lt_of_lt_of_le (by positivity) hcard
  have hF := (phase_algebra κ hκ).2.2.2.2.2.2
  have hr : 0 ≤ rate κ n := (Real.rpow_pos_of_pos (mul_pos hnpos hh) _).le.trans ht.2.2.1
  have hE : 0 ≤ cG κ+200/constantF κ := by unfold cG; positivity
  have htail := upper_treatment_tail_ledger κ hκ n hn j0 huncap
  have he : 3*(10 : ℝ)^(2/κ.p) + 200*(∑ j : Fin (upperJ κ n),
      if j0 < j.val+1 then upperT κ n j.succ^(-2*(κ.p-1)) else 0) ≤
        cG κ+200/constantF κ := by
    dsimp only [cG]
    have hb := add_le_add_left (mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 200))
      (3*(10 : ℝ)^(2/κ.p))
    simpa only [mul_one_div, add_comm] using hb
  have hb := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hh.le)) hcardpos.le
  have hi := one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ)/3) hcard
  have hc := mul_le_mul_of_nonneg_left hi (mul_nonneg (inv_nonneg.mpr hh.le) hE)
  have hscale : ((upperH κ n)⁻¹*(cG κ+200/constantF κ))/(treatmentBlock n).card ≤
      3*(cG κ+200/constantF κ)*(1/((n : ℝ)*upperH κ n)) := by
    calc
      _ = ((upperH κ n)⁻¹*(cG κ+200/constantF κ))*(1/(treatmentBlock n).card) := by ring
      _ ≤ ((upperH κ n)⁻¹*(cG κ+200/constantF κ))*(1/((n : ℝ)/3)) := hc
      _ = _ := by field_simp
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  have hbudget := mul_le_mul_of_nonneg_left (upper_inverse_bandwidth_budget κ hκ n hn)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hE)
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hE)]
  exact (hb.trans hscale).trans hbudget

/-- Only the degenerate threshold energy remains after both projection noise ledgers. -/
-- @node: upper_numerator_deviation_projection_rates
lemma upper_numerator_deviation_projection_rates (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (law : ObservedLaw) (hm : InModel κ law)
    (j0 : ℕ) (hj0 : j0 ≤ upperJ κ n)
    (hcap : ∀ j, j.val ≤ j0 → upperT κ n j = upperT κ n 0)
    (huncap : ∀ j : Fin (upperJ κ n+1), j0 < j.val → upperT κ n j =
      ((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) j.val^(1+2*effectiveA κ))^(1/κ.p)) :
    (∫ o, |numeratorHat κ n o - ∫ z, numeratorHat κ n z
      ∂Measure.pi (fun _ : Fin n => law.P)| ∂Measure.pi (fun _ : Fin n => law.P)) ≤
      Real.sqrt (3*(cG κ+200/constantF κ)) * rate κ n +
      Real.sqrt 30 * (1+40/constantA κ) * rate κ n +
      Real.sqrt (((10/(upperH κ n)^2) * (upperT κ n 0^(2-κ.p) +
        ∑ j : Fin (upperJ κ n), (2 : ℝ)^j.val*upperT κ n j.succ^(2-κ.p))) /
        ((treatmentBlock n).card * (outcomeBlock n).card)) := by
  apply (upper_numerator_deviation_outcome_rate κ hκ n hn law hm j0 hj0 hcap).trans
  exact add_le_add (add_le_add (upper_numerator_treatment_sd_rate κ hκ n hn j0 huncap) le_rfl) le_rfl

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
