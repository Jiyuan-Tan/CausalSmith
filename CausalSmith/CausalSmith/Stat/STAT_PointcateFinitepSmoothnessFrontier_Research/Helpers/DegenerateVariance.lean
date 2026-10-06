module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.TreatmentVariance

/-! Squared mesh-scale ledger for the degenerate numerator projection. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- The uncapped kernel energy is exactly the square of the bias scale. -/
-- @node: upper_uncapped_energy_identity
lemma upper_uncapped_energy_identity (κ : Params) (hκ : κ.Valid)
    (x δ : ℝ) (hx : 0 < x) (hδ : 0 < δ) :
    ((x*δ^(1+2*effectiveA κ))^(1/κ.p))^(2-κ.p)/(x*δ) =
      (x^(-qExp κ)*δ^(-effectiveD κ))^2 := by
  have hp : κ.p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hκ.1.1)
  rw [← Real.rpow_mul (by positivity), Real.mul_rpow hx.le (by positivity),
    ← Real.rpow_mul hδ.le, mul_div_mul_comm, mul_pow]
  have hdiv (z b : ℝ) (hz : 0 < z) : z^b/z = z^(b-1) := by
    rw [Real.rpow_sub hz, Real.rpow_one]
  rw [hdiv x _ hx, hdiv δ _ hδ,
    ← Real.rpow_natCast, ← Real.rpow_mul hx.le,
    ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
  have he : (1/κ.p)*(2-κ.p)-1 = -qExp κ*2 := by
    unfold qExp
    field_simp
    ring
  have hd : (1+2*effectiveA κ)*((1/κ.p)*(2-κ.p))-1 = -effectiveD κ*2 := by
    unfold effectiveD qExp
    field_simp
    ring
  rw [he, hd]
  norm_num

/-- Squared uncapped bias scales sum backwards from the certified finest scale. -/
-- @node: upper_squared_mesh_ledger
lemma upper_squared_mesh_ledger (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) :
    (∑ j : Fin (upperJ κ n),
      (((n : ℝ)^2*upperH κ n)^(-qExp κ) *
        cellLen (upperH κ n) (j.val+1)^(-effectiveD κ))^2) ≤
      16*(rate κ n)^2/(1-(2 : ℝ)^(-(2*effectiveD κ))) := by
  have ht := upper_tuning κ hκ n hn
  have hh : 0 < upperH κ n := ht.1.1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hc (j : ℕ) : 0 < cellLen (upperH κ n) j := div_pos hh (by positivity)
  have hd := (phase_algebra κ hκ).2.2.2.1
  have hden : 0 < 1-(2 : ℝ)^(-(2*effectiveD κ)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hr : 0 ≤ rate κ n := le_trans (by positivity) ht.2.2.1
  by_cases hJ : upperJ κ n = 0
  · have : IsEmpty (Fin (upperJ κ n)) := hJ ▸ inferInstance
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    positivity
  have hfin := (upper_uncapped_finest_bias κ hκ n hn (Nat.pos_of_ne_zero hJ)).trans
    ht.2.2.2.2.1
  have hsq : (((n : ℝ)^2*upperH κ n)^(-qExp κ) *
      cellLen (upperH κ n) (upperJ κ n)^(-effectiveD κ))^2 ≤ 16*(rate κ n)^2 := by
    have hnon : 0 ≤ ((n : ℝ)^2*upperH κ n)^(-qExp κ) *
      cellLen (upperH κ n) (upperJ κ n)^(-effectiveD κ) :=
        mul_nonneg (Real.rpow_nonneg (by positivity) _)
          (Real.rpow_nonneg (hc _).le _)
    nlinarith
  have hgeom := upper_cell_negative_sum (upperH κ n) ht.1.1
    (2*effectiveD κ) (by linarith) (upperJ κ n)
  rw [Finset.sum_range] at hgeom
  have hid (j : ℕ) : (cellLen (upperH κ n) j^(-effectiveD κ))^2 =
      cellLen (upperH κ n) j^(-(2*effectiveD κ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by exact (hc j).le)]
    congr 1
    ring
  simp_rw [mul_pow, hid]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (((n : ℝ)^2*upperH κ n)^(-qExp κ))^2 *
        (cellLen (upperH κ n) (upperJ κ n)^(-(2*effectiveD κ)) /
          (1-(2 : ℝ)^(-(2*effectiveD κ)))) :=
      mul_le_mul_of_nonneg_left hgeom (sq_nonneg _)
    _ = ((((n : ℝ)^2*upperH κ n)^(-qExp κ) *
        cellLen (upperH κ n) (upperJ κ n)^(-effectiveD κ))^2) /
          (1-(2 : ℝ)^(-(2*effectiveD κ))) := by rw [mul_pow, hid]; ring
    _ ≤ _ := div_le_div_of_nonneg_right hsq hden.le

/-- Capping can only decrease a positive-scale second-moment energy. -/
-- @node: upper_level_energy_envelope
lemma upper_level_energy_envelope (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (j : Fin (upperJ κ n)) :
    ((2 : ℝ)^j.val*upperT κ n j.succ^(2-κ.p))/((n : ℝ)^2*(upperH κ n)^2) ≤
      (((n : ℝ)^2*upperH κ n)^(-qExp κ) *
        cellLen (upperH κ n) (j.val+1)^(-effectiveD κ))^2 := by
  have hh := (upper_tuning κ hκ n hn).1.1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hc : 0 < cellLen (upperH κ n) (j.val+1) := div_pos hh (by positivity)
  have hT := upper_threshold_positive κ hκ n hn j.succ
  have huncap : upperT κ n j.succ ≤
      (((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) (j.val+1)^(1+2*effectiveA κ))^(1/κ.p)) := by
    simp only [upperT, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, ↓reduceIte]
    exact min_le_right _ _
  have he := Real.rpow_le_rpow (by linarith : 0 ≤ upperT κ n j.succ) huncap
    (sub_nonneg.mpr hκ.1.2)
  have hnon : 0 ≤ upperT κ n j.succ^(2-κ.p) /
      ((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) (j.val+1)) := by positivity
  calc
    _ = (upperT κ n j.succ^(2-κ.p) /
        ((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) (j.val+1)))/2 := by
      unfold cellLen
      rw [pow_succ]
      field_simp
      ring
    _ ≤ upperT κ n j.succ^(2-κ.p) /
        ((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) (j.val+1)) := by linarith
    _ ≤ (((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) (j.val+1)^(1+2*effectiveA κ))^(1/κ.p))^(2-κ.p) /
        ((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) (j.val+1)) :=
      div_le_div_of_nonneg_right he (by positivity)
    _ = _ := upper_uncapped_energy_identity κ hκ _ _ (by positivity) hc

/-- The coarse degenerate energy is dominated by the coarse moment rate. -/
-- @node: upper_coarse_energy_rate
lemma upper_coarse_energy_rate (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) :
    upperT κ n 0^(2-κ.p)/((n : ℝ)^2*(upperH κ n)^2) ≤ (rate κ n)^2 := by
  have ht := upper_tuning κ hκ n hn
  have hh := ht.1.1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx : 0 < (n : ℝ)*upperH κ n := mul_pos hnpos hh
  have hr : 0 ≤ rate κ n := le_trans (by positivity) ht.2.2.1
  have hu : 0 ≤ ((n : ℝ)*upperH κ n)^(-qExp κ) := by positivity
  have hi : 1/((n : ℝ)*upperH κ n) ≤ 1 := (div_le_one hx).mpr ht.2.1
  calc
    _ = (upperT κ n 0^(2-κ.p)/((n : ℝ)*upperH κ n)) *
        (1/((n : ℝ)*upperH κ n)) := by ring
    _ = (((n : ℝ)*upperH κ n)^(-qExp κ))^2 *
        (1/((n : ℝ)*upperH κ n)) := by rw [upper_coarse_variance_identity κ hκ n hn]
    _ ≤ (((n : ℝ)*upperH κ n)^(-qExp κ))^2 :=
      mul_le_of_le_one_right (sq_nonneg _) hi
    _ ≤ _ := by nlinarith [ht.2.2.1]

/-- All finite kernel energies obey the public squared-rate ledger. -/
-- @node: upper_degenerate_energy_ledger
lemma upper_degenerate_energy_ledger (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) :
    (upperT κ n 0^(2-κ.p) +
      ∑ j : Fin (upperJ κ n), (2 : ℝ)^j.val*upperT κ n j.succ^(2-κ.p)) /
      ((n : ℝ)^2*(upperH κ n)^2) ≤
    (1+(1-(2 : ℝ)^(-(2*effectiveA κ)))⁻¹+
      16*(1-(2 : ℝ)^(-(2*effectiveD κ)))⁻¹)*(rate κ n)^2 := by
  have ha := (phase_algebra κ hκ).2.2.1
  have hA : 0 < 1-(2 : ℝ)^(-(2*effectiveA κ)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hs := (Finset.sum_le_sum (fun j _ => upper_level_energy_envelope κ hκ n hn j)).trans
    (upper_squared_mesh_ledger κ hκ n hn)
  rw [← Finset.sum_div] at hs
  rw [add_div]
  have hc := upper_coarse_energy_rate κ hκ n hn
  have hextra : 0 ≤ (1-(2 : ℝ)^(-(2*effectiveA κ)))⁻¹*(rate κ n)^2 := by positivity
  calc
    _ ≤ (rate κ n)^2 + 16*(rate κ n)^2/(1-(2 : ℝ)^(-(2*effectiveD κ))) := add_le_add hc hs
    _ ≤ _ := by rw [div_eq_mul_inv]; nlinarith

/-- The actual two-block degenerate standard deviation fits the final noise constant. -/
-- @node: upper_numerator_degenerate_sd_rate
lemma upper_numerator_degenerate_sd_rate (κ : Params) (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) :
    Real.sqrt (((10/(upperH κ n)^2) * (upperT κ n 0^(2-κ.p) +
      ∑ j : Fin (upperJ κ n), (2 : ℝ)^j.val*upperT κ n j.succ^(2-κ.p))) /
      ((treatmentBlock n).card * (outcomeBlock n).card)) ≤
    Real.sqrt (90*(1+(1-(2 : ℝ)^(-2*effectiveA κ))⁻¹+
      16*(1-(2 : ℝ)^(-2*effectiveD κ))⁻¹)) * rate κ n := by
  have ht := upper_tuning κ hκ n hn
  have hh := ht.1.1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hr : 0 ≤ rate κ n := le_trans (by positivity) ht.2.2.1
  obtain ⟨hT, hY⟩ := upper_block_card_bounds n hn
  have hTpos : 0 < ((treatmentBlock n).card : ℝ) := lt_of_lt_of_le (by positivity) hT
  have hYpos : 0 < ((outcomeBlock n).card : ℝ) := lt_of_lt_of_le (by positivity) hY
  have hprod : (n : ℝ)^2/9 ≤ ((treatmentBlock n).card : ℝ)*(outcomeBlock n).card := by
    nlinarith
  let E := upperT κ n 0^(2-κ.p) +
    ∑ j : Fin (upperJ κ n), (2 : ℝ)^j.val*upperT κ n j.succ^(2-κ.p)
  have he : 0 ≤ E := by
    dsimp [E]
    apply add_nonneg
    · exact Real.rpow_nonneg (by linarith [upper_threshold_positive κ hκ n hn 0]) _
    · apply Finset.sum_nonneg
      intro j _
      exact mul_nonneg (by positivity)
        (Real.rpow_nonneg (by linarith [upper_threshold_positive κ hκ n hn j.succ]) _)
  let C := 1+(1-(2 : ℝ)^(-2*effectiveA κ))⁻¹+
    16*(1-(2 : ℝ)^(-2*effectiveD κ))⁻¹
  have ha := (phase_algebra κ hκ).2.2.1
  have hd := (phase_algebra κ hκ).2.2.2.1
  have hA : 0 < 1-(2 : ℝ)^(-2*effectiveA κ) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hD : 0 < 1-(2 : ℝ)^(-2*effectiveD κ) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have henergy : E/((n : ℝ)^2*(upperH κ n)^2) ≤ C*(rate κ n)^2 := by
    simpa only [E, C, neg_mul] using upper_degenerate_energy_ledger κ hκ n hn
  have hscale : ((10/(upperH κ n)^2)*E) /
      ((treatmentBlock n).card*(outcomeBlock n).card) ≤
      90*(E/((n : ℝ)^2*(upperH κ n)^2)) := by
    calc
      _ ≤ ((10/(upperH κ n)^2)*E) / ((n : ℝ)^2/9) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hprod
      _ = _ := by field_simp; ring
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 90*C)]
  exact hscale.trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left henergy (by norm_num : (0 : ℝ) ≤ 90))

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
