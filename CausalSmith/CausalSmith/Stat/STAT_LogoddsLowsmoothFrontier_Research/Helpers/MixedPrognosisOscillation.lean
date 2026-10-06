module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.CalibratedModelProperties
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedPropensityOscillation

/-! # Mixed prognosis oscillation

The rationalized covariance retains its effect factor. Control-risk displacement
and the interior logit estimate give oscillation at the prognosis amplitude.
-/
public section
set_option linter.style.whitespace false
noncomputable section
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The covariance is bounded linearly by the effect on the fixed interior box.](goal) Under [the stated assumptions](hyp:ht,he,hm). -/
-- @node: covarianceBranch_effect_bound
lemma covarianceBranch_effect_bound (t e m : ℝ)
    (ht : |t| ≤ 1/8) (he : |e-1/2| ≤ 1/8) (hm : |m-1/2| ≤ 1/8) :
    |covarianceBranch t e m| ≤ |t| := by
  have hL := (covarianceBranch_local_bounds t e m ht he hm).1
  obtain ⟨hel,heh⟩ := abs_le.mp he
  obtain ⟨hml,hmh⟩ := abs_le.mp hm
  let v := e*(1-e)*m*(1-m)
  let L := 1+(Real.exp t-1)*(e*(1-m)+(1-e)*m)
  have hv : 0 ≤ v := by
    dsimp [v]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) (by linarith)
  have hx : 0 ≤ e*(1-e) := mul_nonneg (by linarith) (by linarith)
  have hy : 0 ≤ m*(1-m) := mul_nonneg (by linarith) (by linarith)
  have hxhi : e*(1-e) ≤ 1/4 := by nlinarith [sq_nonneg (e-1/2)]
  have hyhi : m*(1-m) ≤ 1/4 := by nlinarith [sq_nonneg (m-1/2)]
  have hvhi : v ≤ 1/16 := by
    dsimp [v]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxhi) hy]
  have hden : 3/4 ≤ L+Real.sqrt (L^2-4*(Real.exp t-1)^2*v) :=
    hL.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hc : |covarianceBranch t e m| *
      (L+Real.sqrt (L^2-4*(Real.exp t-1)^2*v)) = 2*|Real.exp t-1| *v := by
    unfold covarianceBranch
    change |2*(Real.exp t-1)*v/(L+Real.sqrt (L^2-4*(Real.exp t-1)^2*v))| * _ = _
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg hv, abs_of_pos (by linarith : 0 < L+Real.sqrt (L^2-4*(Real.exp t-1)^2*v))]
    exact div_mul_cancel₀ _ (by linarith)
  have hd := Real.abs_exp_sub_one_le (show |t| ≤ 1 by linarith)
  have hp := mul_le_mul_of_nonneg_right hd hv
  have hq := mul_le_mul_of_nonneg_left hvhi (abs_nonneg t)
  have hr := mul_le_mul_of_nonneg_left hden (abs_nonneg (covarianceBranch t e m))
  nlinarith only [hc, hp, hq, hr, abs_nonneg t]

/-- [Subtracting the covariance correction bounds the control risk's displacement.](goal) Under [the stated assumptions](hyp:he). -/
-- @node: mixed_table_control_displacement
lemma mixed_table_control_displacement (e m c : ℝ)
    (he : |e-1/2| ≤ 1/40) :
    |tableCell e m c false true /
      (tableCell e m c false false + tableCell e m c false true)-1/2| ≤
      |m-1/2|+3*|c| := by
  obtain ⟨hel,heh⟩ := abs_le.mp he
  have hd : 0 < 1-e := by linarith
  have hid : |c/(1-e)| ≤ 3*|c| := by
    rw [abs_div, abs_of_pos hd]
    apply (div_le_iff₀ hd).mpr
    nlinarith [abs_nonneg c]
  have heq : tableCell e m c false true /
      (tableCell e m c false false + tableCell e m c false true)-1/2 =
      (m-1/2)-c/(1-e) := by
    simp only [tableCell, Bool.false_eq_true, ↓reduceIte]
    rw [show (1-e)*(1-m)+c+((1-e)*m-c) = 1-e by ring]
    field_simp [ne_of_gt hd]
    <;> ring
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add_right hid _)

/-- [The actual native prognosis retains the prognosis amplitude in its envelope.](goal) Under [the stated assumptions](hyp:hη,hζ,x). -/
-- @node: mixedCells_prognosis_displacement
lemma mixedCells_prognosis_displacement (b : Bool) (k : ℕ) (σ : Fin (k+1) → Bool)
    (η ζ : ℝ) (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100) (x : Covariate) :
    |prognosisLogit (mixedLaw b k σ η ζ) x| ≤ 18*|ζ| := by
  classical
  by_cases hv : ValidCells (mixedCells b k σ η ζ)
  · let e := if b then 1/2-η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x
      else 1/2+η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x
    let m := 1/2+ζ*signFieldZ k σ x
    let c := if b then covarianceBranch (32*η*ζ) e m else 0
    obtain ⟨he,hm⟩ := mixed_margin_bounds b k σ η ζ x hη hζ
    have ht : |32*η*ζ| ≤ 1/8 := by
      simp only [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 32)]
      nlinarith [mul_le_mul hη hζ (abs_nonneg ζ) (by norm_num : (0:ℝ) ≤ 1/100)]
    have hc : |c| ≤ 32*|η| *|ζ| := by
      dsimp [c]
      split
      · simpa only [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 32)] using
          covarianceBranch_effect_bound (32*η*ζ) e m ht (he.trans (by norm_num)) (hm.trans (by norm_num))
      · simp; positivity
    have hcf : |c| ≤ 1/24 := by
      dsimp [c]
      split
      · exact (covarianceBranch_local_bounds _ _ _ ht (he.trans (by norm_num)) (hm.trans (by norm_num))).2.2
      · norm_num
    have hmamp : |m-1/2| ≤ 2*|ζ| := by
      dsimp [m]
      simpa only [add_sub_cancel_left, abs_mul, mul_comm] using
        mul_le_mul_of_nonneg_left (signFieldZ_abs_le_two k σ x) (abs_nonneg ζ)
    have hr := mixed_table_control_displacement e m c he
    have hi := mixed_table_control_risk_bounds e m c he hm hcf
    have hl := calibrated_logit_difference_le _ (1/2) hi (by norm_num)
    have hh : logit (1/2) = 0 := by norm_num [logit]
    rw [hh, sub_zero] at hl
    change |logit (armRisk _ false x)| ≤ _
    rw [armRisk, mixedLaw, totalCellLaw_cells_of_valid _ hv]
    change |logit (tableCell e m c false true /
      (tableCell e m c false false + tableCell e m c false true))| ≤ _
    have hprod := mul_le_mul_of_nonneg_right hη (abs_nonneg ζ)
    nlinarith only [hc, hprod, hr, hl, hmamp, abs_nonneg ζ]
  · norm_num [prognosisLogit, armRisk, mixedLaw, totalCellLaw, hv, lawFromCells, logit]

/-- [Two centered bounds control mixed prognosis oscillation.](goal) Under [the stated assumptions](hyp:hη,hζ,x). -/
-- @node: mixedCells_prognosis_oscillation
lemma mixedCells_prognosis_oscillation (b : Bool) (k : ℕ) (σ : Fin (k+1) → Bool)
    (η ζ : ℝ) (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100) (x z : Covariate) :
    |prognosisLogit (mixedLaw b k σ η ζ) x-prognosisLogit (mixedLaw b k σ η ζ) z| ≤ 36*|ζ| := by
  have hx := mixedCells_prognosis_displacement b k σ η ζ hη hζ x
  have hz := mixedCells_prognosis_displacement b k σ η ζ hη hζ z
  exact (abs_sub _ _).trans (by linarith)

/-- [The oscillation estimate fits the prescribed scale at every calibrated rank.](goal) Under [the stated assumptions](hyp:hε,hsmall,hα,hβ,hk,x). -/
-- @node: mixedCells_uniform_prognosis_oscillation
lemma mixedCells_uniform_prognosis_oscillation (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε ≤ 1/100) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (k : ℕ) (hk : 1 ≤ k) (σ : Fin (k+1) → Bool) (b : Bool) (x z : Covariate) :
    |prognosisLogit (mixedLaw b k σ (ε*(k : ℝ)^(-α)) (ε*(k : ℝ)^(-β))) x-
      prognosisLogit (mixedLaw b k σ (ε*(k : ℝ)^(-α)) (ε*(k : ℝ)^(-β))) z| ≤
      2*(k : ℝ)^(-β) := by
  have hη := calibrated_amplitude_abs_le ε α hε.le hα k hk
  have hζ := calibrated_amplitude_abs_le ε β hε.le hβ k hk
  have ho := mixedCells_prognosis_oscillation b k σ _ _
    (hη.trans hsmall) (hζ.trans hsmall) x z
  have hp : 0 ≤ ε*(k : ℝ)^(-β) := by positivity
  rw [abs_of_nonneg hp] at ho
  have hh := mul_le_mul_of_nonneg_right (show 36*ε ≤ 2 by linarith)
    (Real.rpow_nonneg (Nat.cast_nonneg k) (-β))
  nlinarith

end CausalSmith.Stat.LogoddsLowsmoothFrontier
