module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedPrognosisOscillation
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.SpatialLipschitz

/-! # Null mixed prognosis spatial bounds

The null covariance vanishes, so its control risk is exactly the prognosis
margin. The shared-sign Lipschitz estimate and interior logit bound preserve
the prognosis amplitude, including the endpoint exponent one.
-/
public section
set_option linter.style.whitespace false
noncomputable section
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [A positive treatment complement identifies the table's control risk
with the prognosis margin minus its covariance correction. [the documented result](goal) Under [the stated assumptions](hyp:he). -/
-- @node: mixed_table_control_risk_eq
lemma mixed_table_control_risk_eq (e m c : ℝ) (he : e < 1) :
    tableCell e m c false true /
      (tableCell e m c false false + tableCell e m c false true) = m-c/(1-e) := by
  simp only [tableCell, Bool.false_eq_true, ↓reduceIte]
  rw [show (1-e)*(1-m)+c+((1-e)*m-c) = 1-e by ring]
  field_simp [show 1-e ≠ 0 by linarith]

/-- [On the fixed interior margin interval, changes in the covariance
correction split into a covariance change and a treatment-margin change. [the documented result](goal) Under [the stated assumptions](hyp:hx,hz). -/
-- @node: mixed_covariance_correction_difference_le
lemma mixed_covariance_correction_difference_le (ex ez cx cz : ℝ)
    (hx : |ex-1/2| ≤ 1/40) (hz : |ez-1/2| ≤ 1/40) :
    |cx/(1-ex)-cz/(1-ez)| ≤ 3*|cx-cz|+9*|cz| *|ex-ez| := by
  have hxpos : 0 < 1-ex := by linarith [(abs_le.mp hx).2]
  have hzpos : 0 < 1-ez := by linarith [(abs_le.mp hz).2]
  have hprod : 0 < (1-ex)*(1-ez) := mul_pos hxpos hzpos
  have hprodlo : 1/9 ≤ (1-ex)*(1-ez) := by
    have ha : (1/3 : ℝ) ≤ 1-ex := by linarith [(abs_le.mp hx).2]
    have hb : (1/3 : ℝ) ≤ 1-ez := by linarith [(abs_le.mp hz).2]
    nlinarith [mul_le_mul ha hb (by norm_num : (0 : ℝ) ≤ 1/3) hxpos.le]
  have ha : |(cx-cz)/(1-ex)| ≤ 3*|cx-cz| := by
    rw [abs_div, abs_of_pos hxpos]
    apply (div_le_iff₀ hxpos).mpr
    nlinarith [(abs_le.mp hx).2, abs_nonneg (cx-cz)]
  have hb : |cz*(ex-ez)/((1-ex)*(1-ez))| ≤ 9*|cz| *|ex-ez| := by
    rw [abs_div, abs_mul, abs_of_pos hprod]
    apply (div_le_iff₀ hprod).mpr
    nlinarith [mul_le_mul_of_nonneg_left hprodlo (mul_nonneg (abs_nonneg cz) (abs_nonneg (ex-ez)))]
  have heq : cx/(1-ex)-cz/(1-ez) =
      (cx-cz)/(1-ex)+cz*(ex-ez)/((1-ex)*(1-ez)) := by
    field_simp [ne_of_gt hxpos, ne_of_gt hzpos]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add ha hb)

/-- [The control-risk formula transfers covariance and margin moduli to
an explicit risk modulus on the fixed interior box. [the documented result](goal) Under [the stated assumptions](hyp:hx,hz). -/
-- @node: mixed_table_control_risk_difference_le
lemma mixed_table_control_risk_difference_le (ex ez mx mz cx cz : ℝ)
    (hx : |ex-1/2| ≤ 1/40) (hz : |ez-1/2| ≤ 1/40) :
    |tableCell ex mx cx false true /
        (tableCell ex mx cx false false + tableCell ex mx cx false true)-
      tableCell ez mz cz false true /
        (tableCell ez mz cz false false + tableCell ez mz cz false true)| ≤
      |mx-mz|+3*|cx-cz|+9*|cz| *|ex-ez| := by
  rw [mixed_table_control_risk_eq _ _ _ (by linarith [(abs_le.mp hx).2]),
    mixed_table_control_risk_eq _ _ _ (by linarith [(abs_le.mp hz).2])]
  rw [show mx-cx/(1-ex)-(mz-cz/(1-ez)) = (mx-mz)-(cx/(1-ex)-cz/(1-ez)) by ring]
  have hh := mixed_covariance_correction_difference_le ex ez cx cz hx hz
  exact (abs_sub _ _).trans (by linarith)

/-- [The valid null mixed law has control risk equal to its prognosis margin.](goal) Under [the stated assumptions](hyp:hη,hζ,x). Under [the stated assumptions](hyp:hv). -/
-- @node: mixedCells_null_control_risk_eq
lemma mixedCells_null_control_risk_eq (k : ℕ) (σ : Fin (k+1) → Bool)
    (η ζ : ℝ) (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100)
    (hv : ValidCells (mixedCells false k σ η ζ)) (x : Covariate) :
    armRisk (mixedLaw false k σ η ζ) false x = 1/2+ζ*signFieldZ k σ x := by
  have he := (abs_le.mp (mixed_margin_bounds false k σ η ζ x hη hζ).1).2
  simp only [Bool.false_eq_true, ↓reduceIte] at he
  rw [armRisk, mixedLaw, totalCellLaw_cells_of_valid _ hv]
  change tableCell _ _ 0 false true / (tableCell _ _ 0 false false + tableCell _ _ 0 false true) = _
  rw [mixed_table_control_risk_eq _ _ 0 (by simp only [Bool.false_eq_true, ↓reduceIte]; linarith)]
  simp

/-- [The null native prognosis logit has a global Lipschitz constant linear
in the prognosis amplitude, independently of the propensity amplitude. [the documented result](goal) Under [the stated assumptions](hyp:hη,hζ,x). Under [the stated assumptions](hyp:hk). -/
-- @node: mixedCells_null_prognosis_linear
lemma mixedCells_null_prognosis_linear (k : ℕ) (hk : 1 ≤ k)
    (σ : Fin (k+1) → Bool) (η ζ : ℝ)
    (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100) (x z : Covariate) :
    |prognosisLogit (mixedLaw false k σ η ζ) x-
      prognosisLogit (mixedLaw false k σ η ζ) z| ≤
      24*|ζ| *(k : ℝ)*|(x : ℝ)-(z : ℝ)| := by
  classical
  by_cases hv : ValidCells (mixedCells false k σ η ζ)
  · have hi (w : Covariate) := abs_le.mp (mixed_margin_bounds false k σ η ζ w hη hζ).2
    change |logit (armRisk _ false x)-logit (armRisk _ false z)| ≤ _
    rw [mixedCells_null_control_risk_eq k σ η ζ hη hζ hv x,
      mixedCells_null_control_risk_eq k σ η ζ hη hζ hv z]
    have hl := calibrated_logit_difference_le (1/2+ζ*signFieldZ k σ x)
      (1/2+ζ*signFieldZ k σ z)
      ⟨by linarith [(hi x).1], by linarith [(hi x).2]⟩
      ⟨by linarith [(hi z).1], by linarith [(hi z).2]⟩
    rw [show 1/2+ζ*signFieldZ k σ x-(1/2+ζ*signFieldZ k σ z) =
      ζ*(signFieldZ k σ x-signFieldZ k σ z) by ring, abs_mul] at hl
    have hs := mul_le_mul_of_nonneg_left (signFieldZ_lipschitz k hk σ x z) (abs_nonneg ζ)
    nlinarith only [hl, hs]
  · have hz : ∀ w, prognosisLogit (mixedLaw false k σ η ζ) w = 0 := by
      intro w
      norm_num [prognosisLogit, armRisk, mixedLaw, totalCellLaw, hv, lawFromCells, logit]
    rw [hz x, hz z, sub_self, abs_zero]
    positivity

/-- [The null prognosis Lipschitz estimate fits the prescribed scale for
all nonnegative public exponents and every calibrated rank. [the documented result](goal) Under [the stated assumptions](hyp:hsmall,hα,hβ,hk,x). Under [the stated assumptions](hyp:hε). -/
-- @node: mixedCells_uniform_null_prognosis_linear
lemma mixedCells_uniform_null_prognosis_linear (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε ≤ 1/100) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (k : ℕ) (hk : 1 ≤ k) (σ : Fin (k+1) → Bool) (x z : Covariate) :
    |prognosisLogit (mixedLaw false k σ (ε*(k : ℝ)^(-α)) (ε*(k : ℝ)^(-β))) x-
      prognosisLogit (mixedLaw false k σ (ε*(k : ℝ)^(-α)) (ε*(k : ℝ)^(-β))) z| ≤
      (k : ℝ)^(1-β)*|(x : ℝ)-(z : ℝ)| := by
  have hη := calibrated_amplitude_abs_le ε α hε.le hα k hk
  have hζ := calibrated_amplitude_abs_le ε β hε.le hβ k hk
  have hl := mixedCells_null_prognosis_linear k hk σ _ _
    (hη.trans hsmall) (hζ.trans hsmall) x z
  have hp : 0 ≤ ε*(k : ℝ)^(-β) := by positivity
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hrate : (k : ℝ)^(1-β) = (k : ℝ)^(-β)*(k : ℝ) := by
    rw [show 1-β = -β+1 by ring, Real.rpow_add hkpos, Real.rpow_one]
  rw [abs_of_nonneg hp] at hl
  have heps : 24*ε ≤ 1 := by linarith
  have hh := mul_le_mul_of_nonneg_right heps (Real.rpow_nonneg hkpos.le (-β))
  have hh' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hh hkpos.le) (abs_nonneg ((x : ℝ)-(z : ℝ)))
  rw [hrate]
  nlinarith only [hl, hh']

end CausalSmith.Stat.LogoddsLowsmoothFrontier
