module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedDensityRanges
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_ObservableOdds

/-! # Homogeneous effects of the calibrated laws

Positive four-cell odds identify the native logit contrast. The mixed covariance
branch and the fair risk shift therefore give the effects of the actual laws,
provided their continuous cell tables are valid.
-/
public section
noncomputable section
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Positive cells turn their odds ratio into the native conditional logit contrast.](goal) Under [the stated assumptions](hyp:x). Under [the stated assumptions](hyp:h). -/
-- @node: cell_odds_logit_difference
lemma cell_odds_logit_difference (P : ObservedLaw) (x : Covariate) (t : ℝ)
    (h : P.cells true true x * P.cells false false x =
      Real.exp t * (P.cells true false x * P.cells false true x)) :
    logit (armRisk P true x) - logit (armRisk P false x) = t := by
  have h0 := armRisk_interior P false x
  have h1 := armRisk_interior P true x
  have h00 := (P.interior_cells false false x).1
  have h01 := (P.interior_cells false true x).1
  have h10 := (P.interior_cells true false x).1
  have h11 := (P.interior_cells true true x).1
  apply Real.exp_injective
  rw [Real.exp_sub, logit, logit,
    Real.exp_log (div_pos h1.1 (sub_pos.mpr h1.2)),
    Real.exp_log (div_pos h0.1 (sub_pos.mpr h0.2))]
  unfold armRisk
  field_simp [ne_of_gt h00, ne_of_gt h01, ne_of_gt h10, ne_of_gt h11,
    ne_of_gt (add_pos h00 h01), ne_of_gt (add_pos h10 h11)]
  nlinarith [h]

/-- [A common conditional cell odds coefficient is the law's scalar effect and
makes its native logistic regression homogeneous. [the documented result](goal) Under [the stated assumptions](hyp:h). -/
-- @node: homogeneous_effect_of_cell_odds
lemma homogeneous_effect_of_cell_odds (P : ObservedLaw) (t : ℝ)
    (h : ∀ x, P.cells true true x * P.cells false false x =
      Real.exp t * (P.cells true false x * P.cells false true x)) :
    effect P = t ∧ HomogeneousLogit P := by
  have hd (x : Covariate) := cell_odds_logit_difference P x t (h x)
  have he : effect P = t := hd ⟨0, le_rfl, zero_le_one⟩
  refine ⟨he, ?_⟩
  intro x
  rw [he]
  have ha : prognosisLogit P x + t = logit (armRisk P true x) := by
    change logit (armRisk P false x) + t = _
    linarith [hd x]
  rw [ha]
  exact (logistic_logit _ (armRisk_interior P true x).1
    (armRisk_interior P true x).2).symm

/-- Valid totalized cells retain the literal supplied table. Under the stated assumptions. [The stated hypotheses](hyp:hp) hold, and [the stated conclusion follows](goal). -/
-- @node: totalCellLaw_cells_of_valid
lemma totalCellLaw_cells_of_valid (p : Bool → Bool → Covariate → ℝ)
    (hp : ValidCells p) : (totalCellLaw p).cells = p := by
  rw [totalCellLaw, dif_pos hp]
  rfl

/-- [Logistic risk shifting multiplies the risk odds by the exponential effect.](goal) Under [the stated assumptions](hyp:hξ,hξ1). -/
-- @node: riskShift_cross_odds
lemma riskShift_cross_odds (t ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) :
    riskShift t ξ * (1-ξ) = Real.exp t * ((1-riskShift t ξ)*ξ) := by
  have hden : 0 < 1+(Real.exp t-1)*ξ := by
    have he := Real.exp_pos t
    nlinarith [mul_pos he hξ]
  have hn : 1-ξ+ξ*Real.exp t ≠ 0 := by nlinarith [hden]
  unfold riskShift
  field_simp [ne_of_gt hden, hn]
  ring_nf
  nlinarith [mul_inv_cancel₀ hn]

/-- [Every valid fair table has its prescribed scalar effect, including the
comparator's effect, and is homogeneous at every covariate. [the documented result](goal) Under [the stated assumptions](hyp:hδ,hv). -/
-- @node: fairCells_homogeneous_effect
lemma fairCells_homogeneous_effect (b : Bool) (k : ℕ) (σ : Fin (k+1) → Bool)
    (t δ : ℝ) (hδ : |δ| ≤ 1/100) (hv : ValidCells (fairCells b k σ t δ)) :
    effect (totalCellLaw (fairCells b k σ t δ)) =
      (if b then t else comparatorEffect t δ) ∧
    HomogeneousLogit (totalCellLaw (fairCells b k σ t δ)) := by
  apply homogeneous_effect_of_cell_odds
  intro x
  rw [totalCellLaw_cells_of_valid _ hv]
  have hμ := fair_control_risk_bounds b k σ t δ x hδ
  have h := riskShift_cross_odds (if b then t else comparatorEffect t δ)
    (if b then fairRoot t δ (cellCoord k x)+δ*signFieldZ k σ x
      else fairRoot t δ (cellCoord k x)) (by linarith [hμ.1]) (by linarith [hμ.2])
  simp only [fairCells, Bool.false_eq_true, ↓reduceIte]
  nlinarith [h]

/-- [Every valid mixed table has the null or calibrated effect, and its logit
coefficient is homogeneous throughout the covariate interval. [the documented result](goal) Under [the stated assumptions](hyp:hη,hζ,hv). -/
-- @node: mixedCells_homogeneous_effect
lemma mixedCells_homogeneous_effect (b : Bool) (k : ℕ) (σ : Fin (k+1) → Bool)
    (η ζ : ℝ) (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100)
    (hv : ValidCells (mixedCells b k σ η ζ)) :
    effect (mixedLaw b k σ η ζ) = (if b then 32*η*ζ else 0) ∧
    HomogeneousLogit (mixedLaw b k σ η ζ) := by
  apply homogeneous_effect_of_cell_odds
  intro x
  simp only [mixedLaw, totalCellLaw_cells_of_valid _ hv]
  obtain ⟨he, hm⟩ := mixed_margin_bounds b k σ η ζ x hη hζ
  cases b
  · simp only [mixedCells, Bool.false_eq_true, ↓reduceIte, Real.exp_zero, one_mul,
      tableCell]
    ring
  · have ht : |32*η*ζ| ≤ 1/8 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 32)]
      have h := mul_le_mul hη hζ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/100)
      nlinarith
    simp only [Bool.false_eq_true, ↓reduceIte] at he hm ⊢
    have hr := covarianceBranch_odds_ratio (32*η*ζ)
      (1/2-η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x)
      (1/2+ζ*signFieldZ k σ x) ht (by linarith) (by linarith)
    have hp := covarianceBranch_table_positive (32*η*ζ)
      (1/2-η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x)
      (1/2+ζ*signFieldZ k σ x) ht (by linarith) (by linarith)
    simpa only [mixedCells, ↓reduceIte] using (div_eq_iff (ne_of_gt (mul_pos (hp true false) (hp false true)))).mp hr

end CausalSmith.Stat.LogoddsLowsmoothFrontier
