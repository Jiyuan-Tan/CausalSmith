module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairSpatialOscillation
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixedDensityRanges

/-! # Mixed propensity oscillation

The root bracket and bounded sign field give linear displacement from one half.
The interior logit bound transfers it to the native propensity and its oscillation.
-/
public section
set_option linter.style.whitespace false
noncomputable section
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The literal treatment margin is the propensity whenever the cells are valid.](goal) Under [the stated assumptions](hyp:x). Under [the stated assumptions](hyp:hv). -/
-- @node: mixedCells_propensity_eq
lemma mixedCells_propensity_eq (b : Bool) (k : ℕ) (σ : Fin (k+1) → Bool)
    (η ζ : ℝ) (hv : ValidCells (mixedCells b k σ η ζ)) (x : Covariate) :
    propensity (mixedLaw b k σ η ζ) x =
      (if b then 1/2-η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x
      else 1/2+η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x) := by
  rw [propensity, mixedLaw, totalCellLaw_cells_of_valid _ hv]
  simp only [mixedCells, tableCell, Bool.false_eq_true, ↓reduceIte]
  ring

/-- [Root and sign bounds retain the amplitude factor in the margin displacement.](goal) Under [the stated assumptions](hyp:x). -/
-- @node: mixed_margin_displacement
lemma mixed_margin_displacement (b : Bool) (k : ℕ) (σ : Fin (k+1) → Bool)
    (η ζ : ℝ) (x : Covariate) :
    |(if b then 1/2-η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x
      else 1/2+η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x)-1/2| ≤
      (5/2)*|η| := by
  have hq := mixedRoot_mem_bracket η ζ (cellCoord k x)
  have hqa : |mixedRoot η ζ (cellCoord k x)| ≤ 5/4 := by
    rw [abs_of_pos (by linarith [hq.1])]
    exact hq.2.le
  have hs := signFieldZ_abs_le_two k σ x
  have hp : |η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x| ≤ (5/2)*|η| := by
    simp only [abs_mul]
    calc
      _ ≤ (|η| *(5/4))*2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hqa (abs_nonneg η)) hs
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  cases b <;> simpa using hp

/-- [The native propensity logit has linear displacement, including fallback laws.](goal) Under [the stated assumptions](hyp:hη,hζ,x). -/
-- @node: mixedCells_propensity_displacement
lemma mixedCells_propensity_displacement (b : Bool) (k : ℕ) (σ : Fin (k+1) → Bool)
    (η ζ : ℝ) (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100) (x : Covariate) :
    |propensityLogit (mixedLaw b k σ η ζ) x| ≤ 15*|η| := by
  classical
  by_cases hv : ValidCells (mixedCells b k σ η ζ)
  · have hm := (mixed_margin_bounds b k σ η ζ x hη hζ).1
    have hp := mixed_margin_displacement b k σ η ζ x
    have hi := abs_le.mp hm
    change |logit (propensity (mixedLaw b k σ η ζ) x)| ≤ _
    rw [mixedCells_propensity_eq b k σ η ζ hv x]
    have hl := calibrated_logit_difference_le
      (if b then 1/2-η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x
        else 1/2+η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x) (1/2)
      ⟨by linarith [hi.1], by linarith [hi.2]⟩ (by norm_num)
    have hhalf : logit (1/2) = 0 := by norm_num [logit]
    rw [hhalf, sub_zero] at hl
    linarith
  · norm_num [propensityLogit, propensity, mixedLaw, totalCellLaw, hv, lawFromCells, logit]

/-- [Two centered displacements bound the oscillation at the propensity amplitude.](goal) Under [the stated assumptions](hyp:hη,hζ,x). -/
-- @node: mixedCells_propensity_oscillation
lemma mixedCells_propensity_oscillation (b : Bool) (k : ℕ) (σ : Fin (k+1) → Bool)
    (η ζ : ℝ) (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100) (x z : Covariate) :
    |propensityLogit (mixedLaw b k σ η ζ) x-
      propensityLogit (mixedLaw b k σ η ζ) z| ≤ 30*|η| := by
  have hx := mixedCells_propensity_displacement b k σ η ζ hη hζ x
  have hz := mixedCells_propensity_displacement b k σ η ζ hη hζ z
  exact (abs_sub _ _).trans (by linarith)

/-- [Every sufficiently small calibration radius gives the prescribed oscillation
uniformly over ranks and nonnegative exponents, for both mixed constructions. [the documented result](goal) Under [the stated assumptions](hyp:hsmall,hα,hβ,hk,x). Under [the stated assumptions](hyp:hε). -/
-- @node: mixedCells_uniform_propensity_oscillation
lemma mixedCells_uniform_propensity_oscillation (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε ≤ 1/100) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (k : ℕ) (hk : 1 ≤ k) (σ : Fin (k+1) → Bool) (b : Bool) (x z : Covariate) :
    |propensityLogit (mixedLaw b k σ (ε*(k : ℝ)^(-α)) (ε*(k : ℝ)^(-β))) x-
      propensityLogit (mixedLaw b k σ (ε*(k : ℝ)^(-α)) (ε*(k : ℝ)^(-β))) z| ≤
      2*(k : ℝ)^(-α) := by
  have hη := calibrated_amplitude_abs_le ε α hε.le hα k hk
  have hζ := calibrated_amplitude_abs_le ε β hε.le hβ k hk
  have ho := mixedCells_propensity_oscillation b k σ _ _
    (hη.trans hsmall) (hζ.trans hsmall) x z
  have hp : 0 ≤ ε*(k : ℝ)^(-α) := by positivity
  rw [abs_of_nonneg hp] at ho
  have he : 30*ε ≤ 2 := by linarith
  have hh := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg (Nat.cast_nonneg k) (-α))
  nlinarith

end CausalSmith.Stat.LogoddsLowsmoothFrontier
