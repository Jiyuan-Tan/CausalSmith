module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairDensityRanges
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_ExactCalibrations

/-! # Mixed four-cell density bounds

The literal root bracket bounds both perturbed margins. The covariance branch
bound then gives a common density floor and ceiling for the actual mixed cells,
including signed amplitudes and the law constructor's fallback inputs.
-/
public section
noncomputable section
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The mixed selector always lies in its bracket, including its fallback value. [the stated conclusion](goal) holds. -/
-- @node: mixedRoot_mem_bracket
lemma mixedRoot_mem_bracket (η ζ u : ℝ) :
    mixedRoot η ζ u ∈ Set.Ioo (3/4 : ℝ) (5/4) := by
  classical
  by_cases h : ∃ q : ℝ, q ∈ Set.Ioo (3/4) (5/4) ∧ mixedEquation η ζ u q = 0
  · exact (mixedRoot_spec η ζ u h).1
  · rw [mixedRoot, dif_neg h]
    constructor <;> norm_num

/-- Small signed amplitudes keep both mixed margins near one half. Under the stated assumptions. [The stated hypotheses](hyp:hη,hζ) hold, and [the stated conclusion follows](goal). -/
-- @node: mixed_margin_bounds
lemma mixed_margin_bounds (b : Bool) (k : ℕ) (σ : Fin (k+1) → Bool)
    (η ζ : ℝ) (x : Covariate) (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100) :
    |(if b then 1/2-η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x
      else 1/2+η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x)-1/2| ≤ 1/40 ∧
    |(1/2+ζ*signFieldZ k σ x)-1/2| ≤ 1/40 := by
  have hq := mixedRoot_mem_bracket η ζ (cellCoord k x)
  have hqabs : |mixedRoot η ζ (cellCoord k x)| ≤ 5/4 := by
    rw [abs_of_pos (by linarith [hq.1])]
    exact hq.2.le
  have hz := signFieldZ_abs_le_two k σ x
  have hprod : |η*mixedRoot η ζ (cellCoord k x)*signFieldZ k σ x| ≤ 1/40 := by
    simp only [abs_mul]
    calc
      _ ≤ ((1/100 : ℝ)*(5/4))*2 :=
        mul_le_mul (mul_le_mul hη hqabs (abs_nonneg _) (by norm_num)) hz
          (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hprod' : |ζ*signFieldZ k σ x| ≤ 1/40 := by
    rw [abs_mul]
    calc
      _ ≤ (1/100 : ℝ)*2 := mul_le_mul hζ hz (abs_nonneg _) (by norm_num)
      _ ≤ _ := by norm_num
  constructor
  · cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · simpa only [add_sub_cancel_left] using hprod
    · simpa only [sub_sub_cancel_left, abs_neg] using hprod
  · simpa only [add_sub_cancel_left] using hprod'

/-- [Products of the centered margins have uniform lower and upper bounds.](goal) Under [the stated assumptions](hyp:x). Under [the stated assumptions](hyp:hx,hy). -/
-- @node: mixed_centered_product_bounds
lemma mixed_centered_product_bounds (x y : ℝ)
    (hx : x ∈ Set.Icc (19/40 : ℝ) (21/40))
    (hy : y ∈ Set.Icc (19/40 : ℝ) (21/40)) :
    (361/1600 : ℝ) ≤ x*y ∧ x*y ≤ 441/1600 := by
  constructor
  · have h := mul_le_mul hx.1 hy.1 (by norm_num : (0 : ℝ) ≤ 19/40)
      (by linarith [hx.1])
    norm_num at h
    exact h
  · have h := mul_le_mul hx.2 hy.2 (by linarith [hy.1]) (by norm_num)
    norm_num at h
    exact h

/-- [All four mixed cells retain a fixed density floor and ceiling.](goal) Under [the stated assumptions](hyp:he,hm,hc). -/
-- @node: mixed_table_density_bounds
lemma mixed_table_density_bounds (e m c : ℝ)
    (he : |e-1/2| ≤ 1/40) (hm : |m-1/2| ≤ 1/40) (hc : |c| ≤ 1/24)
    (a y : Bool) : (1/2 : ℝ) ≤ 4*tableCell e m c a y ∧
      4*tableCell e m c a y ≤ 2 := by
  obtain ⟨helo, hehi⟩ := abs_le.mp he
  obtain ⟨hmlo, hmhi⟩ := abs_le.mp hm
  obtain ⟨hclo, hchi⟩ := abs_le.mp hc
  have he' : e ∈ Set.Icc (19/40 : ℝ) (21/40) := ⟨by linarith, by linarith⟩
  have hm' : m ∈ Set.Icc (19/40 : ℝ) (21/40) := ⟨by linarith, by linarith⟩
  have hec : 1-e ∈ Set.Icc (19/40 : ℝ) (21/40) := ⟨by linarith, by linarith⟩
  have hmc : 1-m ∈ Set.Icc (19/40 : ℝ) (21/40) := ⟨by linarith, by linarith⟩
  have h1 := mixed_centered_product_bounds e m he' hm'
  have h2 := mixed_centered_product_bounds e (1-m) he' hmc
  have h3 := mixed_centered_product_bounds (1-e) m hec hm'
  have h4 := mixed_centered_product_bounds (1-e) (1-m) hec hmc
  cases a <;> cases y <;> simp only [tableCell, Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

/-- [The complete substituted mixed cells satisfy the support density bounds.](goal) Under [the stated assumptions](hyp:hη,hζ,x). -/
-- @node: mixedCells_density_bounds
lemma mixedCells_density_bounds (b : Bool) (k : ℕ) (σ : Fin (k+1) → Bool)
    (η ζ : ℝ) (hη : |η| ≤ 1/100) (hζ : |ζ| ≤ 1/100)
    (a y : Bool) (x : Covariate) :
    (1/2 : ℝ) ≤ 4*mixedCells b k σ η ζ a y x ∧
      4*mixedCells b k σ η ζ a y x ≤ 2 := by
  obtain ⟨he, hm⟩ := mixed_margin_bounds b k σ η ζ x hη hζ
  have ht : |32*η*ζ| ≤ 1/8 := by
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 32)]
    have h := mul_le_mul hη hζ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/100)
    nlinarith
  unfold mixedCells
  dsimp only
  apply mixed_table_density_bounds _ _ _ he hm
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at he ⊢
  · norm_num
  · exact (covarianceBranch_local_bounds _ _ _ ht (by linarith) (by linarith)).2.2

end CausalSmith.Stat.LogoddsLowsmoothFrontier
