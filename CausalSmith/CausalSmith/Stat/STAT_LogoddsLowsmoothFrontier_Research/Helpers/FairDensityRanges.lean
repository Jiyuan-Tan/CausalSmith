module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairRootSelection

/-! # Fair four-cell density bounds

The literal root bracket and the explicit effect bounds control every fair cell
on a fixed signed amplitude neighborhood, without a smoothness assumption.
-/
public section
noncomputable section
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Endpoint signs have unit magnitude. [the stated conclusion](goal) holds. -/
-- @node: endpointSign_abs
lemma endpointSign_abs (k : ℕ) (σ : Fin (k + 1) → Bool) (j : ℕ) :
    |endpointSign k σ j| = 1 := by
  unfold endpointSign signValue
  split <;> norm_num

/-- The shared endpoint sign field is bounded on every covariate. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: signFieldZ_abs_le_two
lemma signFieldZ_abs_le_two (k : ℕ) (σ : Fin (k + 1) → Bool) (x : Covariate) :
    |signFieldZ k σ x| ≤ 2 := by
  unfold signFieldZ
  calc
    _ ≤ |endpointSign k σ (cellIndex k x) * Real.cos (Real.pi * cellCoord k x / 2)| +
        |endpointSign k σ (cellIndex k x + 1) * Real.sin (Real.pi * cellCoord k x / 2)| := abs_add_le _ _
    _ ≤ 2 := by
      simp only [abs_mul, endpointSign_abs, one_mul]
      linarith [Real.abs_cos_le_one (Real.pi * cellCoord k x / 2),
        Real.abs_sin_le_one (Real.pi * cellCoord k x / 2)]

/-- [A small nonnegative shift preserves a fixed interior risk interval. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:ht,hξ). -/
-- @node: riskShift_quarter_bounds
lemma riskShift_quarter_bounds (t ξ : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hξ : ξ ∈ Set.Icc (1/4 : ℝ) (3/5)) :
    riskShift t ξ ∈ Set.Icc (1/4 : ℝ) (3/4) := by
  obtain ⟨hdlo, hdhi⟩ := fair_exp_increment_bounds t ht
  have hd : 0 ≤ Real.exp t - 1 := by linarith [ht.1]
  have hd' : Real.exp t - 1 ≤ 1/3 := by linarith [ht.2]
  obtain ⟨hξlo, hξhi⟩ := hξ
  have hden : 0 < 1 + (Real.exp t - 1)*ξ := by positivity
  unfold riskShift
  constructor
  · apply (le_div_iff₀ hden).mpr
    nlinarith [mul_nonneg hd (show 0 ≤ ξ - 1/4 by linarith)]
  · apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg (show 0 ≤ 1/3 - (Real.exp t - 1) by linarith)
      (show 0 ≤ ξ by linarith)]

/-- The root bracket and small signed perturbation keep the fair control risk interior. Under the stated assumptions. [The stated hypotheses](hyp:hδ) hold, and [the stated conclusion follows](goal). -/
-- @node: fair_control_risk_bounds
lemma fair_control_risk_bounds (b : Bool) (k : ℕ) (σ : Fin (k + 1) → Bool)
    (t δ : ℝ) (x : Covariate) (hδ : |δ| ≤ 1/100) :
    (if b then fairRoot t δ (cellCoord k x) + δ*signFieldZ k σ x
      else fairRoot t δ (cellCoord k x)) ∈ Set.Icc (1/4 : ℝ) (3/5) := by
  have hp := fairRoot_mem_bracket t δ (cellCoord k x)
  have hz := signFieldZ_abs_le_two k σ x
  have hprod : |δ*signFieldZ k σ x| ≤ 1/50 := by
    rw [abs_mul]
    calc
      _ ≤ (1/100 : ℝ)*2 := mul_le_mul hδ hz (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  obtain ⟨hlo, hhi⟩ := abs_le.mp hprod
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> linarith [hp.1, hp.2]

/-- [All four literal fair cells have the required common density floor and ceiling.](goal) Under [the stated assumptions](hyp:hδ,x). Under [the stated assumptions](hyp:ht). -/
-- @node: fairCells_density_bounds
lemma fairCells_density_bounds (b : Bool) (k : ℕ) (σ : Fin (k + 1) → Bool)
    (t δ : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/4)) (hδ : |δ| ≤ 1/100)
    (a y : Bool) (x : Covariate) :
    (1/2 : ℝ) ≤ 4*fairCells b k σ t δ a y x ∧
      4*fairCells b k σ t δ a y x ≤ 2 := by
  have hμ := fair_control_risk_bounds b k σ t δ x hδ
  have hT := comparatorEffect_range_bounds t δ ht hδ
  have heffect : (if b then t else comparatorEffect t δ) ∈ Set.Icc (0 : ℝ) (1/4) := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · constructor <;> linarith [ht.1, ht.2, hT.1, hT.2]
    · exact ht
  have hshift := riskShift_quarter_bounds _ _ heffect hμ
  unfold fairCells
  cases a <;> cases y <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> linarith [hμ.1, hμ.2, hshift.1, hshift.2]

/-- [Totalizing a bounded table preserves its density bounds, including the fallback table.](goal) Under [the stated assumptions](hyp:x). Under [the stated assumptions](hyp:hp). -/
-- @node: totalCellLaw_density_bounds
lemma totalCellLaw_density_bounds (p : Bool → Bool → Covariate → ℝ)
    (hp : ∀ a y x, (1/2 : ℝ) ≤ 4*p a y x ∧ 4*p a y x ≤ 2)
    (a y : Bool) (x : Covariate) :
    (1/2 : ℝ) ≤ 4*(totalCellLaw p).cells a y x ∧
      4*(totalCellLaw p).cells a y x ≤ 2 := by
  classical
  unfold totalCellLaw
  split
  · exact hp a y x
  · norm_num [lawFromCells]

end CausalSmith.Stat.LogoddsLowsmoothFrontier
