module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.LowerDirectionDefs
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Elementary analytic facts for the two lower-bound directions. -/

public section

open MeasureTheory Set Filter

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

lemma endpointDirection_continuous (c : ClassConstants) (cut : CutoffData c)
    (u h : ℝ) (_hh : h ≠ 0) : Continuous (endpointDirection c cut u h) := by
  unfold endpointDirection
  exact continuous_const.mul (cut.bump_smooth.continuous.comp
    ((continuous_const.sub continuous_id).div_const h))

lemma endpointDirection_measurable (c : ClassConstants) (cut : CutoffData c)
    (u h : ℝ) (hh : h ≠ 0) : Measurable (endpointDirection c cut u h) :=
  (endpointDirection_continuous c cut u h hh).measurable

lemma recurrenceIntensity_isFinite_of_continuous (f : ℝ → ℝ)
    (hf : Continuous f) :
    IsFiniteMeasure ((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
      (fun t => ENNReal.ofReal (f t))) := by
  apply isFiniteMeasure_withDensity_ofReal
  exact ((hf.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self).2

lemma endpointDirection_nonneg (c : ClassConstants) (cut : CutoffData c)
    {u h t : ℝ} (hu : 0 ≤ u) (hh : 0 ≤ h) :
    0 ≤ endpointDirection c cut u h t := by
  unfold endpointDirection
  exact mul_nonneg (mul_nonneg hu (Real.rpow_nonneg hh c.beta))
    (cut.bump_nonneg _)

lemma endpointDirection_eq_zero_of_not_mem (c : ClassConstants) (cut : CutoffData c)
    {u h t : ℝ} (ht : (1 - t) / h ∉ Set.Ioo (0 : ℝ) 1) :
    endpointDirection c cut u h t = 0 := by
  have hb : cut.bump ((1 - t) / h) = 0 := by
    by_contra hn
    exact ht (cut.bump_support _ hn)
  simp [endpointDirection, hb]

lemma add_direction_mem_band {lambdaMin lambda0 lambdaMax : ℝ}
    {d : ℝ → ℝ} {t : ℝ}
    (hlo : |d t| ≤ lambda0 - lambdaMin)
    (hhi : |d t| ≤ lambdaMax - lambda0) :
    lambdaMin ≤ lambda0 + d t ∧ lambda0 + d t ≤ lambdaMax := by
  constructor
  · have := neg_le_of_abs_le hlo
    linarith
  · have := le_of_abs_le hhi
    linarith

lemma HolderSeminormLe.const_add {k : ℕ} {γ L lambda0 : ℝ} {d : ℝ → ℝ}
    (hd : HolderSeminormLe k γ L d) :
    HolderSeminormLe k γ L (fun t => lambda0 + d t) := by
  constructor
  · exact contDiffOn_const.add hd.1
  · intro x hx y hy
    have hud : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) :=
      uniqueDiffOn_Icc (by norm_num)
    rw [iteratedDerivWithin_fun_add hx hud contDiffWithinAt_const (hd.1 x hx),
      iteratedDerivWithin_fun_add hy hud contDiffWithinAt_const (hd.1 y hy)]
    cases k <;> simpa [iteratedDerivWithin_const] using hd.2 x hx y hy

lemma endpointDirection_add_mem_band (c : ClassConstants) (cut : CutoffData c)
    {lambdaMin lambda0 lambdaMax u h t : ℝ}
    (hlo : |endpointDirection c cut u h t| ≤ lambda0 - lambdaMin)
    (hhi : |endpointDirection c cut u h t| ≤ lambdaMax - lambda0) :
    lambdaMin ≤ lambda0 + endpointDirection c cut u h t ∧
      lambda0 + endpointDirection c cut u h t ≤ lambdaMax :=
  add_direction_mem_band hlo hhi

lemma criticalDirection_at_one (c : ClassConstants) (cut : CutoffData c)
    (u : ℝ) (n : ℕ) : criticalDirection c cut u n 1 = 0 := by
  simp [criticalDirection]

lemma criticalDirection_eq_zero_of_scaled_le_one
    (c : ClassConstants) (cut : CutoffData c) {u : ℝ} {n : ℕ} {t : ℝ}
    (hx : 1 - t ≠ 0)
    (hx0 : 0 ≤ (1 - t) / criticalBandwidth c n)
    (hx1 : (1 - t) / criticalBandwidth c n ≤ 1) :
    criticalDirection c cut u n t = 0 := by
  rw [criticalDirection]
  simp only [hx, ↓reduceIte]
  rw [cut.chi_zero _ ⟨hx0, hx1⟩]
  ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
