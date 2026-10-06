module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.TMatchedCurveFrontier

/-! Parametric fixed-alphabet specialization and linear budget curves. -/

public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open scoped BigOperators

-- @node: poCellMass_nonneg_budget
/-- The po cell mass nonneg budget result. It proves [the stated conclusion](goal). -/
lemma poCellMass_nonneg_budget {d : ℕ} (Q : PotentialLaw d) (j : Fin d) :
    0 ≤ poCellMass Q j := by
  unfold poCellMass CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

-- @node: poCellMass_sum_budget
/-- The po cell mass sum budget result. It proves [the stated conclusion](goal). -/
lemma poCellMass_sum_budget {d : ℕ} (Q : PotentialLaw d) :
    ∑ j : Fin d, poCellMass Q j = 1 := by
  calc
    _ = ∑ z : FullObs d, (Q.pmf z).toReal := by
      simp [poCellMass, PotentialLaw.pmf,
        CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass,
        CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fullMass,
        Fintype.sum_prod_type]
    _ = 1 := by
      simpa using (PMF.integral_eq_sum Q.pmf (fun _ : FullObs d => (1 : ℝ))).symm

-- @node: constant_effect_budget_value
/-- The constant effect budget value result. Under [the hcpos premise](hyp:hcpos), [the hc premise](hyp:hc), [the hb premise](hyp:hb), It proves [the stated conclusion](goal). -/
lemma constant_effect_budget_value {d : ℕ} (Q : PotentialLaw d) (c b : ℝ)
    (hcpos : 0 < c) (hc : ∀ j, 0 < poCellMass Q j → effect Q j = c)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    budgetValue Q b = controlValue Q + c * b := by
  have hw (j : Fin d) : 0 ≤ poCellMass Q j := poCellMass_nonneg_budget Q j
  have hsum : ∑ j, poCellMass Q j = 1 := poCellMass_sum_budget Q
  have hcell (j : Fin d) (t : ℝ) :
      poCellMass Q j * t * effect Q j = c * (poCellMass Q j * t) := by
    by_cases hp : poCellMass Q j = 0
    · simp [hp]
    · have hpos : 0 < poCellMass Q j := lt_of_le_of_ne (hw j) (Ne.symm hp)
      rw [hc j hpos]
      ring
  have hgain (pi : Fin d → ℝ) :
      (∑ j, poCellMass Q j * pi j * effect Q j) =
        c * ∑ j, poCellMass Q j * pi j := by
    simp_rw [hcell]
    rw [Finset.mul_sum]
  let pi : Fin d → ℝ := fun _ => b
  have hpi : pi ∈ budgetPolicyClass Q ⟨b, hb⟩ := by
    constructor
    · intro j
      exact hb
    · change ∑ j, poCellMass Q j * pi j ≤ b
      simp only [pi]
      rw [← Finset.sum_mul, hsum]
      simp
  have hupper (rho : Fin d → ℝ) (hrho : rho ∈ budgetPolicyClass Q ⟨b, hb⟩) :
      ∑ j, poCellMass Q j * rho j * effect Q j ≤ c * b := by
    rw [hgain]
    exact mul_le_mul_of_nonneg_left hrho.2 (le_of_lt hcpos)
  have hhit : ∑ j, poCellMass Q j * pi j * effect Q j = c * b := by
    rw [hgain]
    simp only [pi]
    rw [← Finset.sum_mul, hsum]
    ring
  have hsup : sSup ((fun rho : Fin d → ℝ =>
      ∑ j, poCellMass Q j * rho j * effect Q j) ''
        budgetPolicyClass Q ⟨b, hb⟩) = c * b := by
    apply le_antisymm
    · apply csSup_le
      · exact ⟨_, ⟨pi, hpi, rfl⟩⟩
      · rintro x ⟨rho, hrho, rfl⟩
        exact hupper rho hrho
    · rw [← hhit]
      exact le_csSup (by
        refine ⟨c * b, ?_⟩
        rintro x ⟨rho, hrho, rfl⟩
        exact hupper rho hrho) ⟨pi, hpi, rfl⟩
  simp only [budgetValue, dif_pos hb]
  exact congrArg (controlValue Q + ·) hsup

-- @node: prop:fixed-alphabet-reduction
/-- The fixed alphabet reduction result. Under [the he premise](hyp:he), [the he' premise](hyp:he'), [the hd premise](hyp:hd), It proves [the stated conclusion](goal). -/
theorem fixed_alphabet_reduction (epsilon : ℝ) (d : ℕ)
    (he : 0 < epsilon) (he' : epsilon < 1 / 2) (hd : 2 ≤ d)
    (_of_gate : JHWKnownQL1LowerRegime) :
    (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ n : ℕ, 1 ≤ n → ∀ b0 ∈ Set.Icc (0 : ℝ) (1 / 2),
        c / n ≤ curveMinimaxRisk n d epsilon b0 ∧
          curveMinimaxRisk n d epsilon b0 ≤ C / n) ∧
    (∀ Q : PotentialLaw d, CausalModelClass epsilon Q →
      ∀ c : ℝ, 0 < c →
        (∀ j, 0 < poCellMass Q j → effect Q j = c) →
        ∀ b0 ∈ Set.Icc (0 : ℝ) (1 / 2),
          ∀ b ∈ Set.Icc b0 (1 - b0),
            budgetValue Q b = controlValue Q + c * b) := by
  have hdreal : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hdpos : (0 : ℝ) < d := by linarith
  have hlog : logAlphabet d = 1 + Real.log d := by
    unfold logAlphabet
    rw [Real.log_mul (by positivity : Real.exp 1 ≠ 0) (by positivity : (d : ℝ) ≠ 0)]
    simp
  have hlogpos : 0 < logAlphabet d := by
    rw [hlog]
    have := Real.log_pos hdreal
    linarith
  have hlogle : logAlphabet d ≤ d := by
    rw [hlog]
    have := Real.log_le_sub_one_of_pos hdpos
    linarith
  let alpha : ℝ := d / logAlphabet d
  have halpha : 1 ≤ alpha := (le_div_iff₀ hlogpos).2 (by simpa using hlogle)
  have hrate (n : ℕ) (hn : 1 ≤ n) :
      1 / (n : ℝ) ≤ curveRate n d ∧ curveRate n d ≤ alpha / n := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hratio : (d : ℝ) / (n * logAlphabet d) = alpha / n := by
      dsimp [alpha]
      field_simp
    rw [curveRate, hratio]
    constructor
    · apply le_min
      · exact (div_le_iff₀ hnpos).2 (by nlinarith)
      · exact div_le_div_of_nonneg_right halpha (le_of_lt hnpos)
    · exact min_le_right _ _
  constructor
  · obtain ⟨c, C, hcpos, hcC, hfront⟩ :=
      matched_curve_frontier epsilon he he' _of_gate
    refine ⟨c, C * alpha, hcpos, ?_, ?_⟩
    · have hCpos : 0 ≤ C := by linarith
      nlinarith
    · intro n hn b0 hb0
      have hF := (hfront n d b0 hn hd hb0).1
      have hr := hrate n hn
      have hCpos : 0 ≤ C := by linarith
      constructor
      · calc
          c / n = c * (1 / n) := by ring
          _ ≤ c * curveRate n d := mul_le_mul_of_nonneg_left hr.1 (le_of_lt hcpos)
          _ ≤ curveMinimaxRisk n d epsilon b0 := hF.1
      · calc
          curveMinimaxRisk n d epsilon b0 ≤ C * curveRate n d := hF.2
          _ ≤ C * (alpha / n) := mul_le_mul_of_nonneg_left hr.2 hCpos
          _ = (C * alpha) / n := by ring
  · intro Q _hQ c hcpos hc b0 hb0 b hb
    have hbi : b ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact le_trans hb0.1 hb.1
      · have := hb0.1
        linarith [hb.2]
    exact constant_effect_budget_value Q c b hcpos hc hbi

end CausalSmith.Stat.DiscreteBudgetvalueCurve
