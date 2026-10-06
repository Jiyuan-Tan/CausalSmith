module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.TCapacityActiveLower
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.TCurveUpper

/-! The matched all-procedure budget-curve frontier. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory
open scoped BigOperators

-- @node: curve_coordinate_in_budget_interval
/-- The curve coordinate in budget interval result. Under [the hb0 premise](hyp:hb0), It proves [the stated conclusion](goal). -/
lemma curve_coordinate_in_budget_interval (b0 : ℝ)
    (hb0 : b0 ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    (1 / 2 : ℝ) ∈ Set.Icc b0 (1 - b0) := by
  constructor <;> linarith [hb0.2]

-- @node: curve_loss_pointwise_bound
/-- The curve loss pointwise bound result. Under [the hb0 premise](hyp:hb0), [the hB premise](hyp:hB), It proves [the stated conclusion](goal). -/
lemma curve_loss_pointwise_bound {n d : ℕ} {epsilon b0 : ℝ}
    (hb0 : b0 ∈ Set.Icc (0 : ℝ) (1 / 2))
    (est : CurveEstimator n d b0) (Q : ModelLaw d epsilon)
    (B : ℝ) (hB : ∀ z b, |est.1 z b| ≤ B)
    (z : Fin n → Obs d) (b : Set.Icc b0 (1 - b0)) :
    (est.1 z b - budgetValue Q.1 b.1) ^ 2 ≤ (B + 1) ^ 2 := by
  have hbi : b.1 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact le_trans hb0.1 b.2.1
    · linarith [b.2.2, hb0.1]
  obtain ⟨hv0, hv1⟩ := budgetValue_unit_interval Q.1 b.1 hbi
  obtain ⟨he0, he1⟩ := abs_le.mp (hB z b)
  apply sq_le_sq'
  · linarith
  · linarith

-- @node: curve_loss_sup_bound
/-- The curve loss sup bound result. Under [the hb0 premise](hyp:hb0), [the hB premise](hyp:hB), It proves [the stated conclusion](goal). -/
lemma curve_loss_sup_bound {n d : ℕ} {epsilon b0 : ℝ}
    (hb0 : b0 ∈ Set.Icc (0 : ℝ) (1 / 2))
    (est : CurveEstimator n d b0) (Q : ModelLaw d epsilon)
    (B : ℝ) (hB : ∀ z b, |est.1 z b| ≤ B)
    (z : Fin n → Obs d) :
    (⨆ b : Set.Icc b0 (1 - b0),
      (est.1 z b - budgetValue Q.1 b.1) ^ 2) ≤ (B + 1) ^ 2 := by
  letI : Nonempty (Set.Icc b0 (1 - b0)) :=
    ⟨⟨1 / 2, curve_coordinate_in_budget_interval b0 hb0⟩⟩
  exact ciSup_le fun b => curve_loss_pointwise_bound hb0 est Q B hB z b

-- @node: curve_risk_bddAbove
/-- The curve risk bdd above result. Under [the hb0 premise](hyp:hb0), It proves [the stated conclusion](goal). -/
lemma curve_risk_bddAbove {n d : ℕ} {epsilon b0 : ℝ}
    (hb0 : b0 ∈ Set.Icc (0 : ℝ) (1 / 2))
    (est : CurveEstimator n d b0) :
    BddAbove (Set.range (curveRisk n (d := d) (epsilon := epsilon) b0 est)) := by
  obtain ⟨B, hB⟩ := est.2.2.2
  refine ⟨(B + 1) ^ 2, ?_⟩
  rintro x ⟨Q, rfl⟩
  unfold curveRisk
  calc
    (∫ z, (⨆ b : Set.Icc b0 (1 - b0),
      (est.1 z b - budgetValue Q.1 b.1) ^ 2) ∂productLaw (observedMarginal Q.1) n)
        ≤ ∫ _z, (B + 1) ^ 2 ∂productLaw (observedMarginal Q.1) n := by
          apply integral_mono (Integrable.of_finite) (integrable_const _)
          intro z
          exact curve_loss_sup_bound hb0 est Q B hB z
    _ = (B + 1) ^ 2 := by simp

-- @node: curve_risk_nonneg
/-- The curve risk nonneg result. Under [the hb0 premise](hyp:hb0), It proves [the stated conclusion](goal). -/
lemma curve_risk_nonneg {n d : ℕ} {epsilon b0 : ℝ}
    (hb0 : b0 ∈ Set.Icc (0 : ℝ) (1 / 2))
    (est : CurveEstimator n d b0) (Q : ModelLaw d epsilon) :
    0 ≤ curveRisk n b0 est Q := by
  obtain ⟨B, hB⟩ := est.2.2.2
  unfold curveRisk
  apply integral_nonneg
  intro z
  have hbdd : BddAbove (Set.range (fun b : Set.Icc b0 (1 - b0) =>
      (est.1 z b - budgetValue Q.1 b.1) ^ 2)) := by
    exact ⟨(B + 1) ^ 2, by
      rintro x ⟨b, rfl⟩
      exact curve_loss_pointwise_bound hb0 est Q B hB z b⟩
  calc
    0 ≤ (est.1 z ⟨1 / 2, curve_coordinate_in_budget_interval b0 hb0⟩ -
      budgetValue Q.1 (1 / 2)) ^ 2 := sq_nonneg _
    _ ≤ ⨆ b : Set.Icc b0 (1 - b0),
      (est.1 z b - budgetValue Q.1 b.1) ^ 2 :=
        le_ciSup hbdd ⟨1 / 2, curve_coordinate_in_budget_interval b0 hb0⟩

-- @node: scalar_coordinate_of_curve_estimator
/-- For [n](hyp:n), [b0](hyp:b0), [hb0](hyp:hb0), [est](hyp:est), the scalar coordinate of curve estimator definition specifies [the stated object](goal). -/
@[no_expose]
noncomputable def scalar_coordinate_of_curve_estimator {n d : ℕ} {b0 : ℝ}
    (hb0 : b0 ∈ Set.Icc (0 : ℝ) (1 / 2))
    (est : CurveEstimator n d b0) : ScalarEstimator n d :=
  ⟨fun z => est.1 z ⟨1 / 2, curve_coordinate_in_budget_interval b0 hb0⟩,
    by fun_prop⟩

-- @node: scalar_coordinate_risk_le_curve_risk
/-- The scalar coordinate risk le curve risk result. Under [the hb0 premise](hyp:hb0), It proves [the stated conclusion](goal). -/
lemma scalar_coordinate_risk_le_curve_risk {n d : ℕ} {epsilon b0 : ℝ}
    (hb0 : b0 ∈ Set.Icc (0 : ℝ) (1 / 2))
    (est : CurveEstimator n d b0) (Q : ModelLaw d epsilon) :
    Causalean.Stat.sqRisk (productLaw (observedMarginal Q.1) n)
      (scalar_coordinate_of_curve_estimator hb0 est).1 (budgetValue Q.1 (1 / 2)) ≤
      curveRisk n b0 est Q := by
  obtain ⟨B, hB⟩ := est.2.2.2
  unfold Causalean.Stat.sqRisk curveRisk
  apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro z
  have hbdd : BddAbove (Set.range (fun b : Set.Icc b0 (1 - b0) =>
      (est.1 z b - budgetValue Q.1 b.1) ^ 2)) := by
    exact ⟨(B + 1) ^ 2, by
      rintro x ⟨b, rfl⟩
      exact curve_loss_pointwise_bound hb0 est Q B hB z b⟩
  exact le_ciSup hbdd ⟨1 / 2, curve_coordinate_in_budget_interval b0 hb0⟩

-- @node: curveRate_nonneg
/-- The curve rate nonneg result. Under [the hn premise](hyp:hn), [the hd premise](hyp:hd), It proves [the stated conclusion](goal). -/
lemma curveRate_nonneg (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d) :
    0 ≤ curveRate n d := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdgt : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hlog : 0 < logAlphabet d := by
    unfold logAlphabet
    exact Real.log_pos (by
      have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      nlinarith)
  unfold curveRate
  apply le_min
  · norm_num
  · positivity

-- @node: full_budget_cell_mass_nonneg
/-- The full budget cell mass nonneg result. It proves [the stated conclusion](goal). -/
lemma full_budget_cell_mass_nonneg {d : ℕ} (Q : PotentialLaw d) (j : Fin d) :
    0 ≤ poCellMass Q j := by
  unfold poCellMass CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

-- @node: full_budget_cell_mass_sum
/-- The full budget cell mass sum result. It proves [the stated conclusion](goal). -/
lemma full_budget_cell_mass_sum {d : ℕ} (Q : PotentialLaw d) :
    ∑ j : Fin d, poCellMass Q j = 1 := by
  calc
    _ = ∑ z : FullObs d, (Q.pmf z).toReal := by
      simp [poCellMass, PotentialLaw.pmf,
        CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass,
        CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fullMass,
        Fintype.sum_prod_type]
    _ = 1 := by
      simpa using (PMF.integral_eq_sum Q.pmf (fun _ : FullObs d => (1 : ℝ))).symm

-- @node: full_budget_value
/-- The full budget value result. It proves [the stated conclusion](goal). -/
lemma full_budget_value {d : ℕ} (Q : PotentialLaw d) :
    budgetValue Q 1 = controlValue Q +
      ∑ j : Fin d, poCellMass Q j * max (effect Q j) 0 := by
  let pi : Fin d → ℝ := fun j => if 0 ≤ effect Q j then 1 else 0
  have hpi : pi ∈ budgetPolicyClass Q ⟨1, by norm_num⟩ := by
    constructor
    · intro j
      dsimp [pi]
      split_ifs <;> norm_num
    · change ∑ j, poCellMass Q j * pi j ≤ (1 : ℝ)
      calc
        _ ≤ ∑ j : Fin d, poCellMass Q j := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_of_le_one_right (full_budget_cell_mass_nonneg Q j)
          dsimp [pi]
          split_ifs <;> norm_num
        _ = 1 := by
          exact full_budget_cell_mass_sum Q
  have hpoint (j : Fin d) :
      poCellMass Q j * pi j * effect Q j =
        poCellMass Q j * max (effect Q j) 0 := by
    dsimp [pi]
    by_cases h : 0 ≤ effect Q j
    · simp [h]
    · have hle : effect Q j ≤ 0 := le_of_lt (lt_of_not_ge h)
      simp [h, max_eq_right hle]
  have hupper (rho : Fin d → ℝ) (hrho : rho ∈ budgetPolicyClass Q ⟨1, by norm_num⟩) :
      (∑ j, poCellMass Q j * rho j * effect Q j) ≤
        ∑ j, poCellMass Q j * max (effect Q j) 0 := by
    apply Finset.sum_le_sum
    intro j _
    have hp := full_budget_cell_mass_nonneg Q j
    have hlo := (hrho.1 j).1
    have hhi := (hrho.1 j).2
    by_cases h : 0 ≤ effect Q j
    · rw [max_eq_left h]
      calc
        poCellMass Q j * rho j * effect Q j =
            poCellMass Q j * (rho j * effect Q j) := by ring
        _ ≤ poCellMass Q j * (1 * effect Q j) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hhi h) hp
        _ = poCellMass Q j * effect Q j := by ring
    · have hle : effect Q j ≤ 0 := le_of_lt (lt_of_not_ge h)
      rw [max_eq_right hle, mul_zero]
      have hneg : rho j * effect Q j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlo hle
      calc
        poCellMass Q j * rho j * effect Q j =
            poCellMass Q j * (rho j * effect Q j) := by ring
        _ ≤ poCellMass Q j * 0 := mul_le_mul_of_nonneg_left hneg hp
        _ = 0 := mul_zero _
  have hhit : (∑ j, poCellMass Q j * pi j * effect Q j) =
      ∑ j, poCellMass Q j * max (effect Q j) 0 := by
    apply Finset.sum_congr rfl
    intro j _
    exact hpoint j
  have hsup : sSup ((fun rho : Fin d → ℝ =>
      ∑ j, poCellMass Q j * rho j * effect Q j) ''
        budgetPolicyClass Q ⟨1, by norm_num⟩) =
      ∑ j, poCellMass Q j * max (effect Q j) 0 := by
    apply le_antisymm
    · apply csSup_le
      · exact ⟨_, ⟨pi, hpi, rfl⟩⟩
      · rintro x ⟨rho, hrho, rfl⟩
        exact hupper rho hrho
    · rw [← hhit]
      exact le_csSup (by
        refine ⟨∑ j : Fin d, poCellMass Q j * max (effect Q j) 0, ?_⟩
        rintro x ⟨rho, hrho, rfl⟩
        exact hupper rho hrho) ⟨pi, hpi, rfl⟩
  simp only [budgetValue, dif_pos (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)]
  exact congrArg (controlValue Q + ·) hsup

-- @node: thm:matched-curve-frontier
/-- The matched curve frontier result. Under [the he premise](hyp:he), [the he' premise](hyp:he'), It proves [the stated conclusion](goal). -/
theorem matched_curve_frontier (epsilon : ℝ)
    (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (_of_gate : JHWKnownQL1LowerRegime) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ n d : ℕ, ∀ b0 : ℝ,
        1 ≤ n → 2 ≤ d → b0 ∈ Set.Icc (0 : ℝ) (1 / 2) →
        (c * curveRate n d ≤ curveMinimaxRisk n d epsilon b0 ∧
         curveMinimaxRisk n d epsilon b0 ≤ C * curveRate n d) ∧
        (∀ T : ScalarEstimator n d, ∃ Q : PotentialLaw d,
          Q ∈ capacityHardClass d epsilon ∧
          (∀ j : Fin d, 0 < poCellMass Q j → 0 < effect Q j) ∧
          BindingHalfBudget Q ∧
          budgetValue Q 1 = 1 / 2 ∧
          c * curveRate n d ≤
            Causalean.Stat.sqRisk (productLaw (observedMarginal Q) n)
              T.1 (budgetValue Q (1 / 2))) ∧
        (b0 = 0 → ∀ Q : ModelLaw d epsilon,
          budgetValue Q.1 1 = controlValue Q.1 +
            ∑ j : Fin d, poCellMass Q.1 j * max (effect Q.1 j) 0) := by
  obtain ⟨c, hc, hlower⟩ := capacity_active_lower epsilon he he' _of_gate
  obtain ⟨C, hC, hupper⟩ := curve_upper epsilon he he'
  refine ⟨c, C + c, hc, by linarith, ?_⟩
  intro n d b0 hn hd hb0
  let mu : PotentialLaw d → Measure (Fin n → Obs d) :=
    fun Q => productLaw (observedMarginal Q) n
  have hmu : ∀ Q, IidSampling (observedMarginal Q) (mu Q) := by
    intro Q
    rfl
  have hrate := curveRate_nonneg n d hn hd
  have hmodel_nonempty : Nonempty (ModelLaw d epsilon) := by
    let T : ScalarEstimator n d := ⟨fun _ => 0, by fun_prop⟩
    obtain ⟨Q, hQ, _⟩ := hlower n d hn hd mu hmu T
    exact ⟨⟨Q, hQ.1⟩⟩
  letI : Nonempty (ModelLaw d epsilon) := hmodel_nonempty
  letI : Nonempty (CurveEstimator n d b0) :=
    ⟨jfCurveEstimator n d epsilon b0 hb0⟩
  have hminlower : c * curveRate n d ≤ curveMinimaxRisk n d epsilon b0 := by
    unfold curveMinimaxRisk
    apply Causalean.Stat.le_minimaxValue
    intro est
    obtain ⟨Q, hQ, hrisk⟩ :=
      hlower n d hn hd mu hmu (scalar_coordinate_of_curve_estimator hb0 est)
    let Qm : ModelLaw d epsilon := ⟨Q, hQ.1⟩
    calc
      c * curveRate n d ≤
          Causalean.Stat.sqRisk (mu Q)
            (scalar_coordinate_of_curve_estimator hb0 est).1
            (budgetValue Q (1 / 2)) := hrisk
      _ ≤ curveRisk n b0 est Qm :=
        scalar_coordinate_risk_le_curve_risk hb0 est Qm
      _ ≤ Causalean.Stat.worstCaseRiskReal
          (curveRisk n (d := d) (epsilon := epsilon) b0) est :=
        Causalean.Stat.le_worstCaseRisk (curve_risk_bddAbove hb0 est) Qm
  have hminupper : curveMinimaxRisk n d epsilon b0 ≤ C * curveRate n d := by
    unfold curveMinimaxRisk
    calc
      Causalean.Stat.minimaxValueReal
          (curveRisk n (d := d) (epsilon := epsilon) b0) ≤
          Causalean.Stat.worstCaseRiskReal
            (curveRisk n (d := d) (epsilon := epsilon) b0)
            (jfCurveEstimator n d epsilon b0 hb0) := by
        exact Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
          (fun est Q => curve_risk_nonneg hb0 est Q) _
      _ ≤ C * curveRate n d := by
        apply Causalean.Stat.worstCaseRisk_le
        intro Q
        have hup := hupper n d b0 hn hd hb0
          (fun Q : ModelLaw d epsilon => productLaw (observedMarginal Q.1) n)
          (by intro Q; rfl)
        have hmem :
            curveRisk n b0 (jfCurveEstimator n d epsilon b0 hb0) Q ≤
            sSup (Set.range (fun Q : ModelLaw d epsilon =>
              ∫ z, (⨆ b : Set.Icc b0 (1 - b0),
                (jfEstimator n d epsilon b0 z b - budgetValue Q.1 b.1) ^ 2)
                ∂productLaw (observedMarginal Q.1) n)) := by
          apply le_csSup
          · change BddAbove (Set.range (curveRisk n b0
              (jfCurveEstimator n d epsilon b0 hb0)))
            exact curve_risk_bddAbove hb0 (jfCurveEstimator n d epsilon b0 hb0)
          · exact ⟨Q, rfl⟩
        exact hmem.trans (by simpa [curveRate, curveRisk, jfCurveEstimator] using hup)
  refine ⟨⟨hminlower, ?_⟩, ?_, ?_⟩
  · calc
      curveMinimaxRisk n d epsilon b0 ≤ C * curveRate n d := hminupper
      _ ≤ (C + c) * curveRate n d := by nlinarith
  · intro T
    obtain ⟨Q, hQ, hrisk⟩ := hlower n d hn hd mu hmu T
    rcases hQ with ⟨hmodel, hvalue, heffect, hbinding⟩
    refine ⟨Q, ⟨hmodel, hvalue, heffect, hbinding⟩, ?_, hbinding,
      hvalue, hrisk⟩
    intro j hj
    have hlow := (heffect j hj).1
    linarith
  · intro _ Q
    exact full_budget_value Q.1

end CausalSmith.Stat.DiscreteBudgetvalueCurve
