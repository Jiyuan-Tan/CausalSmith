module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.TDualRepresentation
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.TwoSampleL1
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.PairedObservedAtom

/-! The positive-effect paired family and its exact fixed-sample reduction. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory
open scoped BigOperators

/-- The observed arm mass is the corresponding full-data treatment marginal. With [the specified inputs and conditions](hyp:d,Q,j,a), [the stated relationship holds](goal). -/
lemma observedMarginal_armMass_eq_poTreatmentAtom {d : ℕ} (Q : PotentialLaw d)
    (j : Fin d) (a : Bool) :
    armMass (observedMarginal Q) a j = poTreatmentAtom Q j a := by
  simp [CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.armMass,
    poTreatmentAtom,
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal_jointMass]

/-- Binding capacity with an attaining randomized policy. -/
def BindingHalfBudget {d : ℕ} (Q : PotentialLaw d) : Prop :=
  ∃ pi ∈ budgetPolicyClass Q ⟨1 / 2, by norm_num⟩,
    (∑ j, poCellMass Q j * pi j) = 1 / 2 ∧
      budgetValue Q (1 / 2) = controlValue Q +
        ∑ j, poCellMass Q j * pi j * effect Q j

/-- The two sampled simplex vectors give valid pair masses and contrasts. With [the specified inputs and conditions](hyp:k,R,S), [the stated relationship holds](goal). -/
-- @node: normalizedPairedParameters
lemma normalizedPairedParameters {k : ℕ} (R S : ProbabilitySimplex k) :
    ∃ r : ProbabilitySimplex k, ∃ theta : PairedContrasts k,
      (∀ i, r.1 i = (R.1 i + S.1 i) / 2) ∧
      (∀ i, theta.1 i =
        if R.1 i + S.1 i = 0 then 0
        else (R.1 i - S.1 i) / (8 * (R.1 i + S.1 i))) := by
  let r : ProbabilitySimplex k :=
    ⟨fun i => (R.1 i + S.1 i) / 2, by
      constructor
      · intro i
        exact div_nonneg (add_nonneg (R.2.1 i) (S.2.1 i)) (by norm_num)
      · simp only [← Finset.sum_div, Finset.sum_add_distrib, R.2.2, S.2.2]
        norm_num⟩
  let theta : PairedContrasts k :=
    ⟨fun i => if R.1 i + S.1 i = 0 then 0
       else (R.1 i - S.1 i) / (8 * (R.1 i + S.1 i)), by
      intro i
      have hR := R.2.1 i
      have hS := S.2.1 i
      by_cases h : R.1 i + S.1 i = 0
      · simp only [h, ↓reduceIte, Set.mem_Icc]
        constructor <;> norm_num
      · have hp : 0 < R.1 i + S.1 i := lt_of_le_of_ne (add_nonneg hR hS) (Ne.symm h)
        simp only [h, ↓reduceIte, Set.mem_Icc]
        constructor
        · apply (le_div_iff₀ (by positivity)).2
          nlinarith [hR, hS]
        · apply (div_le_iff₀ (by positivity)).2
          nlinarith [hR, hS]⟩
  exact ⟨r, theta, fun _ => rfl, fun _ => rfl⟩

/-- The normalized embedding converts the paired capacity term to L1 distance. With [the specified inputs and conditions](hyp:k,R,S,r,theta,hr,htheta), [the stated relationship holds](goal). -/
-- @node: normalizedPairedL1
lemma normalizedPairedL1 {k : ℕ} (R S r : ProbabilitySimplex k)
    (theta : PairedContrasts k)
    (hr : ∀ i, r.1 i = (R.1 i + S.1 i) / 2)
    (htheta : ∀ i, theta.1 i =
      if R.1 i + S.1 i = 0 then 0
      else (R.1 i - S.1 i) / (8 * (R.1 i + S.1 i))) :
    (∑ i, r.1 i * |theta.1 i|) = simplexL1 R S / 16 := by
  rw [simplexL1,
    Causalean.Stat.Minimax.Multinomial.TwoSampleL1.simplexL1,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  calc
    r.1 i * |theta.1 i| = |r.1 i * theta.1 i| := by
      rw [abs_mul, abs_of_nonneg (r.2.1 i)]
    _ = |R.1 i - S.1 i| / 16 := by
      rw [normalizedPairedMassContrast R S r theta hr htheta i,
        abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 16)]

/-- Occupied cells of a paired completion have the specified positive effects. With [the specified inputs and conditions](hyp:k,Q,r,theta,h,j,hj), [the stated relationship holds](goal). -/
-- @node: pairedCompletion_effect_bounds
lemma pairedCompletion_effect_bounds {k : ℕ} (Q : PotentialLaw (2 * k))
    (r : ProbabilitySimplex k) (theta : PairedContrasts k)
    (h : PairedCompletion Q r theta) (j : Fin (2 * k))
    (hj : 0 < poCellMass Q j) :
    effect Q j ∈ Set.Icc (1 / 8 : ℝ) (3 / 8) := by
  let pair := (finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j
  obtain ⟨_, _, h0, h1⟩ := h.2.2 j
  have hr0 : poRegression Q 0 j = 1 / 4 := by
    nlinarith
  have hr1 : poRegression Q 1 j =
      1 / 2 + (if pair.1 = 0 then 1 else -1) * theta.1 pair.2 := by
    dsimp [pair] at h1 ⊢
    nlinarith
  have ht := theta.2 pair.2
  simp only [Set.mem_Icc] at ht ⊢
  rw [effect, hr0, hr1]
  by_cases hs : pair.1 = 0
  · simp only [hs, ↓reduceIte]
    constructor <;> nlinarith [ht.1, ht.2]
  · simp only [hs, ↓reduceIte]
    constructor <;> nlinarith [ht.1, ht.2]

/-- The paired family has a fixed control-policy value. With [the specified inputs and conditions](hyp:k,Q,r,theta,h), [the stated relationship holds](goal). -/
-- @node: pairedCompletion_controlValue
lemma pairedCompletion_controlValue {k : ℕ} (Q : PotentialLaw (2 * k))
    (r : ProbabilitySimplex k) (theta : PairedContrasts k)
    (h : PairedCompletion Q r theta) : controlValue Q = 1 / 4 := by
  unfold controlValue
  calc
    (∑ j : Fin (2 * k), poCellMass Q j * poRegression Q 0 j) =
        ∑ j : Fin (2 * k), poCellMass Q j * (1 / 4 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j _
          exact (h.2.2 j).2.2.1
    _ = 1 / 4 := by
      rw [← Finset.sum_mul, poCellMass_sum_one_budget]
      ring

/-- Pairwise cancellation makes the value of treating every cell constant. With [the specified inputs and conditions](hyp:k,Q,r,theta,h), [the stated relationship holds](goal). -/
-- @node: pairedCompletion_fullTreatmentValue
lemma pairedCompletion_fullTreatmentValue {k : ℕ} (Q : PotentialLaw (2 * k))
    (r : ProbabilitySimplex k) (theta : PairedContrasts k)
    (h : PairedCompletion Q r theta) :
    (∑ j : Fin (2 * k), poCellMass Q j * poRegression Q 1 j) = 1 / 2 := by
  calc
    (∑ j : Fin (2 * k), poCellMass Q j * poRegression Q 1 j) =
        ∑ j : Fin (2 * k),
          r.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2 / 2 *
            (1 / 2 +
              (if ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).1 = 0
               then 1 else -1) *
                theta.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [(h.2.2 j).2.2.2, (h.2.2 j).1]
    _ = 1 / 2 := by
      rw [← Equiv.sum_comp (finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k))]
      simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
      simp [Fin.sum_univ_two, ← Finset.sum_add_distrib]
      calc
        (∑ x : Fin k,
            (r.1 x / 2 * (2⁻¹ + theta.1 x) +
              r.1 x / 2 * (2⁻¹ + -theta.1 x))) =
            (∑ x : Fin k, r.1 x) / 2 := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = 2⁻¹ := by rw [r.2.2]; norm_num

/-- Every paired completion obeys the causal model restrictions. With [the specified inputs and conditions](hyp:k,hk,epsilon,he,he',Q,r,theta,h), [the stated relationship holds](goal). -/
-- @node: pairedCompletion_modelClass
lemma pairedCompletion_modelClass {k : ℕ} (hk : 1 ≤ k) (epsilon : ℝ)
    (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (Q : PotentialLaw (2 * k)) (r : ProbabilitySimplex k)
    (theta : PairedContrasts k) (h : PairedCompletion Q r theta) :
    CausalModelClass epsilon Q := by
  apply CausalModelClass.mk
  · omega
  · exact ⟨he, he'⟩
  · exact Q.property.1
  · exact h.2.1
  intro j hj
  have hmass : cellMass (observedMarginal Q) j = poCellMass Q j :=
    observedMarginal_cellMass_eq_poCellMass Q j
  have harm : armMass (observedMarginal Q) true j = poTreatmentAtom Q j true :=
    observedMarginal_armMass_eq_poTreatmentAtom Q j true
  have hhalf := (h.2.2 j).2.1
  have hp : poCellMass Q j ≠ 0 := by rw [← hmass]; exact ne_of_gt hj
  have hprop : propensity (observedMarginal Q) j = 1 / 2 := by
    change CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.armMass
      (observedMarginal Q) true j /
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass
        (observedMarginal Q) j = 1 / 2
    change CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.armMass
      (observedMarginal Q) true j = poTreatmentAtom Q j true at harm
    change CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass
      (observedMarginal Q) j = poCellMass Q j at hmass
    rw [harm, hhalf, hmass]
    field_simp
  rw [hprop]
  constructor <;> linarith

/-! PRIOR PROOF (carry-over before the constrained-law carrier):
  refine ⟨by omega, ⟨he, he'⟩, h.1, h.2.1, ?_⟩
  intro j hj
  have hmass : cellMass (observedMarginal Q) j = poCellMass Q j :=
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal_cellMass Q j
  have harm : armMass (observedMarginal Q) true j = poTreatmentAtom Q j true := by
    simp [CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.armMass,
      poTreatmentAtom,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal_jointMass]
  have hhalf := (h.2.2 j).2.1
  have hp : poCellMass Q j ≠ 0 := by rw [← hmass]; exact ne_of_gt hj
  have hprop : propensity (observedMarginal Q) j = 1 / 2 := by
    change CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.armMass
      (observedMarginal Q) true j /
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass
        (observedMarginal Q) j = 1 / 2
    change CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.armMass
      (observedMarginal Q) true j = poTreatmentAtom Q j true at harm
    change CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass
      (observedMarginal Q) j = poCellMass Q j at hmass
    rw [harm, hhalf, hmass]
    field_simp
  rw [hprop]
  constructor <;> linarith

/-- Positive paired effects make treating every cell optimal at unit capacity. -/
-/

-- @node: pairedCompletion_budgetValue_one
/-! PRIOR PROOF (carry-over: auto; signature-unchanged `pairedCompletion_modelClass`). Stage 3: replace the
   placeholder above with this body, run `lean_diagnostic_messages`, patch failures only.
   := by  refine ⟨by omega, ⟨he, he'⟩, h.1, h.2.1, ?_⟩
  intro j hj
  have hmass : cellMass (observedMarginal Q) j = poCellMass Q j :=
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal_cellMass Q j
  have harm : armMass (observedMarginal Q) true j = poTreatmentAtom Q j true := by
    simp [CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.armMass,
      poTreatmentAtom,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal_jointMass]
  have hhalf := (h.2.2 j).2.1
  have hp : poCellMass Q j ≠ 0 := by rw [← hmass]; exact ne_of_gt hj
  have hprop : propensity (observedMarginal Q) j = 1 / 2 := by
    change CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.armMass
      (observedMarginal Q) true j /
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass
        (observedMarginal Q) j = 1 / 2
    change CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.armMass
      (observedMarginal Q) true j = poTreatmentAtom Q j true at harm
    change CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass
      (observedMarginal Q) j = poCellMass Q j at hmass
    rw [harm, hhalf, hmass]
    field_simp
  rw [hprop]
  constructor <;> linarith

-/
/-- The paired completion budget value one result. It proves [the stated conclusion](goal). -/
lemma pairedCompletion_budgetValue_one {k : ℕ} (Q : PotentialLaw (2 * k))
    (r : ProbabilitySimplex k) (theta : PairedContrasts k)
    (h : PairedCompletion Q r theta) : budgetValue Q 1 = 1 / 2 := by
  let gain : (Fin (2 * k) → ℝ) → ℝ :=
    fun pi => ∑ j, poCellMass Q j * pi j * effect Q j
  let feasible := budgetPolicyClass Q ⟨1, by norm_num⟩
  have hp : ∀ j : Fin (2 * k), 0 ≤ poCellMass Q j := by
    intro j
    unfold poCellMass
    unfold CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fullMass
    positivity
  have hfull : (fun _ : Fin (2 * k) => (1 : ℝ)) ∈ feasible := by
    constructor
    · intro j
      norm_num
    · simp only [mul_one]
      rw [poCellMass_sum_one_budget]
  have hupper (pi : Fin (2 * k) → ℝ) (hpi : pi ∈ feasible) :
      gain pi ≤ gain (fun _ => 1) := by
    dsimp [gain]
    apply Finset.sum_le_sum
    intro j _
    have hle := (hpi.1 j).2
    by_cases hj : 0 < poCellMass Q j
    · have heff : 0 ≤ effect Q j :=
        le_trans (by norm_num) (pairedCompletion_effect_bounds Q r theta h j hj).1
      have hprod : poCellMass Q j * pi j ≤ poCellMass Q j * 1 :=
        mul_le_mul_of_nonneg_left hle (hp j)
      exact mul_le_mul_of_nonneg_right hprod heff
    · have hz : poCellMass Q j = 0 := le_antisymm (le_of_not_gt hj) (hp j)
      simp [hz]
  have hsup : sSup (gain '' feasible) = gain (fun _ => 1) := by
    apply le_antisymm
    · apply csSup_le
      · exact ⟨_, ⟨_, hfull, rfl⟩⟩
      · rintro y ⟨pi, hpi, rfl⟩
        exact hupper pi hpi
    · exact le_csSup (⟨_, fun y hy => by
        rcases hy with ⟨pi, hpi, rfl⟩
        exact hupper pi hpi⟩ : BddAbove (gain '' feasible)) ⟨_, hfull, rfl⟩
  have hvalue : controlValue Q + gain (fun _ => 1) =
      ∑ j : Fin (2 * k), poCellMass Q j * poRegression Q 1 j := by
    unfold controlValue gain effect
    simp only [mul_one, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [budgetValue, dif_pos (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)]
  change controlValue Q + sSup (gain '' feasible) = 1 / 2
  rw [hsup, hvalue]
  exact pairedCompletion_fullTreatmentValue Q r theta h

/-- Select exactly the better member of each cell pair, including at ties. -/
-- @node: pairedSignPolicy
noncomputable def pairedSignPolicy {k : ℕ} (theta : PairedContrasts k) (j : Fin (2 * k)) : ℝ :=
  let pair := (finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j
  if 0 ≤ theta.1 pair.2 then
    if pair.1 = 0 then 1 else 0
  else if pair.1 = 0 then 0 else 1

/-- The sign-selecting policy treats exactly half the population. With [the specified inputs and conditions](hyp:k,Q,r,theta,h), [the stated relationship holds](goal). -/
-- @node: pairedSignPolicy_budget
lemma pairedSignPolicy_budget {k : ℕ} (Q : PotentialLaw (2 * k))
    (r : ProbabilitySimplex k) (theta : PairedContrasts k)
    (h : PairedCompletion Q r theta) :
    pairedSignPolicy theta ∈ budgetPolicyClass Q ⟨1 / 2, by norm_num⟩ ∧
      (∑ j, poCellMass Q j * pairedSignPolicy theta j) = 1 / 2 := by
  have hbox : ∀ j, pairedSignPolicy theta j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j
    simp only [pairedSignPolicy]
    split_ifs <;> norm_num
  have hmass : (∑ j, poCellMass Q j * pairedSignPolicy theta j) = 1 / 2 := by
    calc
      (∑ j, poCellMass Q j * pairedSignPolicy theta j) =
          ∑ j : Fin (2 * k),
            r.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2 / 2 *
              pairedSignPolicy theta j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [(h.2.2 j).1]
      _ = 1 / 2 := by
        rw [← Equiv.sum_comp (finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k))]
        simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
        simp only [Fin.sum_univ_two, pairedSignPolicy, Equiv.symm_apply_apply,
          Fin.isValue, ↓reduceIte, one_ne_zero]
        simp only [← Finset.sum_add_distrib]
        calc
          (∑ i : Fin k,
              (r.1 i / 2 * (if 0 ≤ theta.1 i then 1 else 0) +
                r.1 i / 2 * (if 0 ≤ theta.1 i then 0 else 1))) =
              ∑ i : Fin k, r.1 i / 2 := by
                apply Finset.sum_congr rfl
                intro i _
                split_ifs <;> ring
          _ = 1 / 2 := by rw [← Finset.sum_div, r.2.2]
  exact ⟨⟨hbox, hmass.le⟩, hmass⟩

/-- The sign-selecting feasible policy realizes the paired value formula. With [the specified inputs and conditions](hyp:k,Q,r,theta,h), [the stated relationship holds](goal). -/
-- @node: pairedSignPolicy_value
lemma pairedSignPolicy_value {k : ℕ} (Q : PotentialLaw (2 * k))
    (r : ProbabilitySimplex k) (theta : PairedContrasts k)
    (h : PairedCompletion Q r theta) :
    controlValue Q +
      (∑ j, poCellMass Q j * pairedSignPolicy theta j * effect Q j) =
        3 / 8 + (1 / 2) * ∑ i, r.1 i * |theta.1 i| := by
  rw [pairedCompletion_controlValue Q r theta h]
  have hcell (j : Fin (2 * k)) :
      poCellMass Q j * pairedSignPolicy theta j * effect Q j =
        r.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2 / 2 *
          pairedSignPolicy theta j *
          (1 / 4 +
            (if ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).1 = 0
             then 1 else -1) *
              theta.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2) := by
    obtain ⟨hp, _, h0, h1⟩ := h.2.2 j
    calc
      poCellMass Q j * pairedSignPolicy theta j * effect Q j =
          pairedSignPolicy theta j *
            (poCellMass Q j * poRegression Q 1 j -
              poCellMass Q j * poRegression Q 0 j) := by unfold effect; ring
      _ = _ := by rw [h0, h1, hp]; ring
  calc
    (1 / 4 : ℝ) + ∑ j, poCellMass Q j * pairedSignPolicy theta j * effect Q j =
        1 / 4 + ∑ j : Fin (2 * k),
          r.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2 / 2 *
            pairedSignPolicy theta j *
              (1 / 4 +
                (if ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).1 = 0
                 then 1 else -1) *
                  theta.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2) := by
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          exact hcell j
    _ = 3 / 8 + (1 / 2) * ∑ i, r.1 i * |theta.1 i| := by
      rw [← Equiv.sum_comp (finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k))]
      simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        pairedSignPolicy, Fin.isValue, ↓reduceIte, one_ne_zero]
      simp only [one_mul, neg_mul]
      rw [← Finset.sum_add_distrib]
      have hterm (i : Fin k) :
          r.1 i / 2 * (if 0 ≤ theta.1 i then 1 else 0) * (1 / 4 + theta.1 i) +
            r.1 i / 2 * (if 0 ≤ theta.1 i then 0 else 1) * (1 / 4 - theta.1 i) =
            r.1 i / 8 + r.1 i * |theta.1 i| / 2 := by
        by_cases ht : 0 ≤ theta.1 i
        · simp only [ht, ↓reduceIte, one_mul, mul_one, mul_zero, add_zero,
            abs_of_nonneg ht]
          ring

        · have ht' : theta.1 i ≤ 0 := le_of_lt (lt_of_not_ge ht)
          simp only [ht, ↓reduceIte, mul_zero, zero_mul, zero_add, mul_one,
            abs_of_nonpos ht']
          ring
      calc
        1 / 4 + ∑ i : Fin k,
            (r.1 i / 2 * (if 0 ≤ theta.1 i then 1 else 0) * (1 / 4 + theta.1 i) +
              r.1 i / 2 * (if 0 ≤ theta.1 i then 0 else 1) * (1 / 4 - theta.1 i)) =
            1 / 4 + ∑ i : Fin k, (r.1 i / 8 + r.1 i * |theta.1 i| / 2) := by
              congr 1
              apply Finset.sum_congr rfl
              intro i _
              exact hterm i
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
            r.2.2]
          ring

/-- The shadow price one quarter evaluates to the paired capacity value. With [the specified inputs and conditions](hyp:k,Q,r,theta,h,epsilon,he,he',hk), [the stated relationship holds](goal). -/
-- @node: pairedCompletion_dualQuarter
lemma pairedCompletion_dualQuarter {k : ℕ} (Q : PotentialLaw (2 * k))
    (r : ProbabilitySimplex k) (theta : PairedContrasts k)
    (h : PairedCompletion Q r theta) (epsilon : ℝ)
    (he : 0 < epsilon) (he' : epsilon < 1 / 2) (hk : 1 ≤ k) :
    (1 / 8 : ℝ) + dualProcessReal epsilon (observedMarginal Q) (1 / 4) =
      3 / 8 + (1 / 2) * ∑ i, r.1 i * |theta.1 i| := by
  have hQ := pairedCompletion_modelClass hk epsilon he he' Q r theta h
  rw [budget_dualProcess_identified epsilon Q hQ (1 / 4) (by norm_num),
    pairedCompletion_controlValue Q r theta h]
  have hcell (j : Fin (2 * k)) :
      poCellMass Q j * max 0 (effect Q j - 1 / 4) =
        r.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2 / 2 *
          max 0 ((if ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).1 = 0
            then 1 else -1) *
              theta.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2) := by
    obtain ⟨hp, _, h0, h1⟩ := h.2.2 j
    by_cases hz : poCellMass Q j = 0
    · rw [← hp, hz]
      simp
    · have heff : effect Q j = 1 / 4 +
          (if ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).1 = 0
            then 1 else -1) *
              theta.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2 := by
        unfold effect
        apply (mul_left_cancel₀ hz)
        linear_combination h1 - h0
      rw [heff, hp]
      simp only [add_sub_cancel_left]
  calc
    (1 / 8 : ℝ) +
        (1 / 4 + ∑ j : Fin (2 * k),
          poCellMass Q j * max 0 (effect Q j - 1 / 4)) =
        3 / 8 + ∑ j : Fin (2 * k),
          r.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2 / 2 *
            max 0 ((if ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).1 = 0
              then 1 else -1) *
                theta.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2) := by
          simp_rw [hcell]
          ring
    _ = _ := by
      rw [← Equiv.sum_comp (finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k))]
      simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Fin.isValue, ↓reduceIte, one_ne_zero, one_mul, neg_one_mul]
      rw [← Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases ht : 0 ≤ theta.1 i
      · rw [max_eq_right ht, max_eq_left (neg_nonpos.mpr ht), abs_of_nonneg ht]
        ring
      · have ht' : theta.1 i ≤ 0 := le_of_lt (lt_of_not_ge ht)
        rw [max_eq_left ht', max_eq_right (neg_nonneg.mpr ht'), abs_of_nonpos ht']
        ring

/-- The sign policy attains the shadow-price bound and uses the full half budget. With [the specified inputs and conditions](hyp:k,Q,r,theta,h,epsilon,he,he',hk), [the stated relationship holds](goal). -/
-- @node: pairedCompletion_bindingValue
lemma pairedCompletion_bindingValue {k : ℕ} (Q : PotentialLaw (2 * k))
    (r : ProbabilitySimplex k) (theta : PairedContrasts k)
    (h : PairedCompletion Q r theta) (epsilon : ℝ)
    (he : 0 < epsilon) (he' : epsilon < 1 / 2) (hk : 1 ≤ k) :
    BindingHalfBudget Q ∧
      budgetValue Q (1 / 2) = 3 / 8 + (1 / 2) * ∑ i, r.1 i * |theta.1 i| ∧
      budgetValue Q (1 / 2) =
        1 / 8 + dualProcessReal epsilon (observedMarginal Q) (1 / 4) := by
  let pi := pairedSignPolicy theta
  let gain : (Fin (2 * k) → ℝ) → ℝ :=
    fun pi => ∑ j, poCellMass Q j * pi j * effect Q j
  let feasible := budgetPolicyClass Q ⟨1 / 2, by norm_num⟩
  have hpi := pairedSignPolicy_budget Q r theta h
  have hvalue := pairedSignPolicy_value Q r theta h
  have hQ := pairedCompletion_modelClass hk epsilon he he' Q r theta h
  have hdual := pairedCompletion_dualQuarter Q r theta h epsilon he he' hk
  have hupper : budgetValue Q (1 / 2) ≤
      3 / 8 + (1 / 2) * ∑ i, r.1 i * |theta.1 i| := by
    calc
      budgetValue Q (1 / 2) ≤
          (1 / 2 : ℝ) * (1 / 4) +
            dualProcessReal epsilon (observedMarginal Q) (1 / 4) :=
        budget_dual_weak_bound epsilon Q hQ (1 / 2) (1 / 4) (by norm_num) (by norm_num)
      _ = _ := by convert hdual using 1 <;> ring
  have hlower : 3 / 8 + (1 / 2) * ∑ i, r.1 i * |theta.1 i| ≤
      budgetValue Q (1 / 2) := by
    rw [← hvalue]
    rw [budgetValue, dif_pos (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc 0 1)]
    change controlValue Q + gain pi ≤ controlValue Q + sSup (gain '' feasible)
    gcongr
    apply le_csSup
    · refine ⟨(1 / 2 : ℝ) * (1 / 4) +
          ∑ j, poCellMass Q j * max 0 (effect Q j - 1 / 4), ?_⟩
      rintro y ⟨pi', hpi', rfl⟩
      -- The generic budget bound supplies a finite upper bound for the image.
      have hbound := weighted_budget_weak_duality
        (poCellMass Q) (effect Q) pi' (1 / 2) (1 / 4)
        (by intro j; unfold poCellMass
            unfold CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass
              CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fullMass
            positivity)
        hpi'.1 hpi'.2 (by norm_num : (0 : ℝ) ≤ 1 / 4)
      exact hbound
    · exact ⟨pi, hpi.1, rfl⟩
  have hv : budgetValue Q (1 / 2) =
      3 / 8 + (1 / 2) * ∑ i, r.1 i * |theta.1 i| :=
    le_antisymm hupper (by simpa [gain, pi] using hlower)
  refine ⟨?_, hv, ?_⟩
  · refine ⟨pi, hpi.1, hpi.2, ?_⟩
    rw [hv]
    simpa [gain, pi] using hvalue.symm
  · rw [hv, hdual]

/-- The normalized pair's half-budget value is an affine copy of L1 distance. With [the specified inputs and conditions](hyp:k,hk,epsilon,he,he',R,S,r,theta,Q,hQ,hr,htheta), [the stated relationship holds](goal). -/
-- @node: normalizedPairedBudgetValue
lemma normalizedPairedBudgetValue {k : ℕ} (hk : 1 ≤ k)
    (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (R S r : ProbabilitySimplex k) (theta : PairedContrasts k)
    (Q : PotentialLaw (2 * k)) (hQ : PairedCompletion Q r theta)
    (hr : ∀ i, r.1 i = (R.1 i + S.1 i) / 2)
    (htheta : ∀ i, theta.1 i =
      if R.1 i + S.1 i = 0 then 0
      else (R.1 i - S.1 i) / (8 * (R.1 i + S.1 i))) :
    budgetValue Q (1 / 2) = 3 / 8 + simplexL1 R S / 32 := by
  have h := (pairedCompletion_bindingValue Q r theta hQ epsilon he he' hk).2.1
  rw [h, normalizedPairedL1 R S r theta hr htheta]
  ring

-- @node: prop:paired-capacity-identity
/-- The paired capacity identity result. Under [the hk premise](hyp:hk), [the he premise](hyp:he), [the he' premise](hyp:he'), It proves [the stated conclusion](goal). -/
theorem paired_capacity_identity (k : ℕ) (hk : 1 ≤ k) (epsilon : ℝ)
    (he : 0 < epsilon) (he' : epsilon < 1 / 2) :
    (∀ Q : PotentialLaw (2 * k), Q ∈ pairedFamily k →
      ∀ r : ProbabilitySimplex k, ∀ theta : PairedContrasts k,
      PairedCompletion Q r theta →
      CausalModelClass epsilon Q ∧
      (∀ j, 0 < poCellMass Q j → effect Q j ∈ Set.Icc (1 / 8 : ℝ) (3 / 8)) ∧
      BindingHalfBudget Q ∧
      budgetValue Q (1 / 2) = 3 / 8 + (1 / 2) * ∑ i, r.1 i * |theta.1 i| ∧
      budgetValue Q 1 = 1 / 2 ∧
      budgetValue Q (1 / 2) =
        1 / 8 + dualProcessReal epsilon (observedMarginal Q) (1 / 4)) ∧
    (∀ n : ℕ,
      ∃ K : ((Fin n → Fin k) × (Fin n → Fin k)) → PMF (Fin n → Obs (2 * k)),
      ∀ R S : ProbabilitySimplex k,
      ∃ r : ProbabilitySimplex k, ∃ theta : PairedContrasts k,
        (∀ i, r.1 i = (R.1 i + S.1 i) / 2) ∧
        (∀ i, theta.1 i =
          if R.1 i + S.1 i = 0 then 0
          else (R.1 i - S.1 i) / (8 * (R.1 i + S.1 i))) ∧
        pairedLaw r theta ∈ pairedFamily k ∧
          ∀ z : Fin n → Obs (2 * k),
            (∑ x : (Fin n → Fin k) × (Fin n → Fin k),
              (twoSampleLaw n (R, S)) {x} * K x z) =
              (productLaw (observedMarginal (pairedLaw r theta)) n) {z}) := by
  constructor
  · intro Q _ r theta h
    have hb := pairedCompletion_bindingValue Q r theta h epsilon he he' hk
    exact ⟨pairedCompletion_modelClass hk epsilon he he' Q r theta h,
      (fun j hj => pairedCompletion_effect_bounds Q r theta h j hj),
      hb.1, hb.2.1, pairedCompletion_budgetValue_one Q r theta h, hb.2.2⟩
  · intro n
    refine ⟨pairedSampleKernel n, ?_⟩
    intro R S
    obtain ⟨r, theta, hr, htheta⟩ := normalizedPairedParameters R S
    refine ⟨r, theta, hr, htheta, ?_, ?_⟩
    · exact ⟨r, theta, pairedLaw_completion r theta⟩
    · intro z
      exact pairedSampleKernel_reproduces R S r theta hr htheta z

end CausalSmith.Stat.DiscreteBudgetvalueCurve
