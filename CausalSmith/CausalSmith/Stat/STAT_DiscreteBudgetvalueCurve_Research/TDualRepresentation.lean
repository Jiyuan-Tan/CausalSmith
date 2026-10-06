module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Basic
public import Causalean.Mathlib.Optimization.FiniteKnapsack
public import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.TCausalOptimalValueCorollary

/-! Fractional-knapsack duality and contraction of the dual minimum. -/

@[expose] public section


namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

/-- The observed cell mass is the corresponding full-data covariate marginal. With [the specified inputs and conditions](hyp:d,Q,j), [the stated relationship holds](goal). -/
lemma observedMarginal_cellMass_eq_poCellMass {d : ℕ} (Q : PotentialLaw d)
    (j : Fin d) : cellMass (observedMarginal Q) j = poCellMass Q j :=
  CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal_cellMass Q.val j

-- @node: budget_pairwise_implies_armwise
/-- Joint conditional independence of both potential outcomes implies armwise independence. With [the specified inputs and conditions](hyp:d,Q,h), [the stated relationship holds](goal). -/
lemma budget_pairwise_implies_armwise {d : ℕ} (Q : PotentialLaw d)
    (h : ConditionalExchangeability Q) :
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.ConditionalExchangeability Q.val := by
  intro x r a ya
  have h00 := h x a false false
  have h01 := h x a false true
  have h10 := h x a true false
  have h11 := h x a true true
  fin_cases r <;> fin_cases a <;> fin_cases ya
  all_goals
    simp [CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poArmAtom,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poAtom,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass,
      poJointAtom, poTreatmentAtom, poPairAtom, poCellMass] at h00 h01 h10 h11 ⊢
    first
    | linear_combination h00 + h01
    | linear_combination h10 + h11
    | linear_combination h00 + h10
    | linear_combination h01 + h11

-- @node: budget_cell_mass_as_totalMass
/-- The budget cell mass as total mass result. It proves [the stated conclusion](goal). -/
lemma budget_cell_mass_as_totalMass {d : ℕ} (P : DiscreteLaw d) (j : Fin d) :
    totalMass (cellVector P j) = cellMass P j := by
  simp [totalMass, armMassFn,
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass,
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellVector,
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.jointMass, finTwoEquiv]
  ring

-- @node: budget_arm_mass_as_armMassFn
/-- The budget arm mass as arm mass fn result. It proves [the stated conclusion](goal). -/
lemma budget_arm_mass_as_armMassFn {d : ℕ} (P : DiscreteLaw d)
    (j : Fin d) (a : Fin 2) :
    armMassFn a (cellVector P j) = armMass P (finTwoEquiv a) j := by
  fin_cases a <;> simp [armMassFn,
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.armMass,
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellVector,
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.jointMass, finTwoEquiv]
    <;> ring

-- @node: budget_cell_success_mass
/-- The budget cell success mass result. It proves [the stated conclusion](goal). -/
lemma budget_cell_success_mass {d : ℕ} (P : DiscreteLaw d)
    (j : Fin d) (a : Fin 2) :
    cellVector P j (a, 1) = jointMass P j (finTwoEquiv a) true := by
  fin_cases a <;> simp [CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellVector,
    finTwoEquiv]

-- @node: budget_armValue_identified
/-- Under causal identification and overlap, the extended arm value is cell mass times mean. With [the specified inputs and conditions](hyp:d,epsilon,Q,hQ,j,a), [the stated relationship holds](goal). -/
lemma budget_armValue_identified {d : ℕ} (epsilon : ℝ) (Q : PotentialLaw d)
    (hQ : CausalModelClass epsilon Q) (j : Fin d) (a : Fin 2) :
    armValue epsilon a (cellVector (observedMarginal Q) j) =
      poCellMass Q j * poRegression Q a j := by
  let P := observedMarginal Q
  have hm : totalMass (cellVector P j) = cellMass P j :=
    budget_cell_mass_as_totalMass P j
  have ha : armMassFn a (cellVector P j) = armMass P (finTwoEquiv a) j :=
    budget_arm_mass_as_armMassFn P j a
  have hy : cellVector P j (a, 1) = jointMass P j (finTwoEquiv a) true :=
    budget_cell_success_mass P j a
  have hp : cellMass P j = poCellMass Q j :=
    observedMarginal_cellMass_eq_poCellMass Q j
  by_cases hz : cellMass P j = 0
  · change armValue epsilon a (cellVector P j) = poCellMass Q j * poRegression Q a j
    rw [armValue, hm, ← hp]
    simp only [hz, zero_mul, zero_div]
  have hnonneg : 0 ≤ cellMass P j := by
    unfold cellMass
    unfold CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.jointMass
    positivity
  have hpos : 0 < cellMass P j := lt_of_le_of_ne hnonneg (Ne.symm hz)
  obtain ⟨hlo, hhi⟩ := hQ.overlap j hpos
  have hsum : cellMass P j = armMass P false j + armMass P true j := by
    simp [CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.armMass]
    ring
  have hband : epsilon * cellMass P j ≤ armMass P (finTwoEquiv a) j := by
    fin_cases a
    · change epsilon * cellMass P j ≤ armMass P false j
      change armMass P true j / cellMass P j ≤ 1 - epsilon at hhi
      rw [div_le_iff₀ hpos] at hhi
      linarith
    · change epsilon * cellMass P j ≤ armMass P true j
      exact (le_div_iff₀ hpos).mp hlo
  have harm : 0 < armMass P (finTwoEquiv a) j :=
    lt_of_lt_of_le (mul_pos hQ.overlapParameter.1 hpos) hband
  have hmax : max (armMassFn a (cellVector P j))
      (epsilon * totalMass (cellVector P j)) = armMassFn a (cellVector P j) := by
    rw [hm, ha]
    exact max_eq_left hband
  have hident : poRegression Q a j =
      jointMass P j (finTwoEquiv a) true / armMass P (finTwoEquiv a) j := by
    exact CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poRegression_eq_outcomeMean_of_pos
      Q.val Q.property.1 (budget_pairwise_implies_armwise Q hQ.exchangeability)
      j a hpos harm
  rw [armValue, hmax, hm, ha, hy, ← hp, hident]
  ring

/-! PRIOR PROOF (carry-over before the constrained-law carrier):
  let P := observedMarginal Q
  have hm : totalMass (cellVector P j) = cellMass P j :=
    budget_cell_mass_as_totalMass P j
  have ha : armMassFn a (cellVector P j) = armMass P (finTwoEquiv a) j :=
    budget_arm_mass_as_armMassFn P j a
  have hy : cellVector P j (a, 1) = jointMass P j (finTwoEquiv a) true :=
    budget_cell_success_mass P j a
  have hp : cellMass P j = poCellMass Q j :=
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal_cellMass Q j
  by_cases hz : cellMass P j = 0
  · change armValue epsilon a (cellVector P j) = poCellMass Q j * poRegression Q a j
    rw [armValue, hm, ← hp]
    simp only [hz, zero_mul, zero_div]
  have hnonneg : 0 ≤ cellMass P j := by
    unfold cellMass
    unfold CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.jointMass
    positivity
  have hpos : 0 < cellMass P j := lt_of_le_of_ne hnonneg (Ne.symm hz)
  obtain ⟨hlo, hhi⟩ := hQ.overlap j hpos
  have hsum : cellMass P j = armMass P false j + armMass P true j := by
    simp [CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.armMass]
    ring
  have hband : epsilon * cellMass P j ≤ armMass P (finTwoEquiv a) j := by
    fin_cases a
    · change epsilon * cellMass P j ≤ armMass P false j
      change armMass P true j / cellMass P j ≤ 1 - epsilon at hhi
      rw [div_le_iff₀ hpos] at hhi
      linarith
    · change epsilon * cellMass P j ≤ armMass P true j
      exact (le_div_iff₀ hpos).mp hlo
  have harm : 0 < armMass P (finTwoEquiv a) j :=
    lt_of_lt_of_le (mul_pos hQ.overlapParameter.1 hpos) hband
  have hmax : max (armMassFn a (cellVector P j))
      (epsilon * totalMass (cellVector P j)) = armMassFn a (cellVector P j) := by
    rw [hm, ha]
    exact max_eq_left hband
  have hident : poRegression Q a j =
      jointMass P j (finTwoEquiv a) true / armMass P (finTwoEquiv a) j := by
    exact CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poRegression_eq_outcomeMean_of_pos
      Q hQ.consistency (budget_pairwise_implies_armwise Q hQ.exchangeability)
      j a hpos harm
  rw [armValue, hmax, hm, ha, hy, ← hp, hident]
  ring
-/

/-! PRIOR PROOF (carry-over: auto; signature-unchanged `budget_armValue_identified`). Stage 3: replace the
   placeholder above with this body, run `lean_diagnostic_messages`, patch failures only.
   := by  let P := observedMarginal Q
  have hm : totalMass (cellVector P j) = cellMass P j :=
    budget_cell_mass_as_totalMass P j
  have ha : armMassFn a (cellVector P j) = armMass P (finTwoEquiv a) j :=
    budget_arm_mass_as_armMassFn P j a
  have hy : cellVector P j (a, 1) = jointMass P j (finTwoEquiv a) true :=
    budget_cell_success_mass P j a
  have hp : cellMass P j = poCellMass Q j :=
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal_cellMass Q j
  by_cases hz : cellMass P j = 0
  · change armValue epsilon a (cellVector P j) = poCellMass Q j * poRegression Q a j
    rw [armValue, hm, ← hp]
    simp only [hz, zero_mul, zero_div]
  have hnonneg : 0 ≤ cellMass P j := by
    unfold cellMass
    unfold CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.jointMass
    positivity
  have hpos : 0 < cellMass P j := lt_of_le_of_ne hnonneg (Ne.symm hz)
  obtain ⟨hlo, hhi⟩ := hQ.overlap j hpos
  have hsum : cellMass P j = armMass P false j + armMass P true j := by
    simp [CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.cellMass,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.armMass]
    ring
  have hband : epsilon * cellMass P j ≤ armMass P (finTwoEquiv a) j := by
    fin_cases a
    · change epsilon * cellMass P j ≤ armMass P false j
      change armMass P true j / cellMass P j ≤ 1 - epsilon at hhi
      rw [div_le_iff₀ hpos] at hhi
      linarith
    · change epsilon * cellMass P j ≤ armMass P true j
      exact (le_div_iff₀ hpos).mp hlo
  have harm : 0 < armMass P (finTwoEquiv a) j :=
    lt_of_lt_of_le (mul_pos hQ.overlapParameter.1 hpos) hband
  have hmax : max (armMassFn a (cellVector P j))
      (epsilon * totalMass (cellVector P j)) = armMassFn a (cellVector P j) := by
    rw [hm, ha]
    exact max_eq_left hband
  have hident : poRegression Q a j =
      jointMass P j (finTwoEquiv a) true / armMass P (finTwoEquiv a) j := by
    exact CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poRegression_eq_outcomeMean_of_pos
      Q hQ.consistency (budget_pairwise_implies_armwise Q hQ.exchangeability)
      j a hpos harm
  rw [armValue, hmax, hm, ha, hy, ← hp, hident]
  ring

-- @node: budget_threshold_identified
-/
/-- The observed threshold term is the causal baseline plus the positive effect hinge. With [the specified inputs and conditions](hyp:d,epsilon,Q,hQ,j,lambda,hlambda), [the stated relationship holds](goal). -/
lemma budget_threshold_identified {d : ℕ} (epsilon : ℝ) (Q : PotentialLaw d)
    (hQ : CausalModelClass epsilon Q) (j : Fin d) (lambda : ℝ)
    (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1) :
    thresholdFunReal epsilon lambda (cellVector (observedMarginal Q) j) =
      poCellMass Q j * poRegression Q 0 j +
        poCellMass Q j * max 0 (effect Q j - lambda) := by
  have hp : 0 ≤ poCellMass Q j := by
    unfold poCellMass
    unfold CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fullMass
    positivity
  have hmax (x : ℝ) : max 0 (poCellMass Q j * x) = poCellMass Q j * max 0 x := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_right (mul_nonneg hp hx), max_eq_right hx]
    · have hxle : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
      rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos hp hxle), max_eq_left hxle]
      simp
  simp only [thresholdFunReal, dif_pos hlambda, thresholdFun]
  rw [budget_armValue_identified epsilon Q hQ j 0,
    budget_armValue_identified epsilon Q hQ j 1,
    budget_cell_mass_as_totalMass]
  have hmass : cellMass (observedMarginal Q) j = poCellMass Q j :=
    observedMarginal_cellMass_eq_poCellMass Q j
  rw [hmass]
  have hrew : poCellMass Q j * poRegression Q 1 j -
      poCellMass Q j * poRegression Q 0 j - lambda * poCellMass Q j =
        poCellMass Q j * (effect Q j - lambda) := by
    unfold effect
    ring
  rw [hrew, hmax]

/-! PRIOR PROOF (carry-over before the constrained-law carrier):
  have hp : 0 ≤ poCellMass Q j := by
    unfold poCellMass
    unfold CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fullMass
    positivity
  have hmax (x : ℝ) : max 0 (poCellMass Q j * x) = poCellMass Q j * max 0 x := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_right (mul_nonneg hp hx), max_eq_right hx]
    · have hxle : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
      rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos hp hxle), max_eq_left hxle]
      simp
  simp only [thresholdFunReal, dif_pos hlambda, thresholdFun]
  rw [budget_armValue_identified epsilon Q hQ j 0,
    budget_armValue_identified epsilon Q hQ j 1,
    budget_cell_mass_as_totalMass]
  have hmass : cellMass (observedMarginal Q) j = poCellMass Q j :=
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal_cellMass Q j
  rw [hmass]
  have hrew : poCellMass Q j * poRegression Q 1 j -
      poCellMass Q j * poRegression Q 0 j - lambda * poCellMass Q j =
        poCellMass Q j * (effect Q j - lambda) := by
    unfold effect
    ring
  rw [hrew, hmax]
-/

/-! PRIOR PROOF (carry-over: auto; signature-unchanged `budget_threshold_identified`). Stage 3: replace the
   placeholder above with this body, run `lean_diagnostic_messages`, patch failures only.
   := by  have hp : 0 ≤ poCellMass Q j := by
    unfold poCellMass
    unfold CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fullMass
    positivity
  have hmax (x : ℝ) : max 0 (poCellMass Q j * x) = poCellMass Q j * max 0 x := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_right (mul_nonneg hp hx), max_eq_right hx]
    · have hxle : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
      rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos hp hxle), max_eq_left hxle]
      simp
  simp only [thresholdFunReal, dif_pos hlambda, thresholdFun]
  rw [budget_armValue_identified epsilon Q hQ j 0,
    budget_armValue_identified epsilon Q hQ j 1,
    budget_cell_mass_as_totalMass]
  have hmass : cellMass (observedMarginal Q) j = poCellMass Q j :=
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal_cellMass Q j
  rw [hmass]
  have hrew : poCellMass Q j * poRegression Q 1 j -
      poCellMass Q j * poRegression Q 0 j - lambda * poCellMass Q j =
        poCellMass Q j * (effect Q j - lambda) := by
    unfold effect
    ring
  rw [hrew, hmax]

-- @node: budget_dualProcess_identified
-/
/-- The threshold process equals control value plus the sum of positive effect hinges. With [the specified inputs and conditions](hyp:d,epsilon,Q,hQ,lambda,hlambda), [the stated relationship holds](goal). -/
lemma budget_dualProcess_identified {d : ℕ} (epsilon : ℝ) (Q : PotentialLaw d)
    (hQ : CausalModelClass epsilon Q) (lambda : ℝ)
    (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1) :
    dualProcessReal epsilon (observedMarginal Q) lambda =
      controlValue Q + ∑ j : Fin d, poCellMass Q j * max 0 (effect Q j - lambda) := by
  simp only [dualProcessReal, dif_pos hlambda, dualProcess, controlValue]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simpa [thresholdFunReal, hlambda] using
    (budget_threshold_identified epsilon Q hQ j lambda hlambda)

/-- The minimum of an indexed shadow-price process on `[0,1]`. -/
noncomputable def dualMinimum (b : ℝ) (F : ℝ → ℝ) : ℝ :=
  sInf ((fun lambda : ℝ => b * lambda + F lambda) '' Set.Icc 0 1)

-- @node: dualMinimum_lipschitz
/-- The dual minimum lipschitz result. Under [the hF premise](hyp:hF), [the hG premise](hyp:hG), [the hM premise](hyp:hM), It proves [the stated conclusion](goal). -/
lemma dualMinimum_lipschitz (b : ℝ) (F G : ℝ → ℝ) (M : ℝ)
    (hF : BddBelow ((fun lambda : ℝ => b * lambda + F lambda) '' Set.Icc 0 1))
    (hG : BddBelow ((fun lambda : ℝ => b * lambda + G lambda) '' Set.Icc 0 1))
    (hM : ∀ lambda ∈ Set.Icc (0 : ℝ) 1, |F lambda - G lambda| ≤ M) :
    |dualMinimum b F - dualMinimum b G| ≤ M := by
  have hneF : ((fun lambda : ℝ => b * lambda + F lambda) '' Set.Icc 0 1).Nonempty :=
    ⟨F 0, 0, by norm_num, by simp⟩
  have hneG : ((fun lambda : ℝ => b * lambda + G lambda) '' Set.Icc 0 1).Nonempty :=
    ⟨G 0, 0, by norm_num, by simp⟩
  have hFG : dualMinimum b F ≤ dualMinimum b G + M := by
    have h : dualMinimum b F - M ≤ dualMinimum b G := by
      unfold dualMinimum
      apply le_csInf hneG
      rintro x ⟨lambda, hlambda, rfl⟩
      have hleft := csInf_le hF (Set.mem_image_of_mem _ hlambda)
      have hdiff := (abs_le.mp (hM lambda hlambda)).2
      linarith
    linarith
  have hGF : dualMinimum b G ≤ dualMinimum b F + M := by
    have h : dualMinimum b G - M ≤ dualMinimum b F := by
      unfold dualMinimum
      apply le_csInf hneF
      rintro x ⟨lambda, hlambda, rfl⟩
      have hleft := csInf_le hG (Set.mem_image_of_mem _ hlambda)
      have hdiff := (abs_le.mp (hM lambda hlambda)).1
      linarith
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

-- @node: weighted_budget_weak_duality
/-- The weighted budget weak duality result. Under [the hp premise](hyp:hp), [the hpi premise](hyp:hpi), [the hbudget premise](hyp:hbudget), [the hlambda premise](hyp:hlambda), It proves [the stated conclusion](goal). -/
lemma weighted_budget_weak_duality {d : ℕ} (p tau pi : Fin d → ℝ)
    (b lambda : ℝ) (hp : ∀ j, 0 ≤ p j)
    (hpi : ∀ j, pi j ∈ Set.Icc (0 : ℝ) 1)
    (hbudget : ∑ j, p j * pi j ≤ b) (hlambda : 0 ≤ lambda) :
    ∑ j, p j * pi j * tau j ≤
      b * lambda + ∑ j, p j * max 0 (tau j - lambda) := by
  have hcell (j : Fin d) :
      p j * pi j * (tau j - lambda) ≤ p j * max 0 (tau j - lambda) := by
    rcases hpi j with ⟨hpi0, hpi1⟩
    by_cases ht : 0 ≤ tau j - lambda
    · rw [max_eq_right ht]
      nlinarith [mul_nonneg (hp j) (sub_nonneg.mpr hpi1),
        mul_nonneg (hp j) ht]
    · rw [max_eq_left (le_of_not_ge ht)]
      nlinarith [mul_nonneg (hp j) hpi0]
  have hsum :
      ∑ j, p j * pi j * (tau j - lambda) ≤
        ∑ j, p j * max 0 (tau j - lambda) :=
    Finset.sum_le_sum (fun j _ => hcell j)
  have hbudget' : (∑ j, p j * pi j) * lambda ≤ b * lambda :=
    mul_le_mul_of_nonneg_right hbudget hlambda
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
  linarith

-- @node: dualMinimum_uniform_lipschitz
/-- The dual minimum uniform lipschitz result. Under [the hF premise](hyp:hF), [the hG premise](hyp:hG), [the hM premise](hyp:hM), It proves [the stated conclusion](goal). -/
lemma dualMinimum_uniform_lipschitz (F G : ℝ → ℝ) (M : ℝ)
    (hF : ∀ b ∈ Set.Icc (0 : ℝ) 1,
      BddBelow ((fun lambda : ℝ => b * lambda + F lambda) '' Set.Icc 0 1))
    (hG : ∀ b ∈ Set.Icc (0 : ℝ) 1,
      BddBelow ((fun lambda : ℝ => b * lambda + G lambda) '' Set.Icc 0 1))
    (hM : ∀ lambda ∈ Set.Icc (0 : ℝ) 1, |F lambda - G lambda| ≤ M) :
    sSup ((fun b : ℝ => |dualMinimum b F - dualMinimum b G|) '' Set.Icc 0 1) ≤ M := by
  apply csSup_le
  · exact ⟨|dualMinimum 0 F - dualMinimum 0 G|, 0, by norm_num, rfl⟩
  · rintro x ⟨b, hb, rfl⟩
    exact dualMinimum_lipschitz b F G M (hF b hb) (hG b hb) hM

-- @node: dualMinimum_uniform_contraction
/-- The dual minimum uniform contraction result. Under [the hF premise](hyp:hF), [the hG premise](hyp:hG), It proves [the stated conclusion](goal). -/
lemma dualMinimum_uniform_contraction (F G : ℝ → ℝ)
    (hF : ∃ B : ℝ, ∀ lambda ∈ Set.Icc (0 : ℝ) 1, |F lambda| ≤ B)
    (hG : ∃ B : ℝ, ∀ lambda ∈ Set.Icc (0 : ℝ) 1, |G lambda| ≤ B) :
    sSup ((fun b : ℝ => |dualMinimum b F - dualMinimum b G|) '' Set.Icc 0 1) ≤
      sSup ((fun lambda : ℝ => |F lambda - G lambda|) '' Set.Icc 0 1) := by
  obtain ⟨BF, hBF⟩ := hF
  obtain ⟨BG, hBG⟩ := hG
  have hdiff : BddAbove ((fun lambda : ℝ => |F lambda - G lambda|) ''
      Set.Icc (0 : ℝ) 1) := by
    refine ⟨BF + BG, ?_⟩
    rintro x ⟨lambda, hlambda, rfl⟩
    calc
      |F lambda - G lambda| ≤ |F lambda| + |G lambda| := by
        simpa using (abs_sub_le (F lambda) 0 (G lambda))
      _ ≤ BF + BG := add_le_add (hBF lambda hlambda) (hBG lambda hlambda)
  have hbelow (H : ℝ → ℝ) (B : ℝ)
      (hB : ∀ lambda ∈ Set.Icc (0 : ℝ) 1, |H lambda| ≤ B) :
      ∀ b ∈ Set.Icc (0 : ℝ) 1,
        BddBelow ((fun lambda : ℝ => b * lambda + H lambda) '' Set.Icc 0 1) := by
    intro b hb
    refine ⟨-B, ?_⟩
    rintro x ⟨lambda, hlambda, rfl⟩
    have hnonneg : 0 ≤ b * lambda := mul_nonneg hb.1 hlambda.1
    have hlow := (abs_le.mp (hB lambda hlambda)).1
    linarith
  apply dualMinimum_uniform_lipschitz F G _
    (hbelow F BF hBF) (hbelow G BG hBG)
  intro lambda hlambda
  exact le_csSup hdiff ⟨lambda, hlambda, rfl⟩

-- @node: dualProcessReal_bounded
/-- The dual process real bounded result. It proves [the stated conclusion](goal). -/
lemma dualProcessReal_bounded {d : ℕ} (epsilon : ℝ) (P : DiscreteLaw d) :
    ∃ B : ℝ, ∀ lambda ∈ Set.Icc (0 : ℝ) 1,
      |dualProcessReal epsilon P lambda| ≤ B := by
  let F : ℝ → ℝ := fun lambda =>
    ∑ j : Fin d,
      (armValue epsilon 0 (cellVector P j) +
        max 0 (armValue epsilon 1 (cellVector P j) -
          armValue epsilon 0 (cellVector P j) - lambda * totalMass (cellVector P j)))
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have heq : ∀ lambda ∈ Set.Icc (0 : ℝ) 1,
      dualProcessReal epsilon P lambda = F lambda := by
    intro lambda hlambda
    simp [dualProcessReal, dualProcess, thresholdFun, F, hlambda]
  have hcont : ContinuousOn (dualProcessReal epsilon P) (Set.Icc (0 : ℝ) 1) := by
    exact hF.continuousOn.congr fun lambda hlambda => heq lambda hlambda
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (f := dualProcessReal epsilon P) hcont
  exact ⟨B, by simpa only [Real.norm_eq_abs] using hB⟩

-- @node: budget_dual_weak_bound
/-- Every feasible policy lies below every nonnegative shadow-price objective. With [the specified inputs and conditions](hyp:d,epsilon,Q,hQ,b,lambda,hb,hlambda), [the stated relationship holds](goal). -/
lemma budget_dual_weak_bound {d : ℕ} (epsilon : ℝ) (Q : PotentialLaw d)
    (hQ : CausalModelClass epsilon Q) (b lambda : ℝ)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hlambda : lambda ∈ Set.Icc (0 : ℝ) 1) :
    budgetValue Q b ≤ b * lambda + dualProcessReal epsilon (observedMarginal Q) lambda := by
  let S := ((fun pi : Fin d → ℝ =>
    ∑ j, poCellMass Q j * pi j * effect Q j) '' budgetPolicyClass Q ⟨b, hb⟩)
  have hnonempty : S.Nonempty := by
    refine ⟨0, fun _ => 0, ?_, by simp [S]⟩
    simp [budgetPolicyClass, hb.1]
  have hp : ∀ j : Fin d, 0 ≤ poCellMass Q j := by
    intro j
    unfold poCellMass
    unfold CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fullMass
    positivity
  have hsup : sSup S ≤ b * lambda +
      ∑ j : Fin d, poCellMass Q j * max 0 (effect Q j - lambda) := by
    apply csSup_le hnonempty
    rintro y ⟨pi, hpi, rfl⟩
    exact weighted_budget_weak_duality
      (poCellMass Q) (effect Q) pi b lambda hp hpi.1 hpi.2 hlambda.1
  rw [budgetValue, dif_pos hb, budget_dualProcess_identified epsilon Q hQ lambda hlambda]
  dsimp [S] at hsup
  linarith

-- @node: prop:dual-representation
/-- The dual representation result. Under [the hd premise](hyp:hd), [the hQ premise](hyp:hQ), [the he premise](hyp:he), [the he' premise](hyp:he'), It proves [the stated conclusion](goal). -/
theorem dual_representation {d : ℕ} (epsilon : ℝ) (Q : PotentialLaw d)
    (hd : 2 ≤ d) (hQ : CausalModelClass epsilon Q) (he : 0 < epsilon)
    (he' : epsilon < 1 / 2) :
    (∀ b ∈ Set.Icc (0 : ℝ) 1,
      budgetValue Q b = dualMinimum b (dualProcessReal epsilon (observedMarginal Q))) ∧
    (∀ Fhat : ℝ → ℝ, (∃ B : ℝ, ∀ lambda ∈ Set.Icc (0 : ℝ) 1, |Fhat lambda| ≤ B) →
      sSup ((fun b : ℝ =>
        |dualMinimum b Fhat - budgetValue Q b|) '' Set.Icc 0 1) ≤
      sSup ((fun lambda : ℝ =>
        |Fhat lambda - dualProcessReal epsilon (observedMarginal Q) lambda|) ''
          Set.Icc 0 1)) := by
  have hdual : ∀ b ∈ Set.Icc (0 : ℝ) 1,
      budgetValue Q b = dualMinimum b (dualProcessReal epsilon (observedMarginal Q)) := by
    intro b hb
    have hweak : budgetValue Q b ≤
        dualMinimum b (dualProcessReal epsilon (observedMarginal Q)) := by
      unfold dualMinimum
      apply le_csInf
      · exact ⟨b * 0 + dualProcessReal epsilon (observedMarginal Q) 0,
          0, by norm_num, rfl⟩
      · rintro y ⟨lambda, hlambda, rfl⟩
        exact budget_dual_weak_bound epsilon Q hQ b lambda hb hlambda
    have hstrong : dualMinimum b (dualProcessReal epsilon (observedMarginal Q)) ≤
        budgetValue Q b := by
      have hp : ∀ j : Fin d, 0 ≤ poCellMass Q j := by
        intro j
        unfold poCellMass
        unfold CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass
          CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.fullMass
        positivity
      have ht : ∀ j : Fin d, effect Q j ≤ 1 := by
        intro j
        have h0 := (poRegression_unit_interval_budget Q 0 j).1
        have h1 := (poRegression_unit_interval_budget Q 1 j).2
        unfold effect
        linarith
      obtain ⟨pi, hpi, hpibudget, lambda, hlambda, heq⟩ :=
        Causalean.Mathlib.Optimization.finite_knapsack_dual_witness
          (poCellMass Q) (effect Q) b hp ht hb
      have hpifeas : (fun j => pi j) ∈ budgetPolicyClass Q ⟨b, hb⟩ :=
        ⟨hpi, hpibudget⟩
      let gains := ((fun rho : Fin d → ℝ =>
        ∑ j, poCellMass Q j * rho j * effect Q j) '' budgetPolicyClass Q ⟨b, hb⟩)
      have hgains_bdd : BddAbove gains := by
        refine ⟨1, ?_⟩
        rintro y ⟨rho, hrho, rfl⟩
        calc
          (∑ j, poCellMass Q j * rho j * effect Q j) ≤
              ∑ j, poCellMass Q j * rho j := by
            apply Finset.sum_le_sum
            intro j _
            have hpr : 0 ≤ poCellMass Q j * rho j :=
              mul_nonneg (hp j) (hrho.1 j).1
            nlinarith [ht j]
          _ ≤ b := hrho.2
          _ ≤ 1 := hb.2
      have hpigain_le : controlValue Q +
          (∑ j, poCellMass Q j * pi j * effect Q j) ≤ budgetValue Q b := by
        rw [budgetValue, dif_pos hb]
        simpa [gains, add_comm] using add_le_add_left
          (le_csSup hgains_bdd ⟨(fun j => pi j), hpifeas, rfl⟩) (controlValue Q)
      have hdual_bdd : BddBelow
          ((fun l : ℝ => b * l + dualProcessReal epsilon (observedMarginal Q) l) ''
            Set.Icc 0 1) := by
        obtain ⟨B, hB⟩ := dualProcessReal_bounded epsilon (observedMarginal Q)
        refine ⟨-B, ?_⟩
        rintro y ⟨l, hl, rfl⟩
        have hbl : 0 ≤ b * l := mul_nonneg hb.1 hl.1
        have hlow := (abs_le.mp (hB l hl)).1
        linarith
      unfold dualMinimum
      calc
        sInf ((fun l : ℝ => b * l + dualProcessReal epsilon (observedMarginal Q) l) ''
            Set.Icc 0 1) ≤
            b * lambda + dualProcessReal epsilon (observedMarginal Q) lambda :=
          csInf_le hdual_bdd ⟨lambda, hlambda, rfl⟩
        _ = controlValue Q + ∑ j, poCellMass Q j * pi j * effect Q j := by
          rw [budget_dualProcess_identified epsilon Q hQ lambda hlambda]
          linarith
        _ ≤ budgetValue Q b := hpigain_le
    exact le_antisymm hweak hstrong
  constructor
  · exact hdual
  · intro Fhat hFhat
    let F := dualProcessReal epsilon (observedMarginal Q)
    have hcontract := dualMinimum_uniform_contraction Fhat F hFhat
      (dualProcessReal_bounded epsilon (observedMarginal Q))
    have himage :
        ((fun b : ℝ => |dualMinimum b Fhat - budgetValue Q b|) '' Set.Icc 0 1) =
          ((fun b : ℝ => |dualMinimum b Fhat - dualMinimum b F|) '' Set.Icc 0 1) := by
      ext x
      constructor
      · rintro ⟨b, hb, rfl⟩
        refine ⟨b, hb, ?_⟩
        change |dualMinimum b Fhat - dualMinimum b F| =
          |dualMinimum b Fhat - budgetValue Q b|
        rw [hdual b hb]
      · rintro ⟨b, hb, rfl⟩
        refine ⟨b, hb, ?_⟩
        change |dualMinimum b Fhat - budgetValue Q b| =
          |dualMinimum b Fhat - dualMinimum b F|
        rw [hdual b hb]
    simpa only [himage, F] using hcontract

end CausalSmith.Stat.DiscreteBudgetvalueCurve
