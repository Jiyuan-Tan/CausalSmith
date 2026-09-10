import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.TIdentificationAndExtension

/-! Causal interpretation of the observed optimal-regression value. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open scoped BigOperators

-- @node: observedMarginal_jointMass
/-- [each observed-marginal atom equals the sum of compatible full-data atoms](goal). -/
lemma observedMarginal_jointMass {d : ℕ} (Q : PotentialLaw d) (x : Fin d) (a y : Bool) :
    jointMass (observedMarginal Q) x a y =
      ∑ y0 : Bool, ∑ y1 : Bool, fullMass Q (x, a, y, y0, y1) := by
  classical
  have hmap : (observedMarginal Q).pmf (x, a, y) =
      ∑ y0 : Bool, ∑ y1 : Bool, Q.pmf (x, a, y, y0, y1) := by
    change (Q.pmf.map (fun z => (z.1, z.2.1, z.2.2.1))) (x, a, y) = _
    rw [PMF.map_apply, tsum_fintype]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single x]
    · fin_cases a <;> fin_cases y <;>
        simp [Fintype.sum_prod_type]
    · intro b _hb hbx
      simp [Ne.symm hbx]
    · simp
  rw [jointMass, hmap]
  simp [fullMass, ENNReal.toReal_add, PMF.apply_ne_top]

-- @node: observedMarginal_cellMass
/-- [the cell mass of the observed marginal equals the corresponding covariate mass of the potential-outcome law](goal). -/
lemma observedMarginal_cellMass {d : ℕ} (Q : PotentialLaw d) (x : Fin d) :
    cellMass (observedMarginal Q) x = poCellMass Q x := by
  simp [cellMass, poCellMass, observedMarginal_jointMass]

-- @node: consistent_observed_selected_atom
/-- [under consistency, each observed atom equals the compatible selected potential-outcome atom](goal). -/
lemma consistent_observed_selected_atom {d : ℕ} (Q : PotentialLaw d) (h : Consistency Q)
    (x : Fin d) (r : Fin 2) (y : Bool) :
    jointMass (observedMarginal Q) x (finTwoEquiv r) y =
      poArmAtom Q x r (finTwoEquiv r) y := by
  simp [Consistency] at h
  fin_cases r <;> fin_cases y <;>
    simp [observedMarginal_jointMass, poArmAtom, poAtom, finTwoEquiv, h]

-- @node: poRegression_eq_poArmAtom_ratio
/-- [the stated potential-outcome regression identity potential-outcome arm atom ratio relation holds](goal). -/
lemma poRegression_eq_poArmAtom_ratio {d : ℕ} (Q : PotentialLaw d)
    (x : Fin d) (r : Fin 2) :
    poRegression Q r x =
      (∑ arm : Bool, poArmAtom Q x r arm true) / poCellMass Q x := by
  fin_cases r <;>
    simp [poRegression, poCellMass, poArmAtom, poAtom] <;>
    ring

-- @node: consistent_observed_armMass
/-- [under consistency, observed arm mass equals the total compatible potential-outcome arm mass](goal). -/
lemma consistent_observed_armMass {d : ℕ} (Q : PotentialLaw d) (h : Consistency Q)
    (x : Fin d) (r : Fin 2) :
    armMass (observedMarginal Q) (finTwoEquiv r) x =
      ∑ y : Bool, poArmAtom Q x r (finTwoEquiv r) y := by
  simp [armMass, consistent_observed_selected_atom Q h x r]

-- @node: poArmAtom_total_eq_cellMass
/-- [summing the compatible potential-outcome arm atoms over arm and outcome gives cell mass](goal). -/
lemma poArmAtom_total_eq_cellMass {d : ℕ} (Q : PotentialLaw d)
    (x : Fin d) (r : Fin 2) :
    (∑ a : Bool, ∑ y : Bool, poArmAtom Q x r a y) = poCellMass Q x := by
  fin_cases r <;>
    simp [poCellMass, poArmAtom, poAtom] <;>
    ring

-- @node: poRegression_eq_outcomeMean_of_pos
/-- If [the stated cons condition holds](hyp:hcons), and [the stated exch condition holds](hyp:hexch), and [the stated cell condition holds](hyp:hcell), and [the stated arm condition holds](hyp:harm), then [the stated potential-outcome regression identity outcome mean of pos relation holds](goal). -/
lemma poRegression_eq_outcomeMean_of_pos {d : ℕ} (Q : PotentialLaw d)
    (hcons : Consistency Q) (hexch : ConditionalExchangeability Q)
    (x : Fin d) (r : Fin 2)
    (hcell : 0 < cellMass (observedMarginal Q) x)
    (harm : 0 < armMass (observedMarginal Q) (finTwoEquiv r) x) :
    poRegression Q r x = outcomeMean (observedMarginal Q) (finTwoEquiv r) x := by
  have heq := hexch x r (finTwoEquiv r) true
  rw [poArmAtom_total_eq_cellMass] at heq
  rw [← observedMarginal_cellMass] at heq
  rw [consistent_observed_armMass Q hcons] at harm
  rw [poRegression_eq_poArmAtom_ratio, outcomeMean,
    consistent_observed_selected_atom Q hcons, consistent_observed_armMass Q hcons,
    ← observedMarginal_cellMass]
  field_simp [ne_of_gt hcell, ne_of_gt harm]
  nlinarith

-- @node: prop:causal-optimal-value-corollary
/-- If [the potential-outcome law satisfies the stated causal restrictions](hyp:hQ), then [the causal oracle value equals the optimal value identified from the observed marginal](goal). -/
theorem causal_optimal_value_corollary {d : ℕ} {epsilon : ℝ} (Q : PotentialLaw d)
    (hQ : CausalCompletionClass epsilon Q) :
    oracleValue Q = observedOptimalValue (observedMarginal Q) hQ.observedModel := by
  classical
  rw [oracleValue, observedOptimalValue, observedOptimalValueRaw]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [← observedMarginal_cellMass]
  by_cases hx : cellMass (observedMarginal Q) x = 0
  · simp [hx]
  · have hnonneg : 0 ≤ cellMass (observedMarginal Q) x := by
      unfold cellMass jointMass
      positivity
    have hxpos : 0 < cellMass (observedMarginal Q) x :=
      lt_of_le_of_ne hnonneg (Ne.symm hx)
    have hov := hQ.overlap x hxpos
    have ht : 0 < armMass (observedMarginal Q) true x := by
      have he : 0 < epsilon * cellMass (observedMarginal Q) x :=
        mul_pos hQ.epsilon_pos hxpos
      exact lt_of_lt_of_le he ((le_div_iff₀ hxpos).mp hov.1)
    have hsum : cellMass (observedMarginal Q) x =
        armMass (observedMarginal Q) false x + armMass (observedMarginal Q) true x := by
      simp [cellMass, armMass]
      ring
    have hf : 0 < armMass (observedMarginal Q) false x := by
      rw [propensity, div_le_iff₀ hxpos] at hov
      nlinarith [mul_pos hQ.epsilon_pos hxpos]
    rw [poRegression_eq_outcomeMean_of_pos Q hQ.consistency hQ.exchangeability x 0 hxpos hf,
      poRegression_eq_outcomeMean_of_pos Q hQ.consistency hQ.exchangeability x 1 hxpos ht]
    rfl

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
