module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Constructions
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Candidate count of the exhaustive grid

The finite simplex grid has a stars-and-bars count. Its candidate-list
cardinality has degree-nineteen growth for fixed mixing scale.
-/

public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

-- @node: simplexGrid_card
/-- Stars and bars for the four-coordinate grid. [the stated conclusion holds](goal).-/
lemma simplexGrid_card (M : Nat) :
    (simplexGrid M).card = Nat.choose (M + 3) 3 := by
  classical
  let E : (simplexGrid M) ≃ {P : Fin 4 → Nat // ∑ i, P i = M} := {
    toFun := fun u => ⟨fun i => (u.1 i).val, by
      have h := u.2
      simpa [simplexGrid, IsGridRow] using h⟩
    invFun := fun v => ⟨fun i => ⟨v.1 i, by
      have h := Finset.single_le_sum_of_canonicallyOrdered
        (s := (Finset.univ : Finset (Fin 4))) (f := v.1) (Finset.mem_univ i)
      rw [v.2] at h
      omega⟩, by
        simp [simplexGrid, IsGridRow, v.2]⟩
    left_inv := by
      intro u
      apply Subtype.ext
      funext i
      apply Fin.ext
      rfl
    right_inv := by
      intro v
      apply Subtype.ext
      funext i
      rfl
  }
  calc
    (simplexGrid M).card = Fintype.card (simplexGrid M) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (Sym (Fin 4) M) := by
      exact Fintype.card_congr
        (E.trans (Sym.equivNatSumOfFintype (Fin 4) M).symm)
    _ = Nat.choose (M + 3) 3 := by
      rw [Sym.card_sym_eq_choose]
      simp only [Fintype.card_fin]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.choose_symm_add (a := M) (b := 3))

-- @node: gridMatrixRows_card
/-- Four independently selected simplex rows form the matrix grid. [the stated conclusion holds](goal).-/
lemma gridMatrixRows_card (M : Nat) :
    (gridMatrixRows M).card = (simplexGrid M).card ^ 4 := by
  classical
  unfold gridMatrixRows
  simp only
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_pi]
    simp
  · intro R S h
    funext i hi j
    have heq := congrFun h i
    exact congrFun heq j

-- @node: gridCandidateUniverse_card
/-- An unfiltered code consists of an initial row, four matrix rows, and rewards. [the stated conclusion holds](goal).-/
lemma gridCandidateUniverse_card (M : Nat) :
    (gridCandidateUniverse M).card =
      (simplexGrid M).card ^ 5 * (M + 1) ^ 4 := by
  classical
  have heq : gridCandidateUniverse M =
      (simplexGrid M).product ((gridMatrixRows M).product
        (Finset.univ : Finset (Fin 4 → Fin (M + 1)))) := by
    ext c
    rcases c with ⟨nu, R, r⟩
    simp [gridCandidateUniverse]
  rw [heq]
  change ((simplexGrid M) ×ˢ ((gridMatrixRows M) ×ˢ
    (Finset.univ : Finset (Fin 4 → Fin (M + 1))))).card = _
  rw [Finset.card_product, Finset.card_product, gridMatrixRows_card]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  ring

-- @node: gridCandidateUniverse_growth
/-- The exact count is bounded by a degree-nineteen monomial. [the stated conclusion holds](goal).-/
lemma gridCandidateUniverse_growth (M : Nat) :
    (gridCandidateUniverse M).card ≤ (M + 3) ^ 19 := by
  rw [gridCandidateUniverse_card, simplexGrid_card]
  calc
    (Nat.choose (M + 3) 3)^5 * (M + 1)^4
      ≤ ((M + 3)^3)^5 * (M + 3)^4 := by
          gcongr
          · exact Nat.choose_le_pow (M + 3) 3
          · omega
    _ = (M + 3)^19 := by ring

-- @node: gridSize_linear_bound
/-- The ceiling resolution grows linearly with the trajectory length. [Under the listed formal conditions](hyp:ha,hT), [the stated conclusion holds](goal).-/
lemma gridSize_linear_bound (T : Nat) (alpha : ℝ)
    (ha : 0 < alpha) (hT : 1 ≤ T) :
    ((gridSize T alpha : Nat) : ℝ) + 3 ≤
      (26 + 36 / alpha) * (T : ℝ) := by
  have hA : 0 ≤ (22 + 36 / alpha) * (T : ℝ) := by positivity
  have hc := Nat.ceil_lt_add_one hA
  have hc' : ((gridSize T alpha : Nat) : ℝ) <
      (22 + 36 / alpha) * (T : ℝ) + 1 := by
    simpa [gridSize] using hc
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hdiv : 0 ≤ 36 / alpha := by positivity
  nlinarith

-- @node: prop:exhaustive-grid-arithmetic-complexity
/-- For [positive mixing time](hyp:_ht0), the [stars-and-bars grid size, exact
unfiltered candidate count, and degree-nineteen candidate-list growth](goal)
hold for fixed `t0`. No fitting or selection cost is assigned. -/
theorem exhaustiveGrid_candidate_count (t0 : ℝ) (_ht0 : 0 < t0) :
    (∀ M : Nat, (simplexGrid M).card = Nat.choose (M + 3) 3) ∧
    (∀ M : Nat, (gridCandidateUniverse M).card =
      (Nat.choose (M + 3) 3) ^ 5 * (M + 1) ^ 4) ∧
    (∀ M : Nat, ∀ alpha : ℝ,
      (gridCandidates M alpha).card ≤ (gridCandidateUniverse M).card) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ T : Nat, 1 ≤ T →
      ((gridCandidateUniverse (gridSize T (mixingAlpha t0))).card : ℝ) ≤
        c * (T : ℝ) ^ 19 ∧
      ((gridCandidates (gridSize T (mixingAlpha t0))
        (mixingAlpha t0)).card : ℝ) ≤ c * (T : ℝ) ^ 19) := by
  refine ⟨simplexGrid_card, ?_, ?_, ?_⟩
  · intro M
    rw [gridCandidateUniverse_card, simplexGrid_card]
  · intro M alpha
    exact Finset.card_filter_le _ _
  · let alpha := mixingAlpha t0
    let c := (26 + 36 / alpha) ^ 19
    have ha : 0 < alpha := by
      change 0 < Real.exp (-(1 / t0))
      exact Real.exp_pos _
    have hc : 0 < c := by dsimp [c]; positivity
    refine ⟨c, hc, ?_⟩
    intro T hT
    let M := gridSize T alpha
    have hM : ((M : Nat) : ℝ) + 3 ≤
        (26 + 36 / alpha) * (T : ℝ) :=
      gridSize_linear_bound T alpha ha hT
    have hcount : (gridCandidateUniverse M).card ≤ (M + 3) ^ 19 :=
      gridCandidateUniverse_growth M
    have hreal : ((gridCandidateUniverse M).card : ℝ) ≤
        (((M + 3) ^ 19 : Nat) : ℝ) := by exact_mod_cast hcount
    have hpower : (((M + 3) ^ 19 : Nat) : ℝ) ≤ c * (T : ℝ) ^ 19 := by
      calc
        (((M + 3) ^ 19 : Nat) : ℝ) = ((M : ℝ) + 3) ^ 19 := by
          simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
        _ ≤ ((26 + 36 / alpha) * (T : ℝ)) ^ 19 := by
          exact pow_le_pow_left₀
            (add_nonneg (Nat.cast_nonneg _) (by norm_num)) hM 19
        _ = c * (T : ℝ) ^ 19 := by
          change ((26 + 36 / alpha) * (T : ℝ)) ^ 19 =
            (26 + 36 / alpha) ^ 19 * (T : ℝ) ^ 19
          exact mul_pow _ _ _
    have hfiltered : (gridCandidates M alpha).card ≤
        (gridCandidateUniverse M).card := Finset.card_filter_le _ _
    constructor
    · exact le_trans hreal hpower
    · exact le_trans (by exact_mod_cast hfiltered) (le_trans hreal hpower)

end CausalSmith.Stat.PomdpBinaryhiddenRate
