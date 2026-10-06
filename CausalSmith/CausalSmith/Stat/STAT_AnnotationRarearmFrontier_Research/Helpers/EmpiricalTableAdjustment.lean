module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.ExperimentComparison
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.InverseCountArmRisk
public import Causalean.Stat.Minimax.SideInformation.Finite.Concentration
public import Causalean.Stat.Sample.EmpiricalMass
public import Mathlib.Algebra.Order.Chebyshev

/-!
Legal overlap adjustment of empirical marginal tables, its factor-three L¹ bound,
and the expected empirical approximation error.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- Clamp the treated mass while keeping the empirical covariate mass fixed. -/
-- @node: comparisonAdjustedTreated
noncomputable def comparisonAdjustedTreated (eps x0 x1 : Real) : Real :=
  min ((1 - eps) * (x0 + x1)) (max (eps * (x0 + x1)) x1)

/-- The legal adjustment is total on the ambient real table space. -/
-- @node: comparisonAdjustedTable
noncomputable def comparisonAdjustedTable {d : Nat} (eps : Real) (v : AuxTable d) :
    AuxTable d := fun z =>
  let h := comparisonAdjustedTreated eps (v (z.1, false)) (v (z.1, true))
  if z.2 then h else v (z.1, false) + v (z.1, true) - h

/-- The adjustment is Borel, including at empty cells. This gives [the stated conclusion](goal). -/
@[fun_prop]
-- @node: comparisonAdjustedTable_measurable
lemma comparisonAdjustedTable_measurable (d : Nat) (eps : Real) :
    Measurable (comparisonAdjustedTable (d := d) eps) := by
  apply measurable_pi_lambda
  intro z
  unfold comparisonAdjustedTable comparisonAdjustedTreated
  split_ifs <;> fun_prop

/-- [Under the stated inputs and conditions](hyp:d,eps,v,j), Adjustment preserves the covariate mass cell by cell.  This gives [the stated result](goal).-/
-- @node: comparisonAdjustedTable_cell_sum
lemma comparisonAdjustedTable_cell_sum {d : Nat} (eps : Real) (v : AuxTable d)
    (j : Fin d) :
    comparisonAdjustedTable eps v (j, false) + comparisonAdjustedTable eps v (j, true) =
      v (j, false) + v (j, true) := by
  simp only [comparisonAdjustedTable, Bool.false_eq_true, if_false, if_true]
  ring

/-- [Under the stated inputs and conditions](hyp:_heps,heps',hx0,hx1,eps,x0,x1), A nonnegative cell is adjusted into the overlap interval.  This gives [the stated result](goal).-/
-- @node: comparisonAdjustedTreated_bounds
lemma comparisonAdjustedTreated_bounds (eps x0 x1 : Real)
    (_heps : 0 ≤ eps) (heps' : eps ≤ 1 / 2) (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) :
    eps * (x0 + x1) ≤ comparisonAdjustedTreated eps x0 x1 ∧
    comparisonAdjustedTreated eps x0 x1 ≤ (1 - eps) * (x0 + x1) := by
  have hends : eps * (x0 + x1) ≤ (1 - eps) * (x0 + x1) := by
    nlinarith
  exact ⟨le_min hends (le_max_left _ _), min_le_left _ _⟩

/-- [Under the stated inputs and conditions](hyp:heps,heps',hlo,hhi,hends,eps,x0,x1,v0,v1), Relative to a legal population cell, moving the treated entry costs at most its L¹ error.  This gives [the stated result](goal).-/
-- @node: comparisonAdjustedTreated_movement
lemma comparisonAdjustedTreated_movement (eps x0 x1 v0 v1 : Real)
    (heps : 0 ≤ eps) (heps' : eps ≤ 1)
    (hlo : eps * (v0 + v1) ≤ v1) (hhi : v1 ≤ (1 - eps) * (v0 + v1))
    (hends : eps * (x0 + x1) ≤ (1 - eps) * (x0 + x1)) :
    |comparisonAdjustedTreated eps x0 x1 - x1| ≤ |x0 - v0| + |x1 - v1| := by
  have h0 := abs_le.mp (le_refl |x0 - v0|)
  have h1 := abs_le.mp (le_refl |x1 - v1|)
  have he1 : 0 ≤ 1 - eps := by linarith
  have h0e := mul_le_mul_of_nonneg_left h0.2 heps
  have h1e := mul_le_mul_of_nonneg_left h1.2 heps
  have h0c := mul_le_mul_of_nonneg_left h0.1 he1
  have h1c := mul_le_mul_of_nonneg_left h1.1 he1
  have hb0 := mul_le_mul_of_nonneg_right heps' (abs_nonneg (x0 - v0))
  have hb1 := mul_le_mul_of_nonneg_right heps' (abs_nonneg (x1 - v1))
  have hc0 := mul_le_mul_of_nonneg_right (show 1 - eps ≤ 1 by linarith)
    (abs_nonneg (x0 - v0))
  have hc1 := mul_le_mul_of_nonneg_right (show 1 - eps ≤ 1 by linarith)
    (abs_nonneg (x1 - v1))
  unfold comparisonAdjustedTreated
  by_cases hl : x1 ≤ eps * (x0 + x1)
  · rw [max_eq_left hl, min_eq_right hends, abs_of_nonneg (by linarith)]
    nlinarith
  · rw [max_eq_right (le_of_not_ge hl)]
    by_cases hu : (1 - eps) * (x0 + x1) ≤ x1
    · rw [min_eq_left hu, abs_of_nonpos (by linarith)]
      nlinarith
    · rw [min_eq_right (le_of_not_ge hu), sub_self, abs_zero]
      positivity

/-- [Under the stated inputs and conditions](hyp:d,eps,heps,heps',j,hx0,hx1,hlo,hhi,x,v), Both entries together incur at most three times their original L¹ error.  This gives [the stated result](goal).-/
-- @node: comparisonAdjustedTable_cell_error
lemma comparisonAdjustedTable_cell_error {d : Nat} (eps : Real) (x v : AuxTable d)
    (heps : 0 ≤ eps) (heps' : eps ≤ 1 / 2) (j : Fin d)
    (hx0 : 0 ≤ x (j, false)) (hx1 : 0 ≤ x (j, true))
    (hlo : eps * (v (j, false) + v (j, true)) ≤ v (j, true))
    (hhi : v (j, true) ≤ (1 - eps) * (v (j, false) + v (j, true))) :
    |comparisonAdjustedTable eps x (j, false) - v (j, false)| +
      |comparisonAdjustedTable eps x (j, true) - v (j, true)| ≤
      3 * (|x (j, false) - v (j, false)| + |x (j, true) - v (j, true)|) := by
  let h := comparisonAdjustedTreated eps (x (j, false)) (x (j, true))
  have hmove : |h - x (j, true)| ≤
      |x (j, false) - v (j, false)| + |x (j, true) - v (j, true)| :=
    comparisonAdjustedTreated_movement eps _ _ _ _ heps (by linarith) hlo hhi (by
      nlinarith)
  have hcontrol : |x (j, false) + x (j, true) - h - v (j, false)| ≤
      |x (j, false) - v (j, false)| + |h - x (j, true)| := by
    calc
      _ = |(x (j, false) - v (j, false)) + -(h - x (j, true))| := by congr 1; ring
      _ ≤ |x (j, false) - v (j, false)| + |-(h - x (j, true))| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have htreated : |h - v (j, true)| ≤ |h - x (j, true)| + |x (j, true) - v (j, true)| :=
    abs_sub_le h (x (j, true)) (v (j, true))
  change |x (j, false) + x (j, true) - h - v (j, false)| + |h - v (j, true)| ≤ _
  linarith

/-- [Under the stated inputs and conditions](hyp:d,eps,heps,heps',hx,hlo,hhi,x,v), Summing the cell bounds gives the factor-three table adjustment estimate in the roadmap.  This gives [the stated result](goal).-/
-- @node: comparisonAdjustedTable_l1_error
lemma comparisonAdjustedTable_l1_error {d : Nat} (eps : Real) (x v : AuxTable d)
    (heps : 0 ≤ eps) (heps' : eps ≤ 1 / 2) (hx : ∀ z, 0 ≤ x z)
    (hlo : ∀ j, eps * (v (j, false) + v (j, true)) ≤ v (j, true))
    (hhi : ∀ j, v (j, true) ≤ (1 - eps) * (v (j, false) + v (j, true))) :
    (∑ z : AuxObs d, |comparisonAdjustedTable eps x z - v z|) ≤
      3 * ∑ z : AuxObs d, |x z - v z| := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simpa only [add_comm] using comparisonAdjustedTable_cell_error eps x v heps heps' j
    (hx _) (hx _) (hlo j) (hhi j)

/-- [Under the stated inputs and conditions](hyp:d,eps,x,heps,heps',hx), Nonnegative input coordinates remain nonnegative after adjustment.  This gives [the stated result](goal).-/
-- @node: comparisonAdjustedTable_nonneg
lemma comparisonAdjustedTable_nonneg {d : Nat} (eps : Real) (x : AuxTable d)
    (heps : 0 ≤ eps) (heps' : eps ≤ 1 / 2) (hx : ∀ z, 0 ≤ x z) :
    ∀ z, 0 ≤ comparisonAdjustedTable eps x z := by
  intro ⟨j, a⟩
  obtain ⟨hlo, hhi⟩ := comparisonAdjustedTreated_bounds eps (x (j, false)) (x (j, true))
    heps heps' (hx _) (hx _)
  have hp : 0 ≤ x (j, false) + x (j, true) := add_nonneg (hx _) (hx _)
  cases a <;> simp only [comparisonAdjustedTable, Bool.false_eq_true, if_false, if_true]
  · nlinarith
  · exact (mul_nonneg heps hp).trans hlo

/-- [Under the stated inputs and conditions](hyp:d,eps,x,hsum), A normalized empirical table stays normalized.  This gives [the stated result](goal).-/
-- @node: comparisonAdjustedTable_sum
lemma comparisonAdjustedTable_sum {d : Nat} (eps : Real) (x : AuxTable d)
    (hsum : ∑ z, x z = 1) : ∑ z, comparisonAdjustedTable eps x z = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool] at hsum ⊢
  simpa only [add_comm, comparisonAdjustedTable_cell_sum] using hsum

/-- [Under the stated inputs and conditions](hyp:d,eps,x,heps,heps',hx,j), The adjusted table satisfies both arm overlap inequalities, including at null cells.  This gives [the stated result](goal).-/
-- @node: comparisonAdjustedTable_overlap
lemma comparisonAdjustedTable_overlap {d : Nat} (eps : Real) (x : AuxTable d)
    (heps : 0 ≤ eps) (heps' : eps ≤ 1 / 2) (hx : ∀ z, 0 ≤ x z) (j : Fin d) :
    eps * (comparisonAdjustedTable eps x (j, false) + comparisonAdjustedTable eps x (j, true)) ≤
      comparisonAdjustedTable eps x (j, true) ∧
    comparisonAdjustedTable eps x (j, true) ≤ (1 - eps) *
      (comparisonAdjustedTable eps x (j, false) + comparisonAdjustedTable eps x (j, true)) := by
  rw [comparisonAdjustedTable_cell_sum]
  exact comparisonAdjustedTreated_bounds eps (x (j, false)) (x (j, true))
    heps heps' (hx _) (hx _)

/-- [Under the stated inputs and conditions](hyp:d,eps,v,hlo,hhi), A legal input table is fixed by the adjustment.  This gives [the stated result](goal).-/
-- @node: comparisonAdjustedTable_eq_self
lemma comparisonAdjustedTable_eq_self {d : Nat} (eps : Real) (v : AuxTable d)
    (hlo : ∀ j, eps * (v (j, false) + v (j, true)) ≤ v (j, true))
    (hhi : ∀ j, v (j, true) ≤ (1 - eps) * (v (j, false) + v (j, true))) :
    comparisonAdjustedTable eps v = v := by
  funext ⟨j, a⟩
  have ht : comparisonAdjustedTreated eps (v (j, false)) (v (j, true)) = v (j, true) := by
    rw [comparisonAdjustedTreated, max_eq_right (hlo j), min_eq_right (hhi j)]
  cases a <;> simp [comparisonAdjustedTable, ht]

/-- [Under the stated inputs and conditions](hyp:d,eps,P,hP,j), The population marginal has exactly the legal overlap bounds used in the L¹ estimate.  This gives [the stated result](goal).-/
-- @node: comparison_population_table_overlap
lemma comparison_population_table_overlap {d : Nat} (eps : Real) (P : DiscreteLaw d)
    (hP : ModelClass d eps P) (j : Fin d) :
    eps * (auxTable P (j, false) + auxTable P (j, true)) ≤ auxTable P (j, true) ∧
    auxTable P (j, true) ≤ (1 - eps) * (auxTable P (j, false) + auxTable P (j, true)) := by
  have ht := armMass_ge_overlap_cellMass P eps hP j true
  have hc := armMass_ge_overlap_cellMass P eps hP j false
  have hp : armMass P j false + armMass P j true = cellMass P j := by
    simp [cellMass, armMass, add_comm]
  simp only [auxTable, auxMarginal_toReal_armMass, hp]
  exact ⟨ht, by linarith⟩

/-- Auxiliary records determine the adjusted empirical table without using labeled data. -/
-- @node: comparisonEmpiricalTable
noncomputable def comparisonEmpiricalTable {m d : Nat} (eps : Real) (hm : 0 < m)
    (V : Fin m → AuxObs d) : AuxTable d :=
  comparisonAdjustedTable eps
    (Causalean.Stat.Minimax.FiniteSideInformation.empiricalFrequency (AuxObs d) hm V)

/-- [Under the stated hypotheses](hyp:hm), the adjusted empirical table is a total Borel function of the auxiliary array. This gives [the stated conclusion](goal). -/
@[fun_prop]
-- @node: comparisonEmpiricalTable_measurable
lemma comparisonEmpiricalTable_measurable (m d : Nat) (eps : Real) (hm : 0 < m) :
    Measurable (comparisonEmpiricalTable (d := d) eps hm) := by
  exact measurable_of_countable _

/-- [Under the stated inputs and conditions](hyp:eps,hm,hd,heps,heps',V,m,d), Empirical adjustment preserves positivity and the normalization to a probability table.  This gives [the stated result](goal).-/
-- @node: comparisonEmpiricalTable_probability
lemma comparisonEmpiricalTable_probability {m d : Nat} (eps : Real) (hm : 0 < m)
    (hd : 2 ≤ d) (heps : 0 ≤ eps) (heps' : eps ≤ 1 / 2) (V : Fin m → AuxObs d) :
    (∀ z, 0 ≤ comparisonEmpiricalTable eps hm V z) ∧
      (∑ z, comparisonEmpiricalTable eps hm V z) = 1 := by
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  exact ⟨comparisonAdjustedTable_nonneg eps _ heps heps'
    (Causalean.Stat.Minimax.FiniteSideInformation.empiricalFrequency_nonneg _ hm V),
    comparisonAdjustedTable_sum eps _
      (Causalean.Stat.Minimax.FiniteSideInformation.sum_empiricalFrequency _ hm V)⟩

/-- [Under the stated inputs and conditions](hyp:eps,hm,heps,heps',V,j,m,d), The adjusted empirical table belongs to the legal marginal set.  This gives [the stated result](goal).-/
-- @node: comparisonEmpiricalTable_overlap
lemma comparisonEmpiricalTable_overlap {m d : Nat} (eps : Real) (hm : 0 < m)
    (heps : 0 ≤ eps) (heps' : eps ≤ 1 / 2) (V : Fin m → AuxObs d) (j : Fin d) :
    eps * (comparisonEmpiricalTable eps hm V (j, false) +
      comparisonEmpiricalTable eps hm V (j, true)) ≤
      comparisonEmpiricalTable eps hm V (j, true) ∧
    comparisonEmpiricalTable eps hm V (j, true) ≤ (1 - eps) *
      (comparisonEmpiricalTable eps hm V (j, false) +
        comparisonEmpiricalTable eps hm V (j, true)) := by
  exact comparisonAdjustedTable_overlap eps _ heps heps'
    (Causalean.Stat.Minimax.FiniteSideInformation.empiricalFrequency_nonneg _ hm V) j

/-- [Under the stated inputs and conditions](hyp:eps,hm,heps,heps',P,hP,V,m,d), The data-only legal adjustment costs at most three times the raw empirical L¹ error.  This gives [the stated result](goal).-/
-- @node: comparisonEmpiricalTable_l1_error
lemma comparisonEmpiricalTable_l1_error {m d : Nat} (eps : Real) (hm : 0 < m)
    (heps : 0 ≤ eps) (heps' : eps ≤ 1 / 2) (P : DiscreteLaw d)
    (hP : ModelClass d eps P) (V : Fin m → AuxObs d) :
    (∑ z : AuxObs d, |comparisonEmpiricalTable eps hm V z - auxTable P z|) ≤
      3 * ∑ z : AuxObs d,
        |Causalean.Stat.Minimax.FiniteSideInformation.empiricalFrequency (AuxObs d) hm V z -
          auxTable P z| := by
  exact comparisonAdjustedTable_l1_error eps _ _ heps heps'
    (Causalean.Stat.Minimax.FiniteSideInformation.empiricalFrequency_nonneg _ hm V)
    (fun j => (comparison_population_table_overlap eps P hP j).1)
    (fun j => (comparison_population_table_overlap eps P hP j).2)

/-- [Under the stated inputs and conditions](hyp:hm,V,z,m,d), The library's empirical mass and the empirical-frequency table agree.  This gives [the stated result](goal).-/
-- @node: comparisonEmpiricalFrequency_eq_mass
lemma comparisonEmpiricalFrequency_eq_mass {m d : Nat} (hm : 0 < m)
    (V : Fin m → AuxObs d) (z : AuxObs d) :
    Causalean.Stat.Minimax.FiniteSideInformation.empiricalFrequency (AuxObs d) hm V z =
      Causalean.Stat.empiricalMass V z := by
  classical
  simp only [Causalean.Stat.Minimax.FiniteSideInformation.empiricalFrequency,
    Causalean.Stat.empiricalMass, div_eq_mul_inv, mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

/-- [Under the stated inputs and conditions](hyp:hm,P,z,m,d), Each empirical marginal coordinate has the exact binomial mean squared error.  This gives [the stated result](goal).-/
-- @node: comparisonEmpiricalFrequency_mse
lemma comparisonEmpiricalFrequency_mse {m d : Nat} (hm : 0 < m)
    (P : DiscreteLaw d) (z : AuxObs d) :
    (∫ V, (Causalean.Stat.Minimax.FiniteSideInformation.empiricalFrequency
      (AuxObs d) hm V z - auxTable P z) ^ 2 ∂auxProductLaw P m) =
      (auxTable P z - (auxTable P z) ^ 2) / m := by
  classical
  let μ := (auxMarginal P).toMeasure
  let : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let : IsProbabilityMeasure (auxProductLaw P m) := by
    unfold auxProductLaw; infer_instance
  have hatom : μ.real {z} = auxTable P z := by
    simp [μ, auxTable, measureReal_def]
  have hmean := Causalean.Stat.integral_empiricalMass μ hm z (measurableSet_singleton z)
  have hsecond := Causalean.Stat.integral_empiricalMass_sq μ hm z
    (measurableSet_singleton z)
  rw [hatom] at hmean hsecond
  change (∫ V, _ ∂Measure.pi (fun _ : Fin m => μ)) = _ at hmean hsecond
  simp_rw [comparisonEmpiricalFrequency_eq_mass]
  have hexpand : (fun V : Fin m → AuxObs d =>
      (Causalean.Stat.empiricalMass V z - auxTable P z) ^ 2) =
      fun V => Causalean.Stat.empiricalMass V z ^ 2 -
        2 * auxTable P z * Causalean.Stat.empiricalMass V z + (auxTable P z) ^ 2 := by
    funext V; ring
  rw [hexpand]
  have hi : Integrable (fun V : Fin m → AuxObs d =>
      Causalean.Stat.empiricalMass V z ^ 2 -
        2 * auxTable P z * Causalean.Stat.empiricalMass V z) (auxProductLaw P m) :=
    Integrable.of_finite
  have hi2 : Integrable (fun V : Fin m → AuxObs d =>
      Causalean.Stat.empiricalMass V z ^ 2) (auxProductLaw P m) := Integrable.of_finite
  have hi1 : Integrable (fun V : Fin m → AuxObs d =>
      2 * auxTable P z * Causalean.Stat.empiricalMass V z) (auxProductLaw P m) :=
    Integrable.of_finite
  integral_linearity
  change (∫ V, Causalean.Stat.empiricalMass V z ^ 2 ∂Measure.pi (fun _ : Fin m => μ)) -
    2 * auxTable P z * (∫ V, Causalean.Stat.empiricalMass V z
      ∂Measure.pi (fun _ : Fin m => μ)) + _ = _
  rw [hmean, hsecond]
  simp only [integral_const, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul,
    measureReal_def]
  ring

/-- [Under the stated inputs and conditions](hyp:d,x,v), The squared L¹ error is controlled by the sum of squared coordinate errors.  This gives [the stated result](goal).-/
-- @node: comparisonTable_l1_sq_le
lemma comparisonTable_l1_sq_le {d : Nat} (x v : AuxTable d) :
    (∑ z : AuxObs d, |x z - v z|) ^ 2 ≤
      (2 * (d : Real)) * ∑ z : AuxObs d, (x z - v z) ^ 2 := by
  simpa [AuxObs, Fintype.card_prod, sq_abs, mul_comm] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun z : AuxObs d => |x z - v z|))

/-- [Under the stated inputs and conditions](hyp:hm,P,d,m), The empirical marginal's expected squared L¹ error is at most alphabet size over budget.  This gives [the stated result](goal).-/
-- @node: comparisonEmpiricalFrequency_l1_sq
lemma comparisonEmpiricalFrequency_l1_sq {m d : Nat} (hm : 0 < m)
    (P : DiscreteLaw d) :
    (∫ V, (∑ z : AuxObs d,
      |Causalean.Stat.Minimax.FiniteSideInformation.empiricalFrequency (AuxObs d) hm V z -
        auxTable P z|) ^ 2 ∂auxProductLaw P m) ≤ 2 * (d : Real) / m := by
  let : IsProbabilityMeasure (auxProductLaw P m) := by
    unfold auxProductLaw; infer_instance
  have hsum : ∑ z : AuxObs d, auxTable P z = 1 := by
    simpa [auxTable] using
      (PMF.integral_eq_sum (auxMarginal P) (fun _ => (1 : Real))).symm
  calc
    _ ≤ ∫ V, (2 * (d : Real)) * ∑ z : AuxObs d,
        (Causalean.Stat.Minimax.FiniteSideInformation.empiricalFrequency (AuxObs d) hm V z -
          auxTable P z) ^ 2 ∂auxProductLaw P m :=
      integral_mono Integrable.of_finite Integrable.of_finite
        (fun V => comparisonTable_l1_sq_le _ _)
    _ = (2 * (d : Real)) * ∑ z : AuxObs d,
        (auxTable P z - (auxTable P z) ^ 2) / m := by
      rw [integral_const_mul, integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
      simp_rw [comparisonEmpiricalFrequency_mse hm]
    _ ≤ (2 * (d : Real)) * ∑ z : AuxObs d, auxTable P z / m := by
      gcongr with z
      exact sub_le_self _ (sq_nonneg _)
    _ = 2 * (d : Real) / m := by rw [← Finset.sum_div, hsum]; ring

/-- [Under the stated inputs and conditions](hyp:hm,P,d,m), Nonnegative variance converts the squared L¹ bound into its expected-error bound.  This gives [the stated result](goal).-/
-- @node: comparisonEmpiricalFrequency_expected_l1
lemma comparisonEmpiricalFrequency_expected_l1 {m d : Nat} (hm : 0 < m)
    (P : DiscreteLaw d) :
    (∫ V, ∑ z : AuxObs d,
      |Causalean.Stat.Minimax.FiniteSideInformation.empiricalFrequency (AuxObs d) hm V z -
        auxTable P z| ∂auxProductLaw P m) ≤ Real.sqrt (2 * (d : Real) / m) := by
  let : IsProbabilityMeasure (auxProductLaw P m) := by
    unfold auxProductLaw; infer_instance
  let W := fun V : Fin m → AuxObs d => ∑ z : AuxObs d,
    |Causalean.Stat.Minimax.FiniteSideInformation.empiricalFrequency (AuxObs d) hm V z -
      auxTable P z|
  have hW : MemLp W 2 (auxProductLaw P m) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 Integrable.of_finite
  have hv := variance_nonneg W (auxProductLaw P m)
  rw [variance_eq_sub hW] at hv
  have hsecond := comparisonEmpiricalFrequency_l1_sq hm P
  change (∫ V, W V ^ 2 ∂auxProductLaw P m) ≤ _ at hsecond
  have hmean : (∫ V, W V ∂auxProductLaw P m) ^ 2 ≤ 2 * (d : Real) / m := by
    calc
      _ ≤ ∫ V, W V ^ 2 ∂auxProductLaw P m := by
        simpa only [Pi.pow_apply] using (sub_nonneg.mp hv)
      _ ≤ _ := hsecond
  exact Real.le_sqrt_of_sq_le hmean

/-- [Under the stated inputs and conditions](hyp:eps,hm,heps,heps',P,hP,d,m), The legal empirical table has expected L¹ error at most three times the iid square-root rate.  This gives [the stated result](goal).-/
-- @node: comparisonEmpiricalTable_expected_l1
lemma comparisonEmpiricalTable_expected_l1 {m d : Nat} (eps : Real) (hm : 0 < m)
    (heps : 0 ≤ eps) (heps' : eps ≤ 1 / 2) (P : DiscreteLaw d)
    (hP : ModelClass d eps P) :
    (∫ V, ∑ z : AuxObs d,
      |comparisonEmpiricalTable eps hm V z - auxTable P z| ∂auxProductLaw P m) ≤
      3 * Real.sqrt (2 * (d : Real) / m) := by
  let : IsProbabilityMeasure (auxProductLaw P m) := by
    unfold auxProductLaw; infer_instance
  calc
    _ ≤ ∫ V, 3 * ∑ z : AuxObs d,
        |Causalean.Stat.Minimax.FiniteSideInformation.empiricalFrequency (AuxObs d) hm V z -
          auxTable P z| ∂auxProductLaw P m :=
      integral_mono Integrable.of_finite Integrable.of_finite
        (comparisonEmpiricalTable_l1_error eps hm heps heps' P hP)
    _ = 3 * (∫ V, ∑ z : AuxObs d,
        |Causalean.Stat.Minimax.FiniteSideInformation.empiricalFrequency (AuxObs d) hm V z -
          auxTable P z| ∂auxProductLaw P m) := by rw [integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (comparisonEmpiricalFrequency_expected_l1 hm P)
      (by norm_num)

end CausalSmith.Stat.AnnotationRarearmFrontier
