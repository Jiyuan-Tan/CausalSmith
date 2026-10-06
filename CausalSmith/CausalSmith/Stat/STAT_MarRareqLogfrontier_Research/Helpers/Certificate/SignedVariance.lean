module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.CrossCellIndependence

/-! Cross-cell independence assembles the signed raw variance and the active
ideal risk bound in roadmap (20)--(24), retaining random membership weights. -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P), [the stated mathematical conclusion holds](goal). -/
-- @node: variance_poissonRawMixedValue_eq_four_sum
lemma variance_poissonRawMixedValue_eq_four_sum (n d : ℕ) (q : ℝ) (P : FullLaw d) :
    variance (poissonRawMixedValue n d q)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) =
    4 * ∑ j : Cell d, variance (fun s ↦ poissonMemberWeight n j s *
      poissonSelectedCellEstimate n d q j s)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  classical
  let μ := finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)
  let X (j : Cell d) := fun s ↦ poissonMemberWeight n j s *
    poissonSelectedCellEstimate n d q j s
  let Z (j : Cell d) := fun s ↦ armSign j.1 * X j s
  have hZ (j : Cell d) : MemLp (Z j) 2 μ :=
    (memLp_poissonMemberWeight_mul_selectedCellEstimate n d q P j).const_mul _
  have hi : Set.Pairwise (↑(Finset.univ : Finset (Cell d)))
      (fun i j ↦ IndepFun (Z i) (Z j) μ) := by
    intro i _ j _ hij
    exact (indepFun_memberWeight_mul_selectedCellEstimate n d q P hij).comp
      (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
  have hv := IndepFun.variance_sum (fun j _ ↦ hZ j) hi
  have hsign (j : Cell d) : armSign j.1 ^ 2 = 1 := by
    cases j.1 <;> norm_num [armSign]
  change variance (fun s ↦ 2 * ∑ j : Cell d, armSign j.1 *
    poissonMemberWeight n j s * poissonSelectedCellEstimate n d q j s) μ = _
  have heq : (fun s ↦ ∑ j : Cell d, armSign j.1 *
      poissonMemberWeight n j s * poissonSelectedCellEstimate n d q j s) =
      ∑ j : Cell d, Z j := by
    funext s
    simp only [Finset.sum_apply, Z, X, mul_assoc]
  rw [variance_const_mul, heq]
  rw [hv]
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change variance (fun s ↦ armSign j.1 * X j s) μ = _
  rw [variance_const_mul, hsign, one_mul]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: variance_poissonRawMixedValue_le_active_budget
lemma variance_poissonRawMixedValue_le_active_budget (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) (hb : needleBranch n d q) :
    variance (poissonRawMixedValue n d q)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
    8 * (4 / streamEffectiveSize n q + 1 / streamSize n) +
      64 * d * (Real.exp (logScale n q / 8) + 1) *
        (needleRadius n q ^ 2 / streamEffectiveSize n q ^ 2 +
          needleRadius n q / (streamSize n * streamEffectiveSize n q)) +
      32 * Real.exp (-32 * logScale n q) * (1 + 1 / streamSize n) := by
  rw [variance_poissonRawMixedValue_eq_four_sum]
  exact four_sum_variance_memberWeight_mul_selectedCellEstimate_le n d q P hP hb

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,hb,hlarge), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_sq_poissonAuxiliaryMixedValue_le_active_budget
lemma integral_sq_poissonAuxiliaryMixedValue_le_active_budget
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) (hb : needleBranch n d q)
    (hlarge : ¬ effectiveSize n q ≤ 1) :
    (∫ s, (poissonAuxiliaryMixedValue n d q s - cellFunctional P) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
    (2 * (4 * d * needleRadius n q /
      (streamEffectiveSize n q * (needleDegree n q : ℝ)^2) +
      3 * Real.exp (-16 * logScale n q))) ^ 2 +
    (8 * (4 / streamEffectiveSize n q + 1 / streamSize n) +
      64 * d * (Real.exp (logScale n q / 8) + 1) *
        (needleRadius n q ^ 2 / streamEffectiveSize n q ^ 2 +
          needleRadius n q / (streamSize n * streamEffectiveSize n q)) +
      32 * Real.exp (-32 * logScale n q) * (1 + 1 / streamSize n)) := by
  have hr := integral_sq_poissonAuxiliaryMixedValue_le_variance_add_active_bias_sq
    n d q P hP hb hlarge
  have hv := variance_poissonRawMixedValue_le_active_budget n d q P hP hb
  exact hr.trans (by linarith)

end CausalSmith.Stat.MarRareqLogfrontier
