module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.RatioSecondMoment
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.CellIntensity
public import Mathlib.Probability.Moments.Variance

/-! Null-cell completion and variance bounds for roadmap (15). -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j,hzero), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_sq_markedPoissonRatioBranch_of_zero
lemma integral_sq_markedPoissonRatioBranch_of_zero (n d : ℕ) (P : FullLaw d)
    (j : Cell d) (hzero : arrivedCell P j = 0) :
    (∫ s, (poissonRatioBranch j s) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) = 0 := by
  have hint : Integrable (poissonRatioBranch j)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
    apply Integrable.of_bound (measurable_poissonRatioBranch j).aestronglyMeasurable 1
    filter_upwards [] with s
    rcases poissonRatioBranch_mem_unitInterval j s with ⟨hs0, hs1⟩
    simpa [Real.norm_eq_abs, abs_of_nonneg hs0] using hs1
  apply le_antisymm _ (integral_nonneg fun s ↦ sq_nonneg _)
  calc
    _ ≤ ∫ s, poissonRatioBranch j s
        ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2) := by
      apply integral_mono (integrable_poissonRatioBranch_sq n d P j) hint
      intro s
      rcases poissonRatioBranch_mem_unitInterval j s with ⟨hs0, hs1⟩
      nlinarith
    _ = 0 := integral_markedPoissonRatioBranch_of_zero n d P j hzero

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: markedPoissonRatioBranch_centered_secondMoment_le
lemma markedPoissonRatioBranch_centered_secondMoment_le
    (n d : ℕ) (P : FullLaw d) (j : Cell d) :
    (∫ s, (poissonRatioBranch j s - cellMean P j) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      4 / (1 + streamSize n * arrivedCell P j) := by
  by_cases hpos : 0 < arrivedCell P j
  · exact integral_sq_markedPoissonRatioBranch_sub_cellMean_le n d P j hpos
  · have hzero : arrivedCell P j = 0 :=
      le_antisymm (le_of_not_gt hpos) measureReal_nonneg
    simp only [cellMean, hpos, if_false, sub_zero]
    rw [integral_sq_markedPoissonRatioBranch_of_zero n d P j hzero, hzero]
    norm_num

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: markedPoissonRatioBranch_variance_le
lemma markedPoissonRatioBranch_variance_le
    (n d : ℕ) (P : FullLaw d) (j : Cell d) :
    variance (poissonRatioBranch j)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      4 / (1 + streamSize n * arrivedCell P j) := by
  have hm := (measurable_poissonRatioBranch j).aestronglyMeasurable
    (μ := finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2))
  calc
    _ = variance (fun s ↦ poissonRatioBranch j s - cellMean P j)
        (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) :=
      (variance_sub_const hm (cellMean P j)).symm
    _ ≤ ∫ s, (poissonRatioBranch j s - cellMean P j) ^ 2
        ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2) :=
      variance_le_expectation_sq (hm.sub aestronglyMeasurable_const)
    _ ≤ _ := markedPoissonRatioBranch_centered_secondMoment_le n d P j

/-- Given [the probability law](hyp:P), [the cell probabilities sum to one](goal). -/
-- @node: sum_cellProb_eq_one
lemma sum_cellProb_eq_one (P : FullLaw d) :
    (∑ j : Cell d, cellProb P j) = 1 := by
  classical
  letI : IsProbabilityMeasure P.1 := P.2
  have h := sum_measureReal_preimage_singleton (μ := P.1)
    (Finset.univ : Finset (Cell d))
    (f := fun r : FullRecord d ↦ (r.A, r.X, r.S)) (by intro; simp)
  have heq (j : Cell d) : {r : FullRecord d | inCell r j} =
      (fun r : FullRecord d ↦ (r.A, r.X, r.S)) ⁻¹' {j} := by
    ext r
    simp [inCell, Prod.ext_iff]
  simpa [cellProb, heq] using h

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,j), [the stated mathematical conclusion holds](goal). -/
-- @node: cellProb_sq_div_one_add_intensity_le
lemma cellProb_sq_div_one_add_intensity_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) (j : Cell d) :
    (cellProb P j) ^ 2 / (1 + streamSize n * arrivedCell P j) ≤
      cellProb P j / streamEffectiveSize n q := by
  have hm : 0 < streamSize n := by
    unfold streamSize
    have hn : 0 < (n : ℝ) := by exact_mod_cast hP.n_pos
    positivity
  have hN : 0 < streamEffectiveSize n q := by
    unfold streamEffectiveSize
    exact mul_pos hm hP.q_pos
  have hp : 0 ≤ cellProb P j := measureReal_nonneg
  have ht : 0 ≤ streamSize n * arrivedCell P j := mul_nonneg hm.le measureReal_nonneg
  have hlo := streamEffectiveSize_mul_cellProb_le_arrivedStreamIntensity
    n d q P hP 2 j
  rw [coe_arrivedStreamIntensity] at hlo
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + streamSize n * arrivedCell P j) hN).2
  have hmul := mul_le_mul_of_nonneg_left hlo hp
  nlinarith

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP), [the stated mathematical conclusion holds](goal). -/
-- @node: sum_cellProb_sq_mul_ratioVariance_le
lemma sum_cellProb_sq_mul_ratioVariance_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) :
    (∑ j : Cell d, (cellProb P j) ^ 2 * variance (poissonRatioBranch j)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2))) ≤
      4 / streamEffectiveSize n q := by
  calc
    _ ≤ ∑ j : Cell d, 4 * (cellProb P j / streamEffectiveSize n q) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ ≤ (cellProb P j) ^ 2 * (4 / (1 + streamSize n * arrivedCell P j)) :=
          mul_le_mul_of_nonneg_left (markedPoissonRatioBranch_variance_le n d P j)
            (sq_nonneg _)
        _ = 4 * ((cellProb P j) ^ 2 / (1 + streamSize n * arrivedCell P j)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (cellProb_sq_div_one_add_intensity_le n d q P hP j) (by norm_num)
    _ = _ := by
      rw [← Finset.mul_sum, ← Finset.sum_div, sum_cellProb_eq_one]
      ring

end CausalSmith.Stat.MarRareqLogfrontier
