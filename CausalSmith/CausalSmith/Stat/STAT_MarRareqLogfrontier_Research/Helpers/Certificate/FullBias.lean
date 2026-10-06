module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.HeavyBias
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.PilotBiasBounds

/-! Assembly of the light and heavy needle biases and the complementary pilot
term into the signed bias bound in roadmap (20). -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment
attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: abs_sum_pilot_needle_bias_le
lemma abs_sum_pilot_needle_bias_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) (hb : needleBranch n d q) :
    |2 * ∑ j : Cell d, armSign j.1 * cellProb P j * cellMean P j *
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
        {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} *
      (chebNeedle n d q).eval (streamSize n * arrivedCell P j)| ≤
      8 * d * needleRadius n q /
        (streamEffectiveSize n q * (needleDegree n q : ℝ)^2) +
      4 * Real.exp (-16 * logScale n q) := by
  classical
  let f : Cell d → ℝ := fun j ↦ armSign j.1 * cellProb P j * cellMean P j *
    (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
      {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} *
    (chebNeedle n d q).eval (streamSize n * arrivedCell P j)
  have hsplit : (∑ j : Cell d, f j) =
      (∑ j ∈ (Finset.univ : Finset (Cell d)).filter
        (fun j ↦ streamSize n * arrivedCell P j ≤ needleRadius n q), f j) +
      (∑ j ∈ (Finset.univ : Finset (Cell d)).filter
        (fun j ↦ needleRadius n q < streamSize n * arrivedCell P j), f j) := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : streamSize n * arrivedCell P j ≤ needleRadius n q
    · simp [hj, not_lt.mpr hj]
    · simp [hj, lt_of_not_ge hj]
  have hl := abs_sum_light_pilot_needle_bias_le n d q P hP hb
    (fun j ↦ (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
      {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4})
    (fun _ ↦ ⟨measureReal_nonneg, measureReal_le_one⟩)
  have hh := abs_sum_heavy_pilot_needle_bias_le n d q P hb
  change |2 * ∑ j : Cell d, f j| ≤ _
  rw [hsplit, mul_add]
  exact (abs_add_le _ _).trans (add_le_add hl hh)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: abs_sum_markedPoissonSelectedCellEstimate_bias_le
lemma abs_sum_markedPoissonSelectedCellEstimate_bias_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) (hb : needleBranch n d q) :
    |2 * ∑ j : Cell d, armSign j.1 * cellProb P j *
      ((∫ s, poissonSelectedCellEstimate n d q j s
        ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) - cellMean P j)| ≤
      2 * (4 * d * needleRadius n q /
        (streamEffectiveSize n q * (needleDegree n q : ℝ)^2) +
        3 * Real.exp (-16 * logScale n q)) := by
  classical
  let f : Cell d → ℝ := fun j ↦ armSign j.1 * cellProb P j * cellMean P j *
    (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
      {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} *
    (chebNeedle n d q).eval (streamSize n * arrivedCell P j)
  let g : Cell d → ℝ := fun j ↦ armSign j.1 * cellProb P j * cellMean P j *
    (1 - (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
      {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4}) *
    Real.exp (-(streamSize n * arrivedCell P j))
  have heq : (2 * ∑ j : Cell d, armSign j.1 * cellProb P j *
      ((∫ s, poissonSelectedCellEstimate n d q j s
        ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) - cellMean P j)) =
      -(2 * ∑ j : Cell d, f j) - (2 * ∑ j : Cell d, g j) := by
    have hj (j : Cell d) : armSign j.1 * cellProb P j *
        ((∫ s, poissonSelectedCellEstimate n d q j s
          ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) - cellMean P j) =
        -f j - g j := by
      rw [markedPoissonSelectedCellEstimate_bias n d q P j hb]
      dsimp [f, g]
      ring
    simp_rw [hj]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    ring
  have hf := abs_sum_pilot_needle_bias_le n d q P hP hb
  have hg := abs_sum_pilot_heavy_exp_bias_le n d q P hb
  rw [heq]
  calc
    _ ≤ |2 * ∑ j : Cell d, f j| + |2 * ∑ j : Cell d, g j| := by
      simpa only [abs_neg] using abs_sub (-(2 * ∑ j : Cell d, f j))
        (2 * ∑ j : Cell d, g j)
    _ ≤ (8 * d * needleRadius n q /
        (streamEffectiveSize n q * (needleDegree n q : ℝ)^2) +
        4 * Real.exp (-16 * logScale n q)) +
        2 * Real.exp (-16 * logScale n q) := add_le_add hf hg
    _ = _ := by ring

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: memLp_poissonMemberWeight_mul_selectedCellEstimate
lemma memLp_poissonMemberWeight_mul_selectedCellEstimate
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d) :
    MemLp (fun s ↦ poissonMemberWeight n j s * poissonSelectedCellEstimate n d q j s) 2
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  have h := (memLp_poissonMemberWeight_mul_ratioBranch n d P j).add
    (memLp_poissonMemberWeight_mul_selectedCorrection n d q P j)
  convert h using 1
  funext s
  simp only [Pi.add_apply]
  ring

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hn), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_poissonMemberWeight_mul_selectedCellEstimate
lemma integral_poissonMemberWeight_mul_selectedCellEstimate
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d) (hn : 0 < n) :
    (∫ s, poissonMemberWeight n j s * poissonSelectedCellEstimate n d q j s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) =
    cellProb P j * (∫ s, poissonSelectedCellEstimate n d q j s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  have hD := (memLp_poissonRatioBranch n d P j).integrable (by norm_num)
  have hC := (memLp_poissonSelectedCellEstimate_sub_ratio n d q P j).integrable
    (by norm_num)
  have hWD := (memLp_poissonMemberWeight_mul_ratioBranch n d P j).integrable
    (by norm_num)
  have hWC := (memLp_poissonMemberWeight_mul_selectedCorrection n d q P j).integrable
    (by norm_num)
  have hmeanD := (indepFun_poissonMemberWeight_ratioBranch n d P j).integral_fun_mul_eq_mul_integral
      (measurable_poissonMemberWeight n d j).aestronglyMeasurable
      (measurable_poissonRatioBranch j).aestronglyMeasurable
  have hiC := indepFun_poissonMemberWeight_selectedCorrection n d q P j
  have hmeanC := hiC.integral_fun_mul_eq_mul_integral
      (measurable_poissonMemberWeight n d j).aestronglyMeasurable
      ((measurable_poissonSelectedCellEstimate n d q j).sub
        (measurable_poissonRatioBranch j)).aestronglyMeasurable
  have heq : (fun s ↦ poissonMemberWeight n j s * poissonSelectedCellEstimate n d q j s) =
      (fun s ↦ poissonMemberWeight n j s * poissonRatioBranch j s +
        poissonMemberWeight n j s *
          (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s)) := by
    funext s
    ring
  have hGeq : (fun s ↦ poissonRatioBranch j s +
      (poissonSelectedCellEstimate n d q j s - poissonRatioBranch j s)) =
      poissonSelectedCellEstimate n d q j := by
    funext s
    ring
  rw [heq, integral_add hWD hWC, hmeanD, hmeanC,
    integral_poissonMemberWeight n d P j hn]
  rw [← mul_add, ← integral_add hD hC, hGeq]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: abs_integral_raw_poissonSelected_estimator_bias_le
lemma abs_integral_raw_poissonSelected_estimator_bias_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) (hb : needleBranch n d q) :
    |(∫ s, 2 * ∑ j : Cell d, armSign j.1 * poissonMemberWeight n j s *
        poissonSelectedCellEstimate n d q j s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) - cellFunctional P| ≤
      2 * (4 * d * needleRadius n q /
        (streamEffectiveSize n q * (needleDegree n q : ℝ)^2) +
        3 * Real.exp (-16 * logScale n q)) := by
  classical
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hP.n_pos
  have hj (j : Cell d) : Integrable (fun s ↦ armSign j.1 * poissonMemberWeight n j s *
      poissonSelectedCellEstimate n d q j s)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
    simpa only [mul_assoc] using
      ((memLp_poissonMemberWeight_mul_selectedCellEstimate n d q P j).integrable
        (by norm_num)).const_mul (armSign j.1)
  have hc (j : Cell d) : cellContribution P j = cellProb P j * cellMean P j := by
    by_cases ha : 0 < arrivedCell P j
    · simp [cellContribution, ha]
    · simp [cellContribution, cellMean, ha]
  rw [integral_const_mul, integral_finsetSum _ (fun j _ ↦ hj j)]
  simp_rw [mul_assoc (armSign _) (poissonMemberWeight _ _ _) _, integral_const_mul,
    integral_poissonMemberWeight_mul_selectedCellEstimate n d q P _ hn]
  rw [cellFunctional]
  simp_rw [hc, ← mul_assoc]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have heq : (∑ j : Cell d, (
      armSign j.1 * cellProb P j *
        (∫ s, poissonSelectedCellEstimate n d q j s
          ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) -
        armSign j.1 * cellProb P j * cellMean P j)) =
      ∑ j : Cell d, armSign j.1 * cellProb P j *
        ((∫ s, poissonSelectedCellEstimate n d q j s
          ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) - cellMean P j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  exact abs_sum_markedPoissonSelectedCellEstimate_bias_le n d q P hP hb

end CausalSmith.Stat.MarRareqLogfrontier
