module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.HeavyCorrection

/-! Heavy needle bias via the exact factorial mean and Cauchy--Schwarz,
as required by roadmap (18)--(20). -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment
attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: sq_integral_markedPoissonFactorialBranch_le
lemma sq_integral_markedPoissonFactorialBranch_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d) :
    (∫ s, poissonFactorialBranch n d q j s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ^ 2 ≤
    (∫ s, (poissonFactorialBranch n d q j s) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  have hv := variance_nonneg (poissonFactorialBranch n d q j)
    (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2))
  rw [variance_eq_sub (memLp_poissonFactorialBranch n d q P j)] at hv
  exact sub_nonneg.mp hv

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hb,hh), [the stated mathematical conclusion holds](goal). -/
-- @node: markedPoisson_pilot_light_mul_abs_factorial_mean_le
lemma markedPoisson_pilot_light_mul_abs_factorial_mean_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d)
    (hb : needleBranch n d q)
    (hh : needleRadius n q < streamSize n * arrivedCell P j) :
    (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
      {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} *
    |∫ s, poissonFactorialBranch n d q j s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)| ≤
      Real.exp (-(streamSize n * arrivedCell P j) / 16) := by
  let p := (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
    {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4}
  let a := ∫ s, poissonFactorialBranch n d q j s
    ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)
  let b := ∫ s, (poissonFactorialBranch n d q j s) ^ 2
    ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  have ha : a ^ 2 ≤ b := sq_integral_markedPoissonFactorialBranch_le n d q P j
  have hprod : p * b ≤ Real.exp (-(streamSize n * arrivedCell P j) / 8) :=
    markedPoisson_pilot_light_mul_factorial_secondMoment_le_intensity n d q P j hb hh
  have hs : (p * |a|) ^ 2 ≤ Real.exp (-(streamSize n * arrivedCell P j) / 8) := by
    calc
      _ = p * (p * a ^ 2) := by rw [mul_pow, sq_abs]; ring
      _ ≤ p * a ^ 2 := by
        have h := mul_le_mul_of_nonneg_right hp1 (mul_nonneg hp0 (sq_nonneg a))
        simpa only [one_mul] using h
      _ ≤ p * b := mul_le_mul_of_nonneg_left ha hp0
      _ ≤ _ := hprod
  have he : (Real.exp (-(streamSize n * arrivedCell P j) / 16)) ^ 2 =
      Real.exp (-(streamSize n * arrivedCell P j) / 8) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  change p * |a| ≤ _
  nlinarith [Real.exp_pos (-(streamSize n * arrivedCell P j) / 16)]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hb,hh), [the stated mathematical conclusion holds](goal). -/
-- @node: markedPoisson_heavy_needle_bias_le
lemma markedPoisson_heavy_needle_bias_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d)
    (hb : needleBranch n d q)
    (hh : needleRadius n q < streamSize n * arrivedCell P j) :
    cellMean P j *
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
        {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} *
      |(chebNeedle n d q).eval (streamSize n * arrivedCell P j)| ≤
      2 * Real.exp (-(streamSize n * arrivedCell P j) / 16) := by
  let p := (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
    {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4}
  let a := ∫ s, poissonFactorialBranch n d q j s
    ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hmu := cellMean_mem_Icc P j
  have hid : cellMean P j * (chebNeedle n d q).eval
      (streamSize n * arrivedCell P j) = cellMean P j - a := by
    dsimp [a]
    rw [integral_markedPoissonFactorialBranch_eq_needle n d q P j]
    ring
  have ht0 : 0 ≤ streamSize n * arrivedCell P j := by
    have : 0 ≤ arrivedCell P j := measureReal_nonneg
    unfold streamSize
    positivity
  have hp : p ≤ Real.exp (-(streamSize n * arrivedCell P j) / 16) := by
    apply (markedPoisson_pilot_light_probability_le_of_heavy n d q P j hb hh).trans
    apply Real.exp_le_exp.mpr
    linarith
  have ha := markedPoisson_pilot_light_mul_abs_factorial_mean_le n d q P j hb hh
  change cellMean P j * p * _ ≤ _
  calc
    _ = p * |cellMean P j - a| := by
      rw [← hid, abs_mul, abs_of_nonneg hmu.1]
      ring
    _ ≤ p * (cellMean P j + |a|) := by
      apply mul_le_mul_of_nonneg_left _ hp0
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hmu.1])
    _ ≤ p + p * |a| := by nlinarith [mul_le_mul_of_nonneg_left hmu.2 hp0]
    _ ≤ _ := by change p * |a| ≤ _ at ha; linarith

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: abs_sum_heavy_pilot_needle_bias_le
lemma abs_sum_heavy_pilot_needle_bias_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (hb : needleBranch n d q) :
    |2 * ∑ j ∈ (Finset.univ : Finset (Cell d)).filter
        (fun j ↦ needleRadius n q < streamSize n * arrivedCell P j),
      armSign j.1 * cellProb P j * cellMean P j *
        (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
          {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} *
        (chebNeedle n d q).eval (streamSize n * arrivedCell P j)| ≤
      4 * Real.exp (-16 * logScale n q) := by
  classical
  have hj (j : Cell d) (hh : needleRadius n q < streamSize n * arrivedCell P j) :
      |armSign j.1 * cellProb P j * cellMean P j *
        (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
          {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} *
        (chebNeedle n d q).eval (streamSize n * arrivedCell P j)| ≤
      cellProb P j * (2 * Real.exp (-16 * logScale n q)) := by
    have hp : 0 ≤ cellProb P j := measureReal_nonneg
    have hmu := cellMean_mem_Icc P j
    have hsign : |armSign j.1| = 1 := by cases j.1 <;> simp [armSign]
    rw [abs_mul, abs_mul, abs_mul, abs_mul, hsign, one_mul,
      abs_of_nonneg hp, abs_of_nonneg hmu.1, abs_of_nonneg measureReal_nonneg]
    calc
      _ = cellProb P j * (cellMean P j *
          (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
            {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} *
          |(chebNeedle n d q).eval (streamSize n * arrivedCell P j)|) := by ring
      _ ≤ cellProb P j * (2 * Real.exp (-(streamSize n * arrivedCell P j) / 16)) :=
        mul_le_mul_of_nonneg_left (markedPoisson_heavy_needle_bias_le n d q P j hb hh) hp
      _ ≤ _ := by
        gcongr
        change 256 * logScale n q < streamSize n * arrivedCell P j at hh
        linarith
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * ∑ j ∈ (Finset.univ : Finset (Cell d)).filter
        (fun j ↦ needleRadius n q < streamSize n * arrivedCell P j),
      |armSign j.1 * cellProb P j * cellMean P j *
        (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
          {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} *
        (chebNeedle n d q).eval (streamSize n * arrivedCell P j)| := by
      gcongr
      exact abs_sum_le_sum_abs _ _
    _ ≤ 2 * ∑ j : Cell d, cellProb P j * (2 * Real.exp (-16 * logScale n q)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hh
      · exact hj j hh
      · exact mul_nonneg measureReal_nonneg (by positivity)
    _ = _ := by rw [← Finset.sum_mul, sum_cellProb_eq_one]; ring

end CausalSmith.Stat.MarRareqLogfrontier
