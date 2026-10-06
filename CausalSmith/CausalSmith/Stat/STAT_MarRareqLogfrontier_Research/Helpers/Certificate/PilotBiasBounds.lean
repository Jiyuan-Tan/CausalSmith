module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.PilotBias
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.PilotTailBounds

/-! Complementary pilot probabilities and the signed false-heavy bias contribution
in roadmap (19)--(20), together with the heavy-cell pilot bound for (24). -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment
attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: markedPoisson_pilot_heavy_probability_eq_one_sub_light
lemma markedPoisson_pilot_heavy_probability_eq_one_sub_light
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d) :
    (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
      {s | needleRadius n q / 4 < (eventCount s (streamEvent 1 j true false) : ℝ)} =
    1 - (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
      {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} := by
  have hs : MeasurableSet {s : FiniteSample (ObsRecord d × Fin 3) |
      (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} :=
    ((measurable_of_countable (fun c : ℕ ↦ (c : ℝ))).comp
      (measurable_eventCount _ (Set.Finite.measurableSet (Set.toFinite _))))
        measurableSet_Iic
  have heq : {s : FiniteSample (ObsRecord d × Fin 3) |
      needleRadius n q / 4 < (eventCount s (streamEvent 1 j true false) : ℝ)} =
      {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4}ᶜ := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  rw [heq, measureReal_compl hs, probReal_univ]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: abs_sum_pilot_heavy_exp_bias_le
lemma abs_sum_pilot_heavy_exp_bias_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (hb : needleBranch n d q) :
    |2 * ∑ j : Cell d, armSign j.1 * cellProb P j * cellMean P j *
      (1 - (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
        {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4}) *
      Real.exp (-(streamSize n * arrivedCell P j))| ≤
      2 * Real.exp (-16 * logScale n q) := by
  classical
  have hj (j : Cell d) :
      |armSign j.1 * cellProb P j * cellMean P j *
        (1 - (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
          {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4}) *
        Real.exp (-(streamSize n * arrivedCell P j))| ≤
      cellProb P j * Real.exp (-16 * logScale n q) := by
    rw [← markedPoisson_pilot_heavy_probability_eq_one_sub_light]
    have hp : 0 ≤ cellProb P j := measureReal_nonneg
    have hmu := cellMean_mem_Icc P j
    have hsign : |armSign j.1| = 1 := by cases j.1 <;> simp [armSign]
    rw [abs_mul, abs_mul, abs_mul, abs_mul, hsign, one_mul,
      abs_of_nonneg hp, abs_of_nonneg hmu.1,
      abs_of_nonneg measureReal_nonneg, abs_of_pos (Real.exp_pos _)]
    calc
      _ = cellProb P j * cellMean P j *
          ((finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
            {s | needleRadius n q / 4 < (eventCount s (streamEvent 1 j true false) : ℝ)} *
              Real.exp (-(streamSize n * arrivedCell P j))) := by ring
      _ ≤ cellProb P j * 1 * Real.exp (-16 * logScale n q) := by
        gcongr
        · exact hmu.2
        · exact markedPoisson_pilot_heavy_mul_exp_le n d q P j hb
      _ = _ := by ring
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * ∑ j : Cell d, |armSign j.1 * cellProb P j * cellMean P j *
        (1 - (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
          {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4}) *
        Real.exp (-(streamSize n * arrivedCell P j))| := by
      gcongr
      exact abs_sum_le_sum_abs _ _
    _ ≤ 2 * ∑ j : Cell d, cellProb P j * Real.exp (-16 * logScale n q) := by
      gcongr with j
      exact hj j
    _ = _ := by rw [← Finset.sum_mul, sum_cellProb_eq_one, one_mul]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hb,hh), [the stated mathematical conclusion holds](goal). -/
-- @node: markedPoisson_pilot_light_probability_le_exp_of_heavy
lemma markedPoisson_pilot_light_probability_le_exp_of_heavy
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d)
    (hb : needleBranch n d q)
    (hh : needleRadius n q < streamSize n * arrivedCell P j) :
    (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
      {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} ≤
      Real.exp (-32 * logScale n q) := by
  apply (markedPoisson_pilot_light_probability_le_of_heavy n d q P j hb hh).trans
  apply Real.exp_le_exp.mpr
  have hl := hb.1
  change 256 * logScale n q < streamSize n * arrivedCell P j at hh
  linarith

end CausalSmith.Stat.MarRareqLogfrontier
