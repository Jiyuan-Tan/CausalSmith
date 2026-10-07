module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.RatioSecondMoment

/-! Aggregate deterministic bounds for the empirical-ratio branch. -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:P,j), [the stated mathematical conclusion holds](goal). -/
lemma cellMean_mem_Icc (P : FullLaw d) (j : Cell d) :
    cellMean P j ∈ Set.Icc (0 : ℝ) 1 := by
  letI : IsProbabilityMeasure P.1 := P.2
  by_cases hpos : 0 < arrivedCell P j
  · rw [cellMean, if_pos hpos]
    constructor
    · exact div_nonneg measureReal_nonneg hpos.le
    · apply (div_le_one hpos).2
      exact measureReal_mono (fun r hr ↦ ⟨hr.1, hr.2.1⟩)
        (measure_ne_top P.1 _)
  · simp [cellMean, hpos]

/-- Given [the specified inputs and assumptions](hyp:eps,t,z,heps,ht,hz), [the stated mathematical conclusion holds](goal). -/
lemma cell_exp_envelope {eps t z : ℝ} (heps : 0 < eps) (ht : 0 < t)
    (hz : 0 ≤ z) :
    z * Real.exp (-eps * t * z) ≤ 1 / (eps * Real.exp 1 * t) := by
  have hbase : Real.exp 1 * (eps * t * z) ≤ Real.exp (eps * t * z) :=
    Real.exp_one_mul_le_exp
  have hmul := mul_le_mul_of_nonneg_right hbase
    (Real.exp_pos (-(eps * t * z))).le
  have hprod : Real.exp 1 * (eps * t * z) * Real.exp (-(eps * t * z)) ≤ 1 := by
    calc
      _ ≤ Real.exp (eps * t * z) * Real.exp (-(eps * t * z)) := hmul
      _ = 1 := by rw [← Real.exp_add]; ring_nf; simp
  apply (le_div_iff₀ (by positivity : 0 < eps * Real.exp 1 * t)).2
  calc
    z * Real.exp (-eps * t * z) * (eps * Real.exp 1 * t) =
        Real.exp 1 * (eps * t * z) * Real.exp (-(eps * t * z)) := by ring
    _ ≤ 1 := hprod

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP), [the stated mathematical conclusion holds](goal). -/
lemma abs_ratioBranch_aggregate_bias_le (n d : ℕ) (q : ℝ)
    (P : FullLaw d) (hP : UnrestrictedArrivalModelClass n d q P) :
    abs (2 * ∑ j : Cell d, armSign j.1 * cellProb P j *
      ((∫ s, poissonRatioBranch j s
        ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) -
          cellMean P j)) ≤
      8 * d / (Real.exp 1 * streamEffectiveSize n q) := by
  have hm : 0 < streamSize n := by
    unfold streamSize
    have hn : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hP.n_pos)
    positivity
  have hq : 0 < q := hP.q_pos
  have hN0 : 0 < streamEffectiveSize n q := by
    unfold streamEffectiveSize
    positivity
  have hcell (j : Cell d) :
      abs (armSign j.1 * cellProb P j *
        ((∫ s, poissonRatioBranch j s
          ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) -
            cellMean P j)) ≤
        1 / (Real.exp 1 * streamEffectiveSize n q) := by
    rw [markedPoissonRatioBranch_bias]
    have hmu := cellMean_mem_Icc P j
    have hp : 0 ≤ cellProb P j := measureReal_nonneg
    have harr : q * cellProb P j ≤ arrivedCell P j := by
      by_cases hpj : 0 < cellProb P j
      · exact hP.arrival j hpj
      · have hp0 : cellProb P j = 0 := le_antisymm (le_of_not_gt hpj) hp
        rw [hp0, mul_zero]
        exact measureReal_nonneg
    have hexp : Real.exp (-streamSize n * arrivedCell P j) ≤
        Real.exp (-q * streamSize n * cellProb P j) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left harr hm.le
      nlinarith
    have hfirst :
        abs (armSign j.1 * cellProb P j *
          (-cellMean P j * Real.exp (-streamSize n * arrivedCell P j))) ≤
          cellProb P j * Real.exp (-q * streamSize n * cellProb P j) := by
      rw [abs_mul, abs_mul, abs_mul]
      have hsign : abs (armSign j.1) = 1 := by cases j.1 <;> simp [armSign]
      rw [hsign, one_mul]
      rw [abs_of_nonneg hp, abs_neg, abs_of_nonneg hmu.1,
        abs_of_pos (Real.exp_pos _)]
      calc
        cellProb P j * (cellMean P j * Real.exp (-streamSize n * arrivedCell P j)) ≤
            cellProb P j * (1 * Real.exp (-streamSize n * arrivedCell P j)) := by
          gcongr
          exact hmu.2
        _ ≤ cellProb P j * Real.exp (-q * streamSize n * cellProb P j) := by
          gcongr
          simpa using hexp
    refine hfirst.trans ?_
    have he := cell_exp_envelope hq hm hp
    simpa [streamEffectiveSize, mul_comm, mul_left_comm, mul_assoc] using he
  calc
    abs (2 * ∑ j : Cell d, armSign j.1 * cellProb P j *
      ((∫ s, poissonRatioBranch j s
        ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) -
          cellMean P j)) =
        2 * abs (∑ j : Cell d, armSign j.1 * cellProb P j *
          ((∫ s, poissonRatioBranch j s
            ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) -
              cellMean P j)) := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * ∑ j : Cell d, abs (armSign j.1 * cellProb P j *
          ((∫ s, poissonRatioBranch j s
            ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) -
              cellMean P j)) := by
      gcongr
      exact abs_sum_le_sum_abs _ _
    _ ≤ 2 * ∑ _j : Cell d,
        1 / (Real.exp 1 * streamEffectiveSize n q) := by
      gcongr with j
      exact hcell j
    _ = 8 * d / (Real.exp 1 * streamEffectiveSize n q) := by
      simp [div_eq_mul_inv]
      ring

end CausalSmith.Stat.MarRareqLogfrontier
