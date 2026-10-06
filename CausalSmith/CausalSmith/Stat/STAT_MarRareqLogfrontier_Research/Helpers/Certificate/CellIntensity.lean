module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.CoefficientOverlap

/-! Effective cell intensities inside the ambient marked Poisson sample. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- For [the specified inputs and assumptions](hyp:n,d,P,pool,j), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def arrivedStreamIntensity (n : ℕ) {d : ℕ}
    (P : FullLaw d) (pool : Fin 3) (j : Cell d) : ℝ≥0 :=
  ((n : ℝ≥0) / 2) *
    ((markedObsLaw P) (streamEvent pool j true false)).toNNReal

/-- Given [the specified inputs and assumptions](hyp:n,d,P,pool,j), [the stated mathematical conclusion holds](goal). -/
lemma coe_arrivedStreamIntensity (n : ℕ) {d : ℕ}
    (P : FullLaw d) (pool : Fin 3) (j : Cell d) :
    (arrivedStreamIntensity n P pool j : ℝ) =
      streamSize n * arrivedCell P j := by
  unfold arrivedStreamIntensity
  change ((n : ℝ) / 2) *
    ((markedObsLaw P) (streamEvent pool j true false)).toReal = _
  rw [← measureReal_def, markedObsLaw_streamEvent_real,
    map_obsStreamEvent_arrived_real]
  unfold streamSize
  ring

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,hP,pool,j), [the stated mathematical conclusion holds](goal). -/
lemma streamEffectiveSize_mul_cellProb_le_arrivedStreamIntensity
    (n d : ℕ) (q : ℝ) (P : FullLaw d)
    (hP : UnrestrictedArrivalModelClass n d q P) (pool : Fin 3) (j : Cell d) :
    streamEffectiveSize n q * cellProb P j ≤
      (arrivedStreamIntensity n P pool j : ℝ) := by
  rw [coe_arrivedStreamIntensity]
  unfold streamEffectiveSize
  have hm : 0 ≤ streamSize n := by
    unfold streamSize
    positivity
  by_cases hj : 0 < cellProb P j
  · simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hP.arrival j hj) hm
  · have hj' : cellProb P j = 0 := le_antisymm (le_of_not_gt hj) measureReal_nonneg
    rw [hj', mul_zero]
    exact mul_nonneg hm measureReal_nonneg

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hbranch,hlight), [the stated mathematical conclusion holds](goal). -/
lemma integral_sq_markedPoissonFactorialBranch_le_exp_of_light
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d)
    (hbranch : needleBranch n d q)
    (hlight : streamSize n * arrivedCell P j ≤ needleRadius n q) :
    (∫ s, (poissonFactorialBranch n d q j s) ^ 2
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) ≤
      Real.exp (logScale n q / 8) := by
  apply integral_sq_poissonFactorialBranch_le_exp_effective
    n d q j (markedObsLaw P) ((n : ℝ≥0) / 2) hbranch
  change (arrivedStreamIntensity n P 2 j : ℝ) ≤ needleRadius n q
  rw [coe_arrivedStreamIntensity]
  exact hlight

end CausalSmith.Stat.MarRareqLogfrontier
