module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.CellIntensity
public import Causalean.Stat.Concentration.Poisson.Threshold
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! Pilot-stream Poisson tail terms in roadmap (12) and (19). -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment
open Causalean.Stat.Concentration.Poisson
attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hbranch,hheavy), [the stated mathematical conclusion holds](goal). -/
-- @node: markedPoisson_pilot_light_probability_le_of_heavy
lemma markedPoisson_pilot_light_probability_le_of_heavy
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d)
    (hbranch : needleBranch n d q)
    (hheavy : needleRadius n q < streamSize n * arrivedCell P j) :
    (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
      {s | (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} ≤
      Real.exp (-(streamSize n * arrivedCell P j) / 4) := by
  have hB : 0 ≤ needleRadius n q / 4 := by
    unfold needleRadius
    have := hbranch.1
    positivity
  have hk : (⌊needleRadius n q / 4⌋₊ : ℝ) <
      (arrivedStreamIntensity n P 1 j : ℝ) / 4 := by
    rw [coe_arrivedStreamIntensity]
    exact (Nat.floor_le hB).trans_lt (by linarith)
  have htail := poisson_le_cutoff_of_cutoff_lt_quarter
    (arrivedStreamIntensity n P 1 j) ⌊needleRadius n q / 4⌋₊ hk
  have hmap := finitePoissonSampleLaw_map_eventCount (markedObsLaw P)
    ((n : ℝ≥0) / 2) (streamEvent 1 j true false)
    (Set.Finite.measurableSet (Set.toFinite _))
  simp only [arrivedStreamIntensity] at htail
  rw [← hmap, Measure.map_apply
    (measurable_eventCount _ (Set.Finite.measurableSet (Set.toFinite _)))
    ((Set.to_countable _).measurableSet)] at htail
  have hset : {s : FiniteSample (ObsRecord d × Fin 3) |
      (eventCount s (streamEvent 1 j true false) : ℝ) ≤ needleRadius n q / 4} =
      (fun s ↦ eventCount s (streamEvent 1 j true false)) ⁻¹'
        {w : ℕ | w ≤ ⌊needleRadius n q / 4⌋₊} := by
    ext s
    exact (Nat.le_floor_iff hB).symm
  rw [hset, measureReal_def]
  have hreal := ENNReal.toReal_mono (by finiteness) htail
  change _ ≤ (ENNReal.ofReal
    (Real.exp (-(arrivedStreamIntensity n P 1 j : ℝ) / 4))).toReal at hreal
  simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _),
    coe_arrivedStreamIntensity] using hreal

/-- Given [the specified inputs and assumptions](hyp:n,d,q,lam,hbranch), [the stated mathematical conclusion holds](goal). -/
-- @node: poisson_pilot_heavy_mul_exp_le
lemma poisson_pilot_heavy_mul_exp_le (n d : ℕ) (q : ℝ) (lam : ℝ≥0)
    (hbranch : needleBranch n d q) :
    (poissonMeasure lam).real {w : ℕ | needleRadius n q / 4 < (w : ℝ)} *
      Real.exp (-(lam : ℝ)) ≤ Real.exp (-16 * logScale n q) := by
  have hB : 0 ≤ needleRadius n q / 4 := by
    unfold needleRadius
    have := hbranch.1
    positivity
  have hset : {w : ℕ | needleRadius n q / 4 < (w : ℝ)} =
      {w : ℕ | ⌊needleRadius n q / 4⌋₊ < w} := by
    ext w
    exact (Nat.floor_lt hB).symm
  rw [hset]
  have ht := poisson_upper_tail_mul_exp_le lam ⌊needleRadius n q / 4⌋₊
    (r := 1) (by norm_num)
  simp only [neg_mul, one_mul] at ht
  apply ht.trans
  apply Real.exp_le_exp.mpr
  have hf := Nat.lt_floor_add_one (needleRadius n q / 4)
  have hl := Real.log_two_gt_d9
  have hk : 0 ≤ (⌊needleRadius n q / 4⌋₊ : ℝ) := Nat.cast_nonneg _
  have hlog : logScale n q ≥ 128 := hbranch.1
  norm_num only at ht ⊢
  change 256 * logScale n q / 4 < (⌊needleRadius n q / 4⌋₊ : ℝ) + 1 at hf
  nlinarith

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j,hbranch), [the stated mathematical conclusion holds](goal). -/
-- @node: markedPoisson_pilot_heavy_mul_exp_le
lemma markedPoisson_pilot_heavy_mul_exp_le
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d)
    (hbranch : needleBranch n d q) :
    (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
      {s | needleRadius n q / 4 < (eventCount s (streamEvent 1 j true false) : ℝ)} *
      Real.exp (-(streamSize n * arrivedCell P j)) ≤
      Real.exp (-16 * logScale n q) := by
  have hmap := finitePoissonSampleLaw_map_eventCount (markedObsLaw P)
    ((n : ℝ≥0) / 2) (streamEvent 1 j true false)
    (Set.Finite.measurableSet (Set.toFinite _))
  have hprob :
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)).real
        {s | needleRadius n q / 4 < (eventCount s (streamEvent 1 j true false) : ℝ)} =
      (poissonMeasure (arrivedStreamIntensity n P 1 j)).real
        {w : ℕ | needleRadius n q / 4 < (w : ℝ)} := by
    simp only [arrivedStreamIntensity]
    rw [← hmap]
    simp only [measureReal_def]
    rw [Measure.map_apply
      (measurable_eventCount _ (Set.Finite.measurableSet (Set.toFinite _)))
      ((Set.to_countable _).measurableSet)]
    rfl
  rw [hprob]
  simpa only [coe_arrivedStreamIntensity] using
    poisson_pilot_heavy_mul_exp_le n d q (arrivedStreamIntensity n P 1 j) hbranch

end CausalSmith.Stat.MarRareqLogfrontier
