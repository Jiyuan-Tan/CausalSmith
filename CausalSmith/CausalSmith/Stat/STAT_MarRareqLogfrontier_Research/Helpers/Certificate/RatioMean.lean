module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.CountBridge
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean

/-! The exact, zero-safe ratio-branch mean in the marked Poisson experiment. -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment

attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:X,A,s), [the stated mathematical conclusion holds](goal). -/
-- @node: successFraction_eventCount_eq_cast
lemma successFraction_eventCount_eq_cast {X : Type*} [MeasurableSpace X]
    (A : Set X) (s : FiniteSample X) :
    Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount A s =
      (eventCount s A : ℝ) := by
  classical
  simp only [Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.eventCount,
    Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.iidEventCount,
    eventCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

/-- Given [the specified inputs and assumptions](hyp:d,j,s), [the stated mathematical conclusion holds](goal). -/
-- @node: poissonRatioBranch_eq_successFraction
lemma poissonRatioBranch_eq_successFraction {d : ℕ} (j : Cell d)
    (s : FiniteSample (ObsRecord d × Fin 3)) :
    poissonRatioBranch j s =
      Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction
        (streamEvent 2 j true true) (streamEvent 2 j true false) s := by
  classical
  simp only [poissonRatioBranch,
    Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.successFraction,
    successFraction_eventCount_eq_cast, Nat.cast_eq_zero]
  by_cases h : eventCount s (streamEvent 2 j true false) = 0
  · simp [h]
  · simp [h, Nat.pos_of_ne_zero h]

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j,hpos), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_markedPoissonRatioBranch_of_pos
lemma integral_markedPoissonRatioBranch_of_pos (n d : ℕ) (P : FullLaw d)
    (j : Cell d) (hpos : 0 < arrivedCell P j) :
    (∫ s, poissonRatioBranch j s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) =
      cellMean P j * (1 - Real.exp (-streamSize n * arrivedCell P j)) := by
  letI := markedObsLaw_isProbabilityMeasure P
  simp_rw [poissonRatioBranch_eq_successFraction]
  rw [Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.finitePoisson_successFraction_mean
    (markedObsLaw P) ((n : ℝ≥0) / 2)
    (Set.Finite.measurableSet (Set.toFinite _))
    (Set.Finite.measurableSet (Set.toFinite _))
    (streamEvent_ones_subset_arrived 2 j)
    (by rw [markedObsLaw_streamEvent_real, map_obsStreamEvent_arrived_real]; positivity)]
  rw [markedObsLaw_streamEvent_real, markedObsLaw_streamEvent_real,
    map_obsStreamEvent_arrivedOne_real, map_obsStreamEvent_arrived_real]
  simp only [cellMean, if_pos hpos, NNReal.coe_div, NNReal.coe_natCast,
    NNReal.coe_ofNat]
  congr 1
  · ring
  · congr 2
    unfold streamSize
    ring

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j,hzero), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_markedPoissonRatioBranch_of_zero
lemma integral_markedPoissonRatioBranch_of_zero (n d : ℕ) (P : FullLaw d)
    (j : Cell d) (hzero : arrivedCell P j = 0) :
    (∫ s, poissonRatioBranch j s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) = 0 := by
  have hmass : (markedObsLaw P) (streamEvent 2 j true false) = 0 := by
    apply (measureReal_eq_zero_iff).mp
    rw [markedObsLaw_streamEvent_real, map_obsStreamEvent_arrived_real, hzero,
      zero_div]
  simp_rw [poissonRatioBranch_eq_successFraction]
  exact Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventRatioMean.finitePoisson_successFraction_mean_of_mass_zero
    (markedObsLaw P) ((n : ℝ≥0) / 2)
    (Set.Finite.measurableSet (Set.toFinite _)) hmass

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_markedPoissonRatioBranch
lemma integral_markedPoissonRatioBranch (n d : ℕ) (P : FullLaw d)
    (j : Cell d) :
    (∫ s, poissonRatioBranch j s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) =
      cellMean P j * (1 - Real.exp (-streamSize n * arrivedCell P j)) := by
  by_cases hpos : 0 < arrivedCell P j
  · exact integral_markedPoissonRatioBranch_of_pos n d P j hpos
  · have hzero : arrivedCell P j = 0 :=
      le_antisymm (le_of_not_gt hpos) measureReal_nonneg
    rw [integral_markedPoissonRatioBranch_of_zero n d P j hzero]
    simp [cellMean, hpos]

/-- Given [the specified inputs and assumptions](hyp:n,d,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: markedPoissonRatioBranch_bias
lemma markedPoissonRatioBranch_bias (n d : ℕ) (P : FullLaw d) (j : Cell d) :
    (∫ s, poissonRatioBranch j s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) - cellMean P j =
      -cellMean P j * Real.exp (-streamSize n * arrivedCell P j) := by
  rw [integral_markedPoissonRatioBranch]
  ring

end CausalSmith.Stat.MarRareqLogfrontier
