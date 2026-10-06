module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.CoefficientOverlap

/-! The ideal estimator evaluated on an uncapped marked Poisson sample. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment

/-- For [the specified inputs and assumptions](hyp:n,d,j,s), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def poissonMemberWeight (n : ℕ) {d : ℕ} (j : Cell d)
    (s : FiniteSample (ObsRecord d × Fin 3)) : ℝ :=
  eventCount s (streamEvent 0 j false false) / streamSize n

/-- For [the specified inputs and assumptions](hyp:n,d,q,s), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def poissonRawMixedValue (n d : ℕ) (q : ℝ)
    (s : FiniteSample (ObsRecord d × Fin 3)) : ℝ :=
  2 * ∑ j : Cell d, armSign j.1 * poissonMemberWeight n j s *
    poissonSelectedCellEstimate n d q j s

/-- For [the specified inputs and assumptions](hyp:n,d,q,s), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def poissonAuxiliaryMixedValue (n d : ℕ) (q : ℝ)
    (s : FiniteSample (ObsRecord d × Fin 3)) : ℝ :=
  if effectiveSize n q ≤ 1 then 0 else clip (poissonRawMixedValue n d q s)

/-- Given [the specified inputs and assumptions](hyp:k,d,n,records,assign,j), [the stated mathematical conclusion holds](goal). -/
lemma memberWeight_eq_poissonMemberWeight {k d : ℕ} (n : ℕ)
    (records : Fin k → ObsRecord d) (assign : Fin k → Fin 3) (j : Cell d) :
    memberWeight n records assign j = poissonMemberWeight n j
      (fixedSizeEmbed k (fun i ↦ (records i, assign i))) := by
  rw [memberWeight, poissonMemberWeight, memberCount_eq_eventCount]

/-- Given [the specified inputs and assumptions](hyp:k,d,n,q,records,assign), [the stated mathematical conclusion holds](goal). -/
lemma auxiliaryMixedValue_eq_poissonAuxiliaryMixedValue {k d : ℕ}
    (n : ℕ) (q : ℝ) (records : Fin k → ObsRecord d)
    (assign : Fin k → Fin 3) :
    auxiliaryMixedValue n q records assign =
      poissonAuxiliaryMixedValue n d q
        (fixedSizeEmbed k (fun i ↦ (records i, assign i))) := by
  unfold auxiliaryMixedValue poissonAuxiliaryMixedValue poissonRawMixedValue
  split_ifs
  · rfl
  · congr 2
    apply Finset.sum_congr rfl
    intro j hj
    rw [memberWeight_eq_poissonMemberWeight,
      selectedCellEstimate_eq_poissonSelectedCellEstimate]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,j), [the stated mathematical conclusion holds](goal). -/
@[fun_prop] lemma measurable_poissonFactorialBranch (n d : ℕ) (q : ℝ)
    (j : Cell d) : Measurable (poissonFactorialBranch n d q j) := by
  unfold poissonFactorialBranch
  split_ifs
  · apply Finset.measurable_sum
    intro v hv
    exact (measurable_weightedFactorial
      (streamEvent 2 j true true) (streamEvent 2 j true false)
      (Set.Finite.measurableSet (Set.toFinite _))
      (Set.Finite.measurableSet (Set.toFinite _)) v).const_mul _
  · fun_prop

/-- Given [the specified inputs and assumptions](hyp:n,d,q,j), [the stated mathematical conclusion holds](goal). -/
@[fun_prop] lemma measurable_poissonSelectedCellEstimate (n d : ℕ) (q : ℝ)
    (j : Cell d) : Measurable (poissonSelectedCellEstimate n d q j) := by
  unfold poissonSelectedCellEstimate
  apply Measurable.ite
  · by_cases hbranch : needleBranch n d q
    · simp only [hbranch, true_and]
      have hc : Measurable (fun s : FiniteSample (ObsRecord d × Fin 3) =>
          (eventCount s (streamEvent 1 j true false) : ℝ)) :=
        (measurable_of_countable (fun z : ℕ => (z : ℝ))).comp
          (measurable_eventCount _ (Set.Finite.measurableSet (Set.toFinite _)))
      exact hc measurableSet_Iic
    · simp [hbranch]
  · exact measurable_poissonFactorialBranch n d q j
  · exact measurable_poissonRatioBranch j

/-- Given [the specified inputs and assumptions](hyp:n,d,q), [the stated mathematical conclusion holds](goal). -/
@[fun_prop] lemma measurable_poissonAuxiliaryMixedValue (n d : ℕ) (q : ℝ) :
    Measurable (poissonAuxiliaryMixedValue n d q) := by
  unfold poissonAuxiliaryMixedValue poissonRawMixedValue poissonMemberWeight clip
  split_ifs
  · fun_prop
  · apply Measurable.max measurable_const
    apply Measurable.min measurable_const
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro j hj
    have hmember : Measurable (fun s : FiniteSample (ObsRecord d × Fin 3) =>
        (eventCount s (streamEvent 0 j false false) : ℝ) / streamSize n) := by
      apply Measurable.div_const
      exact (measurable_of_countable (fun z : ℕ => (z : ℝ))).comp
        (measurable_eventCount _ (Set.Finite.measurableSet (Set.toFinite _)))
    exact (hmember.const_mul _).mul
      (measurable_poissonSelectedCellEstimate n d q j)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,s), [the stated mathematical conclusion holds](goal). -/
lemma poissonAuxiliaryMixedValue_mem_Icc (n d : ℕ) (q : ℝ)
    (s : FiniteSample (ObsRecord d × Fin 3)) :
    poissonAuxiliaryMixedValue n d q s ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold poissonAuxiliaryMixedValue clip
  split_ifs
  · norm_num
  · exact ⟨le_max_left _ _, (max_le_iff.mpr ⟨by norm_num, min_le_left _ _⟩)⟩

end CausalSmith.Stat.MarRareqLogfrontier
