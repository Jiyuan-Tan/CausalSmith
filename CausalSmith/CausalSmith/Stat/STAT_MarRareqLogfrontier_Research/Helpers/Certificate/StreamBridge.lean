module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.IdealEstimator

/-! Ordered-stream representation of the ideal marked Poisson estimator. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteMeasurablePartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment

attribute [local instance] Classical.propDecidable

/-- Given [the specified inputs and assumptions](hyp:s,pool,j,arrived,ones), [the stated mathematical conclusion holds](goal). -/
lemma eventCount_unshuffle (s : FiniteSample (ObsRecord d × Fin 3)) (pool : Fin 3)
    (j : Cell d) (arrived ones : Bool) :
    eventCount (unshuffle s pool) (obsStreamEvent j arrived ones) =
      eventCount s (streamEvent pool j arrived ones) := by
  classical
  rcases s with ⟨k, z⟩
  unfold eventCount unshuffle
  simp only [FiniteSample.count, FiniteSample.points]
  let w : Fin k → Fin 3 := fun i => (z i).2
  let y : Fin k → ObsRecord d := fun i => (z i).1
  let e (i : Fin (wordHistogram w pool)) : Fin k :=
    wordUnshuffleEquiv w ⟨pool, i⟩
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    change i ∈ Finset.univ.filter (fun i =>
      gatherWord (fun k => (z k).2) (fun k => (z k).1) pool i ∈
        obsStreamEvent j arrived ones) at hi
    change e i ∈ Finset.univ.filter (fun i => z i ∈
      streamEvent pool j arrived ones)
    rw [Finset.mem_filter] at hi ⊢
    rcases hi with ⟨_, hi⟩
    refine ⟨Finset.mem_univ _, ?_⟩
    have hlabel := (wordFiberEquiv w pool i).property
    change w (e i) = pool at hlabel
    simpa [e, w, y, gatherWord, obsStreamEvent, streamEvent, hlabel] using hi
  · intro i hi i' hi' he
    have hsigma : (⟨pool, i⟩ : Σ a, Fin (wordHistogram w a)) = ⟨pool, i'⟩ :=
      (wordUnshuffleEquiv w).injective he
    cases hsigma
    rfl
  · intro i hi
    change i ∈ Finset.univ.filter (fun i => z i ∈
      streamEvent pool j arrived ones) at hi
    rw [Finset.mem_filter] at hi
    rcases hi with ⟨_, hi⟩
    have hipool : w i = pool := by simpa [w, streamEvent] using hi.1
    let u : {a : Fin k // w a = pool} := ⟨i, hipool⟩
    let r : Fin (wordHistogram w pool) := (wordFiberEquiv w pool).symm u
    refine ⟨r, ?_, ?_⟩
    · change r ∈ Finset.univ.filter (fun r =>
        gatherWord (fun k => (z k).2) (fun k => (z k).1) pool r ∈
          obsStreamEvent j arrived ones)
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have heq : e r = i := by
        change ((wordFiberEquiv w pool) r).1 = i
        exact congrArg Subtype.val ((wordFiberEquiv w pool).apply_symm_apply u)
      simpa [e, w, y, gatherWord, obsStreamEvent, streamEvent, heq] using hi.2
    · change ((wordFiberEquiv w pool) r).1 = i
      exact congrArg Subtype.val ((wordFiberEquiv w pool).apply_symm_apply u)

/-- For [the specified inputs and assumptions](hyp:n,d,q,j,s), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def streamFactorialBranch (n d : ℕ) (q : ℝ) (j : Cell d)
    (s : Fin 3 → FiniteSample (ObsRecord d)) : ℝ :=
  if needleBranch n d q then
    ∑ v ∈ Finset.Icc 1 (needleDegree n q - 1), needleCoeff n d q v *
      weightedFactorial (obsStreamEvent j true true)
        (obsStreamEvent j true false) v (s 2)
  else 0

/-- For [the specified inputs and assumptions](hyp:d,j,s), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def streamRatioBranch {d : ℕ} (j : Cell d)
    (s : Fin 3 → FiniteSample (ObsRecord d)) : ℝ :=
  if 0 < eventCount (s 2) (obsStreamEvent j true false) then
    eventCount (s 2) (obsStreamEvent j true true) /
      eventCount (s 2) (obsStreamEvent j true false)
  else 0

/-- For [the specified inputs and assumptions](hyp:n,d,q,j,s), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def streamSelectedCellEstimate (n d : ℕ) (q : ℝ) (j : Cell d)
    (s : Fin 3 → FiniteSample (ObsRecord d)) : ℝ :=
  if needleBranch n d q ∧
      eventCount (s 1) (obsStreamEvent j true false) ≤ needleRadius n q / 4 then
    streamFactorialBranch n d q j s
  else streamRatioBranch j s

/-- For [the specified inputs and assumptions](hyp:n,d,q,s), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable def streamAuxiliaryMixedValue (n d : ℕ) (q : ℝ)
    (s : Fin 3 → FiniteSample (ObsRecord d)) : ℝ :=
  if effectiveSize n q ≤ 1 then 0 else
    clip (2 * ∑ j : Cell d, armSign j.1 *
      (eventCount (s 0) (obsStreamEvent j false false) / streamSize n) *
        streamSelectedCellEstimate n d q j s)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,s), [the stated mathematical conclusion holds](goal). -/
lemma streamAuxiliaryMixedValue_unshuffle (n d : ℕ) (q : ℝ)
    (s : FiniteSample (ObsRecord d × Fin 3)) :
    streamAuxiliaryMixedValue n d q (unshuffle s) =
      poissonAuxiliaryMixedValue n d q s := by
  unfold streamAuxiliaryMixedValue poissonAuxiliaryMixedValue
  split_ifs
  · rfl
  · congr 2
    unfold poissonMemberWeight
    apply Finset.sum_congr rfl
    intro j hj
    rw [eventCount_unshuffle]
    congr 2
    unfold streamSelectedCellEstimate poissonSelectedCellEstimate
    rw [eventCount_unshuffle]
    split_ifs
    · unfold streamFactorialBranch poissonFactorialBranch
      split_ifs
      · apply Finset.sum_congr rfl
        intro v hv
        unfold weightedFactorial
        rw [eventCount_unshuffle, eventCount_unshuffle]
      · rfl
    · unfold streamRatioBranch poissonRatioBranch
      rw [eventCount_unshuffle, eventCount_unshuffle]

/-- Given [the specified inputs and assumptions](hyp:d,pool,j,arrived,ones), [the stated mathematical conclusion holds](goal). -/
lemma measurable_streamEventCount {d : ℕ} (pool : Fin 3)
    (j : Cell d) (arrived ones : Bool) :
    Measurable (fun s : Fin 3 → FiniteSample (ObsRecord d) ↦
      eventCount (s pool) (obsStreamEvent j arrived ones)) := by
  exact (measurable_eventCount _
    (Set.Finite.measurableSet (Set.toFinite _))).comp
      (measurable_pi_apply pool)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,j), [the stated mathematical conclusion holds](goal). -/
@[fun_prop] lemma measurable_streamFactorialBranch (n d : ℕ) (q : ℝ)
    (j : Cell d) : Measurable (streamFactorialBranch n d q j) := by
  unfold streamFactorialBranch
  split_ifs
  · apply Finset.measurable_sum
    intro v hv
    exact (measurable_weightedFactorial
      (obsStreamEvent j true true) (obsStreamEvent j true false)
      (Set.Finite.measurableSet (Set.toFinite _))
      (Set.Finite.measurableSet (Set.toFinite _)) v |>.comp
        (measurable_pi_apply 2)).const_mul _
  · fun_prop

/-- Given [the specified inputs and assumptions](hyp:d,j), [the stated mathematical conclusion holds](goal). -/
@[fun_prop] lemma measurable_streamRatioBranch {d : ℕ} (j : Cell d) :
    Measurable (streamRatioBranch j) := by
  have hnum : Measurable (fun s : Fin 3 → FiniteSample (ObsRecord d) ↦
      (eventCount (s 2) (obsStreamEvent j true true) : ℝ)) :=
    (measurable_of_countable (fun z : ℕ ↦ (z : ℝ))).comp
      (measurable_streamEventCount 2 j true true)
  have hden : Measurable (fun s : Fin 3 → FiniteSample (ObsRecord d) ↦
      (eventCount (s 2) (obsStreamEvent j true false) : ℝ)) :=
    (measurable_of_countable (fun z : ℕ ↦ (z : ℝ))).comp
      (measurable_streamEventCount 2 j true false)
  unfold streamRatioBranch
  apply Measurable.ite
  · exact (measurable_streamEventCount 2 j true false) measurableSet_Ioi
  · exact hnum.div hden
  · fun_prop

/-- Given [the specified inputs and assumptions](hyp:n,d,q,j), [the stated mathematical conclusion holds](goal). -/
@[fun_prop] lemma measurable_streamSelectedCellEstimate (n d : ℕ) (q : ℝ)
    (j : Cell d) : Measurable (streamSelectedCellEstimate n d q j) := by
  unfold streamSelectedCellEstimate
  apply Measurable.ite
  · by_cases hbranch : needleBranch n d q
    · simp only [hbranch, true_and]
      have hc : Measurable (fun s : Fin 3 → FiniteSample (ObsRecord d) ↦
          (eventCount (s 1) (obsStreamEvent j true false) : ℝ)) :=
        (measurable_of_countable (fun z : ℕ ↦ (z : ℝ))).comp
          (measurable_streamEventCount 1 j true false)
      exact hc measurableSet_Iic
    · simp [hbranch]
  · exact measurable_streamFactorialBranch n d q j
  · exact measurable_streamRatioBranch j

/-- Given [the specified inputs and assumptions](hyp:n,d,q), [the stated mathematical conclusion holds](goal). -/
@[fun_prop] lemma measurable_streamAuxiliaryMixedValue (n d : ℕ) (q : ℝ) :
    Measurable (streamAuxiliaryMixedValue n d q) := by
  unfold streamAuxiliaryMixedValue clip
  split_ifs
  · fun_prop
  · apply Measurable.max measurable_const
    apply Measurable.min measurable_const
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro j hj
    have hmember : Measurable
        (fun s : Fin 3 → FiniteSample (ObsRecord d) ↦
          (eventCount (s 0) (obsStreamEvent j false false) : ℝ) /
            streamSize n) := by
      apply Measurable.div_const
      exact (measurable_of_countable (fun z : ℕ ↦ (z : ℝ))).comp
        (measurable_streamEventCount 0 j false false)
    exact (hmember.const_mul _).mul
      (measurable_streamSelectedCellEstimate n d q j)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,s), [the stated mathematical conclusion holds](goal). -/
lemma streamAuxiliaryMixedValue_mem_Icc (n d : ℕ) (q : ℝ)
    (s : Fin 3 → FiniteSample (ObsRecord d)) :
    streamAuxiliaryMixedValue n d q s ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold streamAuxiliaryMixedValue clip
  split_ifs
  · norm_num
  · exact ⟨le_max_left _ _,
      (max_le_iff.mpr ⟨by norm_num, min_le_left _ _⟩)⟩

end CausalSmith.Stat.MarRareqLogfrontier
