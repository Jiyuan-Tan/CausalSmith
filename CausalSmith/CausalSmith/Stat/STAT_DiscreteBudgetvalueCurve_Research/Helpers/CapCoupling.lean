module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.PoissonSplit
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.GoodPilotAggregate
public import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.UpperRiskCoupling
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix.Basic

/-! Finite auxiliary weights and the capped marked-count coupling interface. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

/-- The finite nonoverflow auxiliary experiment, augmented by one atom for
Poisson overflow. -/
abbrev FiniteCapAuxState (n : ℕ) :=
  Option (Fin (n + 1) × Equiv.Perm (Fin n) × (Fin n → Bool))

/-- Auxiliary weight, with the missing Poisson tail assigned to the overflow
atom. -/
-- @node: finiteCapAuxWeight
noncomputable def finiteCapAuxWeight (n : ℕ) : FiniteCapAuxState n → ℝ
  | none => (poissonMeasure ((n : ℝ≥0) / 4)).real (Set.Ioi n)
  | some a => auxiliaryWeight n a.1

/-- Every augmented finite auxiliary weight is nonnegative. With [the specified inputs and conditions](hyp:n,a), [the stated relationship holds](goal). -/
-- @node: finiteCapAuxWeight_nonneg
lemma finiteCapAuxWeight_nonneg (n : ℕ) (a : FiniteCapAuxState n) :
    0 ≤ finiteCapAuxWeight n a := by
  cases a with
  | none => exact measureReal_nonneg
  | some a =>
      unfold finiteCapAuxWeight auxiliaryWeight
      positivity

/-- The overflow atom completes the subprobability cap weights to a finite
probability vector. With [the specified inputs and conditions](hyp:n), [the stated relationship holds](goal). -/
-- @node: finiteCapAuxWeight_sum
lemma finiteCapAuxWeight_sum (n : ℕ) :
    ∑ a : FiniteCapAuxState n, finiteCapAuxWeight n a = 1 := by
  let μ := poissonMeasure ((n : ℝ≥0) / 4)
  have hcap : ∑ M ∈ Finset.range (n + 1), μ.real {M} = μ.real (Set.Iic n) := by
    rw [MeasureTheory.sum_measureReal_singleton]
    congr 1
    ext M
    simp
  have htail : μ.real (Set.Ioi n) = 1 - μ.real (Set.Iic n) := by
    have hc : (Set.Iic n : Set ℕ)ᶜ = Set.Ioi n := by ext M; simp
    rw [← hc, MeasureTheory.measureReal_compl measurableSet_Iic]
    simp [μ]
  rw [Fintype.sum_option]
  simp only [finiteCapAuxWeight]
  simp_rw [Fintype.sum_prod_type]
  have hcards :
      (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) *
        Fintype.card (Fin n → Bool) := by positivity
  have hfinite :
      (∑ M : Fin (n + 1), ∑ _perm : Equiv.Perm (Fin n),
        ∑ _marks : Fin n → Bool, auxiliaryWeight n M) =
      ∑ M ∈ Finset.range (n + 1), μ.real {M} := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro M _
    simp [auxiliaryWeight, μ, measureReal_def]
    field_simp
  rw [hfinite, hcap, htail]
  have hle : μ.real (Set.Iic n) ≤ 1 := by
    simpa [μ] using measureReal_le_measureReal_univ (μ := μ) (Set.subset_univ _)
  linarith

/-- The paired table read from one nonoverflow auxiliary draw. -/
-- @node: permutedMarkedCountTable
def permutedMarkedCountTable {n d : ℕ} (sample : Fin n → Obs d)
    (perm : Equiv.Perm (Fin n)) (M : ℕ) (marks : Fin n → Bool) :
    (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ) :=
  ((fun j zeta => markedCellCount sample perm M marks false j zeta),
   fun j zeta => markedCellCount sample perm M marks true j zeta)

/-- On the cap event, the paper's permuted marked table is the table component
of the established uncapped finite-Poisson prefix construction. With [the specified inputs and conditions](hyp:n,d,sample,perm,M,marks,hM), [the stated relationship holds](goal). -/
-- @node: permutedMarkedCountTable_eq_uncapped_prefix
lemma permutedMarkedCountTable_eq_uncapped_prefix {n d : ℕ}
    (sample : Fin n → Obs d) (perm : Equiv.Perm (Fin n))
    (M : ℕ) (marks : Fin n → Bool) (hM : M ≤ n) :
    permutedMarkedCountTable sample perm M marks =
      (CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.uncappedMarkedCountMap
        (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.prefixOfLE
          (fun i => (sample (perm i), marks i)) M hM)).2 := by
  symm
  simpa [permutedMarkedCountTable, markedCellCount,
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.markedCellCount] using
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.uncappedMarkedCountMap_prefix_table
      (fun i => sample (perm i)) marks M hM

/-- The established uncapped marked finite-Poisson experiment has exactly the
ideal paired table law used in this paper. With [the specified inputs and conditions](hyp:n,d,P), [the stated relationship holds](goal). -/
-- @node: uncappedMarkedCountLaw_table_eq_idealCountLaw
lemma uncappedMarkedCountLaw_table_eq_idealCountLaw {n d : ℕ}
    (P : DiscreteLaw d) :
    Measure.map Prod.snd
        (CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.uncappedMarkedCountLaw n P) =
      CausalSmith.Stat.DiscreteBudgetvalueCurve.idealCountLaw (n := n) P := by
  rw [CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.uncappedMarkedCountLaw_table]
  unfold CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.pilotEvaluationTableLaw
  unfold CausalSmith.Stat.DiscreteBudgetvalueCurve.idealCountLaw
  have hpool :
      Measure.pi (fun x : Fin d => Measure.pi (fun j : Cell =>
        poissonMeasure (((n : ℝ) / 8 * jointMass P x
          (finTwoEquiv j.1) (finTwoEquiv j.2)).toNNReal))) =
      Measure.pi (fun j : Fin d => Measure.pi (fun zeta : Cell =>
        poissonMeasure ⟨max 0 (((n : ℝ) / 8) * cellVector P j zeta),
          le_max_left 0 _⟩)) := by
    congr 1
    funext j
    congr 1
    funext zeta
    congr 1
    apply NNReal.eq
    change max (((n : ℝ) / 8) * jointMass P j
      (finTwoEquiv zeta.1) (finTwoEquiv zeta.2)) 0 =
      max 0 (((n : ℝ) / 8) * cellVector P j zeta)
    rw [max_comm]
    rfl
  exact congrArg (fun μ => μ.prod μ) hpool

/-- The paper's fair marking law is the fair Boolean law used by the capped
prefix theorem. [The stated relationship holds](goal). -/
-- @node: fairBoolLaw_eq_uncappedFairMarkLaw
lemma fairBoolLaw_eq_uncappedFairMarkLaw :
    Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix.fairBoolLaw =
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.uncappedFairMarkLaw := by
  apply Measure.ext_of_singleton
  intro b
  cases b <;>
    simp [Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix.fairBoolLaw,
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.uncappedFairMarkLaw,
      smul_eq_mul]

/-- The finite auxiliary mixture in `auxiliaryAverage` equals the nonoverflow
part of the established uncapped marked Poisson experiment. With [the specified inputs and conditions](hyp:n,d,P), [the stated relationship holds](goal). -/
-- @node: CappedMarkedCountIntegralIdentity
lemma CappedMarkedCountIntegralIdentity {n d : ℕ} (P : DiscreteLaw d) :
  ∀ g : ((Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) → ℝ,
    Integrable g
      (CausalSmith.Stat.DiscreteBudgetvalueCurve.idealCountLaw (n := n) P) →
    (∫ sample : Fin n → Obs d,
      ∑ M ∈ Finset.range (n + 1),
        ∑ perm : Equiv.Perm (Fin n), ∑ marks : Fin n → Bool,
          auxiliaryWeight n M *
            g (permutedMarkedCountTable sample perm M marks)
      ∂productLaw P n) =
    ∫ z : ℕ ×
        CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.UncappedCountTable d,
      if z.1 ≤ n then g z.2 else 0
      ∂CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.uncappedMarkedCountLaw n P := by
  classical
  intro g hg
  let tableMap := fun s :
      Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample
        (Obs d × Bool) =>
    (CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.uncappedMarkedCountMap s).2
  let μ := Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
    ((CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.obsLaw P).prod
      Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix.fairBoolLaw)
    ((n : ℝ≥0) / 4)
  have hmean : Real.toNNReal ((n : ℝ) / 4) = (n : ℝ≥0) / 4 := by
    apply NNReal.eq
    rw [Real.coe_toNNReal ((n : ℝ) / 4) (by positivity)]
    norm_num
  have hμ : μ =
      Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
        ((CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.obsLaw P).prod
          CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.uncappedFairMarkLaw)
        (Real.toNNReal ((n : ℝ) / 4)) := by
    simp only [μ, hmean, fairBoolLaw_eq_uncappedFairMarkLaw]
  have htable : Measure.map tableMap μ = idealCountLaw (n := n) P := by
    rw [← uncappedMarkedCountLaw_table_eq_idealCountLaw (n := n) P]
    unfold CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.uncappedMarkedCountLaw
    rw [Measure.map_map measurable_snd
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.measurable_uncappedMarkedCountMap]
    rw [hμ]
    rfl
  have htable_meas : Measurable tableMap :=
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.measurable_uncappedMarkedCountMap.snd
  have hG : Integrable (g ∘ tableMap) μ := by
    apply (integrable_map_measure (by simpa [htable] using hg.aestronglyMeasurable)
      htable_meas.aemeasurable).mp
    simpa [htable] using hg
  have hcap :=
    Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix.capped_marked_prefix_integral
      (CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.obsLaw P)
      ((n : ℝ≥0) / 4) n (g ∘ tableMap) hG
  have hprefix (sample : Fin n → Obs d) (M : Fin (n + 1))
      (perm : Equiv.Perm (Fin n)) (marks : Fin n → Bool) :
      (g ∘ tableMap)
          (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.prefixOfLE
            (fun i => (sample (perm i), marks i)) M.val
            (Nat.le_of_lt_succ M.isLt)) =
        g (permutedMarkedCountTable sample perm M.val marks) := by
    dsimp only [Function.comp_apply, tableMap]
    rw [
      permutedMarkedCountTable_eq_uncapped_prefix sample perm M.val marks
        (Nat.le_of_lt_succ M.isLt)]
  simp_rw [hprefix] at hcap
  have hset : MeasurableSet {s :
      Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample
        (Obs d × Bool) | s.count ≤ n} :=
    Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.measurable_finiteSample_count
      measurableSet_Iic
  have hif_meas : AEStronglyMeasurable
      (fun s => if s.count ≤ n then (g ∘ tableMap) s else 0) μ := by
    have hind := hG.aestronglyMeasurable.indicator hset
    convert hind using 1
    funext s
    by_cases hs : s.count ≤ n <;> simp [Set.indicator, hs]
  calc
    _ = ∫ sample : Fin n → Obs d,
        ∑ M : Fin (n + 1),
          ∑ perm : Equiv.Perm (Fin n), ∑ marks : Fin n → Bool,
            ((ProbabilityTheory.poissonMeasure ((n : ℝ≥0) / 4)) {M.val}).toReal /
                ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
                  (Fintype.card (Fin n → Bool) : ℝ)) *
              g (permutedMarkedCountTable sample perm M.val marks)
        ∂Measure.pi (fun _ : Fin n =>
          CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.obsLaw P) := by
            congr 1
            funext sample
            simpa only [auxiliaryWeight] using
              (Fin.sum_univ_eq_sum_range (n := n + 1) (fun M =>
                ∑ perm : Equiv.Perm (Fin n), ∑ marks : Fin n → Bool,
                  ((ProbabilityTheory.poissonMeasure ((n : ℝ≥0) / 4))
                    {M}).toReal /
                      ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
                        (Fintype.card (Fin n → Bool) : ℝ)) *
                    g (permutedMarkedCountTable sample perm M marks))).symm
    _ = ∫ s, if s.count ≤ n then (g ∘ tableMap) s else 0 ∂μ := hcap
    _ = _ := by
      unfold CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.uncappedMarkedCountLaw
      have hread :=
        CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.measurable_uncappedMarkedCountMap
          (d := d)
      rw [← hμ, integral_map hread.aemeasurable
        (Measurable.of_discrete.aestronglyMeasurable :
          AEStronglyMeasurable
            (fun z : ℕ ×
              CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.UncappedCountTable d =>
                if z.1 ≤ n then g z.2 else 0)
            (Measure.map
              CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.uncappedMarkedCountMap μ))]
      rfl

end CausalSmith.Stat.DiscreteBudgetvalueCurve
