module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.RawRiskAssembly

/-! Disjoint cell histograms in the marked Poisson experiment are independent.
This supplies the cross-cell independence required after roadmap (21). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.NestedEventMoment
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
attribute [local instance] markedObsLaw_isProbabilityMeasure Classical.propDecidable

/-- Given [the specified inputs and assumptions](hyp:X,s,B), [the stated mathematical conclusion holds](goal). -/
-- @node: eventCount_eq_sum_singleton_histogram
lemma eventCount_eq_sum_singleton_histogram {X : Type*} [MeasurableSpace X]
    [Fintype X] [DecidableEq X]
    (s : FiniteSample X) (B : Set X) :
    eventCount s B = ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ B),
      finiteSampleHistogram s.points x := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin s.count)) (Finset.univ.filter (fun x ↦ x ∈ B)) s.points
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  rw [eventCount, ← h]
  apply Finset.sum_congr rfl
  intro x hx
  simp [finiteSampleHistogram, Fintype.card_subtype]

/-- For [the specified inputs and assumptions](hyp:d,j), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: markedCellAlphabet
noncomputable def markedCellAlphabet {d : ℕ} (j : Cell d) : Finset (ObsRecord d × Fin 3) :=
  Finset.univ.filter (fun z ↦ z.1.A = j.1 ∧ z.1.X = j.2.1 ∧ z.1.S = j.2.2)

/-- For [the specified inputs and assumptions](hyp:d,j,s), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: poissonCellHistogram
noncomputable def poissonCellHistogram {d : ℕ} (j : Cell d)
    (s : FiniteSample (ObsRecord d × Fin 3)) : markedCellAlphabet j → ℕ :=
  fun z ↦ finiteSampleHistogram s.points z

/-- Given [the specified inputs and assumptions](hyp:d,i,j,hij), [the stated mathematical conclusion holds](goal). -/
-- @node: disjoint_markedCellAlphabet
lemma disjoint_markedCellAlphabet {d : ℕ} {i j : Cell d} (hij : i ≠ j) :
    Disjoint (markedCellAlphabet i) (markedCellAlphabet j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hi hj
  simp only [markedCellAlphabet, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  apply hij
  apply Prod.ext
  · exact hi.1.symm.trans hj.1
  · exact Prod.ext (hi.2.1.symm.trans hj.2.1) (hi.2.2.symm.trans hj.2.2)

/-- Given [the specified inputs and assumptions](hyp:n,d,P,i,j,hij), [the stated mathematical conclusion holds](goal). -/
-- @node: indepFun_poissonCellHistogram
lemma indepFun_poissonCellHistogram (n d : ℕ) (P : FullLaw d)
    {i j : Cell d} (hij : i ≠ j) :
    IndepFun (poissonCellHistogram i) (poissonCellHistogram j)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  classical
  let H := fun s : FiniteSample (ObsRecord d × Fin 3) ↦ finiteSampleHistogram s.points
  have hH : Measurable H := by
    apply measurable_pi_lambda
    intro z
    have he : (fun s : FiniteSample (ObsRecord d × Fin 3) ↦ H s z) =
        (fun s ↦ eventCount s {z}) := by
      funext s
      simp [H, finiteSampleHistogram, eventCount, Fintype.card_subtype]
    rw [he]
    exact measurable_eventCount _ (MeasurableSet.singleton _)
  have hind := (iIndepFun_pi (μ := fun z : ObsRecord d × Fin 3 ↦
      poissonMeasure (((n : ℝ≥0) / 2) * ((markedObsLaw P) {z}).toNNReal))
      (X := fun _ ↦ id) (fun _ ↦ measurable_id.aemeasurable)).indepFun_finset
      (markedCellAlphabet i) (markedCellAlphabet j) (disjoint_markedCellAlphabet hij)
      (fun _ ↦ measurable_pi_apply _)
  change IndepFun (fun h (z : markedCellAlphabet i) ↦ h z)
    (fun h (z : markedCellAlphabet j) ↦ h z)
    (independentPoissonCountLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) at hind
  rw [← finitePoissonSampleLaw_map_histogram (markedObsLaw P) ((n : ℝ≥0) / 2)] at hind
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hind ⊢
  intro a b ha hb
  have hi : Measurable (fun h : (ObsRecord d × Fin 3) → ℕ ↦
      fun z : markedCellAlphabet i ↦ h z) := by fun_prop
  have hj : Measurable (fun h : (ObsRecord d × Fin 3) → ℕ ↦
      fun z : markedCellAlphabet j ↦ h z) := by fun_prop
  have h := hind a b ha hb
  rw [Measure.map_apply hH ((ha.preimage hi).inter (hb.preimage hj)),
    Measure.map_apply hH (ha.preimage hi), Measure.map_apply hH (hb.preimage hj)] at h
  exact h

/-- For [the specified inputs and assumptions](hyp:d,j,pool,arrived,ones,h), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: cellHistogramEventCount
noncomputable def cellHistogramEventCount {d : ℕ} (j : Cell d) (pool : Fin 3)
    (arrived ones : Bool) (h : markedCellAlphabet j → ℕ) : ℕ :=
  ∑ z : markedCellAlphabet j, if z.val ∈ streamEvent pool j arrived ones then h z else 0

/-- Given [the specified inputs and assumptions](hyp:d,j,pool,arrived,ones,s), [the stated mathematical conclusion holds](goal). -/
-- @node: cellHistogramEventCount_poissonCellHistogram
lemma cellHistogramEventCount_poissonCellHistogram {d : ℕ} (j : Cell d)
    (pool : Fin 3) (arrived ones : Bool) (s : FiniteSample (ObsRecord d × Fin 3)) :
    cellHistogramEventCount j pool arrived ones (poissonCellHistogram j s) =
      eventCount s (streamEvent pool j arrived ones) := by
  classical
  rw [eventCount_eq_sum_singleton_histogram]
  unfold cellHistogramEventCount poissonCellHistogram
  rw [Finset.sum_coe_sort (markedCellAlphabet j) (fun z ↦
    if z ∈ streamEvent pool j arrived ones then finiteSampleHistogram s.points z else 0)]
  unfold markedCellAlphabet
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases he : z ∈ streamEvent pool j arrived ones
  · have hc : z ∈ markedCellAlphabet j := by
      simp only [markedCellAlphabet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨he.2.1, he.2.2.1, he.2.2.2.1⟩
    simp [he, he.2.1, he.2.2.1, he.2.2.2.1]
  · simp [he]

/-- For [the specified inputs and assumptions](hyp:n,d,q,j,h), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
-- @node: histogramWeightedSelectedEstimate
noncomputable def histogramWeightedSelectedEstimate (n d : ℕ) (q : ℝ) (j : Cell d)
    (h : markedCellAlphabet j → ℕ) : ℝ :=
  let M := cellHistogramEventCount j 0 false false h
  let C' := cellHistogramEventCount j 1 true false h
  let C := cellHistogramEventCount j 2 true false h
  let U := cellHistogramEventCount j 2 true true h
  (M : ℝ) / streamSize n *
    (if needleBranch n d q ∧ (C' : ℝ) ≤ needleRadius n q / 4 then
      (if needleBranch n d q then
        ∑ v ∈ Finset.Icc 1 (needleDegree n q - 1), needleCoeff n d q v *
          ((U : ℝ) * ((C - 1).descFactorial (v - 1) : ℝ)) else 0)
    else if 0 < C then (U : ℝ) / C else 0)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,j,s), [the stated mathematical conclusion holds](goal). -/
-- @node: histogramWeightedSelectedEstimate_poissonCellHistogram
lemma histogramWeightedSelectedEstimate_poissonCellHistogram (n d : ℕ) (q : ℝ)
    (j : Cell d) (s : FiniteSample (ObsRecord d × Fin 3)) :
    histogramWeightedSelectedEstimate n d q j (poissonCellHistogram j s) =
      poissonMemberWeight n j s * poissonSelectedCellEstimate n d q j s := by
  simp only [histogramWeightedSelectedEstimate,
    cellHistogramEventCount_poissonCellHistogram, poissonMemberWeight,
    poissonSelectedCellEstimate, poissonFactorialBranch, poissonRatioBranch, weightedFactorial]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,i,j,hij), [the stated mathematical conclusion holds](goal). -/
-- @node: indepFun_memberWeight_mul_selectedCellEstimate
lemma indepFun_memberWeight_mul_selectedCellEstimate (n d : ℕ) (q : ℝ) (P : FullLaw d)
    {i j : Cell d} (hij : i ≠ j) :
    IndepFun (fun s ↦ poissonMemberWeight n i s * poissonSelectedCellEstimate n d q i s)
      (fun s ↦ poissonMemberWeight n j s * poissonSelectedCellEstimate n d q j s)
      (finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) := by
  have h := (indepFun_poissonCellHistogram n d P hij).comp
    (measurable_of_countable (histogramWeightedSelectedEstimate n d q i))
    (measurable_of_countable (histogramWeightedSelectedEstimate n d q j))
  simpa only [Function.comp_def, histogramWeightedSelectedEstimate_poissonCellHistogram] using h

end CausalSmith.Stat.MarRareqLogfrontier
