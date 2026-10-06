module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.Experiment
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.ZengLower.GenericFixedPoissonTV
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Depoissonization
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.KL
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.HistogramReconstruction

/-! Exact prefix transfer and the remaining many-cell lower-bound obligation. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

private lemma tvDist_map_le_zengBridge
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P Q : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : A → B) (hf : Measurable f) :
    tvDist (Measure.map f P) (Measure.map f Q) ≤ tvDist P Q := by
  unfold tvDist
  apply ciSup_le
  intro S
  rw [Measure.real, Measure.real, Measure.map_apply hf S.2,
    Measure.map_apply hf S.2]
  exact abs_measureReal_sub_le_tvDist (S.2.preimage hf)

private lemma measurable_finiteSampleHistogram_zengBridge
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X] :
    Measurable (fun s : FiniteSample X => finiteSampleHistogram s.points) := by
  apply measurable_to_countable'
  intro c
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet ((Sigma.mk n) ⁻¹'
    {s : FiniteSample X | finiteSampleHistogram s.points = c})
  exact (Set.toFinite _).measurableSet

/-- For [the specified inputs and assumptions](hyp:d,p), [the object defined here](goal) is the quantity, rule, or mathematical structure specified by this declaration. -/
noncomputable instance zengFiniteTable_isFiniteMeasure
    (d : ℕ) (p π μ : Fin d → ℝ) :
    IsFiniteMeasure (zengFiniteTable d p π μ) := by
  apply IsFiniteMeasure.mk
  simp [zengFiniteTable]

end CausalSmith.Stat.MarRareqLogfrontier
