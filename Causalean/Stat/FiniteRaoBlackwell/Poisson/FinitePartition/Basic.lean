module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Partition.Splitting
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.ProductPools.Risk
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# A single iid pool with independently assigned finite labels

Defines the ordered label streams, the Poisson and label auxiliary experiment,
and its capped conditional expectation on one fixed iid pool.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteMeasurablePartition

variable {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
  [Fintype I] [MeasurableSingletonClass I]

/-- For [label masses](hyp:p) [summing to one](hyp:hp), the [label law](goal) assigns each
label its specified mass. [It is given by the finite mass function's probability
measure](step:1). -/
noncomputable def labelLaw (p : I → ℝ≥0) (hp : ∑ i, p i = 1) : Measure I := by
  classical
  let q : PMF I := PMF.ofFintype (fun i => (p i : ℝ≥0∞)) (by exact_mod_cast hp)
  exact q.toMeasure

omit [MeasurableSingletonClass I] in
/-- [The finite label law is a probability measure](goal) when [its label masses](hyp:p)
[sum to one](hyp:hp). -/
theorem labelLaw_isProbabilityMeasure (p : I → ℝ≥0) (hp : ∑ i, p i = 1) :
    IsProbabilityMeasure (labelLaw p hp) := by
  classical
  unfold labelLaw
  infer_instance

/-- Given [a finite sequence of labeled observations](hyp:s), [ordered label streams](goal)
retain observations of each label in their original relative order. [They are given by
the label-wise regrouping](step:1). -/
noncomputable def unshuffle (s : FiniteSample (X × I)) : I → FiniteSample X :=
  fun i => ⟨wordHistogram (fun k => (s.2 k).2) i,
    gatherWord (fun k => (s.2 k).2) (fun k => (s.2 k).1) i⟩

/-- Given [a fixed iid pool](hyp:x), [an admissible count](hyp:m,h), and [labels for that
prefix](hyp:w), [its ordered label streams](goal) preserve within-label arrival order.
[They are given by unshuffling the labeled prefix](step:1). -/
noncomputable def labeledPrefix {n : ℕ} (x : Fin n → X) (m : ℕ) (h : m ≤ n)
    (w : Fin m → I) : I → FiniteSample X :=
  unshuffle ⟨m, fun k => (x ⟨k.val, lt_of_lt_of_le k.isLt h⟩, w k)⟩

/-- Given [a fixed pool](hyp:x), [a Poisson count and label vector](hyp:z), [a stream
statistic](hyp:T), and [an overflow value](hyp:zOver), the [capped statistic](goal) evaluates
the labeled prefix when it fits and uses the overflow value otherwise. [It is given by
the capacity test](step:1). -/
noncomputable def cappedStatistic {n : ℕ} (x : Fin n → X) (T : (I → FiniteSample X) → ℝ)
    (zOver : ℝ) (z : ℕ × (Fin n → I)) : ℝ :=
  if h : z.1 ≤ n then
    T (labeledPrefix x z.1 h (fun k => z.2 ⟨k.val, lt_of_lt_of_le k.isLt h⟩))
  else zOver

/-- Given [label masses](hyp:p) [summing to one](hyp:hp), [a Poisson mean](hyp:lambda),
and [pool size](hyp:n), the [auxiliary law](goal) draws an independent Poisson count and
independent labels for all positions of the fixed pool. [It is given by their product
measure](step:1). -/
noncomputable def auxiliaryLaw (p : I → ℝ≥0) (hp : ∑ i, p i = 1)
    (lambda : ℝ≥0) (n : ℕ) : Measure (ℕ × (Fin n → I)) := by
  letI := labelLaw_isProbabilityMeasure p hp
  exact (poissonMeasure lambda).prod (Measure.pi (fun _ : Fin n => labelLaw p hp))

/-- Given [label masses](hyp:p) [summing to one](hyp:hp), [a Poisson mean](hyp:lambda),
[a fixed iid pool](hyp:x), [a stream statistic](hyp:T), and [an overflow value](hyp:zOver),
the [fixed-sample statistic](goal) averages the capped statistic over the independent count
and labels. [It is given by that auxiliary expectation](step:1). -/
noncomputable def fixedStatistic (p : I → ℝ≥0) (hp : ∑ i, p i = 1)
    (lambda : ℝ≥0) {n : ℕ} (x : Fin n → X)
    (T : (I → FiniteSample X) → ℝ) (zOver : ℝ) : ℝ :=
  ∫ z, cappedStatistic x T zOver z ∂auxiliaryLaw p hp lambda n

/-- Given [an observation law](hyp:P), [label masses](hyp:p) [summing to one](hyp:hp), and
[a Poisson mean](hyp:lambda), the [uncapped ordered-stream law](goal) labels a finite Poisson
sample and unshuffles it by label. [It is given by the mapped marked-Poisson law](step:1). -/
noncomputable def labeledStreamLaw (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (lambda : ℝ≥0) :
    Measure (I → FiniteSample X) := by
  letI := labelLaw_isProbabilityMeasure p hp
  exact Measure.map unshuffle (finitePoissonSampleLaw (P.prod (labelLaw p hp)) lambda)

/-- Given [an observation law](hyp:P) and [a pool size](hyp:n), the [fixed iid pool law](goal)
has independent observations at each of its positions. [It is given by the finite iid
product measure](step:1). -/
noncomputable def fixedPoolLaw (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) :
    Measure (Fin n → X) := Measure.pi (fun _ : Fin n => P)

end Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition
