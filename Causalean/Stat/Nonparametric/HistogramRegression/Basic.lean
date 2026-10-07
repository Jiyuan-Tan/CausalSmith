module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Totalized finite-partition regression histograms

A finite measurable label map represents a partition: its fibers are disjoint
and cover the covariate space. Empty and zero-mass fibers are allowed. Samples
are tuples of observations, whose covariates and responses are supplied by maps.
The estimator clips the empirical response average to `[0,1]` and uses a fixed
default when the observed cell count is zero, including sample size zero.

Reference for the estimator and integrated marginal loss: A. Nobel, *Histogram
Regression Estimation Using Data-dependent Partitions*, Ann. Statist. 24 (1996),
1084–1105, equations (1)–(2),
https://nobel.web.unc.edu/wp-content/uploads/sites/13591/2017/01/histreg.pdf.
Here partitions are deterministic, and the empty-cell default is arbitrary.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Causalean.Stat.Nonparametric.HistogramRegression

noncomputable section

variable {Ω A κ : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [Finite κ] [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- The [cell](goal) with [label](hyp:k) is the inverse image under the
[partition map](hyp:label) of that label after applying [the covariate map](hyp:X). -/
def cell (label : A → κ) (X : Ω → A) (k : κ) : Set Ω :=
  {ω | label (X ω) = k}

/-- The [cell probability](goal) is the real mass under [the observation law](hyp:μ)
of the cell specified by [the partition, covariate map, and label](hyp:label,X,k). -/
def cellMass (μ : Measure Ω) (label : A → κ) (X : Ω → A) (k : κ) : ℝ :=
  (μ (cell label X k)).toReal

/-- The [sample cell count](goal) counts entries of [the sample](hyp:z) whose
[covariates](hyp:X) have [the specified partition label](hyp:label,k). -/
def cellCount {m : ℕ} (label : A → κ) (X : Ω → A) (k : κ)
    (z : Fin m → Ω) : ℕ :=
  (Finset.univ.filter fun r => label (X (z r)) = k).card

/-- The [cell response sum](goal) sums [responses](hyp:Y) in [the sample](hyp:z)
over the cell specified by [the partition, covariate map, and label](hyp:label,X,k). -/
def cellSum {m : ℕ} (label : A → κ) (X : Ω → A) (Y : Ω → ℝ)
    (k : κ) (z : Fin m → Ω) : ℝ :=
  ∑ r : Fin m, if label (X (z r)) = k then Y (z r) else 0

/-- [Clipping](goal) maps [a real input](hyp:t) to its nearest point in `[0,1]`. -/
def clip (t : ℝ) : ℝ := max 0 (min 1 t)

/-- The [cell estimate](goal) clips the empirical average of [responses](hyp:Y)
in [a sample](hyp:z) within [the specified covariate partition cell](hyp:label,X,k),
and returns [the fixed default](hyp:a) when the cell is empty. -/
def cellEstimate {m : ℕ} (label : A → κ) (X : Ω → A) (Y : Ω → ℝ)
    (a : ℝ) (k : κ) (z : Fin m → Ω) : ℝ :=
  if cellCount label X k z = 0 then a
  else clip (cellSum label X Y k z / (cellCount label X k z : ℝ))

/-- The [histogram prediction](goal) at [a query covariate](hyp:x) is the cell
estimate using [the partition, covariates, responses, default, and sample](hyp:label,X,Y,a,z). -/
def histogram {m : ℕ} (label : A → κ) (X : Ω → A) (Y : Ω → ℝ)
    (a : ℝ) (z : Fin m → Ω) (x : A) : ℝ :=
  cellEstimate label X Y a (label x) z

/-- The [expected integrated squared risk](goal) averages squared prediction
error against [the target](hyp:g), integrating a fresh covariate drawn from
[the observation law](hyp:μ) and training samples drawn from [the sample law](hyp:ν),
using [the partition, covariates, responses, and default](hyp:label,X,Y,a). -/
def risk {m : ℕ} (μ : Measure Ω) (ν : Measure (Fin m → Ω))
    (label : A → κ) (X : Ω → A) (Y : Ω → ℝ) (a : ℝ) (g : A → ℝ) : ℝ :=
  ∫ z, (∫ ω, (histogram label X Y a z (X ω) - g (X ω)) ^ 2 ∂μ) ∂ν

/-- The [positive-mass labels](goal) retain precisely those cells of
[the partition and covariate map](hyp:label,X) with positive mass under [the law](hyp:μ). -/
def positiveCells [Fintype κ] (μ : Measure Ω) (label : A → κ) (X : Ω → A) : Finset κ :=
  Finset.univ.filter fun k => 0 < cellMass μ label X k

/-- [Measurable covariates and partition labels](hyp:hX,hlabel) give
[measurable cell counts](goal). -/
@[fun_prop] theorem measurable_cellCount {m : ℕ} (label : A → κ) (X : Ω → A) (k : κ)
    (hlabel : Measurable label) (hX : Measurable X) :
    Measurable (cellCount (m := m) label X k) := by
  classical
  have hsum : Measurable (fun z : Fin m → Ω =>
      ∑ r : Fin m, if label (X (z r)) = k then (1 : ℕ) else 0) := by
    apply Finset.measurable_fun_sum
    intro r _
    exact Measurable.ite
      ((measurableSet_singleton k).preimage
        (hlabel.comp (hX.comp (measurable_pi_apply r))))
      measurable_const measurable_const
  change Measurable (fun z : Fin m → Ω =>
    (Finset.univ.filter fun r => label (X (z r)) = k).card)
  simpa only [Finset.card_filter] using hsum

/-- [Measurable covariates, responses, and labels](hyp:hX,hY,hlabel) give
[measurable cell estimates](goal), for every fixed default and cell. -/
@[fun_prop] theorem measurable_cellEstimate {m : ℕ} (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (a : ℝ) (k : κ) (hlabel : Measurable label)
    (hX : Measurable X) (hY : Measurable Y) :
    Measurable (cellEstimate (m := m) label X Y a k) := by
  classical
  have hcount := measurable_cellCount (m := m) label X k hlabel hX
  have hsum : Measurable (cellSum (m := m) label X Y k) := by
    unfold cellSum
    apply Finset.measurable_fun_sum
    intro r _
    exact Measurable.ite
      ((measurableSet_singleton k).preimage
        (hlabel.comp (hX.comp (measurable_pi_apply r))))
      (hY.comp (measurable_pi_apply r)) measurable_const
  have hcast : Measurable (fun z : Fin m → Ω => (cellCount label X k z : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hcount
  unfold cellEstimate clip
  exact Measurable.ite ((measurableSet_singleton 0).preimage hcount)
    measurable_const (measurable_const.max (measurable_const.min (hsum.div hcast)))

/-- [Measurable covariates, responses, and labels](hyp:hX,hY,hlabel) give
[jointly measurable histogram predictions in the sample and query](goal). -/
@[fun_prop] theorem measurable_histogram {m : ℕ} (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (a : ℝ) (hlabel : Measurable label)
    (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun q : (Fin m → Ω) × A => histogram label X Y a q.1 q.2) := by
  classical
  let _ := Fintype.ofFinite κ
  have hsum : Measurable (fun q : (Fin m → Ω) × A =>
      ∑ k : κ, if label q.2 = k then cellEstimate label X Y a k q.1 else 0) := by
    apply Finset.measurable_fun_sum
    intro k _
    exact Measurable.ite
      ((measurableSet_singleton k).preimage (hlabel.comp measurable_snd))
      ((measurable_cellEstimate label X Y a k hlabel hX hY).comp measurable_fst)
      measurable_const
  simpa [histogram] using hsum

/-- [A default value in the unit interval](hyp:ha) ensures that
[every cell estimate belongs to the unit interval](goal). -/
theorem cellEstimate_mem_Icc {m : ℕ} (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (a : ℝ) (k : κ) (z : Fin m → Ω)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    cellEstimate label X Y a k z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold cellEstimate
  split_ifs with hzero
  · exact ha
  · exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

end

end Causalean.Stat.Nonparametric.HistogramRegression
