module
public import Causalean.Stat.Concentration.VC.Empirical
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Efron bootstrap measures

This module defines the empirical distribution of a finite data vector, the product law of an
equal-size sample drawn with replacement, and the pushforward bootstrap law of a statistic.  The
definitions follow Efron's nonparametric bootstrap literally: the resample coordinates are
independent draws from the empirical distribution.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

/-- Given [a data vector of length `n`](hyp:x), its [empirical measure](goal) assigns mass `1/n`
to every indexed observation, counting repeated observations with their multiplicity. -/
def empiricalMeasure (x : Fin n → X) : Measure X :=
  Causalean.Stat.Concentration.finiteSampleMeasure x

/-- For [a data vector](hyp:x) with [nonzero length](hyp:hn), [its empirical measure has total
mass one](goal). -/
theorem empiricalMeasure_isProbabilityMeasure (x : Fin n → X) (hn : n ≠ 0) :
    IsProbabilityMeasure (empiricalMeasure x) := by
  exact Causalean.Stat.Concentration.finiteSampleMeasure_isProbabilityMeasure x
    (Nat.pos_of_ne_zero hn)

/-- Given [a data vector](hyp:x) whose length is known to be positive, [its empirical measure is
a probability measure](goal). -/
instance empiricalMeasure.instIsProbabilityMeasure [NeZero n] (x : Fin n → X) :
    IsProbabilityMeasure (empiricalMeasure x) :=
  empiricalMeasure_isProbabilityMeasure x (NeZero.ne n)

/-- Given [a data vector](hyp:x), its [Efron bootstrap resampling law](goal) is the finite product
of its empirical measure, so its `n` coordinates are independent draws with replacement. -/
def bootstrapResample (x : Fin n → X) : Measure (Fin n → X) :=
  Measure.pi (fun _ ↦ empiricalMeasure x)

/-- For [a data vector](hyp:x) with [nonzero length](hyp:hn), [the Efron resampling law has total
mass one](goal). -/
theorem bootstrapResample_isProbabilityMeasure (x : Fin n → X) (hn : n ≠ 0) :
    IsProbabilityMeasure (bootstrapResample x) := by
  -- Proof plan: install `empiricalMeasure_isProbabilityMeasure x hn` locally and use
  -- Mathlib's `Measure.pi.instIsProbabilityMeasure`.
  let _ : IsProbabilityMeasure (empiricalMeasure x) :=
    empiricalMeasure_isProbabilityMeasure x hn
  unfold bootstrapResample
  exact Measure.pi.instIsProbabilityMeasure (fun _ ↦ empiricalMeasure x)

/-- Given [a data vector](hyp:x) whose length is known to be positive, [its Efron resampling law
is a probability measure](goal). -/
instance bootstrapResample.instIsProbabilityMeasure [NeZero n] (x : Fin n → X) :
    IsProbabilityMeasure (bootstrapResample x) :=
  bootstrapResample_isProbabilityMeasure x (NeZero.ne n)

/-- Given [a real-valued sample statistic](hyp:T) and [observed data](hyp:x), the [bootstrap law
of the statistic](goal) is the pushforward of the Efron resampling law through that statistic. -/
def bootstrapLaw (T : (Fin n → X) → ℝ) (x : Fin n → X) : Measure ℝ :=
  (bootstrapResample x).map T

/-- Given [a real-valued sample statistic](hyp:T) and [observed data](hyp:x), if [the statistic
is measurable](hyp:hT) and [the data size is nonzero](hyp:hn), [its bootstrap law has total mass
one](goal). -/
theorem bootstrapLaw_isProbabilityMeasure (T : (Fin n → X) → ℝ) (x : Fin n → X)
    (hn : n ≠ 0) (hT : Measurable T) : IsProbabilityMeasure (bootstrapLaw T x) := by
  -- Proof plan: install the preceding resample-law instance and apply
  -- `Measure.isProbabilityMeasure_map hT.aemeasurable`.
  let _ : IsProbabilityMeasure (bootstrapResample x) :=
    bootstrapResample_isProbabilityMeasure x hn
  unfold bootstrapLaw
  exact Measure.isProbabilityMeasure_map hT.aemeasurable

end

end Causalean.Stat
