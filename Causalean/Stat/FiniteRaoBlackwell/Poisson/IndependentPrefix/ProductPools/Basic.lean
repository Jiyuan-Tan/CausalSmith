/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.Basic

/-!
# Finite families of independent Poisson prefixes

This module provides the measurable experiment, exact product laws, and capped
implementation for finitely many heterogeneous iid pools, each given an
independent Poisson prefix length.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

universe uI uX

variable {I : Type uI} [Fintype I] [DecidableEq I]
  {X : I → Type uX} [∀ i, MeasurableSpace (X i)]

/-- Given a [family of observation alphabets](hyp:X) and [pool capacities](hyp:N),
[fixed pools](goal) give each coordinate an ordered iid observation pool. [They are represented
by the dependent family of coordinate pools](step:1). -/
abbrev FixedPools (X : I → Type uX) [∀ i, MeasurableSpace (X i)]
    (N : I → ℕ) :=
  (i : I) → Fin (N i) → X i

/-- Given a [family of observation alphabets](hyp:X) and [pool capacities](hyp:N),
[the randomized pool family](goal) appends one requested prefix length to each coordinate pool.
[It is represented by the dependent family of pool-length pairs](step:1). -/
abbrev RandomizedPools (X : I → Type uX) [∀ i, MeasurableSpace (X i)]
    (N : I → ℕ) :=
  (i : I) → (Fin (N i) → X i) × ℕ

/-- Given a [family of observation alphabets](hyp:X), [a prefix family](goal) contains one
variable-length finite sample for each coordinate. [It is represented by the dependent family
of finite samples](step:1). -/
abbrev PrefixFamily (X : I → Type uX) [∀ i, MeasurableSpace (X i)] :=
  (i : I) → FiniteSample (X i)

/-- Given a [family of observation alphabets](hyp:X), [a Poisson stream family](goal) gives each
coordinate a requested count and an infinite observation stream. [It is represented by the
dependent family of count-stream pairs](step:1). -/
abbrev PoissonStreamFamily (X : I → Type uX)
    [∀ i, MeasurableSpace (X i)] :=
  (i : I) → ℕ × (ℕ → X i)

/-- Given [coordinatewise probability laws](hyp:P) and [pool capacities](hyp:N), [the fixed-pool
law](goal) makes the observations iid within and independent across pools. [It is given by the
finite product of coordinatewise iid laws](step:1). -/
noncomputable def fixedPoolsLaw
    (P : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    (N : I → ℕ) : Measure (FixedPools X N) :=
  Measure.pi (fun i ↦ Measure.pi (fun _ : Fin (N i) ↦ P i))

/-- Given [coordinatewise probability laws](hyp:P), [Poisson intensities](hyp:lambda), and [pool
capacities](hyp:N), [the randomized-pool law](goal) makes pools, counts, and coordinates mutually
independent. [It is given by the finite product of pool-count laws](step:1). -/
noncomputable def randomizedPoolsLaw
    (P : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    (lambda : I → ℝ≥0) (N : I → ℕ) : Measure (RandomizedPools X N) :=
  Measure.pi (fun i ↦
    (Measure.pi (fun _ : Fin (N i) ↦ P i)).prod (poissonMeasure (lambda i)))

/-- Given [coordinatewise probability laws](hyp:P) and [Poisson intensities](hyp:lambda), [the
independent Poisson-prefix law](goal) is the joint law of all untruncated iid prefixes. [It is
given by the finite product of coordinatewise Poisson sample laws](step:1). -/
noncomputable def independentPoissonPrefixLaw
    (P : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    (lambda : I → ℝ≥0) : Measure (PrefixFamily X) :=
  Measure.pi (fun i ↦ finitePoissonSampleLaw (P i) (lambda i))

/-- Given [coordinatewise probability laws](hyp:P) and [Poisson intensities](hyp:lambda), [the
independent count-and-stream law](goal) independently supplies a count and iid stream in every
coordinate. [It is given by the finite product of coordinatewise stream laws](step:1). -/
noncomputable def independentPoissonStreamLaw
    (P : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    (lambda : I → ℝ≥0) : Measure (PoissonStreamFamily X) :=
  Measure.pi (fun i ↦ poissonIIDStreamLaw (P i) (lambda i))

/-- Given [pool capacities](hyp:N), [the joint nonoverflow event](goal) is the event that
every requested prefix fits its coordinate pool. [It is given by the coordinatewise capacity
bounds](step:1). -/
def nonoverflowSet (N : I → ℕ) : Set (RandomizedPools X N) :=
  {z | ∀ i, (z i).2 ≤ N i}

/-- Given [pool capacities](hyp:N), [the overflow event](goal) is the event that at least one
requested prefix exceeds its coordinate pool. [It is given by the union of marginal overflow
events](step:1). -/
def overflowSet (N : I → ℕ) : Set (RandomizedPools X N) :=
  {z | ∃ i, N i < (z i).2}

/-- Given [pool capacities](hyp:N), [the event that every untruncated prefix fits its coordinate
capacity is measurable](goal). -/
theorem measurableSet_prefixNonoverflowSet (N : I → ℕ) :
    MeasurableSet {s : PrefixFamily X | ∀ i, (s i).count ≤ N i} := by
  rw [show {s : PrefixFamily X | ∀ i, (s i).count ≤ N i} =
      Set.univ.pi (fun i ↦
        (FiniteSample.count : FiniteSample (X i) → ℕ) ⁻¹' Set.Iic (N i)) by
    ext s
    simp]
  exact MeasurableSet.univ_pi (X := fun i ↦ FiniteSample (X i)) fun i ↦
    (measurable_finiteSample_count (X := X i)) measurableSet_Iic

/-- Given [pool capacities](hyp:N), [the joint nonoverflow event is measurable](goal). -/
theorem measurableSet_nonoverflowSet (N : I → ℕ) :
    MeasurableSet (nonoverflowSet (X := X) N) := by
  rw [show nonoverflowSet (X := X) N = Set.univ.pi (fun i ↦
      (Prod.snd : ((Fin (N i) → X i) × ℕ) → ℕ) ⁻¹' Set.Iic (N i)) by
    ext z
    simp [nonoverflowSet]]
  exact MeasurableSet.univ_pi
    (X := fun i ↦ (Fin (N i) → X i) × ℕ) fun i ↦
      (measurable_snd : Measurable
        (Prod.snd : ((Fin (N i) → X i) × ℕ) → ℕ)) measurableSet_Iic

/-- Given [pool capacities](hyp:N), [the union of marginal overflow events is
measurable](goal). -/
theorem measurableSet_overflowSet (N : I → ℕ) :
    MeasurableSet (overflowSet (X := X) N) := by
  rw [show overflowSet (X := X) N =
      ⋃ i, (fun z : RandomizedPools X N ↦ (z i).2) ⁻¹' Set.Ioi (N i) by
    ext z
    simp [overflowSet]]
  exact MeasurableSet.iUnion fun i ↦
    (measurable_snd.comp (measurable_pi_apply i)) measurableSet_Ioi

/-- Given [pool capacities](hyp:N), [joint nonoverflow is the complement of the overflow
event](goal). -/
theorem nonoverflowSet_eq_compl_overflowSet (N : I → ℕ) :
    nonoverflowSet (X := X) N = (overflowSet (X := X) N)ᶜ := by
  ext z
  simp [nonoverflowSet, overflowSet, not_lt]

/-- Given [a count-and-stream family](hyp:z), [its prefix family](goal) retains the requested
initial segment of every stream. [It is given by coordinatewise stream truncation](step:1). -/
def streamFamilyToPrefixFamily (z : PoissonStreamFamily X) : PrefixFamily X :=
  fun i ↦ streamToFiniteSample (z i)

/-- [Conversion of count-and-stream families to prefix families is measurable](goal). -/
@[fun_prop]
theorem measurable_streamFamilyToPrefixFamily :
    Measurable (streamFamilyToPrefixFamily (I := I) (X := X)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_streamToFiniteSample.comp (measurable_pi_apply i)

/-- Given [coordinatewise probability laws](hyp:P) and [Poisson intensities](hyp:lambda),
[mapping independent count-and-stream coordinates to prefixes gives exactly the independent
Poisson-prefix law](goal). -/
theorem map_independentPoissonStreamLaw_eq_independentPoissonPrefixLaw
    (P : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    (lambda : I → ℝ≥0) :
    Measure.map (streamFamilyToPrefixFamily (I := I) (X := X))
        (independentPoissonStreamLaw P lambda) =
      independentPoissonPrefixLaw P lambda := by
  unfold streamFamilyToPrefixFamily independentPoissonStreamLaw
    independentPoissonPrefixLaw finitePoissonSampleLaw
  rw [Measure.pi_map_pi fun i ↦ measurable_streamToFiniteSample.aemeasurable]

/-- Given [fallback prefixes](hyp:overflow) and [a randomized pool family](hyp:z), [the
totalized prefix family](goal) uses genuine prefixes when available and the corresponding
fallback otherwise. [It is given by coordinatewise one-pool totalization](step:1). -/
def totalizedPrefixFamily {N : I → ℕ} (overflow : PrefixFamily X)
    (z : RandomizedPools X N) : PrefixFamily X :=
  fun i ↦ totalizedPrefix (overflow i) (z i).1 (z i).2

/-- Given [fallback prefixes](hyp:overflow), [coordinatewise totalization is measurable](goal). -/
@[fun_prop]
theorem measurable_totalizedPrefixFamily {N : I → ℕ}
    (overflow : PrefixFamily X) :
    Measurable (totalizedPrefixFamily (I := I) overflow :
      RandomizedPools X N → PrefixFamily X) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_totalizedPrefix (overflow i)).comp (measurable_pi_apply i)

/-- Given [a prefix statistic](hyp:T), [an overflow value](hyp:zOver), and [a randomized pool
family](hyp:z), [the capped-prefix statistic](goal) uses genuine prefixes precisely when every
request fits. [It is given by the joint capacity test](step:1). -/
def cappedPrefixStatistic {N : I → ℕ}
    (T : PrefixFamily X → ℝ) (zOver : ℝ)
    (z : RandomizedPools X N) : ℝ :=
  if h : ∀ i, (z i).2 ≤ N i then
    T (fun i ↦ prefixOfLE (z i).1 (z i).2 (h i))
  else zOver

/-- Given [a measurable prefix statistic](hyp:hT) and [an overflow value](hyp:zOver), [the
capped-prefix statistic is measurable](goal). -/
@[fun_prop]
theorem measurable_cappedPrefixStatistic {N : I → ℕ}
    {T : PrefixFamily X → ℝ} (hT : Measurable T) (zOver : ℝ) :
    Measurable (cappedPrefixStatistic (I := I) (N := N) T zOver) := by
  classical
  let overflow : PrefixFamily X := fun _ ↦ ⟨0, Fin.elim0⟩
  have hfun : cappedPrefixStatistic (I := I) (N := N) T zOver =
      (nonoverflowSet (X := X) N).piecewise
        (T ∘ totalizedPrefixFamily overflow) (fun _ ↦ zOver) := by
    funext z
    by_cases h : ∀ i, (z i).2 ≤ N i
    · rw [cappedPrefixStatistic, dif_pos h]
      rw [Set.piecewise, if_pos (show z ∈ nonoverflowSet (X := X) N from h)]
      congr 1
      funext i
      simp [totalizedPrefixFamily, totalizedPrefix, cappedPrefix, h i]
    · rw [cappedPrefixStatistic, dif_neg h]
      simp [Set.piecewise, nonoverflowSet, h]
  rw [hfun]
  exact Measurable.piecewise (measurableSet_nonoverflowSet N)
    (hT.comp (measurable_totalizedPrefixFamily overflow)) measurable_const

/-- Given [a prefix statistic](hyp:T), [an overflow value](hyp:zOver),
[fallback prefixes](hyp:overflow), [a randomized pool family](hyp:z), and
[evidence of no overflow](hyp:hz), [the capped statistic
equals the statistic of the totalized prefixes](goal). -/
theorem cappedPrefixStatistic_eq_off_overflow {N : I → ℕ}
    (T : PrefixFamily X → ℝ) (zOver : ℝ) (overflow : PrefixFamily X)
    (z : RandomizedPools X N) (hz : z ∉ overflowSet (X := X) N) :
    cappedPrefixStatistic T zOver z = T (totalizedPrefixFamily overflow z) := by
  have h : ∀ i, (z i).2 ≤ N i := by
    intro i
    exact Nat.le_of_not_gt fun hi ↦ hz ⟨i, hi⟩
  rw [cappedPrefixStatistic, dif_pos h]
  congr 1
  funext i
  simp [totalizedPrefixFamily, totalizedPrefix, cappedPrefix, h i]

/-- Given [coordinatewise probability laws](hyp:P), [Poisson intensities](hyp:lambda), [pool
capacities](hyp:N), and [fallback prefixes](hyp:overflow), [mapping jointly nonoverflowing
randomized pools to totalized prefixes gives the restricted untruncated product law](goal). -/
theorem map_totalizedPrefixFamily_restrict_nonoverflow
    (P : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    (lambda : I → ℝ≥0) (N : I → ℕ) (overflow : PrefixFamily X) :
    Measure.map (totalizedPrefixFamily overflow)
        ((randomizedPoolsLaw P lambda N).restrict (nonoverflowSet (X := X) N)) =
      (independentPoissonPrefixLaw P lambda).restrict
        {s : PrefixFamily X | ∀ i, (s i).count ≤ N i} := by
  rw [show nonoverflowSet (X := X) N =
      Set.univ.pi (fun i ↦ Prod.snd ⁻¹' Set.Iic (N i)) by
    ext z
    simp [nonoverflowSet]]
  unfold randomizedPoolsLaw independentPoissonPrefixLaw totalizedPrefixFamily
  rw [Measure.restrict_pi_pi]
  rw [Measure.pi_map_pi fun i ↦
    (measurable_totalizedPrefix (overflow i)).aemeasurable]
  simp_rw [map_totalizedPrefix_restrict_nonoverflow]
  rw [← Measure.restrict_pi_pi]
  congr 1
  ext s
  simp

end Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily
