/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Empirical process: vocabulary for uniform laws of large numbers

Causal-agnostic empirical-process primitives for an `Causalean.Stat.IIDSample`,
written for the econometrics workflow (van der Vaart 1998, Ch. 19; Newey &
McFadden 1994, §2).  A *function class* is an indexed family `f : ι → X → ℝ`;
the empirical process measures how far the sample means `Pₙ f_i` are from the
population means `P f_i = ∫ f_i dP`, *uniformly over the class*.

This file fixes the vocabulary; the weak uniform law of large numbers is
proved in `GlivenkoCantelli.lean` and consumed by
`MEstimatorConsistency.lean`.

Main definitions:

* `IIDSample.empiricalProcess f i n` — the centred-and-scaled process
  `√n · (Pₙ f_i − P f_i)` at class member `i`.
* `IIDSample.supDeviation f n` — the finite-class sup deviation
  `⨆ i, |Pₙ f_i − P f_i|` (used as a convenient real-valued statistic when `ι`
  is finite).
* `WeakGlivenkoCantelli S f` — the weak uniform law of large numbers: for every
  `ε > 0`, the probability that *some* class member deviates by `≥ ε` tends to
  `0`.  Phrased with an existential rather than `⨆` so it is meaningful for
  infinite (uncountable) classes without lattice-junk artefacts.
* `L1Bracketing f P ε` — a finite `L¹(P)` `ε`-bracketing of the class: finitely
  many `[lo j, hi j]` brackets with `∫ |hi j − lo j| dP ≤ ε`, together with a
  common full-measure support on which every class member is sandwiched.  The
  bracketing number being finite at every `ε` is the classical sufficient
  condition for Glivenko–Cantelli.
-/

module
public import Causalean.Stat.Sample
public import Causalean.Stat.Limit.Convergence
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Empirical Process Basics

This file introduces the empirical-process vocabulary for uniform laws of large
numbers over indexed classes of real-valued functions.  It defines
`IIDSample.empiricalProcess`, `IIDSample.supDeviation`, the weak uniform law
predicate `WeakGlivenkoCantelli`, the finite-bracketing structure `L1Bracketing`,
and the arbitrary-small-bracketing hypothesis `HasL1Bracketing` consumed by the
Glivenko-Cantelli and M-estimator consistency files. The unqualified name
`GlivenkoCantelli` is reserved for the almost-sure version, which has not yet
been formalized; a deprecated alias preserves the former weak-law API. -/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

namespace IIDSample

/-- The [empirical process](goal) is the root-sample-size-scaled difference between
the empirical and population means of [one function](hyp:i) from [an indexed
class](hyp:f), evaluated on [an i.i.d. sample](hyp:S) of [size](hyp:n).  Its
ambient [spaces and measures](hyp:Ω,X,ι,μ,P) determine the sample law and the
population integral.

The object whose weak limit (a Gaussian process) is the subject of Donsker theory. -/
noncomputable def empiricalProcess (S : IIDSample Ω X μ P) (f : ι → X → ℝ)
    (i : ι) (n : ℕ) : Ω → ℝ :=
  fun ω => Real.sqrt (n : ℝ) * (S.sampleMean (f i) n ω - ∫ x, f i x ∂P)

/-- The [supremum deviation statistic](goal) records the largest absolute gap
between empirical and population means across [a real-valued function
class](hyp:f), using the first [n observations](hyp:n) of [an i.i.d.
sample](hyp:S).  The [ambient spaces and measures](hyp:Ω,X,ι,μ,P) fix the
sampling and population laws.

Meaningful as a real-valued statistic when the class is finite (otherwise the supremum may
collapse to zero on an unbounded family, which is why `WeakGlivenkoCantelli` is stated existentially
instead). -/
noncomputable def supDeviation (S : IIDSample Ω X μ P) (f : ι → X → ℝ)
    (n : ℕ) : Ω → ℝ :=
  fun ω => ⨆ i, |S.sampleMean (f i) n ω - ∫ x, f i x ∂P|

end IIDSample

/-- The [weak Glivenko--Cantelli property](goal) says that the probability of
any member of [a real-valued function class](hyp:f) having a fixed-size
empirical-mean error along [an i.i.d. sample](hyp:S) tends to zero.  The
[ambient spaces and measures](hyp:Ω,X,ι,μ,P) specify the sample and population
laws.

The existential formulation `{ω | ∃ i, ε ≤ |Pₙ f_i − P f_i|}` (rather than
`{ω | ε ≤ supDeviation}`) is robust to infinite classes and matches how the
property is consumed in `MEstimatorConsistency.lean`. -/
def WeakGlivenkoCantelli (S : IIDSample Ω X μ P) (f : ι → X → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto
      (fun n => μ {ω | ∃ i, ε ≤ |S.sampleMean (f i) n ω - ∫ x, f i x ∂P|})
      atTop (𝓝 0)

/-- Deprecated compatibility name for [the weak uniform law of large
numbers](goal) of [an iid sample](hyp:S) over [a function class](hyp:f). -/
@[deprecated (since := "2026-09-17")]
alias GlivenkoCantelli := WeakGlivenkoCantelli

/-- A finite `L¹(P)` `ε`-bracketing of a real-valued function class consists of
finitely many integrable lower and upper endpoints, a common full-measure
support on which every class member is sandwiched by its assigned bracket, and
an integrated absolute bracket width at most `ε`.

This is the standard almost-everywhere `L¹(P)` bracketing formulation: the
sandwich inequalities need hold only on a single `P`-full support set, and the
width of a bracket is measured by `∫ |hi − lo| dP`. -/
structure L1Bracketing (f : ι → X → ℝ) (P : Measure X) (ε : ℝ) where
  /-- Number of brackets. -/
  m : ℕ
  /-- Lower endpoints. -/
  lo : Fin m → X → ℝ
  /-- Upper endpoints. -/
  hi : Fin m → X → ℝ
  lo_meas : ∀ j, Measurable (lo j)
  hi_meas : ∀ j, Measurable (hi j)
  lo_int : ∀ j, Integrable (lo j) P
  hi_int : ∀ j, Integrable (hi j) P
  /-- Common measurable support on which all bracket inequalities hold. -/
  support : Set X
  support_meas : MeasurableSet support
  /-- The common support has full `P`-measure. -/
  support_ae : ∀ᵐ x ∂P, x ∈ support
  /-- Bracket assigned to each class member. -/
  assign : ι → Fin m
  lo_le : ∀ i, ∀ x ∈ support, lo (assign i) x ≤ f i x
  le_hi : ∀ i, ∀ x ∈ support, f i x ≤ hi (assign i) x
  /-- Each bracket has `L¹(P)` width at most `ε`. -/
  mesh : ∀ j, ∫ x, |hi j x - lo j x| ∂P ≤ ε

/-- The [arbitrarily fine finite `L¹`-bracketing property](goal) says that [a
real-valued function class](hyp:f) on [an indexed measurable
space](hyp:X,ι) admits finite brackets of every positive width under [the
population measure](hyp:P), with all sandwiches valid on one common full-measure
set.

This is the standard bracketing hypothesis for the Glivenko-Cantelli theorem. -/
def HasL1Bracketing (f : ι → X → ℝ) (P : Measure X) : Prop :=
  ∀ ε : ℝ, 0 < ε → Nonempty (L1Bracketing f P ε)

end Causalean.Stat
