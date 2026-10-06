/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Partition.Finpartition

/-!
# Cumulants of real random variables, and the Gaussian-law predicate

This module provides the general moment-to-cumulant coordinates used throughout the
moment-problem layer: the joint cumulant of a pair of real random variables at a given
bidegree (defined by the set-partition Möbius formula on mixed moments), the univariate
cumulant of a single real random variable obtained by specializing it, and the predicate
"this law on the real line is a Gaussian law".

The total-order-zero cumulant is defined to be zero, matching the constant term of the
cumulant-generating function. At every positive total order, the usual set-partition formula is
used.

For variables with the needed moments, the second cumulant is the variance, the third is the
centered third moment, and the fourth is the unnormalized fourth cumulant. The standardized ratio
of the fourth cumulant to the variance squared is excess kurtosis when the variance is positive.
This file does not prove that vanishing higher cumulants characterizes Gaussian laws; such a
characterization needs additional moment-existence and determinacy assumptions. The Gaussian
predicate here is the *distributional* property of being some `gaussianReal`, including degenerate
Dirac laws.
-/

@[expose] public section

namespace Causalean.Stat.MomentProblems

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-- For [a measure on the real line](hyp:ν), the [Gaussian-law property](goal) holds exactly when
there exist a real mean and a nonnegative variance parameter such that the measure is the
associated normal distribution. The variance parameter may be zero, so point masses count as
degenerate Gaussian laws.

A probability law on the real line is a **Gaussian law** when it is a normal distribution:
there is a mean and a (possibly zero) variance whose normal distribution is exactly this law.
Allowing zero variance means the point masses (Diracs) count as degenerate Gaussians, so the
negation "not a Gaussian law" is the strongest possible non-Gaussianity requirement. -/
def IsGaussianLaw (ν : Measure ℝ) : Prop :=
  ∃ (mean : ℝ) (v : ℝ≥0), ν = gaussianReal mean v

/-- Given [a sample space equipped with a σ-algebra](hyp:Ω), [a measure on that space](hyp:μ),
[two real-valued random variables](hyp:X,Y), and [two nonnegative integer orders](hyp:p,q), the
[joint cumulant at the specified bidegree](goal) is zero when both orders are zero; otherwise it is
the sum over every partition of the combined slots, with the first $p$ slots assigned to the first
variable and the remaining $q$ slots assigned to the second, of a signed factorial weight times
the product, across its blocks, of the mixed moment whose exponents equal that block's counts of
first- and second-variable slots.

The **joint cumulant** of two real random variables at bidegree `(p, q)`: the cumulant of the
first variable taken `p` times together with the second taken `q` times. At bidegree `(0, 0)` it
is zero. At positive total degree it is obtained from the mixed moments by the classical
set-partition (Möbius) inversion.

For centered variables with the needed moments this reproduces the familiar formulae: bidegree
`(2, 0)` is the variance, `(1, 1)` is the covariance, and bidegree `(4, 0)` is the unnormalized
fourth cumulant. -/
noncomputable def jointCumulant (μ : Measure Ω) (X Y : Ω → ℝ) (p q : ℕ) : ℝ :=
  if p + q = 0 then 0 else
    ∑ π : Finpartition (Finset.univ : Finset (Fin (p + q))),
      (-1 : ℝ) ^ (π.parts.card - 1) * (Nat.factorial (π.parts.card - 1) : ℝ) *
        ∏ B ∈ π.parts,
          ∫ ω, (X ω) ^ (B.filter (fun i => i.val < p)).card
                * (Y ω) ^ (B.filter (fun i => p ≤ i.val)).card ∂μ

/-- Given [a sample space equipped with a σ-algebra](hyp:Ω), [a measure on that space](hyp:μ),
and [two real-valued random variables](hyp:X,Y), [their joint cumulant at bidegree `(0, 0)` is
zero](goal). -/
@[simp]
theorem jointCumulant_zero_zero (μ : Measure Ω) (X Y : Ω → ℝ) :
    jointCumulant μ X Y 0 0 = 0 := by
  simp [jointCumulant]

/-- Given [a sample space equipped with a σ-algebra](hyp:Ω), [a measure on that space](hyp:μ),
[a real-valued random variable](hyp:S), and [a nonnegative integer order](hyp:r), the [cumulant of
that order](goal) is zero at order zero and otherwise is the joint cumulant obtained by placing that
same variable in every slot.

The **cumulant of order `r`** of a single real random variable is zero at order zero. At positive
orders it is the joint cumulant of the variable with itself in which every slot is filled by that
one variable. With the needed moments, order two is the variance, order three the centered third
moment, and order four the unnormalized fourth cumulant. -/
noncomputable def sourceCumulant (μ : Measure Ω) (S : Ω → ℝ) (r : ℕ) : ℝ :=
  jointCumulant μ S S r 0

/-- Given [a sample space equipped with a σ-algebra](hyp:Ω), [a measure on that space](hyp:μ),
and [a real-valued random variable](hyp:S), [its order-zero cumulant is zero](goal). -/
@[simp]
theorem sourceCumulant_zero (μ : Measure Ω) (S : Ω → ℝ) :
    sourceCumulant μ S 0 = 0 := by
  simp [sourceCumulant]

end Causalean.Stat.MomentProblems
