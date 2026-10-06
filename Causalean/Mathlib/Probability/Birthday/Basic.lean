module
public import Causalean.Mathlib.Probability.BernoulliMeasure
public import Mathlib

/-!
# Binomially averaged birthday collisions

This module defines the collision probability for independent uniform labels,
its binomial average, and the mean and pair scales used by the limit theorem.
The falling factorial is zero when the number of draws exceeds the alphabet.
-/

@[expose] public section

namespace Causalean.Mathlib.Probability.Birthday

open Filter

/-- For an [alphabet size](hyp:m) and [draw count](hyp:r), the
[no-repeat kernel](goal) is [given by the falling factorial divided by the
number of all label sequences](step:1). -/
noncomputable def noRepeat (m r : ℕ) : ℝ :=
  (m.descFactorial r : ℝ) / (m : ℝ) ^ r

/-- For an [alphabet size](hyp:m) and [draw count](hyp:r), the
[repeat kernel](goal) is [given by the complement of the no-repeat
kernel](step:1). -/
noncomputable def repeatKernel (m r : ℕ) : ℝ := 1 - noRepeat m r

/-- For a [trial count](hyp:T), [success probability](hyp:eta), and
[count function](hyp:f), the [binomial average](goal) is [given by weighting
each possible success count by its binomial probability](step:1). -/
noncomputable def binomialAverage (T : ℕ) (eta : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (T + 1),
    Causalean.Mathlib.Probability.binomialWeight T eta r * f r

/-- For a [trial count](hyp:T), [alphabet size](hyp:m), and
[success probability](hyp:eta), the [averaged repeat probability](goal) is
[the binomial average of the finite uniform birthday collision
kernel](step:1). -/
noncomputable def birthdayRepeat (T m : ℕ) (eta : ℝ) : ℝ :=
  binomialAverage T eta (repeatKernel m)

/-- [The mean number of successes](goal) in [T trials](hyp:T) with
[success probability η](hyp:eta) is [the product T·η](step:1). -/
noncomputable def mean (T : ℕ) (eta : ℝ) : ℝ := (T : ℝ) * eta

/-- For a [trial count](hyp:T) and [success probability](hyp:eta), the
[expected number of unordered pairs](goal) is [given by the binomial pair
count times the squared success probability](step:1). -/
noncomputable def pairScale (T : ℕ) (eta : ℝ) : ℝ :=
  (T.choose 2 : ℝ) * eta ^ 2

end Causalean.Mathlib.Probability.Birthday
