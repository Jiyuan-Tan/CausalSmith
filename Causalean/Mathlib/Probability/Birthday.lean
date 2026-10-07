module
public import Causalean.Mathlib.Probability.Birthday.Basic
public import Causalean.Mathlib.Probability.Birthday.Concentration
public import Causalean.Mathlib.Probability.Birthday.Finite
public import Causalean.Mathlib.Probability.Birthday.Limit
public import Causalean.Mathlib.Probability.Birthday.LimitAverage
public import Causalean.Mathlib.Probability.Birthday.LimitBand
public import Causalean.Mathlib.Probability.Birthday.LimitScale
public import Causalean.Mathlib.Probability.Birthday.Moments
public import Causalean.Mathlib.Probability.Birthday.Rounding
public import Causalean.Mathlib.Probability.Birthday.Threshold
public import Causalean.Mathlib.Probability.Birthday.ThresholdFinite
public import Causalean.Mathlib.Probability.Birthday.ThresholdScale

/-!
# Birthday collisions with a binomial number of draws

Draw labels independently and uniformly from an alphabet of size m, where the number of draws is
Binomial(T, η). The probability that some label repeats tends to 1 − exp(−q) along any sequence
with mean T·η → ∞ and pair scale C(T, 2)·η²/m → q > 0. Consequently the least alphabet size
whose repeat probability is at most a tolerance δ ∈ (0, 1) is asymptotic to
C(T, 2)·η² / (−log(1 − δ)).

## Contents

* `Birthday.Basic` — the no-repeat probability m(m−1)⋯(m−r+1)/m^r, its complement `repeatKernel`,
  the binomial average `birthdayRepeat`, and the scales `mean` and `pairScale`.
* `Birthday.Finite` — finite bounds: exponential sandwiches for the no-repeat probability, the
  pair-count bound, and monotonicity in the alphabet size.
* `Birthday.Moments`, `Birthday.Concentration` — mass, mean and expected pair count of the
  binomial weights, and concentration of the count around a diverging mean.
* `Birthday.LimitAverage`, `Birthday.LimitBand`, `Birthday.LimitScale`, `Birthday.Limit` — the
  collision limit `repeat_tendsto`, and C(T, 2)·η² ~ (T·η)²/2.
* `Birthday.Rounding`, `Birthday.ThresholdFinite`, `Birthday.ThresholdScale`,
  `Birthday.Threshold` — the least threshold `mStar` and its asymptotic
  `mStar_div_calibratedScale_tendsto_one`.

This file only gathers the modules above.
-/
