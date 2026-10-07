module
public import Causalean.Stat.Concentration.VC.BasicVarianceAdaptiveVCExpectedMaximal
public import Causalean.Stat.Concentration.VC.EmpiricalCover
public import Causalean.Stat.Concentration.VC.EntropyChaining
public import Causalean.Stat.Concentration.VC.ExpectedMaximal
public import Causalean.Stat.Concentration.VC.Rademacher
public import Causalean.Stat.Concentration.VC.Separability

/-!
# Variance-adaptive expected maximal inequalities

For a countable class of measurable functions bounded by `U`, with population L² norm at most
`σ < U` and polynomial empirical L² covering numbers (base `A ≥ e`, exponent `v ≥ 1`), the expected
supremum of the centred empirical process over an i.i.d. sample of size `n` is at most a universal
constant times `σ √(v L / n) + v U L / n`, where `L = log max(e, A U / σ)`. This is the
constant-envelope form of the Chernozhukov–Chetverikov–Kato maximal inequality; the leading term
scales with the standard deviation `σ` rather than with the envelope.

## Main results

* `varianceAdaptiveExpectedMaximal_le` — the expected-supremum bound above, with the explicit
  (non-optimized) constant `varianceAdaptiveVCConstant = 16384`.
* `HasPolynomialL2Cover.varianceAdaptiveExpectedMaximal_le` — the same bound for a class carrying a
  uniform polynomial L² covering certificate, with some entropy constants `A`, `v`.
* `varianceAdaptiveRademacherComplexity_le` — the matching Rademacher-complexity bound, from which
  the expected-supremum bound follows by symmetrization.
* `vcEntropy_chaining_bound` — the countable chaining bound under the packaged hypothesis
  `HasVCUniformEntropy`.
* `hasCountableEmpiricalSupReduction_of_pointwise_dense` — an uncountable empirical supremum equals
  the supremum over a countable pointwise-dense subfamily.

Supporting pieces: the empirical covering hypothesis `HasPolynomialEmpiricalL2Cover` and the rate
`vcExpectedMaximalRate`, and the total-boundedness and covering-number consequences of that
hypothesis used by Dudley's entropy integral. This file only gathers those modules.
-/
