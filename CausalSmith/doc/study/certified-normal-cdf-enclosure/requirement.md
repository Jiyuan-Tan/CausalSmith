# Substrate requirement: certified-normal-cdf-enclosure

## Goal
Build reusable Lean substrate for scalable, proof-producing rational enclosures of the standard normal CDF.

## Provides (API contract)
- A sound rational enclosure interface for the standard normal CDF at rational endpoints.
- The checker must validate caller-supplied cells of width `1e-12` at rational endpoints with absolute value up to `193/5`.
- Verification must be polynomial or logarithmic in the requested precision, not use a uniform mesh whose node count is proportional to the reciprocal target width.
- Central-range enclosures using symmetry and a rational alternating or power-series integral enclosure with an exact remainder bound, including range splitting or argument reduction where needed.
- Mills-ratio tail enclosures for `|x| > 8`, reduced to finite exponential-series checks and rational bounds for `1 / sqrt (2 * pi)`.

## Statement / milestones
For a rational endpoint `q` and caller-supplied rational lower and upper bounds, provide a checkable certificate whose soundness theorem proves that the standard normal CDF at `q` lies in that interval. Provide separate composable central-range and tail certificates, symmetry transport between signs, and a top-level checker that selects and verifies the appropriate certificate.

The resulting API must be suitable for certifying transition probabilities formed as differences of normal-CDF values. Endpoint tables are supplied by callers; the reusable checker validates them rather than generating or trusting them.

## Standard reference
Classical power-series enclosures for the Gaussian integral, symmetry of the standard normal CDF, Mills-ratio tail inequalities, and rigorous rational enclosures of the exponential and normalization constant.

## Intended reuse
Finite-state probabilistic, causal, and sequential-decision models whose transition probabilities are differences of Gaussian CDF values and need machine-checkable high-precision certificates. The immediate consumer is the generic finite-Markov expectation substrate under `Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation`, but this study must be independently reusable.

## May assume / must derive
May assume caller-supplied rational endpoints, rational proposed enclosure values, and finite exact certificate data. Reuse Causalean's certified rational arithmetic and scalar exponential enclosure facilities where applicable. Must derive soundness of central-series remainders, symmetry transport, Mills-tail bounds, exponential enclosures, rational normalization-constant bounds, and the top-level normal-CDF enclosure.

## Non-goals (optional)
Do not generate the caller's 1422-entry endpoint table or any transition matrix, recurrence vector, stationary-distribution calculation, reward expectation, or paper-specific bias expression. Do not trust floating-point values or external computation. Do not import any CausalSmith research module. Do not duplicate the existing generic finite-Markov matrix/vector and stationary-expectation modules. Do not treat the existing uniform-mesh quadrature interface as sufficient for high-precision cells; it may remain only as an optional coarse fallback.

## Known building blocks (optional)
Deduplicate against `Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation`, especially its normal-CDF interface and certified rational/exponential components. Extend or supplement the narrowest existing topical module rather than replacing the seven already-promoted generic modules.
